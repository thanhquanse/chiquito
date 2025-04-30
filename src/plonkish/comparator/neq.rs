use halo2_proofs::halo2curves::ff::PrimeField;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};
use crate::operator::chips::less_than::{LtChip, LtConfig, LtInstruction};
use std::marker::PhantomData;
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::pasta::Fp;

const NUM_BYTES: usize = 10;

pub trait Field: PrimeField<Repr = [u8; 32]> {}

impl<F> Field for F where F: PrimeField<Repr = [u8; 32]> {}

#[derive(Clone, Debug)]
pub struct LtComparisonCircuitConfig<F: Field + Ord> {
    q_enable: Selector,

    a: Column<Advice>,
    b: Column<Advice>,
    check: Column<Advice>,

    compare_condition: Vec<LtConfig<F, NUM_BYTES>>,
    instance: Column<Instance>,
    instance_test: Column<Advice>
}

#[derive(Debug, Clone)]
pub struct LtComparisonChip<F: Field + Ord> {
    config: LtComparisonCircuitConfig<F>
}

impl<F: Field + Ord> LtComparisonChip<F> {
    pub fn construct(config: LtComparisonCircuitConfig<F>) -> Self {
        Self { config }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> LtComparisonCircuitConfig<F> {
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        let instance_test = meta.advice_column();
        meta.enable_equality(instance_test);

        let q_enable = meta.selector();
        let check = meta.advice_column();
        let a = meta.advice_column();
        let b = meta.advice_column();

        // a <= b
        let mut compare_condition = Vec::new();
        let config_lt = LtChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| meta.query_advice(a, Rotation::cur()),
            |meta| meta.query_advice(b, Rotation::cur()),
        );

        meta.create_gate("verify a < b", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let check = meta.query_advice(check, Rotation::cur());
            vec![q_enable * (config_lt.clone().is_lt(meta, None) - check)]
        });

        compare_condition.push(config_lt);

        LtComparisonCircuitConfig {
            q_enable,
            check,
            a,
            b,
            compare_condition,
            instance,
            instance_test
        }
    }

    pub fn assign(
        &self,
        layouter: &mut impl Layouter<F>,

        a: u64,
        b: u64
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut compare_chip = Vec::new();

        for i in 0..self.config.compare_condition.len() {
            let chip = LtChip::construct(self.config.compare_condition[i].clone());
            chip.load(layouter)?;
            compare_chip.push(chip);
        }

        let mut check = false;
        if a <= b {
            check = true;
        }

        layouter.assign_region(
            || "witness",
            |mut region| {
                let _ = region.assign_advice(|| "a_value", self.config.a, 0, || Value::known(F::from(a)));
                let _ = region.assign_advice(|| "b_value", self.config.b, 0, || Value::known(F::from(b)));
                let _ = region.assign_advice(|| "check_value", self.config.check, 0, || Value::known(F::from(check as u64)));

                self.config.q_enable.enable(&mut region, 0)?;
                compare_chip[0].assign(
                    // a <= b
                    &mut region,
                    0,
                    Value::known(F::from(a)),
                    Value::known(F::from(b))
                )?;
                let out = region.assign_advice(
                    || "instance_test",
                    self.config.instance_test,
                    0,
                    || Value::known(F::from(1)),
                )?;
                Ok(out)
            }
        )
    }

    pub fn expose_public(
        &self,
        layouter: &mut impl Layouter<F>,
        cell: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

struct LtComparisonCircuit<F> {
    a: u64,
    b: u64,

    _marker: PhantomData<F>
}

impl<F: Copy + Default> Default for LtComparisonCircuit<F> {
    fn default() -> Self {
        Self {
            a: 0,
            b: 0,
            _marker: PhantomData,
        }
    }
}

impl<F: Field + Ord> Circuit<F> for LtComparisonCircuit<F> {
    type Config = LtComparisonCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        LtComparisonChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let lt_chip = LtComparisonChip::construct(config);

        let out_cells = lt_chip.assign(
            &mut layouter,
            self.a.clone(),
            self.b.clone()
        )?;

        lt_chip.expose_public(&mut layouter, out_cells, 0)?;

        Ok(())
    }
}

pub fn is_not_equal(a: u64, b: u64) -> u32 {
    let mut final_rs = 0;
    let lt_circuit_a_b = LtComparisonCircuit::<Fp> {
        a,
        b,
        _marker: PhantomData,
    };

    let public_input = vec![Fp::from(1)];

    let prover_a_b = MockProver::run(19, &lt_circuit_a_b, vec![public_input]).unwrap();
    
    let result_a_b = prover_a_b.verify();
    println!("Verification a_b result: {:?}", result_a_b); // Debug log
    match result_a_b {
        Ok(()) => {
            println!("Verification succeeded");
            final_rs = 1;
        }
        Err(e) => {
            println!("Verification failed: {:?}", e);
        }
    }

    if final_rs == 0 {
        let lt_circuit_b_a = LtComparisonCircuit::<Fp> {
            b,
            a,
            _marker: PhantomData,
        };

        let public_input = vec![Fp::from(1)];

        let prover_b_a = MockProver::run(19, &lt_circuit_b_a, vec![public_input]).unwrap();
        
        let result_b_a = prover_b_a.verify();
        // println!("Verification b_a result: {:?}", result_b_a); // Debug log

        match result_b_a {
            Ok(()) => {
                // println!("Verification succeeded");
                final_rs = 1;
            }
            Err(e) => {
                println!("Verification failed: {:?}", e);
            }
        }
    }

    final_rs
}
