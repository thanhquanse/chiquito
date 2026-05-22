use halo2_proofs::halo2curves::ff::PrimeField;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};
use crate::operator::chips::lessthan_or_equal_generic::{
    LtEqGenericChip, LtEqGenericConfig, LtEqGenericInstruction
};
use std::marker::PhantomData;
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::pasta::Fp;

const NUM_BYTES: usize = 5;

pub trait Field: PrimeField<Repr = [u8; 32]> {}

impl<F> Field for F where F: PrimeField<Repr = [u8; 32]> {}

#[derive(Clone, Debug)]
pub struct MultisetEqualityConfig<F: Field + Ord> {
    q_enable: Selector,
    q_sort: Selector,       // Only enabled for rows > 0

    a: Column<Advice>,
    b: Column<Advice>,
    check: Column<Advice>,
    a_prev: Column<Advice>,
    b_prev: Column<Advice>,

    sort_check_a: Vec<LtEqGenericConfig<F, NUM_BYTES>>,
    sort_check_b: Vec<LtEqGenericConfig<F, NUM_BYTES>>,
    eq_check_a_to_b: Vec<LtEqGenericConfig<F, NUM_BYTES>>,
    eq_check_b_to_a: Vec<LtEqGenericConfig<F, NUM_BYTES>>,

    instance: Column<Instance>,
    instance_test: Column<Advice>,
}

#[derive(Debug, Clone)]
pub struct MultisetEqualityChip<F: Field + Ord> {
    config: MultisetEqualityConfig<F>,
}

impl<F: Field + Ord> MultisetEqualityChip<F> {
    pub fn construct(config: MultisetEqualityConfig<F>) -> Self {
        Self { config }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MultisetEqualityConfig<F> {
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        
        let instance_test = meta.advice_column();
        meta.enable_equality(instance_test);

        let q_enable = meta.selector();
        let q_sort = meta.selector();
        
        let check = meta.advice_column();
        meta.enable_equality(check);

        let a = meta.advice_column();
        meta.enable_equality(a);

        let b = meta.advice_column();
        meta.enable_equality(b);

        let a_prev = meta.advice_column();
        meta.enable_equality(a_prev);

        let b_prev = meta.advice_column();
        meta.enable_equality(b_prev);

        // Sorting check for multiset1: uses q_sort
        let mut sort_check_a = Vec::new();
        let config_sort_a = LtEqGenericChip::configure(
            meta,
            |meta| meta.query_selector(q_sort),
            |meta| vec![meta.query_advice(a_prev, Rotation::cur())],
            |meta| vec![meta.query_advice(a, Rotation::cur())],
        );
        sort_check_a.push(config_sort_a);

        // Sorting check for multiset2: uses q_sort
        let mut sort_check_b = Vec::new();
        let config_sort_b = LtEqGenericChip::configure(
            meta,
            |meta| meta.query_selector(q_sort),
            |meta| vec![meta.query_advice(b_prev, Rotation::cur())],
            |meta| vec![meta.query_advice(b, Rotation::cur())],
        );
        sort_check_b.push(config_sort_b);

        // Equality check: a <= b - uses q_enable (all rows)
        let mut eq_check_a_to_b = Vec::new();
        let config_eq_ab = LtEqGenericChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| vec![meta.query_advice(a, Rotation::cur())],
            |meta| vec![meta.query_advice(b, Rotation::cur())],
        );
        eq_check_a_to_b.push(config_eq_ab.clone());

        // Equality check: b <= a - uses q_enable (all rows)
        let mut eq_check_b_to_a = Vec::new();
        let config_eq_ba = LtEqGenericChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| vec![meta.query_advice(b, Rotation::cur())],
            |meta| vec![meta.query_advice(a, Rotation::cur())],
        );
        eq_check_b_to_a.push(config_eq_ba);

        // Gate: check = (a <= b) AND (b <= a)
        meta.create_gate("verify equality", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let check = meta.query_advice(check, Rotation::cur());
            let is_ab = config_eq_ab.clone().is_lt(meta, None);
            let is_ba = config_eq_ba.is_lt(meta, None);
            vec![q_enable * (is_ab * is_ba - check)]
        });

        MultisetEqualityConfig {
            q_enable, q_sort, check, a, b, a_prev, b_prev,
            sort_check_a, sort_check_b,
            eq_check_a_to_b, eq_check_b_to_a,
            instance, instance_test,
        }
    }

    pub fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        multiset1: Vec<Vec<u64>>,
        multiset2: Vec<Vec<u64>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut flat1: Vec<u64> = multiset1.into_iter().flatten().collect();
        let mut flat2: Vec<u64> = multiset2.into_iter().flatten().collect();

        flat1.sort();
        flat2.sort();

        let len1 = flat1.len();
        let len2 = flat2.len();

        if len1 != len2 {
            return layouter.assign_region(
                || "multiset length mismatch",
                |mut region| {
                    let cell = region.assign_advice(
                        || "failure", self.config.instance_test, 0,
                        || Value::known(F::ZERO),
                    )?;
                    Ok(cell)
                },
            );
        }

        let n = len1;
        if n == 0 {
            return layouter.assign_region(
                || "empty multisets",
                |mut region| {
                    let cell = region.assign_advice(
                        || "success", self.config.instance_test, 0,
                        || Value::known(F::ONE),
                    )?;
                    Ok(cell)
                },
            );
        }

        let sort_chip_a = LtEqGenericChip::construct(self.config.sort_check_a[0].clone());
        let sort_chip_b = LtEqGenericChip::construct(self.config.sort_check_b[0].clone());
        let eq_chip_ab = LtEqGenericChip::construct(self.config.eq_check_a_to_b[0].clone());
        let eq_chip_ba = LtEqGenericChip::construct(self.config.eq_check_b_to_a[0].clone());

        sort_chip_a.load(layouter)?;
        sort_chip_b.load(layouter)?;
        eq_chip_ab.load(layouter)?;
        eq_chip_ba.load(layouter)?;

        let mut final_cell: Option<AssignedCell<F, F>> = None;

        layouter.assign_region(
            || "multiset equality witness",
            |mut region| {
                for i in 0..n {
                    let a_val = F::from(flat1[i]);
                    let b_val = F::from(flat2[i]);
                    let is_equal = flat1[i] == flat2[i];
                    let check_val = F::from(is_equal as u64);

                    region.assign_advice(
                        || format!("a[{}]", i), self.config.a, i,
                        || Value::known(a_val),
                    )?;
                    region.assign_advice(
                        || format!("b[{}]", i), self.config.b, i,
                        || Value::known(b_val),
                    )?;
                    let check_cell = region.assign_advice(
                        || format!("check[{}]", i), self.config.check, i,
                        || Value::known(check_val),
                    )?;

                    if i > 0 {
                        let a_prev_val = F::from(flat1[i - 1]);
                        let b_prev_val = F::from(flat2[i - 1]);

                        region.assign_advice(
                            || format!("a_prev[{}]", i), self.config.a_prev, i,
                            || Value::known(a_prev_val),
                        )?;
                        region.assign_advice(
                            || format!("b_prev[{}]", i), self.config.b_prev, i,
                            || Value::known(b_prev_val),
                        )?;

                        sort_chip_a.assign(&mut region, i, &[a_prev_val], &[a_val])?;
                        sort_chip_b.assign(&mut region, i, &[b_prev_val], &[b_val])?;
                        self.config.q_sort.enable(&mut region, i)?;
                    } else {
                        region.assign_advice(
                            || "a_prev[0]", self.config.a_prev, 0,
                            || Value::known(F::ZERO),
                        )?;
                        region.assign_advice(
                            || "b_prev[0]", self.config.b_prev, 0,
                            || Value::known(F::ZERO),
                        )?;
                        // NO sort_chip.assign at row 0
                        // NO q_sort.enable at row 0
                    }

                    eq_chip_ab.assign(&mut region, i, &[a_val], &[b_val])?;
                    eq_chip_ba.assign(&mut region, i, &[b_val], &[a_val])?;
                    self.config.q_enable.enable(&mut region, i)?;

                    final_cell = Some(check_cell);
                }
                Ok(final_cell.clone().unwrap())
            },
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

#[derive(Debug, Clone)]
struct MultisetEqualityCircuit<F: Field + Ord> {
    multiset1: Vec<Vec<u64>>,
    multiset2: Vec<Vec<u64>>,
    _marker: PhantomData<F>,
}

impl<F: Field + Ord + Copy + Default> Default for MultisetEqualityCircuit<F> {
    fn default() -> Self {
        Self { multiset1: vec![], multiset2: vec![], _marker: PhantomData }
    }
}

impl<F: Field + Ord + Copy + Default> Circuit<F> for MultisetEqualityCircuit<F> {
    type Config = MultisetEqualityConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self { Self::default() }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MultisetEqualityChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = MultisetEqualityChip::construct(config);
        let out_cells = chip.assign(
            &mut layouter,
            self.multiset1.clone(),
            self.multiset2.clone(),
        )?;
        chip.expose_public(&mut layouter, out_cells, 0)?;
        Ok(())
    }
}

pub fn is_mseq_nonperm(multiset1: Vec<Vec<u64>>, multiset2: Vec<Vec<u64>>, k: u32) -> u32 {
    let circuit = MultisetEqualityCircuit::<Fp> {
        multiset1, multiset2, _marker: PhantomData,
    };
    let public_input = vec![Fp::from(1)];
    let prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
    
    match prover.verify() {
        Ok(()) => { println!("MS-nonperm: Verification succeeded"); 1 },
        Err(e) => { println!("MS-nonperm: Verification failed: {:?}", e); 0 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_equal_multisets() {
        let m1 = vec![vec![2, 1, 2], vec![4, 5]];
        let m2 = vec![vec![5, 4], vec![1, 2, 2]];
        assert_eq!(is_mseq_nonperm(m1, m2, 10), 1);
    }

    #[test]
    fn test_unequal_multisets() {
        let m1 = vec![vec![1, 2, 3]];
        let m2 = vec![vec![1, 2, 4]];
        assert_eq!(is_mseq_nonperm(m1, m2, 10), 0);
    }

    #[test]
    fn test_different_lengths() {
        let m1 = vec![vec![1, 2]];
        let m2 = vec![vec![1, 2, 3]];
        assert_eq!(is_mseq_nonperm(m1, m2, 10), 0);
    }

    #[test]
    fn test_empty_multisets() {
        let m1: Vec<Vec<u64>> = vec![];
        let m2: Vec<Vec<u64>> = vec![];
        assert_eq!(is_mseq_nonperm(m1, m2, 10), 1);
    }
}