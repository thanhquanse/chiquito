use std::result;

use crate::operator::chips::inclusion_check::{InclusionCheckChip, InclusionCheckConfig};

use halo2_proofs::halo2curves::ff::PrimeField;
use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*};
use halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::pasta::Fp};

const TABLE_SIZE: usize = 400000;
const NUM_INCLUSIONS: usize = 400000;

#[derive(Clone, Copy)] // helps with some internal halo2 operations
                       // Circuit is now generic over the sizes of Table A and the number of inclusions from Table B.
                       // This makes the sizes fully dynamic — you specify them only when you create the circuit instance.
struct MyCircuit<F, const TABLESIZE: usize, const NUM_INCLUSIONS: usize> {
    pub base_results_part1: [Value<F>; TABLESIZE],
    pub base_results_part2: [Value<F>; TABLESIZE],
    pub inclusion_indices: [u16; NUM_INCLUSIONS],
}

impl<F: PrimeField, const TABLESIZE: usize, const NUM_INCLUSIONS: usize> Circuit<F>
    for MyCircuit<F, TABLESIZE, NUM_INCLUSIONS>
{
    type Config = InclusionCheckConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            // All private witness values become "unknown" (standard halo2 pattern)
            base_results_part1: [Value::unknown(); TABLESIZE],
            base_results_part2: [Value::unknown(); TABLESIZE],
            // inclusion_indices can be zero-filled — they are only used when a real witness is provided
            inclusion_indices: [0; NUM_INCLUSIONS],
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let col_username = meta.advice_column();
        let col_balance = meta.advice_column();
        let instance = meta.instance_column();

        InclusionCheckChip::configure(meta, [col_username, col_balance], instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // We create a new instance of chip using the config passed as input
        let chip = InclusionCheckChip::<F>::construct(config);

        let mut row_cells: Vec<Option<(AssignedCell<F, F>, AssignedCell<F, F>)>> =
            vec![None; TABLESIZE];

        // loop over the usernames array and assign the rows
        for _i in 0..self.base_results_part1.len() {
            // if row is equal to the inclusion index, assign the value using the assign_inclusion_check_row function
            // else assign the value using the assign_generic_row function
            if self.inclusion_indices.contains(&(_i as u16)) {
                // for _j in 0..self.inclusion_indices.len() {
                // if (_i as u8) == (self.inclusion_indices[_j] as u8) {
                // println!(
                //     "Values: {} - {}: {:?} - {:?}",
                //     _i, self.inclusion_indices[_i], self.usernames[_i], self.balances[_i]
                // );
                // extract username and balances cell from here!
                let (username_cell, balance_cell) = chip.assign_inclusion_check_row(
                    layouter.namespace(|| "inclusion row"),
                    self.base_results_part1[_i],
                    self.base_results_part2[_i],
                )?;

                // expose the public values
                row_cells[_i] = Some((username_cell, balance_cell));
                // chip.expose_public(
                //     layouter.namespace(|| "expose public"),
                //     &username_cell,
                //     &balance_cell,
                // )?;
                // }
                // }
                // } else {
                //     chip.assign_generic_row(
                //         layouter.namespace(|| "generic row"),
                //         self.usernames[_i],
                //         self.balances[_i],
                //     )?;
                // }
                // }
            } else {
                chip.assign_generic_row(
                    layouter.namespace(|| "generic row"),
                    self.base_results_part1[_i],
                    self.base_results_part2[_i],
                )?;
            }
        }
        Ok(())
    }
    
    type Params = ();
}

pub fn is_incl(base_results: Vec<Vec<u64>>, results: Vec<Vec<u64>>, k: u32) -> u32 {
    if base_results[0].len() != TABLE_SIZE {
        panic!("Fatal Error: Expected base_results {} elements, but found {}.", TABLE_SIZE, base_results[0].len());
    }

    let _base_results_part1_tmp: [u64; TABLE_SIZE] = base_results[0].clone()
        .try_into()
        .expect("Length of base_results[0] must match TABLE_SIZE");

    let _base_results_part2_tmp: [u64; TABLE_SIZE] = base_results[1].clone()
        .try_into()
        .expect("Length of base_results[1] must match TABLE_SIZE");


    let base_results_part1: [Value<Fp>; TABLE_SIZE] = _base_results_part1_tmp.map(|x| {
        Value::known(Fp::from(x))
    });
    let base_results_part2: [Value<Fp>; TABLE_SIZE] = _base_results_part2_tmp.map(|x| {
        Value::known(Fp::from(x))
    });

    if results[0].len() != TABLE_SIZE {
        panic!("Fatal Error: Expected results {} elements, but found {}.", TABLE_SIZE, results[0].len());
    }

    let _results_part1_tmp: [u64; TABLE_SIZE] = results[0].clone()
        .try_into()
        .expect("Length of results[0] must match TABLE_SIZE");

    let _results_part2_tmp: [u64; TABLE_SIZE] = results[1].clone()
        .try_into()
        .expect("Length of results[1] must match TABLE_SIZE");

    // let results_part1: [Value<Fp>; TABLE_SIZE] = _results_part1_tmp.map(|x| {
    //     Value::known(Fp::from(x))
    // });
    // let results_part2: [Value<Fp>; TABLE_SIZE] = _results_part2_tmp.map(|x| {
    //     Value::known(Fp::from(x))
    // });

    let mut inclusion_indices: [u16; NUM_INCLUSIONS] = [0; NUM_INCLUSIONS];

    for (j, (&b_user, &b_bal)) in _results_part1_tmp
            .iter()
            .zip(_results_part2_tmp.iter())
            .enumerate()
        {
            let mut found = false;
            for i in 0..TABLE_SIZE {
                if _base_results_part1_tmp[i] == b_user && _base_results_part2_tmp[i] == b_bal {
                    // println!("Value: {}", i);
                    inclusion_indices[j] = i as u16;
                    found = true;
                    break;
                }
            }
            assert!(
                found,
                "Entry from table B not found in table A at position {}",
                j
            );
        }

    let circuit = MyCircuit::<Fp, TABLE_SIZE, NUM_INCLUSIONS> {
        base_results_part1,
        base_results_part2,
        inclusion_indices,
    };

    // Public inputs = padded Table B in the same order as inclusion_indices
    let public_input_valid: Vec<Fp> = _results_part1_tmp
        .into_iter()
        .zip(_results_part2_tmp.into_iter())
        .flat_map(|(u, b)| vec![Fp::from(u), Fp::from(b)])
        .collect();

    let prover = MockProver::run(k, &circuit, vec![public_input_valid]).unwrap();
    // prover.assert_satisfied();

    let result = prover.verify();
    println!("Verification result: {:?}", result); // Debug log
    match result {
        Ok(()) => {
            // println!("Verification succeeded");
            1
        }
        Err(e) => {
            println!("Verification failed: {:?}", e);
            0
        }
    }
}