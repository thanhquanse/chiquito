use std::thread;
use std::collections::HashMap;

use crate::operator::chips::inclusion_check::{InclusionCheckChip, InclusionCheckConfig};

use halo2_proofs::halo2curves::ff::PrimeField;
use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*};
use halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::pasta::Fp};

#[derive(Clone)] // helps with some internal halo2 operations
                       // Circuit is now generic over the sizes of Table A and the number of inclusions from Table B.
                       // This makes the sizes fully dynamic — you specify them only when you create the circuit instance.
struct MyCircuit<F: PrimeField> {
    pub base_results_part1: Vec<Value<F>>,
    pub base_results_part2: Vec<Value<F>>,
    pub inclusion_indices: Vec<u16>,
    // Store sizes internally since we lost the const generics
    pub table_size: usize,
    pub num_inclusions: usize,
}

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
    type Config = InclusionCheckConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            base_results_part1: vec![Value::unknown(); self.table_size],
            base_results_part2: vec![Value::unknown(); self.table_size],
            inclusion_indices: vec![0; self.num_inclusions],
            table_size: self.table_size,
            num_inclusions: self.num_inclusions,
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
        let chip = InclusionCheckChip::<F>::construct(config);

        // Optimization: Use a HashSet for O(1) lookups instead of .contains() O(N)
        let inclusion_set: std::collections::HashSet<u16> = 
            self.inclusion_indices.iter().cloned().collect();

        for i in 0..self.table_size {
            if inclusion_set.contains(&(i as u16)) {
                let (username_cell, balance_cell) = chip.assign_inclusion_check_row(
                    layouter.namespace(|| format!("inclusion row {}", i)),
                    self.base_results_part1[i],
                    self.base_results_part2[i],
                )?;
                // If you need to expose public inputs, do it here using instance columns
            } else {
                chip.assign_generic_row(
                    layouter.namespace(|| format!("generic row {}", i)),
                    self.base_results_part1[i],
                    self.base_results_part2[i],
                )?;
            }
        }
        Ok(())
    }

    type Params = ();
}

pub fn _is_incl(base_results: Vec<Vec<u64>>, results: Vec<Vec<u64>>, k: u32) -> u32 {
    let table_size = base_results[0].len();
    let num_inclusions = results[0].len();

    // 1. Create a Lookup Map for Table A (base_results)
    // Key: (username, balance), Value: Index
    let mut base_map = HashMap::with_capacity(table_size);
    for i in 0..table_size {
        base_map.insert((base_results[0][i], base_results[1][i]), i as u16);
    }

    // 2. Efficiently find indices for Table B (results)
    let mut inclusion_indices = Vec::with_capacity(num_inclusions);
    for j in 0..num_inclusions {
        let key = (results[0][j], results[1][j]);
        let &index = base_map.get(&key).expect("Entry from results not found in base_results");
        inclusion_indices.push(index);
    }

    // 3. Prepare Circuit Witnesses (on the Heap)
    let base_results_part1: Vec<Value<Fp>> = base_results[0]
        .iter()
        .map(|&x| Value::known(Fp::from(x)))
        .collect();
    let base_results_part2: Vec<Value<Fp>> = base_results[1]
        .iter()
        .map(|&x| Value::known(Fp::from(x)))
        .collect();

    let circuit = MyCircuit {
        base_results_part1,
        base_results_part2,
        inclusion_indices,
        table_size,
        num_inclusions,
    };

    // 4. Public Inputs
    let public_input: Vec<Fp> = results[0]
        .iter()
        .zip(results[1].iter())
        .flat_map(|(&u, &b)| vec![Fp::from(u), Fp::from(b)])
        .collect();

    // 5. Run Prover
    // Note: For k=20, this will use ~32GB+ of RAM. 
    // If it crashes, check your system memory.
    let prover = MockProver::run(k, &circuit, vec![public_input])
        .expect("Failed to initialize MockProver");

    match prover.verify() {
        Ok(()) => 1,
        Err(e) => {
            println!("Verification failed: {:?}", e);
            0
        }
    }
}

pub fn is_incl(base_results: Vec<Vec<u64>>, results: Vec<Vec<u64>>, k: u32) -> u32 {
    let handle = thread::Builder::new()
        .stack_size(64 * 1024 * 1024 * 5)  // 64 MiB stack
        .spawn(move || -> Result<u32, Box<dyn std::error::Error + Send + Sync + 'static>> {
            // You can add some logging here if you want to see that the thread really starts
            let ok = _is_incl(base_results, results, k);
            Ok(ok)
        })
        .expect("Failed to spawn thread");

    match handle.join() {
        Ok(Ok(result)) => result,

        Ok(Err(e)) => panic!("Inner Result error: {}", e),

        Err(e) => {
            // Improved panic handling
            if let Some(s) = e.downcast_ref::<&'static str>() {
                panic!("Thread panicked with &str: {}", s);
            } else if let Some(s) = e.downcast_ref::<String>() {
                panic!("Thread panicked with String: {}", s);
            } else if let Some(boxed) = e.downcast_ref::<Box<dyn std::any::Any + Send>>() {
                // Sometimes the payload is nested
                println!("Thread panicked with Box<dyn Any + Send>: {:?}", boxed);
            } else {
                println!("Thread panicked with unknown payload: {:?}", e);
            }

            // Re-panic so the backtrace is shown (very useful!)
            std::panic::resume_unwind(e);
        }
    }
}