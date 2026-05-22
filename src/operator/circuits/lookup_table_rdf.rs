use std::marker::PhantomData;
use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*, poly::Rotation};

#[derive(Debug, Clone)]
pub struct RdfConfig {
    pub advice: [Column<Advice>; 2], 
    pub predicate_fixed: Column<Fixed>,
    pub q_lookup: Selector, // Selector to enable/disable lookup per row
    pub table_s: TableColumn,
    pub table_p: TableColumn,
    pub table_o: TableColumn,
}

pub struct RdfChip<F: Field> {
    config: RdfConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> RdfChip<F> {
    pub fn construct(config: RdfConfig) -> Self {
        Self { config, _marker: PhantomData }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2],
        predicate_fixed: Column<Fixed>,
    ) -> RdfConfig {
        let q_lookup = meta.complex_selector();
        let table_s = meta.lookup_table_column();
        let table_p = meta.lookup_table_column();
        let table_o = meta.lookup_table_column();

        // The lookup only triggers when q_lookup is active (1)
        meta.lookup("rdf_triple_exists", |meta| {
            let q = meta.query_selector(q_lookup);
            let s = meta.query_advice(advice[0], Rotation::cur());
            let p = meta.query_fixed(predicate_fixed, Rotation::cur());
            let o = meta.query_advice(advice[1], Rotation::cur());
            
            // If q is 0, we neutralize the lookup by mapping it to a known table entry
            // Halo2 lookup arguments natively handle this via selectors.
            vec![
                (q.clone() * s, table_s), 
                (q.clone() * p, table_p), 
                (q * o, table_o)
            ]
        });

        RdfConfig { advice, predicate_fixed, q_lookup, table_s, table_p, table_o }
    }

    pub fn load_table(&self, mut layouter: impl Layouter<F>, triples: &[(F, F, F)]) -> Result<(), Error> {
        layouter.assign_table(|| "rdf table", |mut table| {
            // First row acts as the "neutral" target for disabled lookups
            table.assign_cell(|| "s", self.config.table_s, 0, || Value::known(F::ZERO))?;
            table.assign_cell(|| "p", self.config.table_p, 0, || Value::known(F::ZERO))?;
            table.assign_cell(|| "o", self.config.table_o, 0, || Value::known(F::ZERO))?;

            for (idx, (s, p, o)) in triples.iter().enumerate() {
                let row = idx + 1;
                table.assign_cell(|| "s", self.config.table_s, row, || Value::known(*s))?;
                table.assign_cell(|| "p", self.config.table_p, row, || Value::known(*p))?;
                table.assign_cell(|| "o", self.config.table_o, row, || Value::known(*o))?;
            }
            Ok(())
        })
    }
}

#[derive(Default)]
struct RdfCircuit<F: Field> {
    pub all_triples: Vec<(F, F, F)>,
    pub job_predicate: F,
}

impl<F: Field> Circuit<F> for RdfCircuit<F> {
    type Config = RdfConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self { Self::default() }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let predicate_fixed = meta.fixed_column();
        RdfChip::configure(meta, advice, predicate_fixed)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = RdfChip::construct(config.clone());
        chip.load_table(layouter.namespace(|| "load table"), &self.all_triples)?;

        layouter.assign_region(|| "scan results", |mut region| {
            let mut row = 0;
            for (s, p, o) in &self.all_triples {
                if *p == self.job_predicate {
                    config.q_lookup.enable(&mut region, row)?; // Enable lookup for this row
                    region.assign_advice(|| "s", config.advice[0], row, || Value::known(*s))?;
                    region.assign_fixed(|| "p", config.predicate_fixed, row, || Value::known(*p))?;
                    region.assign_advice(|| "o", config.advice[1], row, || Value::known(*o))?;
                    row += 1;
                }
            }
            Ok(())
        })
    }
    
    type Params = ();
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
    use std::time::Instant;
    use rand::prelude::*;
    use halo2_proofs::halo2curves::ff::PrimeField;

    #[test]
    fn benchmark_sorting_vs_unsorted() {
        let k = 18;
        let job_predicate = Fr::from(100);
        let mut rng = thread_rng();

        // 1. Get RDF triples
        let mut triples: Vec<(Fr, Fr, Fr)> = (0..250000)
            .map(|_| {
                (
                    Fr::from(rng.gen_range(0..1000)),
                    Fr::from(rng.gen_range(95..105)),
                    Fr::from(rng.gen_range(0..1000)),
                )
            })
            .collect();

        // CASE A: Unsorted
        let start_unsorted = Instant::now();
        let circuit_unsorted = RdfCircuit {
            all_triples: triples.clone(),
            job_predicate,
        };
        let prover_unsorted = MockProver::run(k, &circuit_unsorted, vec![]).unwrap();
        let proving_unsorted = start_unsorted.elapsed();
        prover_unsorted.assert_satisfied();
        let duration_unsorted = start_unsorted.elapsed();

        // CASE B: Sorted (Simulating an "indexed" approach)
        let start_sorted = Instant::now();
        // The overhead: Sorting the data before synthesis
        triples.sort_by(|a, b| a.1.to_repr().cmp(&b.1.to_repr())); 
        
        let start_single_proving = Instant::now();
        let circuit_sorted = RdfCircuit {
            all_triples: triples,
            job_predicate,
        };
        let prover_sorted = MockProver::run(k, &circuit_sorted, vec![]).unwrap();
        let proving_sorted = start_single_proving.elapsed();
        prover_sorted.assert_satisfied();
        let duration_sorted = start_sorted.elapsed();

        println!("\n--- Performance Results ---");
        println!("Proving Time (Unsorted): {:?}", proving_unsorted);
        println!("Unsorted Total Time: {:?}", duration_unsorted);
        println!("Proving Time (Sorted):   {:?}", proving_sorted);
        println!("Sorted Total Time:   {:?}", duration_sorted);
        
        if duration_sorted > duration_unsorted {
            println!("Result: Sorting increased total time due to preprocessing overhead!");
        }
    }
}
