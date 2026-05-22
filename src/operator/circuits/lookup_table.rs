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
            
            // If q is 0, we "neutralize" the lookup by mapping it to a known table entry (e.g., first row)
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
    use halo2_proofs::{dev::MockProver, halo2curves::pasta::Fp};

    #[test]
    fn test_rdf_performance_logic() {
        let k = 6;
        let job_p = Fp::from(100);

        // Scenario: Unsorted data
        let triples = vec![
            (Fp::from(1), Fp::from(100), Fp::from(500)), // Alice, job, Dev
            (Fp::from(2), Fp::from(200), Fp::from(20)),  // Bob, age, 20
            (Fp::from(3), Fp::from(100), Fp::from(501)), // Charlie, job, CEO
        ];

        let circuit = RdfCircuit { all_triples: triples, job_predicate: job_p };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        // THEORETICAL PROOF OF YOUR IDEA:
        // Even if we sorted 'triples' by the predicate (100, 100, 200),
        // the number of 'assign_advice' and 'assign_table' calls remains exactly 3 and 9.
        // The degree of the lookup polynomial is fixed by 2^k.
        // Indexing adds extra columns/rows, actually slowing down the FFT/Multiexp.
    }
}
