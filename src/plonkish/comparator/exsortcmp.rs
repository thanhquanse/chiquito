use halo2_proofs::{
    arithmetic::Field, circuit::*, dev::MockProver, halo2curves::bn256::Fr as Fp, plonk::*, poly::Rotation,
};

#[derive(Clone, Debug)]
struct SortCompareConfig {
    q_check: Selector,
    input_columns: Vec<Column<Advice>>,
    table_columns: Vec<Column<Advice>>,
}

#[derive(Default)]
struct MseqCircuit<F: Field> {
    pub input: Vec<Vec<F>>,
    pub table: Vec<Vec<F>>,
}

impl<F: Field> Circuit<F> for MseqCircuit<F> {
    type Config = SortCompareConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_check = meta.selector();
        let mut input_columns = Vec::new();
        let mut table_columns = Vec::new();

        // We assume a width of 2 columns based on your example
        for _ in 0..2 {
            input_columns.push(meta.advice_column());
            table_columns.push(meta.advice_column());
        }

        // The "Compare" gate: checks equality for every element in the row
        meta.create_gate("row_compare", |meta| {
            let q = meta.query_selector(q_check);
            let mut constraints = Vec::new();

            for i in 0..input_columns.len() {
                let a = meta.query_advice(input_columns[i], Rotation::cur());
                let b = meta.query_advice(table_columns[i], Rotation::cur());
                // Constraint: q * (a - b) == 0
                constraints.push(q.clone() * (a - b));
            }
            constraints
        });

        SortCompareConfig {
            q_check,
            input_columns,
            table_columns,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "witness_row_by_row",
            |mut region| {
                for i in 0..self.input.len() {
                    config.q_check.enable(&mut region, i)?;

                    for j in 0..config.input_columns.len() {
                        region.assign_advice(
                            || format!("input row {} col {}", i, j),
                            config.input_columns[j],
                            i,
                            || Value::known(self.input[i][j]),
                        )?;
                        region.assign_advice(
                            || format!("table row {} col {}", i, j),
                            config.table_columns[j],
                            i,
                            || Value::known(self.table[i][j]),
                        )?;
                    }
                }
                Ok(())
            },
        )
    }
    
    type Params = ();
}

pub fn is_mseq_esortcmp(mut input: Vec<Vec<u64>>, mut table: Vec<Vec<u64>>, k: u32) -> u32 {
    // 1. Sort the multisets before feeding them to the circuit
    input.sort();
    table.sort();

    // 2. Convert to Field elements
    let _input: Vec<Vec<Fp>> = input.into_iter()
            .map(|row| row.into_iter().map(|v| Fp::from(v)).collect())
            .collect();
    let _table: Vec<Vec<Fp>> = table.into_iter()
            .map(|row| row.into_iter().map(|v| Fp::from(v)).collect())
            .collect();

    let circuit = MseqCircuit::<Fp> {
        input: _input,
        table: _table
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    let result = prover.verify();
    
    match result {
        Ok(()) => {
            println!("Sort & Compare verification succeeded");
            1
        }
        Err(e) => {
            println!("Sort & Compare verification failed: {:?}", e);
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sort_compare_success() {
        let k = 4;
        let input = vec![vec![1, 2], vec![3, 4], vec![3, 4]];
        let table = vec![vec![3, 4], vec![1, 2], vec![3, 4]];

        assert_eq!(is_mseq_esortcmp(input, table, k), 1);
    }

    #[test]
    fn test_sort_compare_failure() {
        let k = 4;
        let input = vec![vec![1, 2]];
        let table = vec![vec![9, 9]];
        assert_eq!(is_mseq_esortcmp(input, table, k), 0);
    }
}
