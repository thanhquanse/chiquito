use crate::operator::chips::permutation_any::{PermAnyChip, PermAnyConfig};
use halo2_proofs::{
    arithmetic::Field, circuit::*, dev::MockProver, halo2curves::bn256::Fr as Fp, plonk::*,
};

#[derive(Default)]
struct MseqCircuit<F: Field> {
    pub input: Vec<Vec<F>>,
    pub table: Vec<Vec<F>>,
}

impl<F: Field> Circuit<F> for MseqCircuit<F> {
    type Config = PermAnyConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // You need TWO selectors because your Chip::configure asks for q_perm1 and q_perm2
        let q_perm1 = meta.complex_selector();
        let q_perm2 = meta.complex_selector();

        let mut input_columns = Vec::new();
        let mut table_columns = Vec::new();

        // Match the width of your data (2 columns based on your test input)
        for _ in 0..2 {
            input_columns.push(meta.advice_column());
            table_columns.push(meta.advice_column());
        }

        // Return the config from the chip
        PermAnyChip::configure(meta, q_perm1, q_perm2, input_columns, table_columns)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = PermAnyChip::<F>::construct(config.clone());

        layouter.assign_region(
            || "witness",
            |mut region| {
                // Enable selectors for each row of data
                for i in 0..self.input.len() {
                    config.q_perm1.enable(&mut region, i)?;
                }
                for i in 0..self.table.len() {
                    config.q_perm2.enable(&mut region, i)?;
                }

                // Call assign1 (Note: ensure row counts match for shuffle)
                chip.assign1(&mut region, self.input.clone(), self.table.clone())?;
                Ok(())
            },
        )
    }
    
    type Params = ();
    
    fn params(&self) -> Self::Params {
        Self::Params::default()
    }
    
    fn configure_with_params(
        meta: &mut ConstraintSystem<F>,
        _params: Self::Params,
    ) -> Self::Config {
        Self::configure(meta)
    }
}

// fn convert_to_field<F: Field>(input: Vec<Vec<u64>>) -> Vec<Vec<F>> {
//     input
//         .into_iter()
//             .map(|row| row.into_iter().map(|v| Fp::from(v)).collect())
//             .collect();
// }

pub fn is_mseq(input: Vec<Vec<u64>>, table: Vec<Vec<u64>>, k: u32) -> u32 {
    let _input  = input.into_iter()
            .map(|row| row.into_iter().map(|v| Fp::from(v)).collect())
            .collect();
    let _table = table.into_iter()
            .map(|row| row.into_iter().map(|v| Fp::from(v)).collect())
            .collect();

    let circuit = MseqCircuit::<Fp> {
        input: _input,
        table: _table
    };

    let public_input = vec![];

    let prover = MockProver::run(k, &circuit, public_input).unwrap();
    
    let result = prover.verify();
    // println!("Verification result: {:?}", result); // Debug log
    match result {
        Ok(()) => {
            println!("Verification succeeded");
            1
        }
        Err(e) => {
            println!("Multiset equality with permutation verification failed: {:?}", e);
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_perm_success() {
        let k = 4;

        let input: Vec<Vec<u64>> = vec![
            vec![1, 2],
            vec![3, 4],
            vec![3, 4],
        ];

        let table: Vec<Vec<u64>> = vec![
            vec![3, 4],
            vec![1, 2],
            vec![3, 4],
        ];

        is_mseq(input.clone(), table.clone(), k);

        let _input  = input.into_iter()
            .map(|row| row.into_iter().map(|v| Fp::from(v)).collect())
            .collect();
        let _table = table.into_iter()
            .map(|row| row.into_iter().map(|v| Fp::from(v)).collect())
            .collect();

        let circuit = MseqCircuit::<Fp> { input: _input, table: _table };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_perm_failure() {
        let k = 4;
        let input = vec![vec![Fp::from(1), Fp::from(2)]];
        let table = vec![vec![Fp::from(9), Fp::from(9)]]; // Different values

        let circuit = MseqCircuit::<Fp> { input, table };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
}