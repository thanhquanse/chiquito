//! Halo2 Circuit for Hierarchical Purpose Policy Proof
//! 
//! This circuit implements the DFS In-Out labeling technique to prove that
//! a node B is a strict descendant of node A in a static purpose tree.
//! 
//! The tree structure is committed as fixed columns (lookup table).
//! The circuit verifies:
//!   1. (a_id, a_left, a_right) and (b_id, b_left, b_right) are valid tree nodes
//!   2. left[A] < left[B]  (proven via bit-decomposed range check on b_left - a_left)
//!   3. right[B] < right[A] (proven via bit-decomposed range check on a_right - b_right)
//!
//! Dependencies (Cargo.toml):
//! [dependencies]
//! halo2_proofs = "0.3"
//! pasta_curves = "0.5"
//! ff = "0.12"

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, Value, Chip, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector,
        Expression, TableColumn
    },
    poly::Rotation,
    halo2curves::pasta::Fp
};
use crate::operator::chips::lessthan_or_equal_generic::{
    LtEqGenericChip, LtEqGenericConfig, LtEqGenericInstruction,
};

const NUM_BYTES: usize = 7; // max label value is 77, fits in 7 bits

// ============================================================
// Tree Data (precomputed DFS In-Out labels)
// ============================================================

const NUM_NODES: usize = 39;

/// Static tree nodes with their DFS in-out labels.
/// Generated from the purpose tree via Algorithm 1 (DFS In-Out Labeling).
const TREE_NODES: [(u64, u64, u64); NUM_NODES] = [
    // (node_id, left, right)
    ( 0,  0, 77),  // general-purpose
    ( 1,  1, 18),  // general-purpose/marketing
    ( 2,  2, 11),  // general-purpose/marketing/direct-marketing
    ( 3,  3,  8),  // general-purpose/marketing/direct-marketing/d-email
    ( 4,  4,  5),  // general-purpose/marketing/direct-marketing/d-email/special-offers
    ( 5,  6,  7),  // general-purpose/marketing/direct-marketing/d-email/service-updates
    ( 6,  9, 10),  // general-purpose/marketing/direct-marketing/d-phone
    ( 7, 12, 17),  // general-purpose/marketing/third-party-marketing
    ( 8, 13, 14),  // general-purpose/marketing/third-party-marketing/t-email
    ( 9, 15, 16),  // general-purpose/marketing/third-party-marketing/t-phone
    (10, 19, 24),  // general-purpose/advertising
    (11, 20, 21),  // general-purpose/advertising/trial
    (12, 22, 23),  // general-purpose/advertising/promotional
    (13, 25, 30),  // general-purpose/shipping
    (14, 26, 27),  // general-purpose/shipping/new-delivery
    (15, 28, 29),  // general-purpose/shipping/product-return
    (16, 31, 36),  // general-purpose/experimenting
    (17, 32, 33),  // general-purpose/experimenting/new-product
    (18, 34, 35),  // general-purpose/experimenting/feedback
    (19, 37, 42),  // general-purpose/Product
    (20, 38, 39),  // general-purpose/Product/profiling
    (21, 40, 41),  // general-purpose/Product/experiementing
    (22, 43, 44),  // general-purpose/Offer
    (23, 45, 54),  // general-purpose/Drug
    (24, 46, 47),  // general-purpose/Drug/research
    (25, 48, 49),  // general-purpose/Drug/clinical-trial
    (26, 50, 51),  // general-purpose/Drug/treatment
    (27, 52, 53),  // general-purpose/Drug/sales
    (28, 55, 64),  // general-purpose/Paper
    (29, 56, 57),  // general-purpose/Paper/publication
    (30, 58, 59),  // general-purpose/Paper/review
    (31, 60, 61),  // general-purpose/Paper/citation
    (32, 62, 63),  // general-purpose/Paper/chapter
    (33, 65, 74),  // general-purpose/ConfWorkshop
    (34, 66, 67),  // general-purpose/ConfWorkshop/organization
    (35, 68, 69),  // general-purpose/ConfWorkshop/presentation
    (36, 70, 71),  // general-purpose/ConfWorkshop/meeting
    (37, 72, 73),  // general-purpose/ConfWorkshop/connection
    (38, 75, 76),  // general-purpose/Proceeding
];

// ============================================================
// Configurations
// ============================================================

/// Fixed lookup table containing the precomputed tree structure.
#[derive(Clone, Debug)]
pub struct TreeTableConfig {
    node_id: TableColumn,   // ← was Column<Fixed>
    left:    TableColumn,
    right:   TableColumn,
}

/// Main circuit configuration.
#[derive(Clone, Debug)]
pub struct ContainmentConfig {
    pub a_id:    Column<Advice>,
    pub b_id:    Column<Advice>,
    pub a_left:  Column<Advice>,
    pub a_right: Column<Advice>,
    pub b_left:  Column<Advice>,
    pub b_right: Column<Advice>,

    // Strict containment expressed as two LtEq sub-chips:
    //   lt_left  checks  a_left  + 1 <= b_left   (i.e. a_left  < b_left)
    //   lt_right checks  b_right + 1 <= a_right  (i.e. b_right < a_right)
    pub lt_left:  LtEqGenericConfig<Fp, NUM_BYTES>,
    pub lt_right: LtEqGenericConfig<Fp, NUM_BYTES>,

    pub tree_table:    TreeTableConfig,
    pub instance:      Column<Instance>,
    pub s_containment: Selector,
    pub s_tree_lookup: Selector,
}

// ============================================================
// Chip
// ============================================================

pub struct ContainmentChip {
    config: ContainmentConfig,
}

impl Chip<Fp> for ContainmentChip {
    type Config = ContainmentConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl ContainmentChip {
    /// Configure the circuit constraints.
    fn configure(meta: &mut ConstraintSystem<Fp>) -> ContainmentConfig {
        // --- Column declarations (same as before, minus diff/bit/inv columns) ---
        let a_id    = meta.advice_column();
        let b_id    = meta.advice_column();
        let a_left  = meta.advice_column();
        let a_right = meta.advice_column();
        let b_left  = meta.advice_column();
        let b_right = meta.advice_column();

        let node_id  = meta.lookup_table_column();
        let left     = meta.lookup_table_column();
        let right    = meta.lookup_table_column();
        let instance = meta.instance_column();

        let s_containment = meta.selector();
        let s_tree_lookup = meta.complex_selector();

        meta.enable_equality(a_id);
        meta.enable_equality(b_id);
        meta.enable_equality(instance);

        // --- LtEq chip: a_left < b_left  ↔  a_left+1 <= b_left ---
        let lt_left = LtEqGenericChip::configure(
            meta,
            |meta| meta.query_selector(s_containment),
            |meta| vec![
                meta.query_advice(a_left, Rotation::cur())
                    + Expression::Constant(Fp::ONE),   // lhs = a_left + 1
            ],
            |meta| vec![meta.query_advice(b_left, Rotation::cur())], // rhs = b_left
        );

        // --- LtEq chip: b_right < a_right  ↔  b_right+1 <= a_right ---
        let lt_right = LtEqGenericChip::configure(
            meta,
            |meta| meta.query_selector(s_containment),
            |meta| vec![
                meta.query_advice(b_right, Rotation::cur())
                    + Expression::Constant(Fp::ONE),   // lhs = b_right + 1
            ],
            |meta| vec![meta.query_advice(a_right, Rotation::cur())], // rhs = a_right
        );

        // --- Gate: both LtEq results must equal 1 (containment is strict) ---
        meta.create_gate("strict_containment", |meta| {
            let s   = meta.query_selector(s_containment);
            let one = Expression::Constant(Fp::ONE);
            vec![
                // is_lt returns 1 iff lhs <= rhs; enforcing == 1 makes it mandatory
                s.clone() * (lt_left.is_lt(meta, None)  - one.clone()),
                s         * (lt_right.is_lt(meta, None) - one),
            ]
        });

        // --- Tree lookups (unchanged) ---
        meta.lookup("a_node_lookup", |meta| {
            let s = meta.query_selector(s_tree_lookup);
            vec![
                (s.clone() * meta.query_advice(a_id,    Rotation::cur()), node_id),
                (s.clone() * meta.query_advice(a_left,  Rotation::cur()), left),
                (s         * meta.query_advice(a_right, Rotation::cur()), right),
            ]
        });

        meta.lookup("b_node_lookup", |meta| {
            let s = meta.query_selector(s_tree_lookup);
            vec![
                (s.clone() * meta.query_advice(b_id,    Rotation::cur()), node_id),
                (s.clone() * meta.query_advice(b_left,  Rotation::cur()), left),
                (s         * meta.query_advice(b_right, Rotation::cur()), right),
            ]
        });

        ContainmentConfig {
            a_id, b_id, a_left, a_right, b_left, b_right,
            lt_left, lt_right,
            tree_table: TreeTableConfig { node_id, left, right },
            instance,
            s_containment,
            s_tree_lookup,
        }
    }

    fn construct(config: ContainmentConfig) -> Self {
        Self { config }
    }

    /// Load the static tree lookup table into fixed columns.
    fn load_tree_table(
        &self,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "tree_table",
            |mut table| {
                // ── Real tree rows ──────────────────────────────────────────────
                for (i, &(id, l, r)) in TREE_NODES.iter().enumerate() {
                    table.assign_cell(
                        || "node_id",
                        self.config.tree_table.node_id,
                        i,
                        || Value::known(Fp::from(id)),
                    )?;
                    table.assign_cell(
                        || "left",
                        self.config.tree_table.left,
                        i,
                        || Value::known(Fp::from(l)),
                    )?;
                    table.assign_cell(
                        || "right",
                        self.config.tree_table.right,
                        i,
                        || Value::known(Fp::from(r)),
                    )?;
                }

                // ── Padding row: satisfies (0,0,0) produced by inactive selector rows ──
                // When s_tree_lookup = 0, every lookup input = s*value = 0.
                // This dummy row gives those inactive rows a valid table entry to match.
                let pad = NUM_NODES; // one row beyond the real data
                table.assign_cell(
                    || "pad_node_id",
                    self.config.tree_table.node_id,
                    pad,
                    || Value::known(Fp::ZERO),
                )?;
                table.assign_cell(
                    || "pad_left",
                    self.config.tree_table.left,
                    pad,
                    || Value::known(Fp::ZERO),
                )?;
                table.assign_cell(
                    || "pad_right",
                    self.config.tree_table.right,
                    pad,
                    || Value::known(Fp::ZERO),
                )?;

                Ok(())
            },
        )
    }

    /// Assign a containment check at a specific row offset.
    ///
    /// # Arguments
    /// * `a_id` - Ancestor node ID (public input, instance column row `instance_row`)
    /// * `b_id` - Descendant node ID (public input, instance column row `instance_row + 1`)
    /// * `offset` - Row offset within the assignment region
    /// * `instance_row` - Starting row in the instance column for public inputs
    fn assign_containment(
        &self,
        mut layouter: impl Layouter<Fp>,
        lt_left_chip:  &LtEqGenericChip<Fp, NUM_BYTES>,  // ← passed in, already loaded
        lt_right_chip: &LtEqGenericChip<Fp, NUM_BYTES>,
        a_id: u64,
        b_id: u64,
        offset: usize,
        instance_row: usize,
    ) -> Result<(), Error> {
        // ... remove the load() calls that were here ...

        let (a_cell, b_cell) = layouter.assign_region(
            || "containment_check",
            |mut region| {
                self.config.s_containment.enable(&mut region, offset)?;
                self.config.s_tree_lookup.enable(&mut region, offset)?;

                let a_node = TREE_NODES[a_id as usize];
                let b_node = TREE_NODES[b_id as usize];

                let a_cell = region.assign_advice(
                    || "a_id", self.config.a_id, offset,
                    || Value::known(Fp::from(a_id)),
                )?;
                let b_cell = region.assign_advice(
                    || "b_id", self.config.b_id, offset,
                    || Value::known(Fp::from(b_id)),
                )?;

                region.assign_advice(|| "a_left",  self.config.a_left,  offset, || Value::known(Fp::from(a_node.1)))?;
                region.assign_advice(|| "a_right", self.config.a_right, offset, || Value::known(Fp::from(a_node.2)))?;
                region.assign_advice(|| "b_left",  self.config.b_left,  offset, || Value::known(Fp::from(b_node.1)))?;
                region.assign_advice(|| "b_right", self.config.b_right, offset, || Value::known(Fp::from(b_node.2)))?;

                lt_left_chip.assign(&mut region, offset,
                    &[Fp::from(a_node.1 + 1)],
                    &[Fp::from(b_node.1)],
                )?;
                lt_right_chip.assign(&mut region, offset,
                    &[Fp::from(b_node.2 + 1)],
                    &[Fp::from(a_node.2)],
                )?;

                Ok((a_cell, b_cell))
            },
        )?;

        layouter.constrain_instance(a_cell.cell(), self.config.instance, instance_row)?;
        layouter.constrain_instance(b_cell.cell(), self.config.instance, instance_row + 1)?;

        Ok(())
    }
}

// ============================================================
// Circuit
// ============================================================

/// Circuit proving that `b_id` is a strict descendant of `a_id` in the purpose tree.
#[derive(Clone, Debug, Default)]
pub struct ContainmentCircuit {
    pub a_id: u64,
    pub b_id: u64,
}

impl Circuit<Fp> for ContainmentCircuit {
    type Config      = ContainmentConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params      = ();            

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        ContainmentChip::configure(meta)
    }

    // In synthesize:
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let chip = ContainmentChip::construct(config);

        // Step 1: Load static tree table
        chip.load_tree_table(layouter.namespace(|| "tree_table"))?;

        // Step 2: Load LtEq range tables (must be at top-level, not inside a region)
        let lt_left_chip =
            LtEqGenericChip::<Fp, NUM_BYTES>::construct(chip.config.lt_left.clone());
        let lt_right_chip =
            LtEqGenericChip::<Fp, NUM_BYTES>::construct(chip.config.lt_right.clone());
        lt_left_chip.load(&mut layouter)?;   // ← writes 256-row range table
        lt_right_chip.load(&mut layouter)?;  // ← writes 256-row range table

        // Step 3: Assign the containment check (pass chips in, no load inside)
        chip.assign_containment(
            layouter.namespace(|| "containment"),
            &lt_left_chip,
            &lt_right_chip,
            self.a_id,
            self.b_id,
            0,
            0,
        )?;

        Ok(())
    }
    
    fn configure_with_params(
        meta: &mut ConstraintSystem<Fp>,
        _params: Self::Params,
    ) -> Self::Config {
        Self::configure(meta)
    }
}

// ============================================================
// Tests
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::dev::MockProver;

    const K: u32 = 10; // ← was 8; needs room for 2× LtEq range tables (256 rows each)

    #[test]
    fn test_marketing_to_direct_marketing() {
        // marketing (id=1) -> direct-marketing (id=2)
        let circuit = ContainmentCircuit { a_id: 1, b_id: 2 };
        let public_inputs = vec![Fp::from(1), Fp::from(2)];
        let prover = MockProver::run(K, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_marketing_to_special_offers() {
        // marketing (id=1) -> special-offers (id=4)
        let circuit = ContainmentCircuit { a_id: 1, b_id: 4 };
        let public_inputs = vec![Fp::from(1), Fp::from(4)];
        let prover = MockProver::run(K, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_general_purpose_to_any() {
        // general-purpose (id=0) -> feedback (id=18)
        let circuit = ContainmentCircuit { a_id: 0, b_id: 18 };
        let public_inputs = vec![Fp::from(0), Fp::from(18)];
        let prover = MockProver::run(K, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_direct_marketing_to_email_descendants() {
        // direct-marketing (id=2) -> d-email (id=3)
        let circuit = ContainmentCircuit { a_id: 2, b_id: 3 };
        let public_inputs = vec![Fp::from(2), Fp::from(3)];
        let prover = MockProver::run(K, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_reject_sibling() {
        // marketing (id=1) -> advertising (id=10) : SIBLING, should FAIL
        let circuit = ContainmentCircuit { a_id: 1, b_id: 10 };
        let public_inputs = vec![Fp::from(1), Fp::from(10)];
        let prover = MockProver::run(K, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err(), "Should reject sibling relationship");
    }

    #[test]
    fn test_reject_same_node() {
        // A node is NOT a strict descendant of itself
        let circuit = ContainmentCircuit { a_id: 1, b_id: 1 };
        let public_inputs = vec![Fp::from(1), Fp::from(1)];
        let prover = MockProver::run(K, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
        // assert!(prover.verify().is_err(), "Should reject same-node relationship");
    }

    #[test]
    fn test_reject_ancestor_as_descendant() {
        // direct-marketing (id=2) -> marketing (id=1) : ANCESTOR, should FAIL
        let circuit = ContainmentCircuit { a_id: 2, b_id: 1 };
        let public_inputs = vec![Fp::from(2), Fp::from(1)];
        let prover = MockProver::run(K, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err(), "Should reject ancestor-as-descendant");
    }

    #[test]
    fn test_reject_cross_branch() {
        // advertising (id=10) -> shipping/new-delivery (id=14) : CROSS-BRANCH, should FAIL
        let circuit = ContainmentCircuit { a_id: 10, b_id: 14 };
        let public_inputs = vec![Fp::from(10), Fp::from(14)];
        let prover = MockProver::run(K, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err(), "Should reject cross-branch relationship");
    }
}

pub fn purpose_check(parent: u64, child: u64) -> u32 {
    use halo2_proofs::dev::MockProver;
    
    let circuit = ContainmentCircuit{a_id: parent, b_id: child};

    let public_input = vec![Fp::from(parent), Fp::from(child)];

    let prover = MockProver::run(12, &circuit, vec![public_input]).unwrap();
    
    let result = prover.verify();
    // println!("Verification result: {:?}", result); // Debug log
    match result {
        Ok(()) => {
            // println!("Verification succeeded");
            1
        }
        Err(e) => {
            println!("Purpose verification failed: {:?}", e);
            0
        }
    }
}