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

// ============================================================
// Tree Data (precomputed DFS In-Out labels)
// ============================================================

const NUM_NODES: usize = 19;
const NUM_BITS: usize = 6; // max label value is 37, fits in 6 bits

/// Static tree nodes with their DFS in-out labels.
/// Generated from the purpose tree via Algorithm 1 (DFS In-Out Labeling).
const TREE_NODES: [(u64, u64, u64); NUM_NODES] = [
    // (node_id, left, right)
    (0,  0,  37),  // general-purpose
    (1,  1,  18),  // general-purpose/marketing
    (2,  2,  11),  // general-purpose/marketing/direct-marketing
    (3,  3,  8),   // general-purpose/marketing/direct-marketing/d-email
    (4,  4,  5),   // general-purpose/marketing/direct-marketing/d-email/special-offers
    (5,  6,  7),   // general-purpose/marketing/direct-marketing/d-email/service-updates
    (6,  9,  10),  // general-purpose/marketing/direct-marketing/d-phone
    (7,  12, 17),  // general-purpose/marketing/third-party-marketing
    (8,  13, 14),  // general-purpose/marketing/third-party-marketing/t-email
    (9,  15, 16),  // general-purpose/marketing/third-party-marketing/t-phone
    (10, 19, 24),  // general-purpose/advertising
    (11, 20, 21),  // general-purpose/advertising/trial
    (12, 22, 23),  // general-purpose/advertising/promotional
    (13, 25, 30),  // general-purpose/shipping
    (14, 26, 27),  // general-purpose/shipping/new-delivery
    (15, 28, 29),  // general-purpose/shipping/product-return
    (16, 31, 36),  // general-purpose/experimenting
    (17, 32, 33),  // general-purpose/experimenting/new-product
    (18, 34, 35),  // general-purpose/experimenting/feedback
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
    // Node IDs (loaded from public instance column)
    a_id: Column<Advice>,
    b_id: Column<Advice>,

    // Interval labels (looked up from tree table based on node IDs)
    a_left: Column<Advice>,
    a_right: Column<Advice>,
    b_left: Column<Advice>,
    b_right: Column<Advice>,

    // Differences for interval containment checks
    diff_left: Column<Advice>,   // b_left - a_left  (must be in [1, 63])
    diff_right: Column<Advice>,  // a_right - b_right (must be in [1, 63])

    // Bit decompositions of differences (6 bits each)
    diff_left_bits: [Column<Advice>; NUM_BITS],
    diff_right_bits: [Column<Advice>; NUM_BITS],

    // Multiplicative inverses for non-zero checks
    diff_left_inv: Column<Advice>,
    diff_right_inv: Column<Advice>,

    // Tree lookup table (fixed columns)
    tree_table: TreeTableConfig,

    // Public inputs (instance column)
    instance: Column<Instance>,

    // Selectors
    s_containment: Selector,     // Enables arithmetic containment gate
    s_tree_lookup: Selector,     // Enables tree table lookups
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
        // --- Define columns ---
        let a_id = meta.advice_column();
        let b_id = meta.advice_column();
        let a_left = meta.advice_column();
        let a_right = meta.advice_column();
        let b_left = meta.advice_column();
        let b_right = meta.advice_column();
        let diff_left = meta.advice_column();
        let diff_right = meta.advice_column();
        let diff_left_inv = meta.advice_column();
        let diff_right_inv = meta.advice_column();

        let diff_left_bits: [Column<Advice>; NUM_BITS] =
            std::array::from_fn(|_| meta.advice_column());
        let diff_right_bits: [Column<Advice>; NUM_BITS] =
            std::array::from_fn(|_| meta.advice_column());

        let node_id = meta.lookup_table_column();
        let left    = meta.lookup_table_column();
        let right   = meta.lookup_table_column();
        let instance = meta.instance_column();

        let s_containment = meta.selector();
        let s_tree_lookup = meta.complex_selector();

        // --- Enable equality for columns used in copy/instance constraints ---
        meta.enable_equality(a_id);
        meta.enable_equality(b_id);
        meta.enable_equality(a_left);
        meta.enable_equality(a_right);
        meta.enable_equality(b_left);
        meta.enable_equality(b_right);
        meta.enable_equality(instance);

        // --- Lookup 1: (a_id, a_left, a_right) must exist in tree table ---
        meta.lookup("a_node_lookup", |meta| {
            let s = meta.query_selector(s_tree_lookup);
            let a_id_expr   = meta.query_advice(a_id,    Rotation::cur());
            let a_left_expr = meta.query_advice(a_left,  Rotation::cur());
            let a_right_expr= meta.query_advice(a_right, Rotation::cur());
            vec![
                (s.clone() * a_id_expr,    node_id),
                (s.clone() * a_left_expr,  left),
                (s         * a_right_expr, right),
            ]
        });

        meta.lookup("b_node_lookup", |meta| {
            let s = meta.query_selector(s_tree_lookup);
            let b_id_expr   = meta.query_advice(b_id,    Rotation::cur());
            let b_left_expr = meta.query_advice(b_left,  Rotation::cur());
            let b_right_expr= meta.query_advice(b_right, Rotation::cur());
            vec![
                (s.clone() * b_id_expr,    node_id),
                (s.clone() * b_left_expr,  left),
                (s         * b_right_expr, right),
            ]
        });

        // --- Interval Containment Gate ---
        // Enforces:
        //   diff_left  = b_left - a_left   (must be > 0, i.e., a_left < b_left)
        //   diff_right = a_right - b_right (must be > 0, i.e., b_right < a_right)
        //
        // The "> 0" property is enforced by:
        //   1. Bit-decomposing diff into NUM_BITS boolean bits
        //   2. Checking diff != 0 via the multiplicative inverse trick
        //
        // If a_left >= b_left, then diff_left = b_left - a_left would be negative
        // (i.e., p - k in the field), which cannot be represented as a sum of
        // NUM_BITS boolean bits (max sum = 2^NUM_BITS - 1 = 63 < p).
        meta.create_gate("interval_containment", |meta| {
            let s = meta.query_selector(s_containment);

            let a_left_expr = meta.query_advice(a_left, Rotation::cur());
            let a_right_expr = meta.query_advice(a_right, Rotation::cur());
            let b_left_expr = meta.query_advice(b_left, Rotation::cur());
            let b_right_expr = meta.query_advice(b_right, Rotation::cur());
            let diff_left_expr = meta.query_advice(diff_left, Rotation::cur());
            let diff_right_expr = meta.query_advice(diff_right, Rotation::cur());
            let diff_left_inv_expr = meta.query_advice(diff_left_inv, Rotation::cur());
            let diff_right_inv_expr = meta.query_advice(diff_right_inv, Rotation::cur());

            let one = Expression::Constant(Fp::ONE);
            let mut constraints = vec![];

            // Constraint 1: diff_left = b_left - a_left
            constraints.push(
                s.clone() * (b_left_expr.clone() - a_left_expr.clone() - diff_left_expr.clone())
            );

            // Constraint 2: diff_right = a_right - b_right
            constraints.push(
                s.clone() * (a_right_expr.clone() - b_right_expr.clone() - diff_right_expr.clone())
            );

            // Constraint 3: diff_left bit decomposition + boolean checks
            let mut left_sum = Expression::Constant(Fp::ZERO);
            for i in 0..NUM_BITS {
                let bit = meta.query_advice(diff_left_bits[i], Rotation::cur());
                // Boolean: bit * (1 - bit) = 0
                constraints.push(s.clone() * bit.clone() * (one.clone() - bit.clone()));
                left_sum = left_sum + bit * Expression::Constant(Fp::from(1u64 << i));
            }
            // diff_left = sum(bits * 2^i)
            constraints.push(s.clone() * (diff_left_expr.clone() - left_sum));

            // Constraint 4: diff_right bit decomposition + boolean checks
            let mut right_sum = Expression::Constant(Fp::ZERO);
            for i in 0..NUM_BITS {
                let bit = meta.query_advice(diff_right_bits[i], Rotation::cur());
                constraints.push(s.clone() * bit.clone() * (one.clone() - bit.clone()));
                right_sum = right_sum + bit * Expression::Constant(Fp::from(1u64 << i));
            }
            constraints.push(s.clone() * (diff_right_expr.clone() - right_sum));

            // Constraint 5: diff_left != 0  (inverse trick)
            // If diff_left = 0, then 0 * inv - 1 = -1 != 0, so constraint fails.
            constraints.push(
                s.clone() * (diff_left_expr * diff_left_inv_expr - one.clone())
            );

            // Constraint 6: diff_right != 0 (inverse trick)
            constraints.push(
                s.clone() * (diff_right_expr * diff_right_inv_expr - one)
            );

            constraints
        });

        ContainmentConfig {
            a_id,
            b_id,
            a_left,
            a_right,
            b_left,
            b_right,
            diff_left,
            diff_right,
            diff_left_bits,
            diff_right_bits,
            diff_left_inv,
            diff_right_inv,
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
        a_id: u64,
        b_id: u64,
        offset: usize,
        instance_row: usize,
    ) -> Result<(), Error> {
        let a_node = TREE_NODES[a_id as usize];
        let b_node = TREE_NODES[b_id as usize];
        assert!(
            a_node.1 < b_node.1 && b_node.2 < a_node.2,
            "Node {} is not a strict descendant of node {}", b_id, a_id
        );

        let diff_left_val  = b_node.1 - a_node.1;
        let diff_right_val = a_node.2 - b_node.2;

        // ── Return the two cells so we can constrain them to instance OUTSIDE the closure ──
        let (a_cell, b_cell) = layouter.assign_region(
            || "containment_check",
            |mut region| {
                self.config.s_containment.enable(&mut region, offset)?;
                self.config.s_tree_lookup.enable(&mut region, offset)?;

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

                region.assign_advice(|| "diff_left",  self.config.diff_left,  offset, || Value::known(Fp::from(diff_left_val)))?;
                region.assign_advice(|| "diff_right", self.config.diff_right, offset, || Value::known(Fp::from(diff_right_val)))?;

                let diff_left_fp  = Fp::from(diff_left_val);
                let diff_right_fp = Fp::from(diff_right_val);
                region.assign_advice(|| "diff_left_inv",  self.config.diff_left_inv,  offset, || Value::known(diff_left_fp.invert().unwrap()))?;
                region.assign_advice(|| "diff_right_inv", self.config.diff_right_inv, offset, || Value::known(diff_right_fp.invert().unwrap()))?;

                for i in 0..NUM_BITS {
                    let left_bit  = ((diff_left_val  >> i) & 1) as u64;
                    let right_bit = ((diff_right_val >> i) & 1) as u64;
                    region.assign_advice(|| format!("diff_left_bit_{}", i),  self.config.diff_left_bits[i],  offset, || Value::known(Fp::from(left_bit)))?;
                    region.assign_advice(|| format!("diff_right_bit_{}", i), self.config.diff_right_bits[i], offset, || Value::known(Fp::from(right_bit)))?;
                }

                Ok((a_cell, b_cell))   // ← return cells
            },
        )?;

        // ── Constrain advice cells to the public instance column ──
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
    type Params      = ();            // ← ADD THIS LINE

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        ContainmentChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let chip = ContainmentChip::construct(config);

        chip.load_tree_table(layouter.namespace(|| "tree_table"))?;

        chip.assign_containment(
            layouter.namespace(|| "containment"),
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

    #[test]
    fn test_marketing_to_direct_marketing() {
        // marketing (id=1) -> direct-marketing (id=2)
        let circuit = ContainmentCircuit { a_id: 1, b_id: 2 };
        let public_inputs = vec![Fp::from(1), Fp::from(2)];

        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_marketing_to_special_offers() {
        // marketing (id=1) -> special-offers (id=4)
        let circuit = ContainmentCircuit { a_id: 1, b_id: 4 };
        let public_inputs = vec![Fp::from(1), Fp::from(4)];

        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_general_purpose_to_any() {
        // general-purpose (id=0) -> feedback (id=18)
        let circuit = ContainmentCircuit { a_id: 0, b_id: 18 };
        let public_inputs = vec![Fp::from(0), Fp::from(18)];

        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_direct_marketing_to_email_descendants() {
        // direct-marketing (id=2) -> d-email (id=3)
        let circuit = ContainmentCircuit { a_id: 2, b_id: 3 };
        let public_inputs = vec![Fp::from(2), Fp::from(3)];

        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_reject_sibling() {
        // marketing (id=1) -> advertising (id=10) : SIBLING, should FAIL
        let circuit = ContainmentCircuit { a_id: 1, b_id: 10 };
        let public_inputs = vec![Fp::from(1), Fp::from(10)];

        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err(), "Should reject sibling relationship");
    }

    #[test]
    fn test_reject_same_node() {
        // A node is NOT a strict descendant of itself
        let circuit = ContainmentCircuit { a_id: 1, b_id: 1 };
        let public_inputs = vec![Fp::from(1), Fp::from(1)];

        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err(), "Should reject same-node relationship");
    }

    #[test]
    fn test_reject_ancestor_as_descendant() {
        // direct-marketing (id=2) -> marketing (id=1) : ANCESTOR, should FAIL
        let circuit = ContainmentCircuit { a_id: 2, b_id: 1 };
        let public_inputs = vec![Fp::from(2), Fp::from(1)];

        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        assert!(
            prover.verify().is_err(),
            "Should reject ancestor-as-descendant relationship"
        );
    }

    #[test]
    fn test_reject_cross_branch() {
        // advertising (id=10) -> shipping/new-delivery (id=14) : CROSS-BRANCH, should FAIL
        let circuit = ContainmentCircuit { a_id: 10, b_id: 14 };
        let public_inputs = vec![Fp::from(10), Fp::from(14)];

        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        assert!(
            prover.verify().is_err(),
            "Should reject cross-branch relationship"
        );
    }
}