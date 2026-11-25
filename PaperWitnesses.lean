import F3

/-!
  Declarative evidence for the 2026-11-25 paper.
  Diagnostics only: adds no axioms or mathematical theorems.
  All theorem names listed here are checked against the elaborator.
-/

set_option maxHeartbeats 0

-- thm:sharp-values (直接＋橋接)
#check @F3.frameValue_eq_formula
#check @F3.geometricValue_eq_sqrt_formula

-- cor:eventual-recurrence (直接)
#check @F3.frameValue_recurrence
#check @F3.frameValue_recurrence_iff

-- prop:matrix-model (組合)
#check @F3.General.geometricSide_iff_feasibleValue
#check @F3.General.value_attained
#check @F3.General.value_trace_equality_iff

-- prop:stacking (組合)
#check @F3.General.value_stacking
#check @F3.General.value_superadditive

-- lem:dominance (組合)
#check @F3.Dominance.dominance_summary

-- cor:two-dimensional (組合)
#check @F3.General.value_two_dimensional_bound

-- lem:multipliers (組合)
#check @F3.exists_multiplier_at_optimum
#check @F3.MultiplierSystem
#check @F3.isCompact_multiplierTuples
#check @F3.multiplierTuples_nonempty_at_optimum

-- lem:rank-one (組合)
#check @F3.multiplier_rank_ge_two_residue_one
#check @F3.multiplier_rank_ge_two_residue_two
#check @F3.singular_multiplier_rank_two_psd_residue_one
#check @F3.singular_multiplier_rank_two_psd_residue_two

-- lem:active-r1 (直接)
#check @F3.active_residue_one

-- lem:full-pd (直接)
#check @F3.full_row_posdef

-- lem:fixed-gram-jets (直接)
#check @F3.secondJetCurvesExist

-- lem:second-order (直接＋前提)
#check @F3.strict_second_order_not_local_min

-- prop:support-bound (直接)
#check @F3.full_support_bound_at_optimum

-- lem:edge-transfer (組合)
#check @F3.Transfer.edge_transfer
#check @F3.actual_edge_transfer
#check @F3.Transfer.edge_inverse
#check @F3.Transfer.deriv_B_range

-- lem:root-isolation (組合)
#check @F3.rootOneEquation_unique
#check @F3.rootTwoEquation_unique

-- prop:exceptional-frames (直接)
#check @F3.canonical_exceptional_frames
#check @F3.core5_feasible
#check @F3.core10_feasible

-- lem:full-row-classification (組合)
#check @F3.full_pair_count_classification
#check @F3.one_full_realized_normal_form
#check @F3.two_full_realized_normal_form

-- prop:r1-one-full (組合)
#check @F3.OneFullData.residue_one

-- prop:r1-two-full (組合)
#check @F3.TwoFullData.residue_one

-- prop:r2-full-exclusion (組合)
#check @F3.full_rows_residue_two_impossible

-- prop:r1-no-full (組合)
#check @F3.no_full_residue_one_bound

-- thm:r1 (直接)
#check @F3.frameValue_first_residue

-- prop:r2-column-bounds (組合)
#check @F3.residue_two_preliminary_upper
#check @F3.residue_two_no_zero_row
#check @F3.residue_two_large_count

-- lem:r2-all-active (直接＋前提)
#check @F3.active_residue_two

-- prop:r2-no-full (組合)
#check @F3.no_full_residue_two_bound

-- thm:r2-sharp (直接)
#check @F3.frameValue_second_residue

-- prop:finite-core (直接)
#check @F3.General.finite_core_iff_stabilization

-- remark:four-row-optimal-existence (直接)
#check @F3.four_noncoordinate_rows
#check @F3.four_noncoordinate_rows_general

-- lem:r2-kernel-reduction (COMPOSITE)
#check @F3.residue_two_zero_row_nondominant
#check @F3.residue_two_unique_zero
#check @F3.singular_multiplier_rank_two_psd_residue_two

-- lem:r2-zero-weight-pair (COMPOSITE)
#check @F3.no_two_coordinate_zero_weight
#check @F3.two_coordinate_kernel_upper

-- lem:r2-full-kernel-structure (COMPOSITE)
#check @F3.residue_two_full_kernel_other_not_full
#check @F3.residue_two_full_kernel_distinct_diagonal
#check @F3.residue_two_full_kernel_ordered_rest

-- lem:r2-strict-triangle (SUBPROOF)
#check @F3.strict_triangle_flow_upper
#check @F3.no_three_coordinate_zero_weight_ordered

-- lem:r2-degenerate-triangle (SUBPROOF)
#check @F3.degenerate_source_flow_impossible
#check @F3.degenerate_middle_flow_impossible
#check @F3.degenerate_sink_flow_impossible
#check @F3.no_three_coordinate_zero_weight_ordered

-- eq:tetrahedron (BRIDGE)
#check @F3.tetrahedronValue_eq_geometricValue
#check @F3.tetrahedronValue_five
#check @F3.centeredTetrahedronEdge_iff_feasibleValue

-- Sensitive bridge and core claims
#print axioms F3.frameValue_eq_formula
#print axioms F3.geometricValue_eq_sqrt_formula
#print axioms F3.active_residue_two
#print axioms F3.General.finite_core_iff_stabilization
#print axioms F3.tetrahedronValue_eq_geometricValue
#print axioms F3.four_noncoordinate_rows
