import F3

/-!
# Auxiliary statement correspondence diagnostics

Every numbered paper theorem/lemma/proposition/corollary has one or more
entries here. `#check` prints the *elaborated Lean type*, including implicit
assumptions. A successful run is not a proof that prose and Lean are identical;
the actual types still need a line-by-line human mathematical comparison
against PAPER_LEAN_ALL_27_PLUS_ONE.csv.
-/

set_option maxHeartbeats 0
set_option pp.all true

-- thm:sharp-values :: DIRECT_WITH_GEOMETRIC_BRIDGE
#check @F3.frameValue_eq_formula
#check @F3.geometricValue_eq_sqrt_formula

-- cor:eventual-recurrence :: DIRECT
#check @F3.frameValue_recurrence
#check @F3.frameValue_recurrence_iff

-- prop:matrix-model :: COMPOSED
#check @F3.General.geometricSide_iff_feasibleValue
#check @F3.General.value_attained
#check @F3.General.value_trace_equality_iff

-- prop:stacking :: DIRECT_AND_COMPANION
#check @F3.General.value_stacking
#check @F3.General.value_superadditive

-- lem:dominance :: DIRECT
#check @F3.Dominance.dominance_summary

-- cor:two-dimensional :: DIRECT
#check @F3.General.value_two_dimensional_bound

-- lem:multipliers :: COMPOSED
#check @F3.exists_multiplier_at_optimum
#check @F3.MultiplierSystem

-- lem:rank-one :: COMPOSED
#check @F3.multiplier_rank_ge_two_residue_one
#check @F3.multiplier_rank_ge_two_residue_two

-- lem:active-r1 :: DIRECT
#check @F3.active_residue_one

-- lem:full-pd :: DIRECT
#check @F3.full_positive_row_posdef

-- lem:fixed-gram-jets :: DIRECT
#check @F3.secondJetCurvesExist

-- lem:second-order :: DIRECT
#check @F3.strict_second_order_not_local_min

-- prop:support-bound :: DIRECT
#check @F3.full_support_bound_at_optimum

-- lem:edge-transfer :: COMPOSED
#check @F3.Transfer.edge_transfer
#check @F3.actual_edge_transfer

-- lem:root-isolation :: COMPOSED
#check @F3.rootOneEquation_unique
#check @F3.rootTwoEquation_unique

-- prop:exceptional-frames :: DIRECT_AND_COMPANION
#check @F3.canonical_exceptional_frames
#check @F3.core5_feasible
#check @F3.core10_feasible

-- lem:full-row-classification :: COMPOSED
#check @F3.full_pair_count_classification
#check @F3.one_full_realized_normal_form
#check @F3.two_full_realized_normal_form

-- prop:r1-one-full :: DIRECT
#check @F3.OneFullData.residue_one

-- prop:r1-two-full :: DIRECT
#check @F3.TwoFullData.residue_one

-- prop:r2-full-exclusion :: DIRECT
#check @F3.full_rows_residue_two_impossible

-- prop:r1-no-full :: DIRECT
#check @F3.no_full_residue_one_bound

-- thm:r1 :: DIRECT
#check @F3.frameValue_first_residue

-- prop:r2-column-bounds :: DIRECT
#check @F3.residue_two_preliminary_upper

-- lem:r2-all-active :: DIRECT
#check @F3.active_residue_two

-- prop:r2-no-full :: DIRECT
#check @F3.no_full_residue_two_bound

-- thm:r2-sharp :: DIRECT
#check @F3.frameValue_second_residue

-- prop:finite-core :: DIRECT
#check @F3.General.finite_core_iff_stabilization

-- remark:four-row-optimal-existence :: NEW_PROPOSED_THEOREM
#check @F3.four_noncoordinate_rows
#check @F3.four_noncoordinate_rows_general

-- Additional necessary definitions / bridges
#check @F3.General.value_three_eq_frameValue
#check @F3.General.noncoordinateCount
#check @F3.General.FeasibleWithCore
#check @F3.General.SignedCoordinate

-- Axioms of the most sensitive paper-to-formal bridge
#print axioms F3.General.geometricSide_iff_feasibleValue
#print axioms F3.geometricValue_sq
#print axioms F3.frameValue_eq_formula
#print axioms F3.active_residue_two
#print axioms F3.four_noncoordinate_rows
#print axioms F3.General.finite_core_iff_stabilization
