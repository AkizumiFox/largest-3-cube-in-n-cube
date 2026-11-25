import F3.Attainment
import F3.MultiplierCompactness
import F3.RowKernelMinors
import F3.TriangleKernel
import F3.LocalVariational

set_option pp.universes false

#check F3.crossGram_rightMul
#print axioms F3.crossGram_rightMul

#check F3.framePairing_rightMul
#print axioms F3.framePairing_rightMul

#check F3.normal_pairing_tangent_zero
#print axioms F3.normal_pairing_tangent_zero

#check F3.normalCoefficient_symmetric
#print axioms F3.normalCoefficient_symmetric

#check F3.tangentProjection_tangent
#print axioms F3.tangentProjection_tangent

#check F3.framePairing_tangentProjection
#print axioms F3.framePairing_tangentProjection

#check F3.frameTangent_zero
#print axioms F3.frameTangent_zero

#check F3.frameTangent_neg
#print axioms F3.frameTangent_neg

#check F3.frameTangent_weightedSum
#print axioms F3.frameTangent_weightedSum

#check F3.exists_symmetric_normal_of_annihilates_tangent
#print axioms F3.exists_symmetric_normal_of_annihilates_tangent

#check F3.isCompact_simplexWeight
#print axioms F3.isCompact_simplexWeight

#check F3.simplexWeight_nonempty
#print axioms F3.simplexWeight_nonempty

#check F3.continuous_convexCombo
#print axioms F3.continuous_convexCombo

#check F3.simplexWeight_segment
#print axioms F3.simplexWeight_segment

#check F3.convexCombo_segment
#print axioms F3.convexCombo_segment

#check F3.exists_minimal_convexCombo
#print axioms F3.exists_minimal_convexCombo

#check F3.finite_strict_alternative
#print axioms F3.finite_strict_alternative

#check F3.finite_strict_affine_alternative
#print axioms F3.finite_strict_affine_alternative

#check F3.affine_certificate_of_no_strict_solution
#print axioms F3.affine_certificate_of_no_strict_solution

#check F3.facetSign_abs
#print axioms F3.facetSign_abs

#check F3.facet_coordinate_le_abs
#print axioms F3.facet_coordinate_le_abs

#check F3.active_facet_saturated
#print axioms F3.active_facet_saturated

#check F3.active_facet_subgradient
#print axioms F3.active_facet_subgradient

#check F3.canonicalSubgradient_spec
#print axioms F3.canonicalSubgradient_spec

#check F3.groupedWeight_nonneg
#print axioms F3.groupedWeight_nonneg

#check F3.weightedFacetGradient_abs_le
#print axioms F3.weightedFacetGradient_abs_le

#check F3.grouped_gradient_product
#print axioms F3.grouped_gradient_product

#check F3.groupedGradient_subgradient
#print axioms F3.groupedGradient_subgradient

#check F3.groupedWeight_complementary
#print axioms F3.groupedWeight_complementary

#check F3.weightedFacetGradient_annihilates
#print axioms F3.weightedFacetGradient_annihilates

#check F3.exists_multiplier_of_facetWeights
#print axioms F3.exists_multiplier_of_facetWeights

#check F3.weightedFacetGradient_pairing
#print axioms F3.weightedFacetGradient_pairing

#check F3.exists_multiplier_realizing_facetWeights
#print axioms F3.exists_multiplier_realizing_facetWeights

#check F3.framePairing_facetMatrix
#print axioms F3.framePairing_facetMatrix

#check F3.framePairing_comm
#print axioms F3.framePairing_comm

#check F3.exists_facetWeights_of_no_affine_tangent_descent
#print axioms F3.exists_facetWeights_of_no_affine_tangent_descent

#check F3.exists_multiplier_of_no_strict_tangent_descent
#print axioms F3.exists_multiplier_of_no_strict_tangent_descent

#check F3.facetValue_canonical
#print axioms F3.facetValue_canonical

#check F3.facetValue_le_one
#print axioms F3.facetValue_le_one

#check F3.no_strict_fixedGram_improvement
#print axioms F3.no_strict_fixedGram_improvement

#check F3.eventually_lt_of_negative_derivative
#print axioms F3.eventually_lt_of_negative_derivative

#check F3.hasDerivAt_facetValue
#print axioms F3.hasDerivAt_facetValue

#check F3.no_strict_tangent_descent_of_curves
#print axioms F3.no_strict_tangent_descent_of_curves

#check F3.exists_multiplier_at_optimum_of_curves
#print axioms F3.exists_multiplier_at_optimum_of_curves

#check F3.secondJetCurvesExist
#print axioms F3.secondJetCurvesExist

#check F3.exists_strict_second_acceleration
#print axioms F3.exists_strict_second_acceleration

#check F3.eventually_lt_of_negative_second_derivative
#print axioms F3.eventually_lt_of_negative_second_derivative

#check F3.strict_second_order_descent_of_curves
#print axioms F3.strict_second_order_descent_of_curves

#check F3.strict_second_order_descent
#print axioms F3.strict_second_order_descent

#check F3.no_face_tangent_at_full_optimum
#print axioms F3.no_face_tangent_at_full_optimum

#check F3.multiplierTuple_spec
#print axioms F3.multiplierTuple_spec

#check F3.isMultiplierTuple_iff_exists_system
#print axioms F3.isMultiplierTuple_iff_exists_system

#check F3.isClosed_multiplierTuples
#print axioms F3.isClosed_multiplierTuples

#check F3.multiplier_weight_le_one
#print axioms F3.multiplier_weight_le_one

#check F3.multiplier_entry_abs_le_inv_level
#print axioms F3.multiplier_entry_abs_le_inv_level

#check F3.isCompact_multiplierTuples
#print axioms F3.isCompact_multiplierTuples

#check F3.multiplierTuples_nonempty_at_optimum
#print axioms F3.multiplierTuples_nonempty_at_optimum

#check F3.RowPairIndependent.linearIndependent
#print axioms F3.RowPairIndependent.linearIndependent

#check F3.rotation_denom_pos
#print axioms F3.rotation_denom_pos

#check F3.continuous_rotationCos
#print axioms F3.continuous_rotationCos

#check F3.continuous_rotationSin
#print axioms F3.continuous_rotationSin

#check F3.rotation_circle
#print axioms F3.rotation_circle

#check F3.rotated_pair_independent
#print axioms F3.rotated_pair_independent

#check F3.rotated_pair_gram
#print axioms F3.rotated_pair_gram

#check F3.saturated_positive_pair_independent
#print axioms F3.saturated_positive_pair_independent

#check F3.exists_slack_pair_rotation
#print axioms F3.exists_slack_pair_rotation

#check F3.replaceTwoRows_gram
#print axioms F3.replaceTwoRows_gram

#check F3.exists_feasible_slack_independent_rows
#print axioms F3.exists_feasible_slack_independent_rows

#check F3.multiplier_annihilates_slack_row
#print axioms F3.multiplier_annihilates_slack_row

#check F3.exists_optimal_independent_kernel_rows
#print axioms F3.exists_optimal_independent_kernel_rows

#check F3.rowCross_nonzero
#print axioms F3.rowCross_nonzero

#check F3.rowCross_proportional
#print axioms F3.rowCross_proportional

#check F3.two_kernel_rows_all_minors_zero
#print axioms F3.two_kernel_rows_all_minors_zero

#check F3.two_kernel_rows_principal_minors_zero
#print axioms F3.two_kernel_rows_principal_minors_zero

#check F3.saturated_row_defect
#print axioms F3.saturated_row_defect

#check F3.two_coordinate_kernel_mass_identity
#print axioms F3.two_coordinate_kernel_mass_identity

#check F3.two_coordinate_kernel_energy_bounds
#print axioms F3.two_coordinate_kernel_energy_bounds

#check F3.two_coordinate_kernel_upper
#print axioms F3.two_coordinate_kernel_upper

#check F3.subgradient_opposite_pair
#print axioms F3.subgradient_opposite_pair

#check F3.no_two_coordinate_zero_weight
#print axioms F3.no_two_coordinate_zero_weight

#check F3.pairEdgeAbsProduct_eq_sum
#print axioms F3.pairEdgeAbsProduct_eq_sum

#check F3.pairEdgeSignedProduct_eq_sum
#print axioms F3.pairEdgeSignedProduct_eq_sum

#check F3.pairEdgeAbsProduct_nonneg
#print axioms F3.pairEdgeAbsProduct_nonneg

#check F3.pairEdgeLoss_eq_two_abs
#print axioms F3.pairEdgeLoss_eq_two_abs

#check F3.pairEdge_abs_signed_le
#print axioms F3.pairEdge_abs_signed_le

#check F3.pairEdgeAbsProduct_of_nonpos
#print axioms F3.pairEdgeAbsProduct_of_nonpos

#check F3.ordered_edge_energy_le_abs
#print axioms F3.ordered_edge_energy_le_abs

#check F3.ordered_edge_deficit_ge_two_abs
#print axioms F3.ordered_edge_deficit_ge_two_abs

#check F3.ordered_edge_energy_le_square
#print axioms F3.ordered_edge_energy_le_square

#check F3.twice_abs_term_le_abs_sum_add_abs_sum
#print axioms F3.twice_abs_term_le_abs_sum_add_abs_sum

#check F3.ordered_edge_energy_lt_one_over_35
#print axioms F3.ordered_edge_energy_lt_one_over_35

#check F3.triangle_source_counts
#print axioms F3.triangle_source_counts

#check F3.strict_triangle_flow_upper
#print axioms F3.strict_triangle_flow_upper

#check F3.degenerate_source_flow_impossible
#print axioms F3.degenerate_source_flow_impossible

#check F3.degenerate_middle_flow_impossible
#print axioms F3.degenerate_middle_flow_impossible

#check F3.degenerate_sink_flow_impossible
#print axioms F3.degenerate_sink_flow_impossible

#check F3.sum_deleted_index
#print axioms F3.sum_deleted_index

#check F3.deleteRow_gram_diagonal
#print axioms F3.deleteRow_gram_diagonal

#check F3.deleteRow_signed_product
#print axioms F3.deleteRow_signed_product

#check F3.deleteRow_large_count
#print axioms F3.deleteRow_large_count

#check F3.deleteRow_card
#print axioms F3.deleteRow_card

#check F3.deleteRow_defect_identity
#print axioms F3.deleteRow_defect_identity

#check F3.subgradient_pair_nonpos
#print axioms F3.subgradient_pair_nonpos

#check F3.no_three_coordinate_zero_weight_ordered
#print axioms F3.no_three_coordinate_zero_weight_ordered

#check F3.rowBudget_le_maxRowBudget
#print axioms F3.rowBudget_le_maxRowBudget

#check F3.facetValue_le_maxRowBudget
#print axioms F3.facetValue_le_maxRowBudget

#check F3.maxRowBudget_lt_one_of_facets
#print axioms F3.maxRowBudget_lt_one_of_facets

#check F3.maxRowBudget_eq_one_of_optimum
#print axioms F3.maxRowBudget_eq_one_of_optimum

#check F3.exists_second_order_curve_with_strict_facets
#print axioms F3.exists_second_order_curve_with_strict_facets

#check F3.strict_second_order_not_local_min
#print axioms F3.strict_second_order_not_local_min

#check F3.strict_second_order_not_local_min_at_optimum
#print axioms F3.strict_second_order_not_local_min_at_optimum

#print F3.MultiplierSystem

#print F3.RowSubgradient

#print F3.NormalizedFacetWeights

#print F3.IsMultiplierTuple

#print F3.NoStrictAffineTangentDescent

#print F3.SecondJetCurvesExist

#print F3.RowPairIndependent

#print F3.maxRowBudget

#print F3.fixedGramSet
