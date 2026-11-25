import F3.KernelNormalization
import F3.FullKernelRows
import F3.TriangleKernel

/-!
# Active-row rigidity in residue two

Every hypothetical zero-weight row is reduced by actual column symmetries to
the full, positive, ordered exceptional-row case. The kernel and energy lemmas
are applied to the original feasible level and a genuine multiplier system.
-/

namespace F3
noncomputable section
open scoped BigOperators

/-- At a genuine optimum above the construction threshold, every row weight
in every normalized multiplier system is strictly positive. -/
theorem active_residue_two {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (hopt : OptimalValue (3*m+2) ((m : ℝ)+d))
    (M : MultiplierSystem A) (hd : 1/5<d) : ∀i,0<M.weight i := by
  intro r
  by_contra hn
  have hr : M.weight r=0 := le_antisymm (le_of_not_gt hn) (M.weight_nonneg r)
  have hfull := residue_two_zero_row_full hA M hd r hr
  let σ : Fin 3 → ℝ := fun j=>Dominance.signUnit (A r j)
  have hσ (j : Fin 3) : σ j*σ j=1 := by simpa [σ,pow_two] using Dominance.signUnit_sq (A r j)
  let B := signColumns A σ
  let N := M.signColumns σ hσ
  have hB : Feasible ((m : ℝ)+d) B := feasible_signColumns hA σ hσ
  have hNr : N.weight r=0 := hr
  have hBpos (j : Fin 3) : 0<B r j := by
    have habs : B r j=|A r j| := by
      change Dominance.signUnit (A r j)*A r j=|A r j|
      simpa only [mul_comm] using Dominance.signUnit_mul (A r j)
    rw [habs]
    exact abs_pos.mpr (hfull j)
  obtain ⟨e,ho⟩ := residue_two_full_kernel_ordered_rest hB hopt N hd r hNr hBpos
  let C := permuteColumns B e
  let P := N.permuteColumns e
  have hC : Feasible ((m : ℝ)+d) C := feasible_permuteColumns hB e
  have hPr : P.weight r=0 := hNr
  have hCpos (j : Fin 3) : 0<C r j := hBpos (e j)
  have hrest := residue_two_unique_zero hC P hd r hPr
  have htri := residue_two_positive_zero_triangle hC P hd r hPr hCpos
  have hordered : OrderedPairFrame (deleteRow C r) := ho
  exact no_three_coordinate_zero_weight_ordered hC hd P r hPr hrest hCpos htri hordered

end
end F3
