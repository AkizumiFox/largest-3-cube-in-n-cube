import F3.KernelRows
import F3.TwoCoordinateKernel
import F3.SignChanges

namespace F3
noncomputable section
open scoped BigOperators

/-- Every hypothetical zero-weight row in residue two must have full support.
The two-coordinate case is normalized by actual column symmetries. -/
theorem residue_two_zero_row_full {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (r : Fin (3*m+2))
    (hr : M.weight r=0) : ∀j,A r j≠0 := by
  intro l hl
  let e : Equiv.Perm (Fin 3) := Equiv.swap 2 l
  let B := permuteColumns A e
  let N := M.permuteColumns e
  have hB : Feasible ((m : ℝ)+d) B := feasible_permuteColumns hA e
  have hBr2 : B r 2=0 := by simpa [B,permuteColumns,e] using hl
  let σ : Fin 3 → ℝ := fun j=>Dominance.signUnit (B r j)
  have hσ (j : Fin 3) : σ j*σ j=1 := by simpa [σ,pow_two] using Dominance.signUnit_sq (B r j)
  let C := signColumns B σ
  let P := N.signColumns σ hσ
  have hC : Feasible ((m : ℝ)+d) C := feasible_signColumns hB σ hσ
  have hPr : P.weight r=0 := hr
  have hCr (j : Fin 3) : C r j=|B r j| := by
    change Dominance.signUnit (B r j)*B r j=|B r j|
    simpa only [mul_comm] using Dominance.signUnit_mul (B r j)
  have hC0 : 0≤C r 0 := by rw [hCr]; exact abs_nonneg _
  have hC1 : 0≤C r 1 := by rw [hCr]; exact abs_nonneg _
  have hC2 : C r 2=0 := by rw [hCr,hBr2,abs_zero]
  have hn := residue_two_zero_row_nondominant hC P hd r hPr
  have h0 : |C r 0|≤Dominance.minorL1 (C r) 0 := le_of_not_gt (hn 0)
  have h1 : |C r 1|≤Dominance.minorL1 (C r) 1 := le_of_not_gt (hn 1)
  have he0 := Dominance.l1_decompose (C r) 0
  have he1 := Dominance.l1_decompose (C r) 1
  have hl1 : Dominance.l1 (C r)=C r 0+C r 1 := by
    simp [Dominance.l1,Fin.sum_univ_three,abs_of_nonneg hC0,abs_of_nonneg hC1,hC2]
  rw [hl1,abs_of_nonneg hC0] at he0
  rw [hl1,abs_of_nonneg hC1] at he1
  rw [abs_of_nonneg hC0] at h0
  rw [abs_of_nonneg hC1] at h1
  have heq : C r 1=C r 0 := by linarith
  have ht : 0<C r 0 := by
    by_contra hn
    have hz0 : C r 0=0 := le_antisymm (le_of_not_gt hn) hC0
    have hz1 : C r 1=0 := heq.trans hz0
    obtain ⟨j,hj⟩ := residue_two_no_zero_row hd hC r
    fin_cases j <;> simp_all
  exact no_two_coordinate_zero_weight hC hd P r hPr
    (residue_two_unique_zero hC P hd r hPr) ht rfl heq hC2

end
end F3
