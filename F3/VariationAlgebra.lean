import F3.SignChanges
import F3.TangentNormal

/-! Algebraic identities for the second-order support-reduction argument. -/
namespace F3
noncomputable section
open scoped BigOperators

def curvature {ι : Type*} [Fintype ι]
    (S : Fin 3 → Fin 3 → ℝ) (H : ι → Fin 3 → ℝ) : ℝ :=
  ∑ i, quadraticThree S (H i)

theorem curvature_eq_crossGram {ι : Type*} [Fintype ι]
    (S : Fin 3 → Fin 3 → ℝ) (H : ι → Fin 3 → ℝ) :
    curvature S H = ∑ j, ∑ k, S j k * crossGram H H j k := by
  unfold curvature quadraticThree crossGram
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem curvature_positive_of_full_row {ι : Type*} [Fintype ι]
    {A H : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hs : 0 < s) (M : MultiplierSystem A)
    (hw : ∀ i, 0 < M.weight i) (i₀ : ι)
    (hu : ∀ j, A i₀ j ≠ 0) (hH : H ≠ 0) :
    0 < curvature M.matrix H := by
  classical
  have hrow (i : ι) : 0 ≤ quadraticThree M.matrix (H i) := by
    by_cases hi : H i = 0
    · simp [hi,quadraticThree]
    · exact (full_row_posdef hA hs M hw i₀ hu (H i) hi).le
  have hex : ∃ i, H i ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hH (funext hh)
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun i _ => hrow i)
    ⟨i,Finset.mem_univ _,full_row_posdef hA hs M hw i₀ hu (H i) hi⟩

theorem crossGram_self_symmetric {ι : Type*} [Fintype ι]
    (H : ι → Fin 3 → ℝ) (j k : Fin 3) :
    crossGram H H j k = crossGram H H k j := by
  unfold crossGram
  apply Finset.sum_congr rfl
  intro i _
  ring

def normalAcceleration {ι : Type*} [Fintype ι]
    (s : ℝ) (A H : ι → Fin 3 → ℝ) : ι → Fin 3 → ℝ :=
  rightMul A (fun j k => -crossGram H H j k/s)

theorem normalAcceleration_crossGram {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hs : 0 < s) (H : ι → Fin 3 → ℝ) (j k : Fin 3) :
    crossGram A (normalAcceleration s A H) j k = -crossGram H H j k := by
  unfold normalAcceleration
  rw [crossGram_rightMul hA]
  field_simp
  ring

theorem normalAcceleration_gram_second_variation {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hs : 0 < s) (H : ι → Fin 3 → ℝ) (j k : Fin 3) :
    crossGram A (normalAcceleration s A H) j k +
      crossGram A (normalAcceleration s A H) k j =
        -2*crossGram H H j k := by
  rw [normalAcceleration_crossGram hA hs,normalAcceleration_crossGram hA hs,
    crossGram_self_symmetric H k j]
  ring

theorem normalAcceleration_pairing {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hs : 0 < s) (H : ι → Fin 3 → ℝ) (S : Fin 3 → Fin 3 → ℝ) :
    framePairing (rightMul A S) (normalAcceleration s A H) = -curvature S H := by
  rw [framePairing_rightMul,curvature_eq_crossGram]
  simp_rw [normalAcceleration_crossGram hA hs,mul_neg]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_neg_distrib]

/-- Exact cubic and quartic remainder of the polynomial second-order path. -/
theorem second_order_gram_expansion {ι : Type*} [Fintype ι]
    {A H W : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hH : FrameTangent A H)
    (hW : ∀ j k, crossGram A W j k + crossGram A W k j =
      -2*crossGram H H j k) (t : ℝ) (j k : Fin 3) :
    crossGram (fun i j => A i j+t*H i j+t^2/2*W i j)
      (fun i j => A i j+t*H i j+t^2/2*W i j) j k =
      (if j=k then s else 0) +
        t^3/2*(crossGram H W j k+crossGram H W k j) +
        t^4/4*crossGram W W j k := by
  have hexp : crossGram (fun i j => A i j+t*H i j+t^2/2*W i j)
      (fun i j => A i j+t*H i j+t^2/2*W i j) j k =
      crossGram A A j k + t*(crossGram A H j k+crossGram A H k j) +
      t^2/2*(crossGram A W j k+crossGram A W k j+2*crossGram H H j k) +
      t^3/2*(crossGram H W j k+crossGram H W k j) +
      t^4/4*crossGram W W j k := by
    unfold crossGram
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hexp,show crossGram A A j k=(if j=k then s else 0) from hA.2 j k,
    hH j k,hW j k]
  ring

end
end F3
