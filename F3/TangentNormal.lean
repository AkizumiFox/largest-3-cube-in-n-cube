import F3.Frames

/-! Exact finite-dimensional tangent/normal algebra for the fixed Gram manifold. -/

namespace F3
noncomputable section
open scoped BigOperators

def framePairing {ι : Type*} [Fintype ι]
    (G H : ι → Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, G i j * H i j

def crossGram {ι : Type*} [Fintype ι]
    (A H : ι → Fin 3 → ℝ) (j k : Fin 3) : ℝ :=
  ∑ i, A i j * H i k

def rightMul {ι : Type*} (A : ι → Fin 3 → ℝ)
    (S : Fin 3 → Fin 3 → ℝ) (i : ι) (j : Fin 3) : ℝ :=
  ∑ k, A i k * S k j

def FrameTangent {ι : Type*} [Fintype ι]
    (A H : ι → Fin 3 → ℝ) : Prop :=
  ∀ j k, crossGram A H j k + crossGram A H k j = 0

theorem crossGram_rightMul {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (S : Fin 3 → Fin 3 → ℝ) (j k : Fin 3) :
    crossGram A (rightMul A S) j k = s * S j k := by
  classical
  unfold crossGram rightMul
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hA.2]
  simp

theorem framePairing_rightMul {ι : Type*} [Fintype ι]
    (A H : ι → Fin 3 → ℝ) (S : Fin 3 → Fin 3 → ℝ) :
    framePairing (rightMul A S) H =
      ∑ j, ∑ k, S k j * crossGram A H k j := by
  classical
  unfold framePairing rightMul crossGram
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem normal_pairing_tangent_zero {ι : Type*} [Fintype ι]
    {A H : ι → Fin 3 → ℝ} {S : Fin 3 → Fin 3 → ℝ}
    (hS : ∀ j k, S j k = S k j) (hH : FrameTangent A H) :
    framePairing (rightMul A S) H = 0 := by
  classical
  rw [framePairing_rightMul]
  have hflip : (∑ j, ∑ k, S k j * crossGram A H k j) =
      ∑ j, ∑ k, S k j * crossGram A H j k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hS]
  have hsum : (∑ j, ∑ k, S k j * crossGram A H k j) +
      (∑ j, ∑ k, S k j * crossGram A H j k) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k hk
    rw [← mul_add, hH k j, mul_zero]
  linarith

def normalCoefficient {ι : Type*} [Fintype ι]
    (s : ℝ) (A G : ι → Fin 3 → ℝ) (j k : Fin 3) : ℝ :=
  (crossGram A G j k + crossGram A G k j) / (2*s)

def tangentProjection {ι : Type*} [Fintype ι]
    (s : ℝ) (A G : ι → Fin 3 → ℝ) (i : ι) (j : Fin 3) : ℝ :=
  G i j - rightMul A (normalCoefficient s A G) i j

theorem normalCoefficient_symmetric {ι : Type*} [Fintype ι]
    (s : ℝ) (A G : ι → Fin 3 → ℝ) (j k : Fin 3) :
    normalCoefficient s A G j k = normalCoefficient s A G k j := by
  unfold normalCoefficient
  rw [add_comm]

theorem tangentProjection_tangent {ι : Type*} [Fintype ι]
    {s : ℝ} {A : ι → Fin 3 → ℝ} (hA : Feasible s A) (hs : 0 < s)
    (G : ι → Fin 3 → ℝ) : FrameTangent A (tangentProjection s A G) := by
  have hc (j k : Fin 3) : crossGram A (tangentProjection s A G) j k =
      crossGram A G j k - s * normalCoefficient s A G j k := by
    unfold crossGram tangentProjection
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [show (∑ i, A i j * rightMul A (normalCoefficient s A G) i k) =
      s * normalCoefficient s A G j k from crossGram_rightMul hA _ j k]
  intro j k
  rw [hc, hc]
  unfold normalCoefficient
  field_simp
  ring

theorem framePairing_tangentProjection {ι : Type*} [Fintype ι]
    {s : ℝ} {A H : ι → Fin 3 → ℝ} (G : ι → Fin 3 → ℝ)
    (hH : FrameTangent A H) :
    framePairing (tangentProjection s A G) H = framePairing G H := by
  have hn := normal_pairing_tangent_zero (normalCoefficient_symmetric s A G) hH
  have he : framePairing (tangentProjection s A G) H = framePairing G H -
      framePairing (rightMul A (normalCoefficient s A G)) H := by
    unfold framePairing tangentProjection
    simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [he, hn, sub_zero]

theorem frameTangent_zero {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) : FrameTangent A (fun _ _ => 0) := by
  intro j k
  simp [crossGram]

theorem frameTangent_neg {ι : Type*} [Fintype ι]
    {A H : ι → Fin 3 → ℝ} (hH : FrameTangent A H) :
    FrameTangent A (fun i j => -H i j) := by
  intro j k
  have h := hH j k
  simp only [crossGram, mul_neg, Finset.sum_neg_distrib] at *
  linarith

theorem frameTangent_weightedSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : ι → Fin 3 → ℝ} (w : κ → ℝ) (H : κ → ι → Fin 3 → ℝ)
    (hH : ∀ k, FrameTangent A (H k)) :
    FrameTangent A (fun i j => ∑ k, w k * H k i j) := by
  intro j l
  have hc (j l : Fin 3) :
      crossGram A (fun i j => ∑ k, w k * H k i j) j l =
      ∑ k, w k * crossGram A (H k) j l := by
    unfold crossGram
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hc, hc, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← mul_add, hH k j l, mul_zero]

theorem exists_symmetric_normal_of_annihilates_tangent
    {ι : Type*} [Fintype ι] {A G : ι → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0 < s)
    (hG : ∀ H, FrameTangent A H → framePairing G H = 0) :
    ∃ S : Fin 3 → Fin 3 → ℝ,
      (∀ j k, S j k = S k j) ∧ G = rightMul A S := by
  classical
  let S : Fin 3 → Fin 3 → ℝ := fun j k =>
    (crossGram A G j k + crossGram A G k j) / (2*s)
  have hS : ∀ j k, S j k = S k j := by
    intro j k
    dsimp [S]
    rw [add_comm]
  let H : ι → Fin 3 → ℝ := fun i j => G i j - rightMul A S i j
  have hcross (j k : Fin 3) :
      crossGram A H j k = crossGram A G j k - s*S j k := by
    change (∑ i, A i j * (G i k - rightMul A S i k)) = _
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [show (∑ i, A i j * rightMul A S i k) = s*S j k from
      crossGram_rightMul hA S j k]
    rfl
  have hH : FrameTangent A H := by
    intro j k
    rw [hcross, hcross]
    dsimp [S]
    field_simp
    ring
  have hzero := hG H hH
  have hnormal := normal_pairing_tangent_zero hS hH
  have hsplit : framePairing G H = framePairing H H +
      framePairing (rightMul A S) H := by
    unfold framePairing
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [H]
    ring
  have hsq : framePairing H H = 0 := by linarith
  have hentry : ∀ i j, H i j = 0 := by
    intro i j
    have hi : (∑ k, H i k * H i k) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg (fun j _ => mul_self_nonneg (H i j)))).mp hsq
        i (Finset.mem_univ i)
    have hj : H i j * H i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (H i j))).mp hi
        j (Finset.mem_univ j)
    nlinarith
  refine ⟨S, hS, ?_⟩
  funext i j
  have hz := hentry i j
  exact sub_eq_zero.mp hz

end
end F3
