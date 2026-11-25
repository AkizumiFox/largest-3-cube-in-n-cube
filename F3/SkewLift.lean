import F3.TangentNormal
import Mathlib.Data.Matrix.Mul

/-! Every tangent vector to a positive fixed-Gram frame has a skew lift. -/
namespace F3
noncomputable section
open scoped BigOperators Matrix

theorem feasible_gram_matrix {ι : Type*} [Fintype ι]
    {A : Matrix ι (Fin 3) ℝ} {s : ℝ} (hA : Feasible s A) :
    Aᵀ*A = s • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext j k
  change (∑ i, A i j*A i k) = _
  rw [hA.2]
  by_cases h : j=k <;> simp [h,Matrix.one_apply]

theorem frameTangent_matrix {ι : Type*} [Fintype ι]
    {A H : Matrix ι (Fin 3) ℝ} (hH : FrameTangent A H) :
    Hᵀ*A = -(Aᵀ*H) := by
  ext j k
  have h := hH j k
  dsimp [crossGram] at h
  change (∑ i, H i j*A i k) = -(∑ i, A i j*H i k)
  have hc : (∑ i, H i j*A i k) = ∑ i, A i k*H i j := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  linarith

def skewLift {ι : Type*} [Fintype ι]
    (s : ℝ) (A H : Matrix ι (Fin 3) ℝ) : Matrix ι ι ℝ :=
  (1/s) • (H*Aᵀ-A*Hᵀ) - (1/s^2) • (A*(Aᵀ*H)*Aᵀ)

theorem skewLift_skew {ι : Type*} [Fintype ι]
    {A H : Matrix ι (Fin 3) ℝ} (s : ℝ) (hH : FrameTangent A H) :
    (skewLift s A H)ᵀ = -skewLift s A H := by
  have hc := frameTangent_matrix hH
  unfold skewLift
  simp only [Matrix.transpose_sub,Matrix.transpose_smul,Matrix.transpose_mul,
    Matrix.transpose_transpose]
  rw [hc]
  simp only [Matrix.mul_neg,Matrix.neg_mul]
  simp only [Matrix.mul_assoc]
  ext i j
  simp only [Matrix.sub_apply,Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem skewLift_mul_frame {ι : Type*} [Fintype ι]
    {A H : Matrix ι (Fin 3) ℝ} {s : ℝ} (hA : Feasible s A)
    (hs : 0 < s) (hH : FrameTangent A H) :
    skewLift s A H * A = H := by
  have hgram := feasible_gram_matrix hA
  have hc := frameTangent_matrix hH
  unfold skewLift
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.smul_mul,Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  rw [hgram,hc]
  simp only [Matrix.mul_smul,Matrix.mul_one,Matrix.mul_neg,sub_neg_eq_add,
    smul_add,smul_smul]
  have hdiv : (1/s)*s=1 := by field_simp
  have hdiv2 : (1/s^2)*s=1/s := by field_simp; ring
  rw [hdiv,hdiv2,one_smul]
  simp

end
end F3
