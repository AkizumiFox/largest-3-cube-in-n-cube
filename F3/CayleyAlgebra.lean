import F3.SkewLift
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact Gram-preserving matrix algebra for the Cayley curve. -/
namespace F3
noncomputable section
open scoped Matrix

def matrixCayley {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1+K)*(1-K)⁻¹

theorem matrixCayley_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℝ} (hK : Kᵀ = -K) (hu : IsUnit (1-K)) :
    (matrixCayley K)ᵀ * matrixCayley K = 1 := by
  have htR : (1-K)ᵀ = (1+K) := by simp [hK]
  have htB : (1+K)ᵀ = (1-K) := by simp [hK,sub_eq_add_neg]
  have huB : IsUnit (1+K) := by
    rw [← htR]
    exact (Matrix.isUnit_transpose (1-K)).mpr hu
  have hc : (1-K)*(1+K) = (1+K)*(1-K) := by
    simp only [Matrix.sub_mul,Matrix.mul_add,Matrix.mul_sub,Matrix.one_mul,
      Matrix.mul_one,Matrix.add_mul]
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply]
    ring
  calc
    (matrixCayley K)ᵀ*matrixCayley K =
        (1+K)⁻¹*((1-K)*(1+K))*(1-K)⁻¹ := by
      simp only [matrixCayley,Matrix.transpose_mul,Matrix.transpose_nonsing_inv,
        htR,htB,Matrix.mul_assoc]
    _ = (1+K)⁻¹*((1+K)*(1-K))*(1-K)⁻¹ := by rw [hc]
    _ = 1 := by
      rw [← Matrix.mul_assoc (1+K)⁻¹ (1+K) (1-K),
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp huB),
        Matrix.one_mul,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]

theorem matrixCayley_preserves_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℝ} (hK : Kᵀ = -K) (hu : IsUnit (1-K))
    (A : Matrix ι (Fin 3) ℝ) :
    (matrixCayley K*A)ᵀ*(matrixCayley K*A) = Aᵀ*A := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (matrixCayley K)ᵀ (matrixCayley K) A,
    matrixCayley_orthogonal hK hu,Matrix.one_mul]

/-- A prescribed second acceleration differs from the square of its skew
lift by a tangent vector. This is the algebra needed for a two-jet curve. -/
theorem residualAcceleration_tangent {ι : Type*} [Fintype ι]
    {A H W : Matrix ι (Fin 3) ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hH : FrameTangent A H)
    (hW : Aᵀ*W+Wᵀ*A = (-2 : ℝ) • (Hᵀ*H)) :
    FrameTangent A (W - skewLift s A H*(skewLift s A H*A)) := by
  let O := skewLift s A H
  have hO : Oᵀ = -O := skewLift_skew s hH
  have hOH : O*A=H := skewLift_mul_frame hA hs hH
  have h1 : Aᵀ*(O*(O*A)) = -(Hᵀ*H) := by
    rw [hOH]
    have ht : Aᵀ*O = -Hᵀ := by
      have hh := congrArg Matrix.transpose hOH
      simp only [Matrix.transpose_mul,hO,Matrix.mul_neg] at hh
      exact neg_eq_iff_eq_neg.mp hh
    rw [← Matrix.mul_assoc,ht,Matrix.neg_mul]
  have h2 : (O*(O*A))ᵀ*A = -(Hᵀ*H) := by
    have hh := congrArg Matrix.transpose h1
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,
      Matrix.transpose_neg] using hh
  have heq : Aᵀ*(W-O*(O*A))+(W-O*(O*A))ᵀ*A=0 := by
    rw [Matrix.mul_sub,Matrix.transpose_sub,Matrix.sub_mul,h1,h2]
    have hh := hW
    ext j k
    have hjk := congrFun (congrFun hh j) k
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,
      Matrix.zero_apply,Matrix.smul_apply,smul_eq_mul] at *
    linarith
  intro j k
  have hjk := congrFun (congrFun heq j) k
  change crossGram A (W-O*(O*A)) j k +
    crossGram A (W-O*(O*A)) k j = 0
  unfold crossGram
  simpa [Matrix.mul_apply,Matrix.transpose_apply,mul_comm] using hjk

end
end F3
