import F3.CayleyAlgebra
import F3.CayleyCalculus
import F3.OptimizationBridge
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Exact fixed-Gram curves realizing prescribed compatible first and second
jets.  The Cayley transform is used only inside this proof; the public curve
statements concern ordinary real-valued matrix entries. -/
namespace F3
noncomputable section
open scoped BigOperators Matrix Topology
open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def appliedEntry (A : Matrix ι (Fin 3) ℝ) (i : ι) (j : Fin 3) :
    Matrix ι ι ℝ →ₗ[ℝ] ℝ where
  toFun O := (O*A) i j
  map_add' O P := by simp [Matrix.add_mul]
  map_smul' r O := by simp [Matrix.smul_mul]

theorem appliedEntry_hasDerivAt {c : ℝ → Matrix ι ι ℝ}
    {V : Matrix ι ι ℝ} {t : ℝ} (hc : HasDerivAt c V t)
    (A : Matrix ι (Fin 3) ℝ) (i : ι) (j : Fin 3) :
    HasDerivAt (fun t => (c t*A) i j) ((V*A) i j) t := by
  let L := LinearMap.toContinuousLinearMap (appliedEntry A i j)
  exact L.hasFDerivAt.comp_hasDerivAt t hc

theorem cayleyParameter_eventually_unit (O P : Matrix ι ι ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (1-cayleyParameter O P t) := by
  have hc := (cayleyParameter_hasDerivAt O P 0).continuousAt
  have hcont : ContinuousAt (fun t => (1 : Matrix ι ι ℝ)-cayleyParameter O P t) 0 :=
    continuousAt_const.sub hc
  apply hcont.eventually
  apply Units.isOpen.mem_nhds
  simp [cayleyParameter]

theorem cayleyParameter_skew {O P : Matrix ι ι ℝ}
    (hO : Oᵀ=-O) (hP : Pᵀ=-P) (t : ℝ) :
    (cayleyParameter O P t)ᵀ = -cayleyParameter O P t := by
  simp [cayleyParameter,hO,hP,add_comm]

theorem cayleyCurve_preserves_gram {O P : Matrix ι ι ℝ}
    (hO : Oᵀ=-O) (hP : Pᵀ=-P) (A : Matrix ι (Fin 3) ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (cayleyCurve O P t*A)ᵀ*(cayleyCurve O P t*A)=Aᵀ*A := by
  filter_upwards [cayleyParameter_eventually_unit O P] with t ht
  simpa only [cayleyCurve,cayleyRing,matrixCayley,Matrix.nonsing_inv_eq_ringInverse]
    using matrixCayley_preserves_gram (cayleyParameter_skew hO hP t) ht A

theorem tangentCurvesExist {A : Matrix ι (Fin 3) ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) : TangentCurvesExist A s := by
  intro H hH
  let O := skewLift s A H
  refine ⟨fun t => cayleyCurve O 0 t*A,?_,?_,?_⟩
  · simp only [cayleyCurve_zero,Matrix.one_mul]
  · have hgram := cayleyCurve_preserves_gram
      (skewLift_skew s hH) (show (0 : Matrix ι ι ℝ)ᵀ = -0 by simp) A
    filter_upwards [hgram] with t ht j k
    have hjk := congrFun (congrFun ht j) k
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,hA.2] using hjk
  · intro i j
    have hd := appliedEntry_hasDerivAt (cayleyCurve_hasDerivAt_zero O 0) A i j
    simpa only [O,skewLift_mul_frame hA hs hH] using hd

theorem exists_multiplier_at_optimum {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s) :
    Nonempty (MultiplierSystem A) :=
  exists_multiplier_at_optimum_of_curves hA hs hopt (tangentCurvesExist hA hs)

theorem exists_matrix_second_jet_curve
    {A H W : Matrix ι (Fin 3) ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hH : FrameTangent A H)
    (hW : ∀ j k, crossGram A W j k+crossGram A W k j =
      -2*crossGram H H j k) :
    ∃ c c' : ℝ → Matrix ι (Fin 3) ℝ,
      c 0=A ∧ c' 0=H ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ j k,
        crossGram (c t) (c t) j k = if j=k then s else 0) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ i j,
        HasDerivAt (fun t => c t i j) (c' t i j) t) ∧
      ∀ i j, HasDerivAt (fun t => c' t i j) (W i j) 0 := by
  let O := skewLift s A H
  let R := W-O*(O*A)
  have hO : Oᵀ=-O := skewLift_skew s hH
  have hOA : O*A=H := skewLift_mul_frame hA hs hH
  have hWmat : Aᵀ*W+Wᵀ*A=(-2 : ℝ) • (Hᵀ*H) := by
    ext j k
    have hh := hW j k
    simpa [crossGram,Matrix.mul_apply,Matrix.transpose_apply,mul_comm] using hh
  have hR : FrameTangent A R := residualAcceleration_tangent hA hs hH hWmat
  let P := skewLift s A R
  have hP : Pᵀ=-P := skewLift_skew s hR
  have hPA : P*A=R := skewLift_mul_frame hA hs hR
  have hacc : (O*O+P)*A=W := by
    rw [Matrix.add_mul,Matrix.mul_assoc,hPA]
    dsimp [R]
    abel
  refine ⟨fun t => cayleyCurve O P t*A,
    fun t => cayleyCurveDerivative O P t*A,?_,?_,?_,?_,?_⟩
  · simp only [cayleyCurve_zero,Matrix.one_mul]
  · simpa only [cayleyCurveDerivative_zero] using hOA
  · filter_upwards [cayleyCurve_preserves_gram hO hP A] with t ht j k
    have hjk := congrFun (congrFun ht j) k
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,hA.2] using hjk
  · filter_upwards [cayleyParameter_eventually_unit O P] with t ht i j
    exact appliedEntry_hasDerivAt (cayleyCurve_hasDerivAt ht) A i j
  · intro i j
    have hd := appliedEntry_hasDerivAt
      (cayleyCurveDerivative_hasDerivAt_zero O P) A i j
    simpa only [hacc] using hd

end
end F3
