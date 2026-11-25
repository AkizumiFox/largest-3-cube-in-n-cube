import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! First and second derivatives of the Cayley curve in a real normed algebra. -/
namespace F3
noncomputable section
open scoped Topology

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [HasSummableGeomSeries R]

theorem hasDerivAt_ringInverse_comp {f : ℝ → R} {v : R} {t : ℝ}
    (hf : HasDerivAt f v t) (hu : IsUnit (f t)) :
    HasDerivAt (fun x => Ring.inverse (f x))
      (-(Ring.inverse (f t)*v*Ring.inverse (f t))) t := by
  obtain ⟨u,hu⟩ := hu
  have hi : HasFDerivAt (Ring.inverse : R → R)
      (-ContinuousLinearMap.mulLeftRight ℝ R (↑u⁻¹) (↑u⁻¹)) (f t) := by
    rw [← hu]
    exact hasFDerivAt_ringInverse (𝕜:=ℝ) u
  have h := hi.comp_hasDerivAt t hf
  simpa only [Function.comp_def,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply,← hu,Ring.inverse_unit] using h

def cayleyRing (K : R) : R := (1+K)*Ring.inverse (1-K)

def cayleyRingDerivative (K V : R) : R :=
  V*Ring.inverse (1-K) +
    (1+K)*(Ring.inverse (1-K)*V*Ring.inverse (1-K))

theorem hasDerivAt_cayleyRing {K : ℝ → R} {V : R} {t : ℝ}
    (hK : HasDerivAt K V t) (hu : IsUnit (1-K t)) :
    HasDerivAt (fun x => cayleyRing (K x))
      (cayleyRingDerivative (K t) V) t := by
  have hi := hasDerivAt_ringInverse_comp ((hasDerivAt_const t (1:R)).sub hK) hu
  have h := ((hasDerivAt_const t (1:R)).add hK).mul hi
  simpa only [cayleyRing,cayleyRingDerivative,zero_add,zero_sub,
    mul_neg,neg_mul,neg_neg] using h

theorem cayleyRing_zero : cayleyRing (0:R)=1 := by
  simp [cayleyRing,Ring.inverse_one]

theorem cayleyRingDerivative_zero (V : R) : cayleyRingDerivative 0 V = V+V := by
  simp [cayleyRingDerivative,Ring.inverse_one]

theorem hasDerivAt_cayleyRingDerivative_zero
    {K G : ℝ → R} {V W : R}
    (hK0 : K 0=0) (hG0 : G 0=V)
    (hK : HasDerivAt K V 0) (hG : HasDerivAt G W 0) :
    HasDerivAt (fun t => cayleyRingDerivative (K t) (G t))
      ((4:ℝ) • (V*V)+(2:ℝ) • W) 0 := by
  have hu : IsUnit (1-K 0) := by simp [hK0]
  have hi0 := hasDerivAt_ringInverse_comp ((hasDerivAt_const 0 (1:R)).sub hK) hu
  have hi : HasDerivAt (fun t => Ring.inverse (1-K t)) V 0 := by
    simpa [hK0,Ring.inverse_one] using hi0
  have h := (hG.mul hi).add
    (((hasDerivAt_const 0 (1:R)).add hK).mul ((hi.mul hG).mul hi))
  simp only [hK0,hG0,sub_zero,add_zero,zero_add,Ring.inverse_one,
    mul_one,one_mul] at h
  convert h using 1
  module

def cayleyParameter (O P : R) (t : ℝ) : R := (t/2) • O + (t^2/4) • P
def cayleyParameterDerivative (O P : R) (t : ℝ) : R :=
  (1/2:ℝ) • O + (t/2) • P

theorem cayleyParameter_hasDerivAt (O P : R) (t : ℝ) :
    HasDerivAt (cayleyParameter O P) (cayleyParameterDerivative O P t) t := by
  have h := (((hasDerivAt_id t).div_const 2).smul_const O).add
    ((((hasDerivAt_id t).pow 2).div_const 4).smul_const P)
  convert h using 1 <;> dsimp [cayleyParameter,cayleyParameterDerivative]
  congr 1
  congr 1
  ring

theorem cayleyParameterDerivative_hasDerivAt (O P : R) (t : ℝ) :
    HasDerivAt (cayleyParameterDerivative O P) ((1/2:ℝ) • P) t := by
  simpa only [cayleyParameterDerivative,zero_add,id_eq] using
    (hasDerivAt_const t ((1/2:ℝ) • O)).add
      (((hasDerivAt_id t).div_const 2).smul_const P)

def cayleyCurve (O P : R) (t : ℝ) : R := cayleyRing (cayleyParameter O P t)
def cayleyCurveDerivative (O P : R) (t : ℝ) : R :=
  cayleyRingDerivative (cayleyParameter O P t) (cayleyParameterDerivative O P t)

theorem cayleyCurve_zero (O P : R) : cayleyCurve O P 0 = 1 := by
  simp [cayleyCurve,cayleyParameter,cayleyRing_zero]

theorem cayleyCurveDerivative_zero (O P : R) : cayleyCurveDerivative O P 0 = O := by
  norm_num [cayleyCurveDerivative,cayleyParameter,cayleyParameterDerivative,
    cayleyRingDerivative_zero]
  module

theorem cayleyCurve_hasDerivAt {O P : R} {t : ℝ}
    (hu : IsUnit (1-cayleyParameter O P t)) :
    HasDerivAt (cayleyCurve O P) (cayleyCurveDerivative O P t) t :=
  hasDerivAt_cayleyRing (cayleyParameter_hasDerivAt O P t) hu

theorem cayleyCurve_hasDerivAt_zero (O P : R) :
    HasDerivAt (cayleyCurve O P) O 0 := by
  have h := cayleyCurve_hasDerivAt (O:=O) (P:=P) (t:=0)
    (by simp [cayleyParameter])
  rwa [cayleyCurveDerivative_zero] at h

theorem cayleyCurveDerivative_hasDerivAt_zero (O P : R) :
    HasDerivAt (cayleyCurveDerivative O P) (O*O+P) 0 := by
  have h := hasDerivAt_cayleyRingDerivative_zero
    (K:=cayleyParameter O P) (G:=cayleyParameterDerivative O P)
    (V:=(1/2:ℝ) • O) (W:=(1/2:ℝ) • P)
    (by simp [cayleyParameter]) (by simp [cayleyParameterDerivative])
    (by simpa [cayleyParameterDerivative] using cayleyParameter_hasDerivAt O P 0)
    (cayleyParameterDerivative_hasDerivAt O P 0)
  convert h using 1
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  module

end
end F3
