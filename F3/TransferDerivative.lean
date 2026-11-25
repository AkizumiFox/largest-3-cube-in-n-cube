import F3.Transfer
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace F3.Transfer
noncomputable section

/-- The derivative of the inverse edge-transfer envelope on its analytic
domain. -/
theorem hasDerivAt_B {D : ℝ} (hD : D<2) :
    HasDerivAt B (1/Real.sqrt (1-D/2)-1) D := by
  have hu : 0<1-D/2 := by linarith
  have hr : HasDerivAt (fun x : ℝ=>1-x/2) (-1/2) D := by
    convert (hasDerivAt_const D (1 : ℝ)).sub ((hasDerivAt_id D).div_const 2) using 1 <;> norm_num
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt hu)).comp D hr
  have hb := (((hasDerivAt_const D (1 : ℝ)).sub hs).pow 2).const_mul 2
  have hroot : Real.sqrt (1-D/2)≠0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  have halg (t : ℝ) (ht : t≠0) : 1/t-1=2*(2*(1-t)*(0-1/(2*t)*(-1/2))) := by
    field_simp
    ring
  convert hb using 1
  simpa only [Function.comp_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one] using halg _ hroot

theorem deriv_B {D : ℝ} (hD : D<2) : deriv B D=1/Real.sqrt (1-D/2)-1 :=
  (hasDerivAt_B hD).deriv

/-- The strict derivative range in the transfer lemma, including the zero
endpoint. -/
theorem deriv_B_range {D : ℝ} (hD0 : 0≤D) (hD : D<3/2) :
    0≤deriv B D ∧ deriv B D<1 := by
  rw [deriv_B (by linarith)]
  have hu : 0<1-D/2 := by linarith
  have hroot := Real.sqrt_nonneg (1-D/2)
  have hrootsq := Real.sq_sqrt hu.le
  have hroot1 : Real.sqrt (1-D/2)≤1 := by nlinarith
  have hroothalf : 1/2<Real.sqrt (1-D/2) := by nlinarith
  have hrootpos : 0<Real.sqrt (1-D/2) := by linarith
  have hlo : 1≤1/Real.sqrt (1-D/2) := (le_div_iff₀ hrootpos).mpr (by simpa using hroot1)
  have hhi : 1/Real.sqrt (1-D/2)<2 := (div_lt_iff₀ hrootpos).mpr (by linarith)
  exact ⟨by linarith,by linarith⟩

end
end F3.Transfer
