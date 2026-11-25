import F3.MultiplierExistence
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

/-! The global optimum excludes a strict improvement of every cube facet. -/

namespace F3
noncomputable section
open scoped BigOperators
open scoped Topology
open Filter

def canonicalFacet (a : Fin 3 → ℝ) : Fin 3 → Bool := by
  classical
  exact fun j => decide (0 ≤ a j)

theorem facetValue_canonical (a : Fin 3 → ℝ) :
    facetValue a (canonicalFacet a) = |a 0|+|a 1|+|a 2| := by
  have he (j : Fin 3) : a j * facetSign (canonicalFacet a) j = |a j| := by
    by_cases h : 0 ≤ a j
    · simp [facetSign,canonicalFacet,h,abs_of_nonneg h]
    · simp [facetSign,canonicalFacet,h,abs_of_neg (lt_of_not_ge h)]
  unfold facetValue
  simp only [he,Fin.sum_univ_three]

theorem facetValue_le_one {a : Fin 3 → ℝ} (ha : RowBound a) (σ : Fin 3 → Bool) :
    facetValue a σ ≤ 1 := by
  calc
    _ ≤ ∑ j, |a j| := Finset.sum_le_sum (fun j _ => facet_coordinate_le_abs a σ j)
    _ = |a 0|+|a 1|+|a 2| := Fin.sum_univ_three _
    _ ≤ 1 := ha

theorem no_strict_fixedGram_improvement {n : ℕ} {s : ℝ}
    (hs : 0 < s) (hopt : OptimalValue n s)
    (B : Fin n → Fin 3 → ℝ)
    (hGram : ∀ j k, (∑ i, B i j*B i k) = if j=k then s else 0) :
    ¬ (∀ i σ, facetValue (B i) σ < 1) := by
  classical
  intro hstrict
  have hr (i : Fin n) : |B i 0|+|B i 1|+|B i 2| < 1 := by
    simpa only [facetValue_canonical] using hstrict i (canonicalFacet (B i))
  let f : Fin n ⊕ Unit → ℝ := Sum.elim
    (fun i => |B i 0|+|B i 1|+|B i 2|) (fun _ => 0)
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image Finset.univ f
    ⟨Sum.inr (),Finset.mem_univ _⟩
  have hm0 : 0 ≤ f k := hmax (Sum.inr ()) (Finset.mem_univ _)
  have hm1 : f k < 1 := by
    cases k with
    | inl i => exact hr i
    | inr z => norm_num [f]
  let t : ℝ := (f k+1)/2
  have ht : 0<t := by dsimp [t]; linarith
  have ht1 : t<1 := by dsimp [t]; linarith
  have hmt : f k ≤ t := by dsimp [t]; linarith
  have hrow (i : Fin n) : |B i 0|+|B i 1|+|B i 2| ≤ t :=
    (hmax (Sum.inl i) (Finset.mem_univ _)).trans hmt
  have hscaled : Feasible (s/t^2) (fun i j => B i j/t) := by
    constructor
    · intro i
      unfold RowBound
      simp only [abs_div,abs_of_pos ht]
      rw [← add_div,← add_div]
      exact (div_le_one ht).2 (hrow i)
    · intro j l
      have he (i : Fin n) : (B i j/t)*(B i l/t) =
          (B i j*B i l)*(t^2)⁻¹ := by
        simp only [div_eq_mul_inv, mul_pow]
        ring
      simp_rw [he]
      rw [← Finset.sum_mul,hGram]
      by_cases hjl : j=l <;> simp [hjl,div_eq_mul_inv]
  have hu := hopt.2 (s/t^2) ⟨_,hscaled⟩
  have hqpos : 0<t^2 := sq_pos_of_pos ht
  have hq : t^2<1 := by nlinarith
  have hb := (div_le_iff₀ hqpos).mp hu
  nlinarith

theorem eventually_lt_of_negative_derivative {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hd : d<0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
  have herr := (hasDerivAt_iff_isLittleO.mp hf).bound (show 0 < -d/2 by linarith)
  have herr' := herr.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  filter_upwards [herr',self_mem_nhdsWithin] with t he ht
  change 0<t at ht
  simp only [sub_zero,smul_eq_mul,Real.norm_eq_abs] at he
  rw [abs_of_pos ht] at he
  have hb := (abs_le.mp he).2
  have hm := mul_neg_of_pos_of_neg ht hd
  nlinarith

theorem hasDerivAt_facetValue {ι : Type*} {c : ℝ → ι → Fin 3 → ℝ}
    {H : ι → Fin 3 → ℝ} {t : ℝ}
    (hc : ∀ i j, HasDerivAt (fun t => c t i j) (H i j) t)
    (i : ι) (σ : Fin 3 → Bool) :
    HasDerivAt (fun t => facetValue (c t i) σ) (facetValue (H i) σ) t := by
  unfold facetValue
  apply HasDerivAt.sum
  intro j hj
  cases hσ : σ j
  · simpa [facetSign,hσ] using (hc i j).neg
  · simpa [facetSign,hσ] using hc i j

/-- Explicit pointwise interface for the first-order fixed-Gram curve. -/
def TangentCurvesExist {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (s : ℝ) : Prop :=
  ∀ H, FrameTangent A H → ∃ c : ℝ → ι → Fin 3 → ℝ,
    c 0 = A ∧
    (∀ᶠ t in 𝓝 (0 : ℝ), ∀ j k,
      crossGram (c t) (c t) j k = if j=k then s else 0) ∧
    ∀ i j, HasDerivAt (fun t => c t i j) (H i j) 0

theorem no_strict_tangent_descent_of_curves {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s)
    (hcurves : TangentCurvesExist A s) :
    ∀ H, FrameTangent A H → ∃ i σ,
      facetValue (A i) σ = 1 ∧ 0 ≤ facetValue (H i) σ := by
  classical
  intro H hH
  by_cases hex : ∃ i σ, facetValue (A i) σ=1 ∧ 0 ≤ facetValue (H i) σ
  · exact hex
  exfalso
  have hneg (i : Fin n) (σ : Fin 3 → Bool) (ha : facetValue (A i) σ=1) :
      facetValue (H i) σ<0 := lt_of_not_ge (fun hh => hex ⟨i,σ,ha,hh⟩)
  obtain ⟨c,hc0,hgram,hderiv⟩ := hcurves H hH
  have he (i : Fin n) (σ : Fin 3 → Bool) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), facetValue (c t i) σ<1 := by
    have hf := hasDerivAt_facetValue hderiv i σ
    by_cases ha : facetValue (A i) σ=1
    · have hlt := eventually_lt_of_negative_derivative hf (hneg i σ ha)
      simpa only [hc0,ha] using hlt
    · have hlt : facetValue (A i) σ<1 :=
        lt_of_le_of_ne (facetValue_le_one (hA.1 i) σ) ha
      have hlt0 : facetValue (c 0 i) σ<1 := by simpa only [hc0] using hlt
      have hneigh : ∀ᶠ t in 𝓝 (0 : ℝ), facetValue (c t i) σ<1 :=
        hf.continuousAt.eventually (eventually_lt_nhds hlt0)
      exact hneigh.filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i σ, facetValue (c t i) σ<1 :=
    eventually_all.2 (fun i => eventually_all.2 (he i))
  have hgram' := hgram.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  obtain ⟨t,hgt,hlt⟩ := (hgram'.and hall).exists
  exact no_strict_fixedGram_improvement hs hopt (c t) hgt hlt

theorem exists_multiplier_at_optimum_of_curves {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s)
    (hcurves : TangentCurvesExist A s) : Nonempty (MultiplierSystem A) :=
  exists_multiplier_of_no_strict_tangent_descent hA hs
    (no_strict_tangent_descent_of_curves hA hs hopt hcurves)

end
end F3
