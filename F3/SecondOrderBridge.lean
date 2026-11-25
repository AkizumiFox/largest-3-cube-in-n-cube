import F3.OptimizationBridge
import F3.VariationAlgebra
import F3.MatrixCurves
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Strict second-order descent from the affine alternative and actual curve jets. -/

namespace F3
noncomputable section
open scoped BigOperators Topology
open Filter

/-- Pointwise second-jet interface, including a derivative on a whole neighborhood. -/
def SecondJetCurvesExist {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (s : ℝ) : Prop :=
  ∀ H W, FrameTangent A H →
    (∀ j k, crossGram A W j k + crossGram A W k j = -2*crossGram H H j k) →
    ∃ c c' : ℝ → ι → Fin 3 → ℝ,
      c 0 = A ∧ c' 0 = H ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ j k,
        crossGram (c t) (c t) j k = if j=k then s else 0) ∧
      (∀ i j, ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => c t i j) (c' t i j) t) ∧
      ∀ i j, HasDerivAt (fun t => c' t i j) (W i j) 0

theorem secondJetCurvesExist {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s) :
    SecondJetCurvesExist A s := by
  classical
  intro H W hH hW
  obtain ⟨c,c',hc,hc',hgram,hder,hsecond⟩ :=
    exists_matrix_second_jet_curve hA hs hH hW
  refine ⟨c,c',hc,hc',hgram,?_,hsecond⟩
  intro i j
  exact hder.mono (fun t ht => ht i j)

theorem exists_strict_second_acceleration {ι : Type*} [Fintype ι]
    {A H : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (hcurv : ∀ M : MultiplierSystem A, 0 < curvature M.matrix H) :
    ∃ K : ι → Fin 3 → ℝ, FrameTangent A K ∧
      ∀ i σ, facetValue (A i) σ=1 →
        facetValue (fun j => normalAcceleration s A H i j + K i j) σ < 0 := by
  classical
  by_cases hex : ∃ K : ι → Fin 3 → ℝ, FrameTangent A K ∧
      ∀ i σ, facetValue (A i) σ=1 →
        facetValue (fun j => normalAcceleration s A H i j + K i j) σ < 0
  · exact hex
  exfalso
  have hNo : NoStrictAffineTangentDescent A (normalAcceleration s A H) := by
    intro K hK
    by_cases he : ∃ i σ, facetValue (A i) σ=1 ∧
        0 ≤ facetValue (fun j => normalAcceleration s A H i j + K i j) σ
    · exact he
    · exfalso
      apply hex
      refine ⟨K,hK,?_⟩
      intro i σ ha
      exact lt_of_not_ge (fun hh => he ⟨i,σ,ha,hh⟩)
  obtain ⟨F,hF⟩ := exists_facetWeights_of_no_affine_tangent_descent hA hs hNo
  obtain ⟨M,hM⟩ := exists_multiplier_realizing_facetWeights hA hs F
  have he := normalAcceleration_pairing hA hs H M.matrix
  rw [hM,weightedFacetGradient_pairing] at he
  have hp := hcurv M
  linarith

theorem eventually_lt_of_negative_second_derivative {f g : ℝ → ℝ} {d : ℝ}
    (hder : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt f (g t) t)
    (hg0 : g 0=0) (hg : HasDerivAt g d 0) (hd : d<0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
  have hgn : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t<0 := by
    simpa only [hg0] using eventually_lt_of_negative_derivative hg hd
  have hgnear : ∀ᶠ t in 𝓝 (0 : ℝ), 0<t → g t<0 :=
    eventually_nhdsWithin_iff.mp hgn
  obtain ⟨l,u,⟨hl,hu⟩,hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hder.and hgnear)
  let δ : ℝ := u/2
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hsub {x : ℝ} (hx : x ∈ Set.Icc 0 δ) : x ∈ Set.Ioo l u := by
    constructor
    · linarith [hx.1]
    · dsimp [δ] at hx
      linarith [hx.2]
  have hcont : ContinuousOn f (Set.Icc 0 δ) := by
    intro x hx
    exact ((hI (hsub hx)).1).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f (Set.Icc 0 δ) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont
    intro x hx
    rw [interior_Icc] at hx
    have hspec := hI (hsub ⟨hx.1.le,hx.2.le⟩)
    rw [hspec.1.deriv]
    exact hspec.2 hx.1
  have htδ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t<δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [htδ,self_mem_nhdsWithin] with t ht ht0
  exact hanti ⟨le_rfl,hδ.le⟩ ⟨ht0.le,ht.le⟩ ht0

theorem strict_second_order_descent_of_curves {n : ℕ}
    {A H : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s)
    (hH : FrameTangent A H)
    (hactive : ∀ i σ, facetValue (A i) σ=1 → facetValue (H i) σ=0)
    (hcurv : ∀ M : MultiplierSystem A, 0 < curvature M.matrix H)
    (hcurves : SecondJetCurvesExist A s) : False := by
  obtain ⟨K,hK,hdecrease⟩ := exists_strict_second_acceleration hA hs hcurv
  let W : Fin n → Fin 3 → ℝ := fun i j => normalAcceleration s A H i j+K i j
  have hW : ∀ j k, crossGram A W j k+crossGram A W k j = -2*crossGram H H j k := by
    intro j k
    have he := normalAcceleration_gram_second_variation hA hs H j k
    have hk := hK j k
    change (∑ i, A i j*(normalAcceleration s A H i k+K i k))+
      (∑ i, A i k*(normalAcceleration s A H i j+K i j)) = _
    simp only [mul_add,Finset.sum_add_distrib]
    change (crossGram A (normalAcceleration s A H) j k+crossGram A K j k)+
      (crossGram A (normalAcceleration s A H) k j+crossGram A K k j) = _
    linarith
  obtain ⟨c,c',hc0,hc'0,hgram,hder,hsecond⟩ := hcurves H W hH hW
  have hfirst0 : ∀ i j, HasDerivAt (fun t => c t i j) (H i j) 0 := by
    intro i j
    have h := mem_of_mem_nhds (hder i j)
    change HasDerivAt (fun t => c t i j) (c' 0 i j) 0 at h
    simpa only [hc'0] using h
  have hderall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i j,
      HasDerivAt (fun t => c t i j) (c' t i j) t :=
    eventually_all.2 (fun i => eventually_all.2 (hder i))
  have he (i : Fin n) (σ : Fin 3 → Bool) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), facetValue (c t i) σ<1 := by
    by_cases ha : facetValue (A i) σ=1
    · have hfd : ∀ᶠ t in 𝓝 (0 : ℝ),
          HasDerivAt (fun t => facetValue (c t i) σ) (facetValue (c' t i) σ) t :=
        hderall.mono (fun t ht => hasDerivAt_facetValue ht i σ)
      have hgd : HasDerivAt (fun t => facetValue (c' t i) σ) (facetValue (W i) σ) 0 :=
        hasDerivAt_facetValue hsecond i σ
      have hg0 : facetValue (c' 0 i) σ=0 := by rw [hc'0]; exact hactive i σ ha
      have hnegative : facetValue (W i) σ<0 := hdecrease i σ ha
      have h := eventually_lt_of_negative_second_derivative hfd hg0 hgd hnegative
      simpa only [hc0,ha] using h
    · have hf := hasDerivAt_facetValue hfirst0 i σ
      have hlt : facetValue (A i) σ<1 := lt_of_le_of_ne (facetValue_le_one (hA.1 i) σ) ha
      have hlt0 : facetValue (c 0 i) σ<1 := by simpa only [hc0] using hlt
      exact (hf.continuousAt.eventually (eventually_lt_nhds hlt0)).filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i σ, facetValue (c t i) σ<1 :=
    eventually_all.2 (fun i => eventually_all.2 (he i))
  have hgram' := hgram.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  obtain ⟨t,hgt,hlt⟩ := (hgram'.and hall).exists
  exact no_strict_fixedGram_improvement hs hopt (c t) hgt hlt

theorem strict_second_order_descent {n : ℕ}
    {A H : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s)
    (hH : FrameTangent A H)
    (hactive : ∀ i σ, facetValue (A i) σ=1 → facetValue (H i) σ=0)
    (hcurv : ∀ M : MultiplierSystem A, 0 < curvature M.matrix H) : False :=
  strict_second_order_descent_of_curves hA hs hopt hH hactive hcurv
    (secondJetCurvesExist hA hs)

theorem no_face_tangent_at_full_optimum {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s)
    (hw : ∀ M : MultiplierSystem A, ∀ i, 0 < M.weight i)
    (hfull : ∃ i, ∀ j, A i j ≠ 0) :
    ∀ H, FrameTangent A H →
      (∀ i σ, facetValue (A i) σ=1 → facetValue (H i) σ=0) → H=0 := by
  intro H hH hactive
  by_contra hne
  obtain ⟨i,hi⟩ := hfull
  exact strict_second_order_descent hA hs hopt hH hactive
    (fun M => curvature_positive_of_full_row hA hs M (hw M) i hi hne)

end
end F3
