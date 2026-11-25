import F3.SecondOrderBridge
import Mathlib.Topology.Order.LocalExtr

/-! Local minimizers of the actual maximum row norm and the second-order
strict-descent statement in its local form. -/

namespace F3
noncomputable section
open scoped BigOperators Topology
open Filter

def maxRowBudget {n : ℕ} (A : Fin n → Fin 3 → ℝ) : ℝ :=
  Finset.univ.sup' (show (Finset.univ : Finset (Fin n ⊕ Unit)).Nonempty from
    ⟨Sum.inr (),Finset.mem_univ _⟩)
    (Sum.elim (fun i => |A i 0|+|A i 1|+|A i 2|) (fun _ => 0))

def fixedGramSet (n : ℕ) (s : ℝ) : Set (Fin n → Fin 3 → ℝ) :=
  {A | ∀ j k,crossGram A A j k=if j=k then s else 0}

theorem rowBudget_le_maxRowBudget {n : ℕ} (A : Fin n → Fin 3 → ℝ) (i : Fin n) :
    |A i 0|+|A i 1|+|A i 2|≤maxRowBudget A := by
  unfold maxRowBudget
  exact Finset.le_sup'
    (Sum.elim (fun q : Fin n => |A q 0|+|A q 1|+|A q 2|) (fun _ : Unit => (0 : ℝ)))
    (Finset.mem_univ (Sum.inl i))

theorem facetValue_le_maxRowBudget {n : ℕ} (A : Fin n → Fin 3 → ℝ)
    (i : Fin n) (σ : Fin 3 → Bool) : facetValue (A i) σ≤maxRowBudget A := by
  calc
    _ ≤ ∑ j, |A i j| := Finset.sum_le_sum (fun j _ => facet_coordinate_le_abs (A i) σ j)
    _ = |A i 0|+|A i 1|+|A i 2| := Fin.sum_univ_three _
    _ ≤ _ := rowBudget_le_maxRowBudget A i

theorem maxRowBudget_lt_one_of_facets {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (h : ∀ i σ,facetValue (A i) σ<1) : maxRowBudget A<1 := by
  unfold maxRowBudget
  apply (Finset.sup'_lt_iff _).mpr
  intro i _
  cases i with
  | inl i => simpa only [Sum.elim_inl,facetValue_canonical] using h i (canonicalFacet (A i))
  | inr u => norm_num

theorem maxRowBudget_eq_one_of_optimum {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s) : maxRowBudget A=1 := by
  have hle : maxRowBudget A≤1 := by
    unfold maxRowBudget
    apply (Finset.sup'_le_iff _ _).mpr
    intro i _
    cases i with
    | inl i => exact hA.1 i
    | inr u => norm_num
  have hnot : ¬maxRowBudget A<1 := by
    intro hh
    apply no_strict_fixedGram_improvement hs hopt A hA.2
    intro i σ
    exact (facetValue_le_maxRowBudget A i σ).trans_lt hh
  exact le_antisymm hle (le_of_not_gt hnot)

theorem exists_second_order_curve_with_strict_facets {n : ℕ}
    {A H : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s)
    (hH : FrameTangent A H)
    (hactive : ∀ i σ, facetValue (A i) σ=1 → facetValue (H i) σ=0)
    (hcurv : ∀ M : MultiplierSystem A, 0 < curvature M.matrix H) :
    ∃ c : ℝ → Fin n → Fin 3 → ℝ, c 0=A ∧ ContinuousAt c 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),c t∈fixedGramSet n s) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ),∀ i σ,facetValue (c t i) σ<1) := by
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
  obtain ⟨c,c',hc0,hc'0,hgram,hder,hsecond⟩ := secondJetCurvesExist hA hs H W hH hW
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
  refine ⟨c,hc0,?_,hgram,hall⟩
  exact continuousAt_pi.2 (fun i => continuousAt_pi.2 (fun j => (hfirst0 i j).continuousAt))

theorem strict_second_order_not_local_min {n : ℕ}
    {A H : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hunit : maxRowBudget A=1)
    (hH : FrameTangent A H)
    (hactive : ∀ i σ,facetValue (A i) σ=1 → facetValue (H i) σ=0)
    (hcurv : ∀ M : MultiplierSystem A,0<curvature M.matrix H) :
    ¬IsLocalMinOn maxRowBudget (fixedGramSet n s) A := by
  intro hlocal
  obtain ⟨c,hc0,hcont,hgram,hfacets⟩ :=
    exists_second_order_curve_with_strict_facets hA hs hH hactive hcurv
  change ∀ᶠ B in 𝓝[fixedGramSet n s] A,maxRowBudget A≤maxRowBudget B at hlocal
  have hnear : ∀ᶠ B in 𝓝 A,B∈fixedGramSet n s → maxRowBudget A≤maxRowBudget B :=
    eventually_nhdsWithin_iff.mp hlocal
  have htend : Tendsto c (𝓝 (0 : ℝ)) (𝓝 A) := by
    change Tendsto c (𝓝 (0 : ℝ)) (𝓝 (c 0)) at hcont
    simpa only [hc0] using hcont
  have hcurve := htend.eventually hnear
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ),1≤maxRowBudget (c t) := by
    filter_upwards [hcurve,hgram] with t ht hg
    simpa only [hunit] using ht hg
  have hbound' := hbound.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ)≤𝓝 0)
  obtain ⟨t,ht,hf⟩ := (hbound'.and hfacets).exists
  exact not_lt_of_ge ht (maxRowBudget_lt_one_of_facets hf)

theorem strict_second_order_not_local_min_at_optimum {n : ℕ}
    {A H : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s)
    (hH : FrameTangent A H)
    (hactive : ∀ i σ,facetValue (A i) σ=1 → facetValue (H i) σ=0)
    (hcurv : ∀ M : MultiplierSystem A,0<curvature M.matrix H) :
    ¬IsLocalMinOn maxRowBudget (fixedGramSet n s) A :=
  strict_second_order_not_local_min hA hs (maxRowBudget_eq_one_of_optimum hA hs hopt)
    hH hactive hcurv

end
end F3
