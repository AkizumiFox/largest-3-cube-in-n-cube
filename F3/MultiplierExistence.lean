import F3.MultiplierAlgebra
import F3.TangentNormal
import F3.FiniteAlternative

/-!
# From normalized active-facet weights to row multipliers

This file proves the grouping and normal-space step of the multiplier lemma.
It does not assume that a maximizing frame has such weights, and does not yet
assert that existence theorem. The optimizer-to-facet-weights step requires a
separate first-order alternative and a curve in the fixed-Gram manifold.
-/

namespace F3
noncomputable section
open scoped BigOperators

def facetSign (σ : Fin 3 → Bool) (j : Fin 3) : ℝ := if σ j then 1 else -1

def facetValue (a : Fin 3 → ℝ) (σ : Fin 3 → Bool) : ℝ :=
  ∑ j, a j * facetSign σ j

theorem facetSign_abs (σ : Fin 3 → Bool) (j : Fin 3) : |facetSign σ j| = 1 := by
  unfold facetSign
  split <;> norm_num

theorem facet_coordinate_le_abs (a : Fin 3 → ℝ) (σ : Fin 3 → Bool) (j : Fin 3) :
    a j * facetSign σ j ≤ |a j| := by
  unfold facetSign
  split
  · simpa using le_abs_self (a j)
  · simpa using neg_le_abs (a j)

theorem active_facet_saturated {a : Fin 3 → ℝ} {σ : Fin 3 → Bool}
    (ha : RowBound a) (hσ : facetValue a σ = 1) :
    |a 0| + |a 1| + |a 2| = 1 := by
  have hle : facetValue a σ ≤ |a 0| + |a 1| + |a 2| := by
    calc
      _ ≤ ∑ j, |a j| := Finset.sum_le_sum (fun j _ => facet_coordinate_le_abs a σ j)
      _ = _ := Fin.sum_univ_three _
  unfold RowBound at ha
  linarith

theorem active_facet_subgradient {a : Fin 3 → ℝ} {σ : Fin 3 → Bool}
    (ha : RowBound a) (hσ : facetValue a σ = 1) : RowSubgradient a (facetSign σ) := by
  refine ⟨fun j => le_of_eq (facetSign_abs σ j), ?_⟩
  have hsat := active_facet_saturated ha hσ
  have hsum : (∑ j, (|a j| - a j * facetSign σ j)) = 0 := by
    rw [Finset.sum_sub_distrib]
    change (∑ j, |a j|) - facetValue a σ = 0
    rw [Fin.sum_univ_three, hsat, hσ]
    ring
  intro j
  have hz : |a j| - a j * facetSign σ j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sub_nonneg.mpr (facet_coordinate_le_abs a σ j))).mp hsum j (Finset.mem_univ j)
  linarith

def canonicalSubgradient (a : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  if 0 ≤ a j then 1 else -1

theorem canonicalSubgradient_spec (a : Fin 3 → ℝ) :
    RowSubgradient a (canonicalSubgradient a) := by
  constructor
  · intro j
    unfold canonicalSubgradient
    split <;> norm_num
  · intro j
    unfold canonicalSubgradient
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]

structure NormalizedFacetWeights {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) where
  coeff : ι → (Fin 3 → Bool) → ℝ
  nonneg : ∀ i σ, 0 ≤ coeff i σ
  normalized : (∑ i, ∑ σ, coeff i σ) = 1
  active : ∀ i σ, 0 < coeff i σ → facetValue (A i) σ = 1
  annihilates : ∀ H, FrameTangent A H →
    (∑ i, ∑ σ, coeff i σ * facetValue (H i) σ) = 0

def groupedWeight {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (W : NormalizedFacetWeights A) (i : ι) : ℝ := ∑ σ, W.coeff i σ

def weightedFacetGradient {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (W : NormalizedFacetWeights A) (i : ι) (j : Fin 3) : ℝ :=
  ∑ σ, W.coeff i σ * facetSign σ j

def groupedGradient {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (W : NormalizedFacetWeights A) (i : ι) (j : Fin 3) : ℝ :=
  if groupedWeight W i = 0 then canonicalSubgradient (A i) j
  else weightedFacetGradient W i j / groupedWeight W i

theorem groupedWeight_nonneg {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (W : NormalizedFacetWeights A) (i : ι) : 0 ≤ groupedWeight W i :=
  Finset.sum_nonneg (fun σ _ => W.nonneg i σ)

theorem weightedFacetGradient_abs_le {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (W : NormalizedFacetWeights A) (i : ι) (j : Fin 3) :
    |weightedFacetGradient W i j| ≤ groupedWeight W i := by
  calc
    _ ≤ ∑ σ, |W.coeff i σ * facetSign σ j| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [abs_mul, abs_of_nonneg (W.nonneg i σ), facetSign_abs, mul_one]

theorem grouped_gradient_product {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (W : NormalizedFacetWeights A) (i : ι) (j : Fin 3) :
    groupedWeight W i * groupedGradient W i j = weightedFacetGradient W i j := by
  unfold groupedGradient
  split_ifs with h
  · have hb := weightedFacetGradient_abs_le W i j
    rw [h] at hb
    have hz : weightedFacetGradient W i j = 0 := abs_nonpos_iff.mp hb
    rw [h, zero_mul, hz]
  · exact mul_div_cancel₀ _ h

theorem groupedGradient_subgradient {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (W : NormalizedFacetWeights A) (i : ι) : RowSubgradient (A i) (groupedGradient W i) := by
  by_cases hi : groupedWeight W i = 0
  · simpa only [RowSubgradient, groupedGradient, hi, if_true]
      using canonicalSubgradient_spec (A i)
  have hpos : 0 < groupedWeight W i :=
    lt_of_le_of_ne (groupedWeight_nonneg W i) (Ne.symm hi)
  constructor
  · intro j
    simp only [groupedGradient, hi, if_false, abs_div, abs_of_pos hpos]
    exact (div_le_one hpos).2 (weightedFacetGradient_abs_le W i j)
  · intro j
    have hprod : A i j * weightedFacetGradient W i j =
        groupedWeight W i * |A i j| := by
      unfold weightedFacetGradient groupedWeight
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ hσ
      by_cases hz : W.coeff i σ = 0
      · simp [hz]
      have hσpos : 0 < W.coeff i σ := lt_of_le_of_ne (W.nonneg i σ) (Ne.symm hz)
      have hsg := (active_facet_subgradient (hA.1 i) (W.active i σ hσpos)).2 j
      nlinarith
    simp only [groupedGradient, hi, if_false]
    rw [← mul_div_assoc, hprod]
    exact mul_div_cancel_left₀ _ hi

theorem groupedWeight_complementary {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (W : NormalizedFacetWeights A) (i : ι) (hi : 0 < groupedWeight W i) :
    |A i 0| + |A i 1| + |A i 2| = 1 := by
  have hex : ∃ σ, 0 < W.coeff i σ := by
    by_contra! h
    have hz : ∀ σ, W.coeff i σ = 0 := fun σ => le_antisymm (h σ) (W.nonneg i σ)
    have he : groupedWeight W i = 0 := by simp [groupedWeight, hz]
    linarith
  obtain ⟨σ,hσ⟩ := hex
  exact active_facet_saturated (hA.1 i) (W.active i σ hσ)

theorem weightedFacetGradient_annihilates {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (W : NormalizedFacetWeights A)
    (H : ι → Fin 3 → ℝ) (hH : FrameTangent A H) :
    framePairing (weightedFacetGradient W) H = 0 := by
  have he : framePairing (weightedFacetGradient W) H =
      ∑ i, ∑ σ, W.coeff i σ * facetValue (H i) σ := by
    unfold framePairing weightedFacetGradient facetValue
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact W.annihilates H hH

theorem exists_multiplier_of_facetWeights {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0 < s)
    (W : NormalizedFacetWeights A) : Nonempty (MultiplierSystem A) := by
  obtain ⟨S,hS,hG⟩ := exists_symmetric_normal_of_annihilates_tangent hA hs
    (fun H hH => weightedFacetGradient_annihilates W H hH)
  refine ⟨{
    weight := groupedWeight W
    gradient := groupedGradient W
    matrix := S
    weight_nonneg := groupedWeight_nonneg W
    weight_sum := W.normalized
    subgradient := groupedGradient_subgradient hA W
    symmetric := hS
    stationarity := ?_
    complementary := groupedWeight_complementary hA W
  }⟩
  intro i j
  change rightMul A S i j = groupedWeight W i * groupedGradient W i j
  rw [← hG, grouped_gradient_product]

theorem weightedFacetGradient_pairing {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (W : NormalizedFacetWeights A) (B : ι → Fin 3 → ℝ) :
    framePairing (weightedFacetGradient W) B =
      ∑ i, ∑ σ, W.coeff i σ * facetValue (B i) σ := by
  unfold framePairing weightedFacetGradient facetValue
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem exists_multiplier_realizing_facetWeights {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0 < s)
    (W : NormalizedFacetWeights A) :
    ∃ M : MultiplierSystem A, rightMul A M.matrix = weightedFacetGradient W := by
  obtain ⟨S,hS,hG⟩ := exists_symmetric_normal_of_annihilates_tangent hA hs
    (fun H hH => weightedFacetGradient_annihilates W H hH)
  let M : MultiplierSystem A := {
    weight := groupedWeight W
    gradient := groupedGradient W
    matrix := S
    weight_nonneg := groupedWeight_nonneg W
    weight_sum := W.normalized
    subgradient := groupedGradient_subgradient hA W
    symmetric := hS
    stationarity := by
      intro i j
      change rightMul A S i j = groupedWeight W i * groupedGradient W i j
      rw [← hG,grouped_gradient_product]
    complementary := groupedWeight_complementary hA W
  }
  exact ⟨M,hG.symm⟩

def facetMatrix {ι : Type*} [DecidableEq ι] (i : ι) (σ : Fin 3 → Bool)
    (r : ι) (j : Fin 3) : ℝ := if r = i then facetSign σ j else 0

theorem framePairing_facetMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (σ : Fin 3 → Bool) (H : ι → Fin 3 → ℝ) :
    framePairing (facetMatrix i σ) H = facetValue (H i) σ := by
  unfold framePairing facetMatrix facetValue
  simp only [ite_mul, zero_mul]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem framePairing_comm {ι : Type*} [Fintype ι]
    (G H : ι → Fin 3 → ℝ) : framePairing G H = framePairing H G := by
  unfold framePairing
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private def pushforwardWeight {κ χ : Type*} [Fintype κ] [DecidableEq χ]
    (f : κ → χ) (w : κ → ℝ) (q : χ) : ℝ := ∑ k, if f k = q then w k else 0

private theorem pushforwardWeight_sum {κ χ : Type*} [Fintype κ] [Fintype χ] [DecidableEq χ]
    (f : κ → χ) (w : κ → ℝ) (p : χ → ℝ) :
    (∑ q, pushforwardWeight f w q * p q) = ∑ k, w k * p (f k) := by
  unfold pushforwardWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp [ite_mul]

/-- No tangent direction strictly decreases every active affine facet. -/
def NoStrictAffineTangentDescent {ι : Type*} [Fintype ι]
    (A B : ι → Fin 3 → ℝ) : Prop :=
  ∀ H, FrameTangent A H → ∃ i σ,
    facetValue (A i) σ = 1 ∧ 0 ≤ facetValue (fun j => B i j + H i j) σ

theorem exists_facetWeights_of_no_affine_tangent_descent
    {ι : Type*} [Fintype ι] {A B : ι → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0 < s) (hNo : NoStrictAffineTangentDescent A B) :
    ∃ W : NormalizedFacetWeights A,
      0 ≤ ∑ i, ∑ σ, W.coeff i σ * facetValue (B i) σ := by
  classical
  let κ := {q : ι × (Fin 3 → Bool) // facetValue (A q.1) q.2 = 1}
  letI : Fintype κ := Fintype.ofFinite κ
  let P : κ → ι → Fin 3 → ℝ := fun f =>
    tangentProjection s A (facetMatrix f.val.1 f.val.2)
  let u : κ → (ι × Fin 3) → ℝ := fun f q => P f q.1 q.2
  let b : κ → ℝ := fun f => facetValue (B f.val.1) f.val.2
  have hP (f : κ) : FrameTangent A (P f) :=
    tangentProjection_tangent hA hs _
  have hp (f : κ) (H : ι → Fin 3 → ℝ) (hH : FrameTangent A H) :
      framePairing (P f) H = facetValue (H f.val.1) f.val.2 := by
    exact (framePairing_tangentProjection _ hH).trans (framePairing_facetMatrix _ _ H)
  have hno : ¬∃ v : (ι × Fin 3) → ℝ,
      ∀ f, (∑ q, u f q*v q)+b f < 0 := by
    rintro ⟨v,hv⟩
    let V : ι → Fin 3 → ℝ := fun i j => v (i,j)
    let H : ι → Fin 3 → ℝ := tangentProjection s A V
    have hH : FrameTangent A H := tangentProjection_tangent hA hs V
    obtain ⟨i,σ,hactive,hbound⟩ := hNo H hH
    let f : κ := ⟨(i,σ),hactive⟩
    have he : facetValue (H i) σ = ∑ q, u f q*v q := by
      calc
        _ = framePairing (P f) H := (hp f H hH).symm
        _ = framePairing H (P f) := framePairing_comm _ _
        _ = framePairing V (P f) := framePairing_tangentProjection V (hP f)
        _ = framePairing (P f) V := framePairing_comm _ _
        _ = _ := by simp only [framePairing,Fintype.sum_prod_type,u,V]
    have hsplit : facetValue (fun j => B i j+H i j) σ =
        facetValue (B i) σ + facetValue (H i) σ := by
      simp only [facetValue,add_mul,Finset.sum_add_distrib]
    rw [hsplit,he] at hbound
    have hneg := hv f
    change (∑ q, u f q*v q)+facetValue (B i) σ < 0 at hneg
    linarith
  obtain ⟨w,hw,hzero,hoff⟩ := affine_certificate_of_no_strict_solution u b hno
  let c : ι → (Fin 3 → Bool) → ℝ := fun i σ => pushforwardWeight Subtype.val w (i,σ)
  have hpush (p : ι → (Fin 3 → Bool) → ℝ) :
      (∑ i, ∑ σ, c i σ*p i σ) = ∑ f : κ, w f*p f.val.1 f.val.2 := by
    simpa only [Fintype.sum_prod_type,c] using
      pushforwardWeight_sum (fun f : κ => f.val) w (fun q => p q.1 q.2)
  have hnonneg : ∀ i σ, 0 ≤ c i σ := by
    intro i σ
    apply Finset.sum_nonneg
    intro f hf
    change 0 ≤ if f.val = (i,σ) then w f else 0
    split_ifs
    · exact hw.1 f
    · exact le_rfl
  have hnorm : (∑ i, ∑ σ, c i σ) = 1 := by
    have he := hpush (fun _ _ => 1)
    simp only [mul_one] at he
    rw [he]
    exact hw.2
  have hactive : ∀ i σ, 0 < c i σ → facetValue (A i) σ = 1 := by
    intro i σ hpos
    by_cases hact : facetValue (A i) σ = 1
    · exact hact
    · have he : c i σ=0 := by
        apply Finset.sum_eq_zero
        intro f hf
        have hne : f.val ≠ (i,σ) := by
          intro hval
          have hf' := f.property
          rw [hval] at hf'
          exact hact hf'
        exact if_neg hne
      linarith
  have hann : ∀ H, FrameTangent A H →
      (∑ i, ∑ σ, c i σ*facetValue (H i) σ) = 0 := by
    intro H hH
    rw [hpush]
    have he : (∑ f : κ, w f*facetValue (H f.val.1) f.val.2) =
        ∑ q : ι × Fin 3, convexCombo u w q * H q.1 q.2 := by
      simp_rw [← hp _ H hH]
      unfold framePairing convexCombo
      simp_rw [Finset.mul_sum]
      rw [Fintype.sum_prod_type]
      calc
        _ = ∑ i, ∑ f : κ, ∑ j, w f*(P f i j*H i j) := by
          rw [Finset.sum_comm]
        _ = ∑ i, ∑ j, ∑ f : κ, w f*(P f i j*H i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
        _ = _ := by
          simp only [Finset.sum_mul,u]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro f hf
          ring
    rw [he]
    simp only [hzero,zero_mul,Finset.sum_const_zero]
  let W : NormalizedFacetWeights A := {
    coeff := c
    nonneg := hnonneg
    normalized := hnorm
    active := hactive
    annihilates := hann
  }
  refine ⟨W,?_⟩
  change 0 ≤ ∑ i, ∑ σ, c i σ*facetValue (B i) σ
  rw [hpush]
  exact hoff

theorem exists_multiplier_of_no_strict_tangent_descent
    {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0 < s)
    (hNo : ∀ H, FrameTangent A H → ∃ i σ,
      facetValue (A i) σ = 1 ∧ 0 ≤ facetValue (H i) σ) :
    Nonempty (MultiplierSystem A) := by
  have hno : NoStrictAffineTangentDescent A (fun _ _ => 0) := by
    intro H hH
    simpa only [zero_add] using hNo H hH
  obtain ⟨W,hW⟩ := exists_facetWeights_of_no_affine_tangent_descent hA hs hno
  exact exists_multiplier_of_facetWeights hA hs W

end
end F3
