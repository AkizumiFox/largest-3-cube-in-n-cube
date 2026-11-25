import F3.Frames
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real

/-! A finite strict alternative proved by compact-simplex minimization. -/

namespace F3
noncomputable section
open scoped BigOperators

def SimplexWeight {κ : Type*} [Fintype κ] (w : κ → ℝ) : Prop :=
  (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1

def convexCombo {κ η : Type*} [Fintype κ]
    (u : κ → η → ℝ) (w : κ → ℝ) (j : η) : ℝ := ∑ k, w k * u k j

private theorem sum_div_const {κ : Type*} [Fintype κ] (f : κ → ℝ) (d : ℝ) :
    (∑ k, f k/d) = (∑ k, f k)/d := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem isCompact_simplexWeight (κ : Type*) [Fintype κ] :
    IsCompact {w : κ → ℝ | SimplexWeight w} := by
  have hbox : IsCompact (Set.univ.pi (fun _ : κ => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hclosed : IsClosed {w : κ → ℝ | SimplexWeight w} := by
    change IsClosed ({w : κ → ℝ | ∀ k, 0 ≤ w k} ∩ {w : κ → ℝ | (∑ k, w k) = 1})
    apply IsClosed.inter
    · rw [Set.setOf_forall]
      exact isClosed_iInter (fun k => isClosed_le continuous_const (continuous_apply k))
    · exact isClosed_eq (continuous_finset_sum _ (fun k _ => continuous_apply k)) continuous_const
  apply hbox.of_isClosed_subset hclosed
  intro w hw
  simp only [Set.mem_univ_pi, Set.mem_Icc]
  intro k
  refine ⟨hw.1 k, ?_⟩
  calc
    w k ≤ ∑ i, w i := Finset.single_le_sum (fun i _ => hw.1 i) (Finset.mem_univ k)
    _ = 1 := hw.2

theorem simplexWeight_nonempty (κ : Type*) [Fintype κ] [Nonempty κ] :
    ({w : κ → ℝ | SimplexWeight w}).Nonempty := by
  classical
  let k₀ : κ := Classical.choice inferInstance
  refine ⟨fun k => if k = k₀ then 1 else 0, ?_, ?_⟩
  · intro k
    change 0 ≤ if k = k₀ then (1 : ℝ) else 0
    split_ifs <;> norm_num
  · simp

theorem continuous_convexCombo {κ η : Type*} [Fintype κ]
    (u : κ → η → ℝ) (j : η) : Continuous (fun w => convexCombo u w j) := by
  apply continuous_finset_sum
  intro k hk
  exact (continuous_apply k).mul continuous_const

theorem simplexWeight_segment {κ : Type*} [Fintype κ] [DecidableEq κ]
    {w : κ → ℝ} (hw : SimplexWeight w) (k₀ : κ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SimplexWeight (fun k => (1-t)*w k + t*(if k = k₀ then 1 else 0)) := by
  classical
  constructor
  · intro k
    change 0 ≤ (1-t)*w k + t*(if k = k₀ then 1 else 0)
    have hA := mul_nonneg (sub_nonneg.mpr ht1) (hw.1 k)
    split_ifs <;> nlinarith
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2]
    simp

theorem convexCombo_segment {κ η : Type*} [Fintype κ] [DecidableEq κ]
    (u : κ → η → ℝ) (w : κ → ℝ) (k₀ : κ) (t : ℝ) (j : η) :
    convexCombo u (fun k => (1-t)*w k + t*(if k = k₀ then 1 else 0)) j =
      (1-t)*convexCombo u w j + t*u k₀ j := by
  classical
  unfold convexCombo
  simp_rw [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [ite_mul]

private theorem quadratic_right_derivative_nonneg {a b : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ 2*t*b+t^2*a) : 0 ≤ b := by
  by_contra hn
  have hb : b < 0 := lt_of_not_ge hn
  let d : ℝ := |a| - b + 1
  let t : ℝ := -b/d
  have hd : 0 < d := by dsimp [d]; linarith [abs_nonneg a]
  have ht : 0 < t := div_pos (neg_pos.mpr hb) hd
  have ht1 : t ≤ 1 := by
    apply (div_le_one hd).2
    dsimp [d]
    linarith [abs_nonneg a]
  have heq : d*t = -b := by
    dsimp [t]
    exact mul_div_cancel₀ _ (ne_of_gt hd)
  have hda : |a| < d := by dsimp [d]; linarith
  have hprod := mul_lt_mul_of_pos_right hda ht
  have hprod' := mul_le_mul_of_nonneg_right (le_abs_self a) ht.le
  have hfactor : 2*b + t*a < 0 := by nlinarith
  have hneg := mul_neg_of_pos_of_neg ht hfactor
  have hq := h t ht.le ht1
  nlinarith

theorem exists_minimal_convexCombo {κ η : Type*}
    [Fintype κ] [Nonempty κ] [Fintype η] (u : κ → η → ℝ) :
    ∃ w : κ → ℝ, SimplexWeight w ∧
      ∀ k, (∑ j, (convexCombo u w j)^2) ≤ ∑ j, u k j * convexCombo u w j := by
  classical
  have hcont : Continuous (fun w => ∑ j, (convexCombo u w j)^2) := by
    apply continuous_finset_sum
    intro j hj
    exact (continuous_convexCombo u j).pow 2
  obtain ⟨w,hw,hmin⟩ :=
    (isCompact_simplexWeight κ).exists_isMinOn (simplexWeight_nonempty κ) hcont.continuousOn
  refine ⟨w,hw,?_⟩
  intro k
  let C : η → ℝ := convexCombo u w
  let q : ℝ := ∑ j, (C j)^2
  let p : ℝ := ∑ j, u k j*C j
  let r : ℝ := ∑ j, (u k j)^2
  have hb : 0 ≤ p-q := by
    apply quadratic_right_derivative_nonneg (a:=q+r-2*p)
    intro t ht0 ht1
    have hv := simplexWeight_segment hw k ht0 ht1
    have hmv := hmin hv
    change (∑ j, (convexCombo u w j)^2) ≤
      ∑ j, (convexCombo u (fun l => (1-t)*w l+t*(if l=k then 1 else 0)) j)^2 at hmv
    simp_rw [convexCombo_segment] at hmv
    have he : (∑ j, ((1-t)*C j+t*u k j)^2) =
        q+2*t*(p-q)+t^2*(q+r-2*p) := by
      calc
        _ = ∑ j, ((C j)^2+2*t*(u k j*C j-(C j)^2)+
            t^2*((C j)^2+(u k j)^2-2*(u k j*C j))) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = _ := by
          dsimp [q,p,r]
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.sum_mul]
    change q ≤ ∑ j, ((1-t)*C j+t*u k j)^2 at hmv
    rw [he] at hmv
    linarith
  exact sub_nonneg.mp hb

/-- Either zero is a convex combination, or the negative of a convex
combination has strictly negative pairing with every given vector. -/
theorem finite_strict_alternative {κ η : Type*}
    [Fintype κ] [Nonempty κ] [Fintype η] (u : κ → η → ℝ) :
    (∃ w : κ → ℝ, SimplexWeight w ∧ ∀ j, convexCombo u w j = 0) ∨
    (∃ w : κ → ℝ, SimplexWeight w ∧
      ∀ k, (∑ j, u k j * (-convexCombo u w j)) < 0) := by
  obtain ⟨w,hw,hmin⟩ := exists_minimal_convexCombo u
  have hq0 : 0 ≤ ∑ j, (convexCombo u w j)^2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  by_cases hq : (∑ j, (convexCombo u w j)^2) = 0
  · left
    refine ⟨w,hw,?_⟩
    intro j
    have hj : (convexCombo u w j)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hq j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hj
  · right
    refine ⟨w,hw,?_⟩
    intro k
    have hpos : 0 < ∑ j, (convexCombo u w j)^2 := lt_of_le_of_ne hq0 (Ne.symm hq)
    simp only [mul_neg, Finset.sum_neg_distrib]
    linarith [hmin k]

/-- Strict affine alternative. The certificate has nonnegative normalized
weights, zero linear part, and a nonnegative weighted offset. -/
theorem finite_strict_affine_alternative {κ η : Type*}
    [Fintype κ] [Fintype η] (u : κ → η → ℝ) (b : κ → ℝ) :
    (∃ w : κ → ℝ, SimplexWeight w ∧ (∀ j, convexCombo u w j = 0) ∧
      0 ≤ ∑ k, w k * b k) ∨
    (∃ v : η → ℝ, ∀ k, (∑ j, u k j*v j)+b k < 0) := by
  classical
  let U : (κ ⊕ Unit) → (η ⊕ Unit) → ℝ := fun k j =>
    match k, j with
    | Sum.inl k, Sum.inl j => u k j
    | Sum.inl k, Sum.inr _ => b k
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr _, Sum.inr _ => -1
  rcases finite_strict_alternative U with ⟨w,hw,hz⟩ | ⟨w,hw,hd⟩
  · left
    let d : ℝ := ∑ k, w (Sum.inl k)
    have hnorm : d + w (Sum.inr ()) = 1 := by
      simpa [d,Fintype.sum_sum_type] using hw.2
    have ho : (∑ k, w (Sum.inl k)*b k) = w (Sum.inr ()) := by
      have h := hz (Sum.inr ())
      simp only [convexCombo,U,Fintype.sum_sum_type,Fintype.sum_unique,mul_neg,mul_one] at h
      linarith
    have hl (j : η) : (∑ k, w (Sum.inl k)*u k j) = 0 := by
      simpa [convexCombo,U,Fintype.sum_sum_type] using hz (Sum.inl j)
    have hd0 : 0 ≤ d := Finset.sum_nonneg (fun k _ => hw.1 (Sum.inl k))
    have hdpos : 0 < d := by
      by_cases he : d=0
      · have hall : ∀ k, w (Sum.inl k)=0 := fun k =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hw.1 (Sum.inl k))).mp he
            k (Finset.mem_univ k)
        have hextra : w (Sum.inr ())=0 := by simpa [hall] using ho.symm
        linarith
      · exact lt_of_le_of_ne hd0 (Ne.symm he)
    refine ⟨fun k => w (Sum.inl k)/d, ⟨?_,?_⟩, ?_, ?_⟩
    · intro k
      exact div_nonneg (hw.1 (Sum.inl k)) hdpos.le
    · rw [sum_div_const]
      exact div_self (ne_of_gt hdpos)
    · intro j
      unfold convexCombo
      simp only [div_mul_eq_mul_div, sum_div_const]
      rw [hl, zero_div]
    · have he : (∑ k, (w (Sum.inl k)/d)*b k) = w (Sum.inr ())/d := by
        simp only [div_mul_eq_mul_div, sum_div_const]
        rw [ho]
      rw [he]
      exact div_nonneg (hw.1 (Sum.inr ())) hdpos.le
  · right
    let V : (η ⊕ Unit) → ℝ := fun j => -convexCombo U w j
    let a : ℝ := V (Sum.inr ())
    have ha : 0 < a := by
      have h := hd (Sum.inr ())
      change (∑ j, U (Sum.inr ()) j*V j) < 0 at h
      simpa [U,Fintype.sum_sum_type,a] using h
    have hk (k : κ) : (∑ j, u k j*V (Sum.inl j))+b k*a < 0 := by
      have h := hd (Sum.inl k)
      change (∑ j, U (Sum.inl k) j*V j) < 0 at h
      simpa [U,Fintype.sum_sum_type,a] using h
    refine ⟨fun j => V (Sum.inl j)/a, ?_⟩
    intro k
    have he : (∑ j, u k j*(V (Sum.inl j)/a))+b k =
        ((∑ j, u k j*V (Sum.inl j))+b k*a)/a := by
      simp only [← mul_div_assoc, sum_div_const]
      field_simp
    rw [he]
    exact div_neg_of_neg_of_pos (hk k) ha

theorem affine_certificate_of_no_strict_solution {κ η : Type*}
    [Fintype κ] [Fintype η] (u : κ → η → ℝ) (b : κ → ℝ)
    (h : ¬∃ v : η → ℝ, ∀ k, (∑ j, u k j*v j)+b k < 0) :
    ∃ w : κ → ℝ, SimplexWeight w ∧ (∀ j, convexCombo u w j = 0) ∧
      0 ≤ ∑ k, w k*b k :=
  (finite_strict_affine_alternative u b).resolve_right h

end
end F3
