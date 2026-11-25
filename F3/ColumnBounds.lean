import F3.Dominance
import F3.Transfer

namespace F3
noncomputable section
open scoped BigOperators

/-- The extremal square sum of numbers in the unit interval with prescribed
sum `m + q`, where `m` is integral and `q` is in the unit interval. -/
theorem unit_interval_square_sum {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (x : ι → ℝ) (m : ℕ) (q : ℝ)
    (hx : ∀ i ∈ t, 0 ≤ x i ∧ x i ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)
    (hsum : ∑ i ∈ t, x i = (m : ℝ) + q) :
    ∑ i ∈ t, (x i)^2 ≤ (m : ℝ) + q^2 := by
  induction t using Finset.induction_on generalizing m q with
  | empty => simp only [Finset.sum_empty] at hsum ⊢; positivity
  | @insert a t hat ih =>
    have ha := hx a (Finset.mem_insert_self _ _)
    have hxt : ∀ i ∈ t, 0 ≤ x i ∧ x i ≤ 1 := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hat] at hsum ⊢
    by_cases haq : x a ≤ q
    · have hq' : 0 ≤ q - x a ∧ q - x a ≤ 1 := by constructor <;> linarith
      have heq : ∑ i ∈ t, x i = (m : ℝ) + (q - x a) := by linarith
      have hb := ih m (q - x a) hxt hq' heq
      nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr haq)]
    · have hqa : q < x a := lt_of_not_ge haq
      cases m with
      | zero =>
        have hn := Finset.sum_nonneg (fun i hi => (hxt i hi).1)
        norm_num at hsum
        linarith
      | succ m =>
        have hq' : 0 ≤ 1 + q - x a ∧ 1 + q - x a ≤ 1 := by constructor <;> linarith
        have heq : ∑ i ∈ t, x i = (m : ℝ) + (1 + q - x a) := by
          push_cast at hsum
          linarith
        have hb := ih m (1 + q - x a) hxt hq' heq
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr (le_of_lt hqa))]

/-- An integer squared mass requires at least that much mass, and a fractional
squared mass requires at least its square root. -/
theorem unit_interval_sum_lower {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (m : ℕ) (d : ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hd : 0 ≤ d ∧ d ≤ 1) (he : ∑ i, (x i)^2 = (m : ℝ) + d) :
    (m : ℝ) + Real.sqrt d ≤ ∑ i, x i := by
  classical
  have he_le : ∑ i, (x i)^2 ≤ ∑ i, x i := Finset.sum_le_sum (by
    intro i _
    nlinarith [(hx i).1, (hx i).2])
  have hlo : (m : ℝ) ≤ ∑ i, x i := by linarith
  have hsqrt := Real.sqrt_nonneg d
  have hsqsqrt := Real.sq_sqrt hd.1
  have hsqrt1 : Real.sqrt d ≤ 1 := by nlinarith
  by_cases hsum : (m : ℝ) + 1 ≤ ∑ i, x i
  · linarith
  · have hq : 0 ≤ (∑ i, x i) - (m : ℝ) ∧ (∑ i, x i) - (m : ℝ) ≤ 1 := by
      constructor <;> linarith
    have hb := unit_interval_square_sum Finset.univ x m ((∑ i, x i) - m)
      (fun i _ => hx i) hq (by ring)
    rw [he] at hb
    nlinarith

theorem feasible_column_sum_lower {n m : ℕ} {d : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible ((m : ℝ) + d) A)
    (hd : 0 ≤ d ∧ d ≤ 1) (j : Fin 3) :
    (m : ℝ) + Real.sqrt d ≤ ∑ i, |A i j| := by
  apply unit_interval_sum_lower (fun i => |A i j|) m d
  · intro i
    have h := Dominance.entry_sq_le_one (Dominance.feasibleK_three_iff.mpr hA) i j
    exact ⟨abs_nonneg _, by nlinarith [sq_abs (A i j)]⟩
  · exact hd
  · simpa [sq_abs, pow_two] using hA.2 j j

theorem residue_two_preliminary_upper {m : ℕ} {d : ℝ} (hd : 0 ≤ d)
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A) : d ≤ 4/9 := by
  have htrace := trace_bound hA
  have hd1 : d ≤ 1 := by simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at htrace; linarith
  have h0 := feasible_column_sum_lower hA ⟨hd,hd1⟩ 0
  have h1 := feasible_column_sum_lower hA ⟨hd,hd1⟩ 1
  have h2 := feasible_column_sum_lower hA ⟨hd,hd1⟩ 2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (f := fun i => |A i 0|+|A i 1|+|A i 2|)
    (g := fun _ => (1 : ℝ)) (fun i _ => hA.1 i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hsum
  have hroot : Real.sqrt d ≤ 2/3 := by push_cast at hsum; linarith
  have hsqrt := Real.sqrt_nonneg d
  nlinarith [Real.sq_sqrt hd]

/-- Above the construction threshold, no row of a residue-two frame vanishes. -/
theorem residue_two_no_zero_row {m : ℕ} {d : ℝ} (hd : 1/5 < d)
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A) :
    ∀ i, ∃ j, A i j ≠ 0 := by
  classical
  have hd0 : 0 ≤ d := by linarith
  have hdhi := residue_two_preliminary_upper hd0 hA
  have hd1 : d ≤ 1 := by linarith
  have h0 := feasible_column_sum_lower hA ⟨hd0,hd1⟩ 0
  have h1 := feasible_column_sum_lower hA ⟨hd0,hd1⟩ 1
  have h2 := feasible_column_sum_lower hA ⟨hd0,hd1⟩ 2
  intro r
  by_contra hn
  have hr : ∀ j, A r j = 0 := by simpa using hn
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (f := fun i => |A i 0|+|A i 1|+|A i 2|)
    (g := fun i => (1 : ℝ) - (if i = r then 1 else 0)) (by
      intro i _
      by_cases hi : i = r
      · simp [hi,hr]
      · simpa [hi] using hA.1 i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hsum
  simp at hsum
  have hsqrt : Real.sqrt d ≤ 1/3 := by push_cast at hsum; linarith
  have hsq0 := Real.sqrt_nonneg d
  nlinarith [Real.sq_sqrt hd0]

def rowEnergy (a : Fin 3 → ℝ) : ℝ := ∑ j, (a j)^2
def rowDefect (a : Fin 3 → ℝ) : ℝ := 1 - rowEnergy a
def largeCount {n : ℕ} (A : Fin n → Fin 3 → ℝ) (j : Fin 3) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => 1/2 < |A i j|)).card

theorem rowDefect_nonneg {a : Fin 3 → ℝ} (ha : RowBound a) : 0 ≤ rowDefect a := by
  have he := row_energy_le_one ha
  simpa [rowDefect,rowEnergy,Fin.sum_univ_three] using sub_nonneg.mpr he

theorem small_coordinate_defect {a : Fin 3 → ℝ} (ha : RowBound a)
    (j : Fin 3) (hj : |a j| ≤ 1/2) : 2*(a j)^2 ≤ rowDefect a := by
  have hd := Dominance.l1_decompose a j
  have he := Dominance.en_decompose a j
  have hb : Dominance.l1 a ≤ 1 := by simpa [Dominance.l1,Fin.sum_univ_three] using ha
  have hm := Dominance.minorL1_nonneg a j
  have hme := Dominance.minorEn_le_sq a j
  have hc := abs_nonneg (a j)
  have hprod : 0 ≤ (1-|a j|-Dominance.minorL1 a j)*(1-|a j|+Dominance.minorL1 a j) := by
    apply mul_nonneg <;> linarith
  change 2*(a j)^2 ≤ 1-Dominance.en a
  nlinarith [sq_abs (a j)]

theorem total_rowDefect {n : ℕ} {s : ℝ} {A : Fin n → Fin 3 → ℝ}
    (hA : Feasible s A) : (∑ i, rowDefect (A i)) = (n : ℝ)-3*s := by
  simp only [rowDefect,rowEnergy,Finset.sum_sub_distrib]
  change (∑ _ : Fin n, (1 : ℝ)) - (∑ i, Dominance.en (A i)) = _
  rw [Dominance.trace_identity (Dominance.feasibleK_three_iff.mpr hA)]
  simp

theorem large_coordinate_energy_bound {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (j : Fin 3) :
    s ≤ (largeCount A j : ℝ) + ((n : ℝ)-3*s)/2 := by
  classical
  have heach (i : Fin n) : (A i j)^2 ≤
      (if 1/2 < |A i j| then (1 : ℝ) else 0) + rowDefect (A i)/2 := by
    by_cases hi : 1/2 < |A i j|
    · rw [if_pos hi]
      have he := Dominance.entry_sq_le_one (Dominance.feasibleK_three_iff.mpr hA) i j
      have hl := rowDefect_nonneg (hA.1 i)
      linarith
    · rw [if_neg hi]
      have h := small_coordinate_defect (hA.1 i) j (le_of_not_gt hi)
      linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have hg : (∑ i, (A i j)^2) = s := by simpa [pow_two] using hA.2 j j
  have hc : (∑ i : Fin n, if 1/2 < |A i j| then (1 : ℝ) else 0) = largeCount A j := by
    simp [largeCount,Finset.sum_ite]
  rw [hg,Finset.sum_add_distrib,hc] at hsum
  simpa only [div_eq_mul_inv,← Finset.sum_mul,total_rowDefect hA] using hsum

theorem residue_two_large_count {m : ℕ} {d : ℝ} (hd : 0 < d)
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A) (j : Fin 3) :
    m ≤ largeCount A j := by
  have h := large_coordinate_energy_bound hA j
  by_contra hn
  have hp : largeCount A j + 1 ≤ m := by omega
  have hpr : (largeCount A j : ℝ)+1 ≤ m := by exact_mod_cast hp
  push_cast at h
  linarith

end
end F3
