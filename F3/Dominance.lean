import F3.Frames
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Dominance for remainder-one cube frames

A signed-vector argument proves the manuscript's row-gap estimate directly
from the Gram equations. All statements here concern actual finite matrices.
-/
namespace F3.Dominance
noncomputable section
open scoped BigOperators

/-- The finite matrix model with arbitrary positive inner dimension. -/
def FeasibleK (n k : ℕ) (s : ℝ) (A : Fin n → Fin k → ℝ) : Prop :=
  (∀ i, (∑ j, |A i j|) ≤ 1) ∧
  (∀ j l, (∑ i, A i j * A i l) = if j = l then s else 0)

def l1 {k : ℕ} (a : Fin k → ℝ) : ℝ := ∑ j, |a j|
def en {k : ℕ} (a : Fin k → ℝ) : ℝ := ∑ j, (a j)^2

def signUnit (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem signUnit_sq (x : ℝ) : (signUnit x)^2 = 1 := by
  unfold signUnit
  split <;> norm_num

theorem signUnit_mul (x : ℝ) : x * signUnit x = |x| := by
  unfold signUnit
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem abs_mul_signUnit (x y : ℝ) : |x * signUnit y| = |x| := by
  unfold signUnit
  split <;> simp

/-- The elementary signed-vector estimate behind the loss/cancellation bound. -/
theorem two_energy_le {ι : Type*} (t : Finset ι) (a : ι → ℝ) :
    2 * (∑ j ∈ t, (a j)^2) ≤ (∑ j ∈ t, |a j|)^2 + (∑ j ∈ t, a j)^2 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
    simp only [Finset.sum_insert hj]
    have hsum := Finset.abs_sum_le_sum_abs a t
    have hlo := (abs_le.mp hsum).1
    have hhi := (abs_le.mp hsum).2
    have hprod : 0 ≤ |a j| * (∑ x ∈ t, |a x|) + a j * (∑ x ∈ t, a x) := by
      by_cases ha : 0 ≤ a j
      · rw [abs_of_nonneg ha]
        have h := mul_nonneg ha (show 0 ≤ (∑ x ∈ t, |a x|) + (∑ x ∈ t, a x) by linarith)
        nlinarith
      · rw [abs_of_neg (lt_of_not_ge ha)]
        have h := mul_nonneg (show 0 ≤ -a j by linarith)
          (show 0 ≤ (∑ x ∈ t, |a x|) - (∑ x ∈ t, a x) by linarith)
        nlinarith
    nlinarith [sq_abs (a j)]

theorem gram_quadratic {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) (v : Fin k → ℝ) :
    (∑ i, (∑ j, A i j * v j)^2) = s * (∑ j, (v j)^2) := by
  calc
    (∑ i, (∑ j, A i j * v j)^2)
        = ∑ i, ∑ j, ∑ l, (A i j * v j) * (A i l * v l) := by
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ j, ∑ l, ∑ i, (A i j * v j) * (A i l * v l) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ l, (v j * v l) * (∑ i, A i j * A i l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = s * (∑ j, (v j)^2) := by
      simp only [hA.2, mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem trace_identity {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) : (∑ i, en (A i)) = (k : ℝ) * s := by
  unfold en
  rw [Finset.sum_comm]
  simp only [pow_two, hA.2, ite_true]
  simp

/-- The pointwise row-gap estimate, without any unproved multiplier premises. -/
theorem row_gap {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) (i : Fin n) :
    (k : ℝ) * s - n + 1 ≤ 2 * en (A i) - (l1 (A i))^2 := by
  let v : Fin k → ℝ := fun j => signUnit (A i j)
  let R : Fin n → ℝ := fun h => 2 * en (A h) - (∑ j, A h j * v j)^2
  have hR (h : Fin n) : R h ≤ 1 := by
    have hineq := two_energy_le Finset.univ (fun j => A h j * v j)
    have hsq : (∑ j, (A h j * v j)^2) = en (A h) := by
      simp [en, v, mul_pow, signUnit_sq]
    have habs : (∑ j, |A h j * v j|) = l1 (A h) := by
      simp [l1, v, abs_mul_signUnit]
    change 2 * (∑ j, (A h j * v j)^2) ≤
      (∑ j, |A h j * v j|)^2 + (∑ j, A h j * v j)^2 at hineq
    rw [hsq, habs] at hineq
    have hnorm : 0 ≤ l1 (A h) := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    have hnorm1 : l1 (A h) ≤ 1 := hA.1 h
    dsimp [R]
    nlinarith [mul_nonneg (sub_nonneg.mpr hnorm1) (show 0 ≤ 1 + l1 (A h) by linarith)]
  have hsum : (∑ h, R h) = (k : ℝ) * s := by
    simp only [R, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [trace_identity hA, gram_quadratic hA v]
    have hv : (∑ j, (v j)^2) = (k : ℝ) := by simp [v, signUnit_sq]
    rw [hv]
    ring
  have hothers : (∑ h ∈ Finset.univ.erase i, R h) ≤
      (∑ h ∈ Finset.univ.erase i, (1 : ℝ)) :=
    Finset.sum_le_sum (fun h _ => hR h)
  have hsumR := Finset.sum_erase_add Finset.univ R (Finset.mem_univ i)
  have hsum1 := Finset.sum_erase_add Finset.univ (fun _ : Fin n => (1 : ℝ)) (Finset.mem_univ i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum1 hothers
  rw [hsum] at hsumR
  have hRi : R i = 2 * en (A i) - (l1 (A i))^2 := by
    simp [R, l1, v, signUnit_mul]
  rw [hRi] at hsumR
  linarith

def minorL1 {k : ℕ} (a : Fin k → ℝ) (j : Fin k) : ℝ :=
  ∑ l ∈ Finset.univ.erase j, |a l|

def minorEn {k : ℕ} (a : Fin k → ℝ) (j : Fin k) : ℝ :=
  ∑ l ∈ Finset.univ.erase j, (a l)^2

def Dominant {k : ℕ} (a : Fin k → ℝ) (j : Fin k) : Prop := minorL1 a j < |a j|

theorem minorL1_nonneg {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    0 ≤ minorL1 a j := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem minorEn_nonneg {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    0 ≤ minorEn a j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem l1_decompose {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    minorL1 a j + |a j| = l1 a :=
  Finset.sum_erase_add _ _ (Finset.mem_univ j)

theorem en_decompose {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    minorEn a j + |a j|^2 = en a := by
  rw [sq_abs]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ j)

theorem minorEn_le_sq {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    minorEn a j ≤ (minorL1 a j)^2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ.erase j) (f := fun l => |a l|) (fun _ _ => abs_nonneg _)
  simpa [minorEn, minorL1, sq_abs] using h

theorem other_entry_le_minorL1 {k : ℕ} (a : Fin k → ℝ)
    {j l : Fin k} (hlj : l ≠ j) : |a l| ≤ minorL1 a j := by
  exact Finset.single_le_sum (s := Finset.univ.erase j) (f := fun l => |a l|)
    (fun _ _ => abs_nonneg _) (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ _⟩)

theorem dominant_unique {k : ℕ} {a : Fin k → ℝ} {j l : Fin k}
    (hj : Dominant a j) (hl : Dominant a l) : j = l := by
  by_contra hne
  have h1 := other_entry_le_minorL1 a hne
  have h2 := other_entry_le_minorL1 a (Ne.symm hne)
  unfold Dominant at hj hl
  linarith

theorem dominant_exists_of_gap {k : ℕ} (hk : 0 < k)
    {a : Fin k → ℝ} {d : ℝ} (hd : 0 < d)
    (hgap : d^2 ≤ 2 * en a - (l1 a)^2) : ∃! j, Dominant a j := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => |a j|)
    (show (Finset.univ : Finset (Fin k)).Nonempty from ⟨⟨0, hk⟩, Finset.mem_univ _⟩)
  have hE : en a ≤ |a j| * l1 a := by
    unfold en l1
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    have hmaxl := hmax l (Finset.mem_univ _)
    have hp := mul_nonneg (abs_nonneg (a l)) (sub_nonneg.mpr hmaxl)
    nlinarith [sq_abs (a l)]
  have hln : 0 ≤ l1 a := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hjdom : Dominant a j := by
    have hdec := l1_decompose a j
    unfold Dominant
    by_contra hn
    have hm : |a j| ≤ minorL1 a j := le_of_not_gt hn
    have hp := mul_nonneg hln (show 0 ≤ l1 a - 2 * |a j| by linarith)
    nlinarith [sq_pos_of_pos hd]
  exact ⟨j, hjdom, fun l hl => dominant_unique hl hjdom⟩

theorem dominant_gap {k : ℕ} {a : Fin k → ℝ} {j : Fin k} {d : ℝ}
    (_hd : 0 ≤ d) (hdom : Dominant a j)
    (hgap : d^2 ≤ 2 * en a - (l1 a)^2) :
    d ≤ |a j| - minorL1 a j := by
  have hE := minorEn_le_sq a j
  have hl := l1_decompose a j
  have he := en_decompose a j
  unfold Dominant at hdom
  have hg : d^2 ≤ (|a j| - minorL1 a j)^2 := by
    rw [← hl, ← he] at hgap
    nlinarith
  by_contra hn
  have hp := mul_pos
    (show 0 < d - (|a j| - minorL1 a j) by linarith)
    (show 0 < d + (|a j| - minorL1 a j) by linarith)
  nlinarith

theorem minorL1_bound {k : ℕ} {a : Fin k → ℝ} {j : Fin k} {d : ℝ}
    (hrow : l1 a ≤ 1) (hd : 0 ≤ d) (hdom : Dominant a j)
    (hgap : d^2 ≤ 2 * en a - (l1 a)^2) :
    minorL1 a j ≤ (1 - d) / 2 := by
  have h := dominant_gap hd hdom hgap
  have hdec := l1_decompose a j
  linarith

/-- Pointwise weighted loss bound, whose sum yields the global E estimate. -/
theorem weighted_minor_energy {k : ℕ} {a : Fin k → ℝ} {j : Fin k} {d : ℝ}
    (hrow : l1 a ≤ 1) (hd : 0 ≤ d) (hdom : Dominant a j)
    (hgap : d^2 ≤ 2 * en a - (l1 a)^2) :
    2 * (1 + d) * minorEn a j ≤ (1 - d) * (1 - en a) := by
  have hgap' := dominant_gap hd hdom hgap
  have hminor := minorEn_le_sq a j
  have hb0 := minorL1_nonneg a j
  have ha0 := abs_nonneg (a j)
  have hE0 := minorEn_nonneg a j
  have hdec := l1_decompose a j
  have he := en_decompose a j
  have hd1 : d ≤ 1 := by linarith
  have hmul := mul_nonneg hd (sub_nonneg.mpr hrow)
  have hratio : (1 + d) * minorL1 a j ≤ (1 - d) * |a j| := by nlinarith
  have hratio2 := mul_le_mul_of_nonneg_right hratio hb0
  have hmin2 := mul_le_mul_of_nonneg_left hminor (show 0 ≤ 2 * (1 + d) by positivity)
  have hnorm := mul_nonneg (sub_nonneg.mpr hrow)
    (show 0 ≤ 1 + l1 a by linarith)
  have hloss : 2 * |a j| * minorL1 a j ≤ 1 - en a := by nlinarith
  have hloss2 := mul_le_mul_of_nonneg_left hloss (show 0 ≤ 1 - d by linarith)
  nlinarith

/-- Total squared energy outside the chosen dominant coordinate in each row. -/
def totalMinor {n k : ℕ} (A : Fin n → Fin k → ℝ) (dom : Fin n → Fin k) : ℝ :=
  ∑ i, minorEn (A i) (dom i)

def domCount {n k : ℕ} (dom : Fin n → Fin k) (j : Fin k) : ℕ :=
  (Finset.univ.filter (fun i => dom i = j)).card

def incoming {n k : ℕ} (A : Fin n → Fin k → ℝ) (dom : Fin n → Fin k) (j : Fin k) : ℝ :=
  ∑ i, if dom i = j then 0 else (A i j)^2

theorem totalMinor_nonneg {n k : ℕ} (A : Fin n → Fin k → ℝ) (dom : Fin n → Fin k) :
    0 ≤ totalMinor A dom := Finset.sum_nonneg (fun _ _ => minorEn_nonneg _ _)

theorem totalMinor_bound {n k : ℕ} {s d : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) (dom : Fin n → Fin k)
    (hdom : ∀ i, Dominant (A i) (dom i)) (hd : 0 ≤ d)
    (hgap : ∀ i, d^2 ≤ 2 * en (A i) - (l1 (A i))^2)
    (hloss : (n : ℝ) - k * s = 1 - d^2) :
    totalMinor A dom ≤ (1 - d)^2 / 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => weighted_minor_energy (hA.1 i) hd (hdom i) (hgap i))
  have hleft : (∑ i, 2 * (1 + d) * minorEn (A i) (dom i)) =
      2 * (1 + d) * totalMinor A dom := by rw [totalMinor, Finset.mul_sum]
  have hright : (∑ i, (1 - d) * (1 - en (A i))) = (1 - d) * (1 - d^2) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, trace_identity hA]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hloss]
  rw [hleft, hright] at h
  have hmul : (2 * (1 + d)) * totalMinor A dom ≤
      (2 * (1 + d)) * ((1 - d)^2 / 2) := by nlinarith
  exact (mul_le_mul_left (by positivity : 0 < 2 * (1 + d))).mp hmul

theorem entry_sq_le_one {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) (i : Fin n) (j : Fin k) : (A i j)^2 ≤ 1 := by
  have he : |A i j| ≤ ∑ l, |A i l| :=
    Finset.single_le_sum (f := fun l => |A i l|) (s := Finset.univ)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have ha0 := abs_nonneg (A i j)
  have ha1 := he.trans (hA.1 i)
  nlinarith [sq_abs (A i j)]

theorem column_balance_bound {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) (dom : Fin n → Fin k) (j : Fin k) :
    s ≤ (domCount dom j : ℝ) + incoming A dom j := by
  have h := Finset.sum_le_sum (s := Finset.univ) (f := fun i => (A i j)^2)
    (g := fun i => (if dom i = j then (1 : ℝ) else 0) + (if dom i = j then 0 else (A i j)^2))
    (by intro i _; dsimp; split_ifs <;> simp_all [entry_sq_le_one hA i j])
  have hgram : (∑ i, (A i j)^2) = s := by simpa [pow_two] using hA.2 j j
  have hcount : (∑ i, if dom i = j then (1 : ℝ) else 0) = (domCount dom j : ℝ) := by
    simp [domCount, Finset.sum_ite, Finset.sum_const]
  rw [hgram, Finset.sum_add_distrib, hcount] at h
  exact h

theorem incoming_nonneg {n k : ℕ} (A : Fin n → Fin k → ℝ)
    (dom : Fin n → Fin k) (j : Fin k) : 0 ≤ incoming A dom j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

theorem minorEn_eq_sum_ite {k : ℕ} (a : Fin k → ℝ) (j : Fin k) :
    minorEn a j = ∑ l, if j = l then 0 else (a l)^2 := by
  unfold minorEn
  rw [← Finset.sum_erase_add Finset.univ (fun l => if j = l then 0 else (a l)^2) (Finset.mem_univ j)]
  simp only [ite_true, add_zero]
  apply Finset.sum_congr rfl
  intro l hl
  have hlj := (Finset.mem_erase.mp hl).1
  simp [Ne.symm hlj]

theorem incoming_sum {n k : ℕ} (A : Fin n → Fin k → ℝ) (dom : Fin n → Fin k) :
    (∑ j, incoming A dom j) = totalMinor A dom := by
  unfold incoming totalMinor
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (minorEn_eq_sum_ite (A i) (dom i)).symm

theorem incoming_le_total {n k : ℕ} (A : Fin n → Fin k → ℝ) (dom : Fin n → Fin k) (j : Fin k) :
    incoming A dom j ≤ totalMinor A dom := by
  rw [← incoming_sum]
  exact Finset.single_le_sum (f := incoming A dom) (s := Finset.univ)
    (fun j _ => incoming_nonneg A dom j) (Finset.mem_univ j)

theorem domCount_sum {n k : ℕ} (dom : Fin n → Fin k) :
    (∑ j, domCount dom j) = n := by
  simp only [domCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- The exact integer multiplicity consequence of one surplus row. -/
theorem count_pattern {k m : ℕ} (c : Fin k → ℕ)
    (hc : ∀ j, m ≤ c j) (hs : (∑ j, c j) = k * m + 1) :
    ∃ j, c j = m + 1 ∧ ∀ l, l ≠ j → c l = m := by
  have hsum : (∑ j, (c j - m)) + k * m = ∑ j, c j := by
    calc
      (∑ j, (c j - m)) + k * m = ∑ j, ((c j - m) + m) := by simp [Finset.sum_add_distrib]
      _ = ∑ j, c j := Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hc j))
  have hone : (∑ j, (c j - m)) = 1 := by omega
  have hex : ∃ j, 0 < c j - m := by
    by_contra hn
    have hz (j : Fin k) : c j - m = 0 := by
      by_contra hne
      have hp : 0 < c j - m := Nat.pos_of_ne_zero hne
      exact hn ⟨j, hp⟩
    simp [hz] at hone
  obtain ⟨j, hj⟩ := hex
  have hjle : c j - m ≤ ∑ l, (c l - m) :=
    Finset.single_le_sum (f := fun l => c l - m) (s := Finset.univ)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hjone : c j - m = 1 := by omega
  refine ⟨j, by have h := hc j; omega, ?_⟩
  intro l hlj
  have hrest := Finset.sum_erase_add Finset.univ (fun l => c l - m) (Finset.mem_univ j)
  have hlle : c l - m ≤ ∑ x ∈ Finset.univ.erase j, (c x - m) :=
    Finset.single_le_sum (f := fun l => c l - m) (s := Finset.univ.erase j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ _⟩)
  have h := hc l
  dsimp only at hrest
  rw [hone, hjone] at hrest
  omega

theorem counts_lower_bound {n k m : ℕ} {d : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k ((m : ℝ) + d) A) (dom : Fin n → Fin k)
    (hd : 0 < d) (hE : totalMinor A dom < 1) (j : Fin k) : m ≤ domCount dom j := by
  have hc := column_balance_bound hA dom j
  have he := incoming_le_total A dom j
  by_contra hn
  have hnat : domCount dom j + 1 ≤ m := by omega
  have hreal : (domCount dom j : ℝ) + 1 ≤ m := by exact_mod_cast hnat
  linarith

theorem minor_lower_bound {n k m : ℕ} {d : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k ((m : ℝ) + d) A) (dom : Fin n → Fin k)
    (j : Fin k) (hc : ∀ l, l ≠ j → domCount dom l = m) :
    ((k : ℝ) - 1) * d ≤ totalMinor A dom := by
  have hdef (l : Fin k) (hl : l ∈ Finset.univ.erase j) : d ≤ incoming A dom l := by
    have h := column_balance_bound hA dom l
    rw [hc l (Finset.mem_erase.mp hl).1] at h
    linarith
  have hsum := Finset.sum_le_sum hdef
  have hcount := Finset.sum_erase_add Finset.univ (fun _ : Fin k => d) (Finset.mem_univ j)
  have htotal := Finset.sum_erase_add Finset.univ (incoming A dom) (Finset.mem_univ j)
  rw [incoming_sum] at htotal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcount hsum
  have hj0 := incoming_nonneg A dom j
  nlinarith

theorem dominance_summary {k m : ℕ} (hk : 2 ≤ k) {d : ℝ}
    (hd : 0 < d) {A : Fin (k * m + 1) → Fin k → ℝ}
    (hA : FeasibleK (k * m + 1) k ((m : ℝ) + d) A) :
    ∃ dom : Fin (k * m + 1) → Fin k,
      (∀ i, Dominant (A i) (dom i)) ∧
      (∀ i, Real.sqrt (k * d) ≤ |A i (dom i)| - minorL1 (A i) (dom i) ∧
        minorL1 (A i) (dom i) ≤ (1 - Real.sqrt (k * d)) / 2) ∧
      ((k : ℝ) - 1) * d ≤ totalMinor A dom ∧
      totalMinor A dom ≤ (1 - Real.sqrt (k * d))^2 / 2 ∧
      (∃ j, domCount dom j = m + 1 ∧ ∀ l, l ≠ j → domCount dom l = m) := by
  have hk0 : 0 < k := by omega
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkd : 0 < (k : ℝ) * d := mul_pos hkr hd
  have hdroot : 0 < Real.sqrt (k * d) := Real.sqrt_pos.mpr hkd
  have hsroot := Real.sq_sqrt (le_of_lt hkd)
  have hgap (i : Fin (k * m + 1)) :
      (Real.sqrt (k * d))^2 ≤ 2 * en (A i) - (l1 (A i))^2 := by
    have h := row_gap hA i
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h
    rw [hsroot]
    nlinarith
  have hex (i : Fin (k * m + 1)) : ∃ j, Dominant (A i) j :=
    (dominant_exists_of_gap hk0 hdroot (hgap i)).exists
  let dom : Fin (k * m + 1) → Fin k := fun i => Classical.choose (hex i)
  have hdom (i : Fin (k * m + 1)) : Dominant (A i) (dom i) := Classical.choose_spec (hex i)
  have hsize (i : Fin (k * m + 1)) :=
    minorL1_bound (hA.1 i) (le_of_lt hdroot) (hdom i) (hgap i)
  have hgap' (i : Fin (k * m + 1)) := dominant_gap (le_of_lt hdroot) (hdom i) (hgap i)
  have hdroot1 : Real.sqrt (k * d) ≤ 1 := by
    let i : Fin (k * m + 1) := ⟨0, by omega⟩
    have h0 := minorL1_nonneg (A i) (dom i)
    have h := hsize i
    linarith
  have hloss : ((k * m + 1 : ℕ) : ℝ) - k * ((m : ℝ) + d) =
      1 - (Real.sqrt (k * d))^2 := by
    rw [hsroot]
    push_cast
    ring
  have hE := totalMinor_bound hA dom hdom (le_of_lt hdroot) hgap hloss
  have hEhalf : totalMinor A dom < 1 / 2 := by
    have hp := mul_pos hdroot (show 0 < 2 - Real.sqrt (k * d) by linarith)
    nlinarith
  have hc (j : Fin k) : m ≤ domCount dom j :=
    counts_lower_bound hA dom hd (by linarith) j
  obtain ⟨j, hj, hjothers⟩ := count_pattern (domCount dom) hc (domCount_sum dom)
  refine ⟨dom, hdom, ?_, minor_lower_bound hA dom j hjothers, hE, j, hj, hjothers⟩
  intro i
  exact ⟨hgap' i, hsize i⟩

/-- The two-dimensional remainder-one bound from the manuscript. -/
theorem two_dimensional_bound {m : ℕ} {s : ℝ} {A : Fin (2 * m + 1) → Fin 2 → ℝ}
    (hA : FeasibleK (2 * m + 1) 2 s A) : s ≤ (m : ℝ) + 1 / 8 := by
  by_cases hs : s ≤ m
  · linarith
  have hd : 0 < s - m := by linarith
  have hA' : FeasibleK (2 * m + 1) 2 ((m : ℝ) + (s - m)) A := by simpa using hA
  obtain ⟨dom, _, _, hlo, hhi, _⟩ := dominance_summary (by norm_num : 2 ≤ 2) hd hA'
  have hr := Real.sqrt_nonneg (2 * (s - m))
  have hr2 := Real.sq_sqrt (show 0 ≤ 2 * (s - m) by linarith)
  norm_num only [Nat.cast_ofNat] at hlo hhi
  have hroot : Real.sqrt (2 * (s - m)) ≤ 1 / 2 := by nlinarith
  have hp := mul_nonneg
    (show 0 ≤ 1 / 2 - Real.sqrt (2 * (s - m)) by linarith)
    (show 0 ≤ 1 / 2 + Real.sqrt (2 * (s - m)) by positivity)
  nlinarith

/-- The general coarse bound in the manuscript, for every inner dimension k≥2. -/
theorem coarse_bound {k m : ℕ} (hk : 2 ≤ k) {d : ℝ}
    (hd : 0 < d) {A : Fin (k * m + 1) → Fin k → ℝ}
    (hA : FeasibleK (k * m + 1) k ((m : ℝ) + d) A) :
    d ≤ 1 / (Real.sqrt (k : ℝ) + Real.sqrt (2 * ((k : ℝ) - 1)))^2 := by
  obtain ⟨dom, _, hsize, hlo, hhi, _⟩ := dominance_summary hk hd hA
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hx := Real.sqrt_nonneg d
  have hx2 := Real.sq_sqrt (le_of_lt hd)
  have hp := Real.sqrt_nonneg (k : ℝ)
  have hp0 : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hq := Real.sqrt_nonneg (2 * ((k : ℝ) - 1))
  have hq2 := Real.sq_sqrt (show 0 ≤ 2 * ((k : ℝ) - 1) by linarith)
  have hprod : Real.sqrt ((k : ℝ) * d) = Real.sqrt (k : ℝ) * Real.sqrt d :=
    Real.sqrt_mul (by positivity) d
  have hprod1 : Real.sqrt (k : ℝ) * Real.sqrt d ≤ 1 := by
    let i : Fin (k * m + 1) := ⟨0, by omega⟩
    have hi := (hsize i).2
    have hn := minorL1_nonneg (A i) (dom i)
    rw [hprod] at hi
    linarith
  have hsq : (Real.sqrt (2 * ((k : ℝ) - 1)) * Real.sqrt d)^2 ≤
      (1 - Real.sqrt (k : ℝ) * Real.sqrt d)^2 := by
    rw [mul_pow, hq2, hx2, ← hprod]
    nlinarith
  have hroot : Real.sqrt (2 * ((k : ℝ) - 1)) * Real.sqrt d ≤
      1 - Real.sqrt (k : ℝ) * Real.sqrt d := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hpos := mul_pos
      (show 0 < Real.sqrt (2 * ((k : ℝ) - 1)) * Real.sqrt d -
          (1 - Real.sqrt (k : ℝ) * Real.sqrt d) by linarith)
      (show 0 < Real.sqrt (2 * ((k : ℝ) - 1)) * Real.sqrt d +
          (1 - Real.sqrt (k : ℝ) * Real.sqrt d) by nlinarith)
    nlinarith
  have hsum : (Real.sqrt (k : ℝ) + Real.sqrt (2 * ((k : ℝ) - 1))) * Real.sqrt d ≤ 1 := by
    nlinarith
  have hsprod := mul_nonneg (sub_nonneg.mpr hsum)
    (show 0 ≤ 1 + (Real.sqrt (k : ℝ) + Real.sqrt (2 * ((k : ℝ) - 1))) * Real.sqrt d by positivity)
  have hsquare : ((Real.sqrt (k : ℝ) + Real.sqrt (2 * ((k : ℝ) - 1))) * Real.sqrt d)^2 ≤ 1 := by
    nlinarith
  rw [mul_pow, hx2] at hsquare
  apply (le_div_iff₀ (sq_pos_of_pos (show 0 < Real.sqrt (k : ℝ) + Real.sqrt (2 * ((k : ℝ) - 1)) by linarith))).mpr
  nlinarith

theorem three_dimensional_bound {m : ℕ} {d : ℝ} (hd : 0 < d)
    {A : Fin (3 * m + 1) → Fin 3 → ℝ}
    (hA : FeasibleK (3 * m + 1) 3 ((m : ℝ) + d) A) :
    d ≤ 7 - 4 * Real.sqrt 3 := by
  have h := coarse_bound (by norm_num : 2 ≤ 3) hd hA
  norm_num only [Nat.cast_ofNat] at h
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h4] at h
  have h3n := Real.sqrt_nonneg 3
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hpos : 0 < (Real.sqrt 3 + 2)^2 := sq_pos_of_pos (by positivity)
  have hmul := (le_div_iff₀ hpos).mp h
  have hid : (7 - 4 * Real.sqrt 3) * (Real.sqrt 3 + 2)^2 = 1 := by
    calc
      _ = 1 + (-4 * Real.sqrt 3 - 9) * ((Real.sqrt 3)^2 - 3) := by ring
      _ = 1 := by rw [h3]; ring
  apply (mul_le_mul_right hpos).mp
  rw [hid]
  exact hmul

theorem three_dimensional_bound_lt_72_div_1000 :
    7 - 4 * Real.sqrt 3 < (72 : ℝ) / 1000 := by
  have h3n := Real.sqrt_nonneg 3
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith

theorem feasibleK_three_iff {n : ℕ} {s : ℝ} {A : Fin n → Fin 3 → ℝ} :
    FeasibleK n 3 s A ↔ F3.Feasible s A := by
  unfold FeasibleK F3.Feasible F3.RowBound
  simp only [Fin.sum_univ_three]

theorem three_column_coarse {m : ℕ} {d : ℝ} (hd : 0 < d)
    {A : Fin (3 * m + 1) → Fin 3 → ℝ} (hA : F3.Feasible ((m : ℝ) + d) A) :
    d ≤ 7 - 4 * Real.sqrt 3 :=
  three_dimensional_bound hd (feasibleK_three_iff.mpr hA)

/-- Orthogonality forces the absolute product of any row to be cancelled
by absolute products in the other rows. -/
theorem finite_cancellation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : ι → ℝ} (hzero : (∑ i, x i) = 0) (i : ι) :
    |x i| ≤ ∑ h ∈ Finset.univ.erase i, |x h| := by
  have heq : (∑ h ∈ Finset.univ.erase i, x h) = -x i := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hzero]
    ring
  have h := Finset.abs_sum_le_sum_abs x (Finset.univ.erase i)
  rw [heq, abs_neg] at h
  exact h

theorem gram_cancellation {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) (i : Fin n) {j l : Fin k} (hjl : j ≠ l) :
    |A i j * A i l| ≤ ∑ h ∈ Finset.univ.erase i, |A h j * A h l| := by
  exact finite_cancellation (x := fun h => A h j * A h l)
    (by simpa [hjl] using hA.2 j l) i

end
end F3.Dominance
