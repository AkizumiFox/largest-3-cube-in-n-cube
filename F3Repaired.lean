/-
Consolidated companion to the repaired f(3,n) manuscript.
Requires mathlib v4.19.0 and Lean 4.19.0.
Generated from F3/Frames.lean, F3/Cores.lean, and F3/Recurrence.lean.
The sharp global upper bounds are NOT asserted as formally proved here.
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Feasible frames and elementary bounds

This file proves statements about the finite frame formulation of the cube
embedding problem. The equivalence with geometric cube embeddings and the
sharp global upper bounds are not asserted as formalized here.
-/

namespace F3

noncomputable section
open scoped BigOperators

def RowBound (a : Fin 3 → ℝ) : Prop :=
  |a 0| + |a 1| + |a 2| ≤ 1

def Feasible {ι : Type*} [Fintype ι] (lam : ℝ)
    (A : ι → Fin 3 → ℝ) : Prop :=
  (∀ i, RowBound (A i)) ∧
  (∀ j k, (∑ i, A i j * A i k) = if j = k then lam else 0)

theorem row_energy_le_one {a : Fin 3 → ℝ} (h : RowBound a) :
    (a 0)^2 + (a 1)^2 + (a 2)^2 ≤ 1 := by
  unfold RowBound at h
  have hp : 0 ≤ (1 - (|a 0| + |a 1| + |a 2|)) *
      (1 + (|a 0| + |a 1| + |a 2|)) :=
    mul_nonneg (sub_nonneg.mpr h) (by positivity)
  have h01 := mul_nonneg (abs_nonneg (a 0)) (abs_nonneg (a 1))
  have h02 := mul_nonneg (abs_nonneg (a 0)) (abs_nonneg (a 2))
  have h12 := mul_nonneg (abs_nonneg (a 1)) (abs_nonneg (a 2))
  nlinarith [sq_abs (a 0), sq_abs (a 1), sq_abs (a 2)]

theorem feasible_nonneg {ι : Type*} [Fintype ι] {lam : ℝ}
    {A : ι → Fin 3 → ℝ} (h : Feasible lam A) : 0 ≤ lam := by
  have hd := h.2 0 0
  simp only [ite_true] at hd
  rw [← hd]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (A i 0))

theorem trace_bound {ι : Type*} [Fintype ι] {lam : ℝ}
    {A : ι → Fin 3 → ℝ} (h : Feasible lam A) :
    3 * lam ≤ (Fintype.card ι : ℝ) := by
  have h0 := h.2 0 0
  have h1 := h.2 1 1
  have h2 := h.2 2 2
  simp only [ite_true] at h0 h1 h2
  have he : (∑ i, ((A i 0)^2 + (A i 1)^2 + (A i 2)^2)) = 3 * lam := by
    simp only [pow_two, Finset.sum_add_distrib]
    rw [h0, h1, h2]
    ring
  calc
    3 * lam = ∑ i, ((A i 0)^2 + (A i 1)^2 + (A i 2)^2) := he.symm
    _ ≤ ∑ _i : ι, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => row_energy_le_one (h.1 i))
    _ = (Fintype.card ι : ℝ) := by simp

def basisRow (i j : Fin 3) : ℝ := if i = j then 1 else 0

theorem basis_row_bound (i : Fin 3) : RowBound (basisRow i) := by
  fin_cases i <;> norm_num [RowBound, basisRow, Fin.ext_iff]

theorem basis_gram (j k : Fin 3) :
    (∑ i : Fin 3, basisRow i j * basisRow i k) =
      if j = k then (1 : ℝ) else 0 := by
  rw [Fin.sum_univ_three]
  fin_cases j <;> fin_cases k <;>
    norm_num [basisRow, Fin.ext_iff]

def appendIdentity {ι : Type*} (A : ι → Fin 3 → ℝ) :
    ι ⊕ Fin 3 → Fin 3 → ℝ :=
  Sum.elim A basisRow

theorem appendIdentity_feasible {ι : Type*} [Fintype ι] {lam : ℝ}
    {A : ι → Fin 3 → ℝ} (h : Feasible lam A) :
    Feasible (lam + 1) (appendIdentity A) := by
  constructor
  · intro i
    cases i with
    | inl i => exact h.1 i
    | inr i => exact basis_row_bound i
  · intro j k
    simp only [appendIdentity, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [h.2 j k, basis_gram j k]
    by_cases hjk : j = k <;> simp [hjk]

theorem reindex_feasible {ι κ : Type*} [Fintype ι] [Fintype κ]
    {lam : ℝ} {A : ι → Fin 3 → ℝ} (e : κ ≃ ι) (h : Feasible lam A) :
    Feasible lam (fun i => A (e i)) := by
  constructor
  · intro i
    exact h.1 (e i)
  · intro j k
    calc
      (∑ i, A (e i) j * A (e i) k) = ∑ i, A i j * A i k :=
        Equiv.sum_comp e (fun i => A i j * A i k)
      _ = if j = k then lam else 0 := h.2 j k

def FeasibleValue (n : ℕ) (lam : ℝ) : Prop :=
  ∃ A : Fin n → Fin 3 → ℝ, Feasible lam A

theorem stacking_feasible_value {n : ℕ} {lam : ℝ}
    (h : FeasibleValue n lam) : FeasibleValue (n + 3) (lam + 1) := by
  rcases h with ⟨A, hA⟩
  exact ⟨fun i => appendIdentity A ((finSumFinEquiv).symm i),
    reindex_feasible (finSumFinEquiv).symm (appendIdentity_feasible hA)⟩

def OptimalValue (n : ℕ) (v : ℝ) : Prop :=
  FeasibleValue n v ∧ ∀ lam, FeasibleValue n lam → lam ≤ v

theorem stacking_optimal_values {n : ℕ} {v w : ℝ}
    (hv : OptimalValue n v) (hw : OptimalValue (n + 3) w) : v + 1 ≤ w := by
  exact hw.2 (v + 1) (stacking_feasible_value hv.1)

theorem zero_feasible_value (n : ℕ) : FeasibleValue n 0 := by
  exact ⟨fun _ _ => 0, by simp [Feasible, RowBound]⟩

theorem feasible_values_nonempty (n : ℕ) :
    ({lam : ℝ | FeasibleValue n lam} : Set ℝ).Nonempty :=
  ⟨0, zero_feasible_value n⟩

theorem feasible_values_bddAbove (n : ℕ) :
    BddAbove ({lam : ℝ | FeasibleValue n lam} : Set ℝ) := by
  refine ⟨(n : ℝ) / 3, ?_⟩
  intro lam hlam
  rcases hlam with ⟨A, hA⟩
  have ht := trace_bound hA
  simp only [Fintype.card_fin] at ht
  linarith

/-- The supremum of the actual finite-frame feasibility problem.
The geometric equivalence is a separate, unformalized manuscript result. -/
def frameValue (n : ℕ) : ℝ := sSup {lam : ℝ | FeasibleValue n lam}

theorem feasible_le_frameValue {n : ℕ} {lam : ℝ}
    (h : FeasibleValue n lam) : lam ≤ frameValue n :=
  le_csSup (feasible_values_bddAbove n) h

theorem frameValue_trace_bound (n : ℕ) : frameValue n ≤ (n : ℝ) / 3 := by
  apply csSup_le (feasible_values_nonempty n)
  intro lam hlam
  rcases hlam with ⟨A, hA⟩
  have ht := trace_bound hA
  simp only [Fintype.card_fin] at ht
  linarith

theorem frameValue_nonneg (n : ℕ) : 0 ≤ frameValue n :=
  feasible_le_frameValue (zero_feasible_value n)

theorem frameValue_eq_of_optimal {n : ℕ} {v : ℝ}
    (hv : OptimalValue n v) : frameValue n = v := by
  apply le_antisymm
  · exact csSup_le (feasible_values_nonempty n) hv.2
  · exact feasible_le_frameValue hv.1

theorem frameValue_stacking (n : ℕ) : frameValue n + 1 ≤ frameValue (n + 3) := by
  have h : frameValue n ≤ frameValue (n + 3) - 1 := by
    apply csSup_le (feasible_values_nonempty n)
    intro lam hlam
    have ht := feasible_le_frameValue (stacking_feasible_value hlam)
    linarith
  linarith

def frameSide (n : ℕ) : ℝ := Real.sqrt (frameValue n)

theorem frameSide_sq (n : ℕ) : (frameSide n)^2 = frameValue n :=
  Real.sq_sqrt (frameValue_nonneg n)

end
end F3


/-!
# Exact algebraic constructions

The five-row and ten-row constructions certify feasible values. They do not,
by themselves, prove the global sharp upper bounds.
-/

namespace F3

noncomputable section
open scoped BigOperators

def core5 (r : ℝ) : Fin 5 → Fin 3 → ℝ :=
  ![ ![1, 0, 0],
     ![r / 2 - 1, 2 - r / 2, 0],
     ![r / 2 - 1, -(2 - r / 2), 0],
     ![r / 2 - 1, 0, 2 - r / 2],
     ![r / 2 - 1, 0, -(2 - r / 2)] ]

theorem core5_feasible_of_root {r : ℝ} (hr : r^2 = 6)
    (hlo : 2 ≤ r) (hhi : r ≤ 4) :
    Feasible (11 - 4 * r) (core5 r) := by
  have hc : 0 ≤ r / 2 - 1 := by linarith
  have hb : 0 ≤ 2 - r / 2 := by linarith
  have hnb : r / 2 - 2 ≤ 0 := by linarith
  constructor
  · intro i
    fin_cases i <;>
      norm_num [RowBound, core5, abs_of_nonneg hc, abs_of_nonneg hb,
        abs_neg, abs_of_nonpos hnb, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
  · intro j k
    fin_cases j <;> fin_cases k <;>
      norm_num [core5, Fin.sum_univ_succ] <;> nlinarith [hr]

theorem core5_feasible : Feasible (11 - 4 * Real.sqrt 6) (core5 (Real.sqrt 6)) := by
  have hsq : (Real.sqrt 6)^2 = 6 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  apply core5_feasible_of_root hsq <;> nlinarith

def core10 (r : ℝ) : Fin 10 → Fin 3 → ℝ :=
  ![ ![r / 2 - 1, 2 - r / 2, 0],
     ![r / 2 - 1, -(2 - r / 2), 0],
     ![r / 2 - 1, 0, 2 - r / 2],
     ![r / 2 - 1, 0, -(2 - r / 2)],
     ![0, 1, 0], ![0, 1, 0], ![0, 1, 0],
     ![0, 0, 1], ![0, 0, 1], ![0, 0, 1] ]

theorem core10_feasible_of_root {r : ℝ} (hr : r^2 = 14)
    (hlo : 2 ≤ r) (hhi : r ≤ 4) :
    Feasible (18 - 4 * r) (core10 r) := by
  have ha : 0 ≤ r / 2 - 1 := by linarith
  have hb : 0 ≤ 2 - r / 2 := by linarith
  have hnb : r / 2 - 2 ≤ 0 := by linarith
  constructor
  · intro i
    fin_cases i <;>
      norm_num [RowBound, core10, abs_of_nonneg ha, abs_of_nonneg hb,
        abs_neg, abs_of_nonpos hnb, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
  · intro j k
    fin_cases j <;> fin_cases k <;>
      norm_num [core10, Fin.sum_univ_succ] <;> nlinarith [hr]

theorem core10_feasible :
    Feasible (18 - 4 * Real.sqrt 14) (core10 (Real.sqrt 14)) := by
  have hsq : (Real.sqrt 14)^2 = 14 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 14 := Real.sqrt_nonneg _
  apply core10_feasible_of_root hsq <;> nlinarith

theorem stacking_iterate {n : ℕ} {lam : ℝ} (h : FeasibleValue n lam) (k : ℕ) :
    FeasibleValue (n + 3 * k) (lam + k) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      simpa [Nat.mul_succ, Nat.cast_add, add_assoc] using stacking_feasible_value ih

theorem empty_frame_feasible : FeasibleValue 0 0 := by
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  constructor
  · intro i
    exact Fin.elim0 i
  · intro j k
    simp

theorem divisible_feasible (m : ℕ) : FeasibleValue (3 * m) m := by
  simpa using stacking_iterate empty_frame_feasible m

theorem divisible_optimal (m : ℕ) : OptimalValue (3 * m) m := by
  constructor
  · exact divisible_feasible m
  · intro lam hlam
    rcases hlam with ⟨A, hA⟩
    have ht := trace_bound hA
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at ht
    linarith

theorem frameValue_three_mul (m : ℕ) : frameValue (3 * m) = m :=
  frameValue_eq_of_optimal (divisible_optimal m)

theorem five_lower_bound {v : ℝ} (hv : OptimalValue 5 v) :
    11 - 4 * Real.sqrt 6 ≤ v := by
  exact hv.2 _ ⟨_, core5_feasible⟩

theorem ten_lower_bound {v : ℝ} (hv : OptimalValue 10 v) :
    18 - 4 * Real.sqrt 14 ≤ v := by
  exact hv.2 _ ⟨_, core10_feasible⟩

theorem mod_two_construction (k : ℕ) :
    FeasibleValue (5 + 3 * k) (11 - 4 * Real.sqrt 6 + k) := by
  exact stacking_iterate ⟨core5 (Real.sqrt 6), core5_feasible⟩ k

theorem mod_one_stable_construction (k : ℕ) :
    FeasibleValue (10 + 3 * k) (18 - 4 * Real.sqrt 14 + k) := by
  exact stacking_iterate ⟨core10 (Real.sqrt 14), core10_feasible⟩ k

theorem stable_correction_positive : 0 < 15 - 4 * Real.sqrt 14 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
  have hn := Real.sqrt_nonneg (14 : ℝ)
  nlinarith

theorem stable_correction_gt_49_div_1600 :
    (49 : ℝ) / 1600 < 15 - 4 * Real.sqrt 14 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
  have hn := Real.sqrt_nonneg (14 : ℝ)
  nlinarith

end
end F3


/-!
# Exact-value specification and recurrence

`formula` is the piecewise expression recorded in the manuscript. It is not
the definition of the geometric optimum. Its two exceptional constants are
parameters so their algebraic isolation is not silently assumed proved.

`formula_recurrence` is an unconditional theorem about that expression.
`optimal_recurrence_of_sharp_values` explicitly takes the sharp-value
identification as a hypothesis. This file does not formalize the global
analytic proof of that identification.
-/

namespace F3

noncomputable section

def stableCorrection (r : ℕ) : ℝ :=
  if r = 0 then 0
  else if r = 1 then 15 - 4 * Real.sqrt 14
  else 10 - 4 * Real.sqrt 6

def formula (δ₁ δ₂ : ℝ) (n : ℕ) : ℝ :=
  if n = 4 then 1 + δ₁
  else if n = 7 then 2 + δ₂
  else (n / 3 : ℕ) + stableCorrection (n % 3)

theorem formula_stable {δ₁ δ₂ : ℝ} {n : ℕ} (hn : 8 ≤ n) :
    formula δ₁ δ₂ n = (n / 3 : ℕ) + stableCorrection (n % 3) := by
  have h4 : n ≠ 4 := by omega
  have h7 : n ≠ 7 := by omega
  simp [formula, h4, h7]

theorem formula_recurrence (δ₁ δ₂ : ℝ) {n : ℕ} (hn : 8 ≤ n) :
    formula δ₁ δ₂ (n + 3) = formula δ₁ δ₂ n + 1 := by
  have hn' : 8 ≤ n + 3 := by omega
  rw [formula_stable hn', formula_stable hn]
  have hq : (n + 3) / 3 = n / 3 + 1 := by omega
  have hr : (n + 3) % 3 = n % 3 := by omega
  rw [hq, hr]
  push_cast
  ring

theorem formula_at_three_mul (δ₁ δ₂ : ℝ) {m : ℕ} (_hm : 1 ≤ m) :
    formula δ₁ δ₂ (3 * m) = m := by
  have h4 : 3 * m ≠ 4 := by omega
  have h7 : 3 * m ≠ 7 := by omega
  simp [formula, h4, h7, stableCorrection]

theorem formula_at_mod_one (δ₁ δ₂ : ℝ) {m : ℕ} (hm : 3 ≤ m) :
    formula δ₁ δ₂ (3 * m + 1) = m + (15 - 4 * Real.sqrt 14) := by
  have hn : 8 ≤ 3 * m + 1 := by omega
  rw [formula_stable hn]
  have hq : (3 * m + 1) / 3 = m := by omega
  have hr : (3 * m + 1) % 3 = 1 := by omega
  simp [hq, hr, stableCorrection]

theorem formula_at_mod_two (δ₁ δ₂ : ℝ) {m : ℕ} (_hm : 1 ≤ m) :
    formula δ₁ δ₂ (3 * m + 2) = m + (10 - 4 * Real.sqrt 6) := by
  have h4 : 3 * m + 2 ≠ 4 := by omega
  have h7 : 3 * m + 2 ≠ 7 := by omega
  have hq : (3 * m + 2) / 3 = m := by omega
  have hr : (3 * m + 2) % 3 = 2 := by omega
  simp [formula, h4, h7, hq, hr, stableCorrection]

theorem formula_exception_four (δ₁ δ₂ : ℝ) : formula δ₁ δ₂ 4 = 1 + δ₁ := by
  norm_num [formula]

theorem formula_exception_seven (δ₁ δ₂ : ℝ) : formula δ₁ δ₂ 7 = 2 + δ₂ := by
  norm_num [formula]

theorem formula_gap_at_four {δ₁ δ₂ : ℝ} (h : δ₁ < δ₂) :
    formula δ₁ δ₂ 4 + 1 < formula δ₁ δ₂ 7 := by
  rw [formula_exception_four, formula_exception_seven]
  linarith

theorem formula_gap_at_seven {δ₁ δ₂ : ℝ}
    (h : δ₂ < 15 - 4 * Real.sqrt 14) :
    formula δ₁ δ₂ 7 + 1 < formula δ₁ δ₂ 10 := by
  rw [formula_exception_seven]
  norm_num [formula, stableCorrection]
  linarith

theorem formula_recurrence_except (δ₁ δ₂ : ℝ) {n : ℕ}
    (hn : 3 ≤ n) (h4 : n ≠ 4) (h7 : n ≠ 7) :
    formula δ₁ δ₂ (n + 3) = formula δ₁ δ₂ n + 1 := by
  by_cases hlarge : 8 ≤ n
  · exact formula_recurrence δ₁ δ₂ hlarge
  · have hnupper : n ≤ 7 := by omega
    interval_cases n <;> norm_num [formula, stableCorrection] at *
    all_goals ring

theorem correction_order_of_root_intervals {y₁ y₂ : ℝ}
    (hy₁0 : 0 ≤ y₁) (hy₁ : y₁ < 17 / 100)
    (hy₂lo : 347 / 2000 < y₂) (hy₂hi : y₂ < 7 / 40) :
    y₁^2 < y₂^2 ∧ y₂^2 < 15 - 4 * Real.sqrt 14 := by
  constructor
  · nlinarith
  · have hbound : y₂^2 < (49 : ℝ) / 1600 := by nlinarith
    exact lt_trans hbound stable_correction_gt_49_div_1600

/-- The two algebraic root conditions used in the paper. Their existence and
uniqueness are recorded for specification, not asserted proved in Lean here. -/
def rootOneEquation (y : ℝ) : ℝ :=
  let x := Real.sqrt (1 + y^2)
  let p := Real.sqrt 2 - x
  (x * p - y)^2 + (x - y * p)^2

def rootTwoEquation (y : ℝ) : ℝ :=
  let x := Real.sqrt (2 + y^2)
  let p := Real.sqrt 2 - y
  ((x * p - y) / 2)^2 + ((x - y * p) / 2)^2

def ExceptionalRoots (y₁ y₂ : ℝ) : Prop :=
  0 < y₁ ∧ y₁ < 17 / 100 ∧
  347 / 2000 < y₂ ∧ y₂ < 7 / 40 ∧
  rootOneEquation y₁ = 1 ∧ rootTwoEquation y₂ = 1

/-- An explicit interface to the analytic sharp-value theorem.

This is a proposition, not a new axiom, and no inhabitant is supplied here.
-/
def SharpValues (F : ℕ → ℝ) (δ₁ δ₂ : ℝ) : Prop :=
  ∀ n, 3 ≤ n → F n = formula δ₁ δ₂ n

theorem recurrence_of_sharp_values {F : ℕ → ℝ} {δ₁ δ₂ : ℝ}
    (hsharp : SharpValues F δ₁ δ₂) {n : ℕ} (hn : 8 ≤ n) :
    F (n + 3) = F n + 1 := by
  rw [hsharp (n + 3) (by omega), hsharp n (by omega)]
  exact formula_recurrence δ₁ δ₂ hn

theorem squared_recurrence_of_sharp_values {f : ℕ → ℝ} {δ₁ δ₂ : ℝ}
    (hsharp : SharpValues (fun n => (f n)^2) δ₁ δ₂)
    {n : ℕ} (hn : 8 ≤ n) :
    (f (n + 3))^2 = (f n)^2 + 1 := by
  exact recurrence_of_sharp_values hsharp hn

theorem frameValue_recurrence_of_sharp_values {δ₁ δ₂ : ℝ}
    (hsharp : SharpValues frameValue δ₁ δ₂) {n : ℕ} (hn : 8 ≤ n) :
    frameValue (n + 3) = frameValue n + 1 :=
  recurrence_of_sharp_values hsharp hn

theorem frameSide_squared_recurrence_of_sharp_values {δ₁ δ₂ : ℝ}
    (hsharp : SharpValues frameValue δ₁ δ₂) {n : ℕ} (hn : 8 ≤ n) :
    (frameSide (n + 3))^2 = (frameSide n)^2 + 1 := by
  rw [frameSide_sq, frameSide_sq]
  exact frameValue_recurrence_of_sharp_values hsharp hn

end
end F3
