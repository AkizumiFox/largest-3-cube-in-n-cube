import F3.Cores

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
