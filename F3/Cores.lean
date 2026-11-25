import F3.Frames

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
