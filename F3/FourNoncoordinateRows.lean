import F3.SharpValues
import F3.FiniteCoreStabilization

/-!
# A four-row residual-core bound for every optimal three-column frame value

The manuscript's explicit constructions have at most four rows which are not
signed unit coordinate vectors. This source records that additional quantified
claim, using the actual finite-frame supremum. No sharp-value hypothesis is
introduced; sharpness follows from `frameValue_eq_formula` and its residue-class
specializations. This file must be rebuilt with the pinned Lean toolchain before
its proof status is described as kernel-verified.
-/

namespace F3
noncomputable section
open scoped BigOperators

private theorem count_le_of_subset {n : ℕ}
    (A : Fin n → Fin 3 → ℝ) (S : Finset (Fin n))
    (h : ∀ i, ¬ General.SignedCoordinate (A i) → i ∈ S) :
    General.noncoordinateCount A ≤ S.card := by
  classical
  exact Finset.card_le_card (by
    intro i hi
    exact h i (Finset.mem_filter.mp hi).2)

private theorem core5_count_le_four (r : ℝ) :
    General.noncoordinateCount (core5 r) ≤ 4 := by
  classical
  have hrow : core5 r (0 : Fin 5) = General.coordinateRow (0 : Fin 3) := by
    funext j
    fin_cases j <;> norm_num [core5, General.coordinateRow]
  have hs : General.SignedCoordinate (core5 r (0 : Fin 5)) := by
    rw [hrow]
    exact General.coordinateRow_signed 0
  have hmem (i : Fin 5) (hi : 0 < i.val) :
      i ∈ ({1, 2, 3, 4} : Finset (Fin 5)) := by
    fin_cases i <;> simp_all
  have ht := count_le_of_subset (core5 r)
      ({1, 2, 3, 4} : Finset (Fin 5)) (by
        intro i hi
        by_cases h : i = 0
        · subst i
          exact False.elim (hi hs)
        · exact hmem i (by have := i.isLt; omega))
  simpa using ht

private theorem exceptional7_tail_signed (x y C S : ℝ) (i : Fin 7)
    (hi : 3 ≤ i.val) :
    General.SignedCoordinate (exceptionalCore7 x y C S i) := by
  have hrow : exceptionalCore7 x y C S i =
      General.coordinateRow (if i.val ≤ 4 then (1 : Fin 3) else 2) := by
    funext j
    fin_cases i <;> fin_cases j <;>
      norm_num [exceptionalCore7, General.coordinateRow] at *
    all_goals simp_all [Fin.ext_iff]
  rw [hrow]
  exact General.coordinateRow_signed _

private theorem exceptional7_count_le_four (x y C S : ℝ) :
    General.noncoordinateCount (exceptionalCore7 x y C S) ≤ 4 := by
  classical
  have hmem (i : Fin 7) (hi : i.val < 3) :
      i ∈ ({0, 1, 2} : Finset (Fin 7)) := by
    fin_cases i <;> simp_all
  have ht := count_le_of_subset (exceptionalCore7 x y C S)
      ({0, 1, 2} : Finset (Fin 7)) (by
        intro i hi
        by_cases h : i.val < 3
        · exact hmem i h
        · exact False.elim (hi (exceptional7_tail_signed x y C S i (by omega))))
  have hc : ({0, 1, 2} : Finset (Fin 7)).card = 3 := by decide
  rw [hc] at ht
  omega

private theorem core10_tail_signed (r : ℝ) (i : Fin 10) (hi : 4 ≤ i.val) :
    General.SignedCoordinate (core10 r i) := by
  have hrow : core10 r i =
      General.coordinateRow (if i.val ≤ 6 then (1 : Fin 3) else 2) := by
    funext j
    fin_cases i <;> fin_cases j <;>
      norm_num [core10, General.coordinateRow] at *
    all_goals simp_all [Fin.ext_iff]
  rw [hrow]
  exact General.coordinateRow_signed _

private theorem core10_count_le_four (r : ℝ) :
    General.noncoordinateCount (core10 r) ≤ 4 := by
  classical
  have hmem (i : Fin 10) (hi : i.val < 4) :
      i ∈ ({0, 1, 2, 3} : Finset (Fin 10)) := by
    fin_cases i <;> simp_all
  have ht := count_le_of_subset (core10 r)
      ({0, 1, 2, 3} : Finset (Fin 10)) (by
        intro i hi
        by_cases h : i.val < 4
        · exact hmem i h
        · exact False.elim (hi (core10_tail_signed r i (by omega))))
  simpa using ht

private theorem zero_core : General.FeasibleWithCore 3 0 0 4 := by
  obtain ⟨A, hA⟩ := General.zero_feasible 3 0
  exact ⟨A, hA, (General.noncoordinateCount_le A).trans (by decide)⟩

private theorem four_core :
    General.FeasibleWithCore 3 4 (General.value 3 4) 4 := by
  obtain ⟨A, hA⟩ := canonical_exceptional_frames.1
  refine ⟨A, ?_, (General.noncoordinateCount_le A).trans (by decide)⟩
  rw [General.value_three_eq_frameValue, frameValue_four]
  exact Dominance.feasibleK_three_iff.mpr hA

private theorem five_core :
    General.FeasibleWithCore 3 5 (General.value 3 5) 4 := by
  refine ⟨core5 (Real.sqrt 6), ?_, core5_count_le_four _⟩
  rw [General.value_three_eq_frameValue, frameValue_five]
  exact Dominance.feasibleK_three_iff.mpr core5_feasible

private theorem seven_core :
    General.FeasibleWithCore 3 7 (General.value 3 7) 4 := by
  have h₂ : secondExceptionalRoot ∈ Set.Icc (0 : ℝ) (27 / 100) :=
    secondExceptionalRoot_spec.1
  rcases exceptional_components_positive h₂ with ⟨_, _, hc, hs⟩
  let A := exceptionalCore7 (exceptionalX 2 secondExceptionalRoot) secondExceptionalRoot
    (exceptionalCTwo secondExceptionalRoot) (exceptionalSTwo secondExceptionalRoot)
  have hA : Feasible (2 + secondExceptionalRoot ^ 2) A := by
    dsimp [A]
    exact exceptionalCore7_feasible (Real.sqrt_nonneg _) h₂.1 hc.le hs.le
      (exceptionalX_sq (by norm_num)) canonical_exceptional_roots.2.2.2.2.2
      (exceptional_two_linear_identities secondExceptionalRoot).1
      (exceptional_two_linear_identities secondExceptionalRoot).2
  refine ⟨A, ?_, ?_⟩
  · rw [General.value_three_eq_frameValue, frameValue_seven]
    exact Dominance.feasibleK_three_iff.mpr hA
  · dsimp [A]
    exact exceptional7_count_le_four _ _ _ _

private theorem ten_core :
    General.FeasibleWithCore 3 10 (General.value 3 10) 4 := by
  refine ⟨core10 (Real.sqrt 14), ?_, core10_count_le_four _⟩
  have hv : frameValue 10 = 18 - 4 * Real.sqrt 14 := by
    have h := frameValue_stable_first_residue (m := 3) (by decide)
    norm_num at h
    linarith
  rw [General.value_three_eq_frameValue, hv]
  exact Dominance.feasibleK_three_iff.mpr core10_feasible

/-- Every ambient dimension n ≥ 3 admits an optimal 3-frame with at most
four non-signed-unit-coordinate rows. In particular, this is an existence
claim, not a classification of every maximizing frame. -/
theorem four_noncoordinate_rows_general (n : ℕ) (hn : 3 ≤ n) :
    General.FeasibleWithCore 3 n (General.value 3 n) 4 := by
  have hdiv := Nat.mod_add_div n 3
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h0 | h1 | h2
  · have he : n = 3 * (n / 3) := by omega
    rw [he]
    have ht := General.iterate_stack_with_core zero_core (n / 3)
    simpa [General.value_divisible (show 0 < 3 by decide) (n / 3)] using ht
  · have he : n = 3 * (n / 3) + 1 := by omega
    rw [he]
    by_cases hq1 : n / 3 = 1
    · simpa [hq1] using four_core
    by_cases hq2 : n / 3 = 2
    · simpa [hq2] using seven_core
    have hm : 3 ≤ n / 3 := by omega
    have hdim : 10 + 3 * (n / 3 - 3) = 3 * (n / 3) + 1 := by omega
    have hval : (18 - 4 * Real.sqrt 14) + (n / 3 - 3 : ℕ) =
        General.value 3 (3 * (n / 3) + 1) := by
      rw [General.value_three_eq_frameValue,
          frameValue_stable_first_residue (m := n / 3) hm]
      rw [Nat.cast_sub hm]
      push_cast
      ring
    have hv10 : General.value 3 10 = 18 - 4 * Real.sqrt 14 := by
      rw [General.value_three_eq_frameValue]
      have h := frameValue_stable_first_residue (m := 3) (by decide)
      norm_num at h
      linarith
    have ht := General.iterate_stack_with_core ten_core (n / 3 - 3)
    rw [hv10, hdim, hval] at ht
    exact ht
  · have he : n = 3 * (n / 3) + 2 := by omega
    rw [he]
    have hm : 1 ≤ n / 3 := by omega
    have hdim : 5 + 3 * (n / 3 - 1) = 3 * (n / 3) + 2 := by omega
    have hval : (11 - 4 * Real.sqrt 6) + (n / 3 - 1 : ℕ) =
        General.value 3 (3 * (n / 3) + 2) := by
      rw [General.value_three_eq_frameValue,
          frameValue_second_residue (m := n / 3) hm]
      rw [Nat.cast_sub hm]
      push_cast
      ring
    have hv5 : General.value 3 5 = 11 - 4 * Real.sqrt 6 := by
      rw [General.value_three_eq_frameValue, frameValue_five]
    have ht := General.iterate_stack_with_core five_core (n / 3 - 1)
    rw [hv5, hdim, hval] at ht
    exact ht

/-- Three-column formulation of the same claim, directly matching the
manuscript's feasible-frame supremum. -/
theorem four_noncoordinate_rows (n : ℕ) (hn : 3 ≤ n) :
    ∃ A : Fin n → Fin 3 → ℝ,
      Feasible (frameValue n) A ∧ General.noncoordinateCount A ≤ 4 := by
  obtain ⟨A, hA, hC⟩ := four_noncoordinate_rows_general n hn
  refine ⟨A, ?_, hC⟩
  rw [← General.value_three_eq_frameValue]
  exact Dominance.feasibleK_three_iff.mp hA

end
end F3
