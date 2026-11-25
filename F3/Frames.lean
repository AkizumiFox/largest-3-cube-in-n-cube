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

This file contains the basic finite-frame formulation and elementary bounds.
The geometric equivalence and the global sharp-value theorems are proved in
`F3.Geometry`, `F3.GeneralGeometry`, and `F3.SharpValues`; they are imported by
`F3.lean`. They are not proved locally in this elementary module.
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
The corresponding geometric equivalence is formalized in `F3.Geometry`. -/
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
