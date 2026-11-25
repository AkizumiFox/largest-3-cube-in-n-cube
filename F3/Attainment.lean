import F3.Geometry
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Compact attainment of the actual frame and geometric suprema

The proof uses the compact coordinate box and a closed Gram constraint.
There is no optimal-value hypothesis.
-/

namespace F3

noncomputable section
open scoped BigOperators

def gramEntry {n : ℕ} (A : Fin n → Fin 3 → ℝ) (j k : Fin 3) : ℝ :=
  ∑ i, A i j * A i k

def frameLevel {n : ℕ} (A : Fin n → Fin 3 → ℝ) : ℝ := gramEntry A 0 0

theorem continuous_gramEntry (n : ℕ) (j k : Fin 3) :
    Continuous (fun A : Fin n → Fin 3 → ℝ => gramEntry A j k) := by
  apply continuous_finset_sum
  intro i hi
  exact ((continuous_apply j).comp (continuous_apply i)).mul
    ((continuous_apply k).comp (continuous_apply i))

theorem continuous_frameLevel (n : ℕ) :
    Continuous (fun A : Fin n → Fin 3 → ℝ => frameLevel A) :=
  continuous_gramEntry n 0 0

theorem isClosed_feasible_frames (n : ℕ) :
    IsClosed {A : Fin n → Fin 3 → ℝ | Feasible (frameLevel A) A} := by
  change IsClosed ({A : Fin n → Fin 3 → ℝ | ∀ i, RowBound (A i)} ∩
    {A : Fin n → Fin 3 → ℝ | ∀ j k, gramEntry A j k =
      if j = k then frameLevel A else 0})
  apply IsClosed.inter
  · rw [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    unfold RowBound
    apply isClosed_le _ continuous_const
    exact (((continuous_apply (0 : Fin 3)).comp (continuous_apply i)).abs.add
      ((continuous_apply (1 : Fin 3)).comp (continuous_apply i)).abs).add
      ((continuous_apply (2 : Fin 3)).comp (continuous_apply i)).abs
  · rw [Set.setOf_forall]
    apply isClosed_iInter
    intro j
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro k
    apply isClosed_eq (continuous_gramEntry n j k)
    by_cases h : j = k
    · simpa [h] using continuous_frameLevel n
    · simp only [h, if_false]
      exact continuous_const

theorem isCompact_feasible_frames (n : ℕ) :
    IsCompact {A : Fin n → Fin 3 → ℝ | Feasible (frameLevel A) A} := by
  have hbox : IsCompact
      (Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  apply hbox.of_isClosed_subset (isClosed_feasible_frames n)
  intro A hA
  simp only [Set.mem_univ_pi]
  intro i j
  have hr := hA.1 i
  unfold RowBound at hr
  have hcoord : |A i j| ≤ 1 := by
    fin_cases j
    · change |A i 0| ≤ 1
      linarith [abs_nonneg (A i 1), abs_nonneg (A i 2)]
    · change |A i 1| ≤ 1
      linarith [abs_nonneg (A i 0), abs_nonneg (A i 2)]
    · change |A i 2| ≤ 1
      linarith [abs_nonneg (A i 0), abs_nonneg (A i 1)]
  exact abs_le.mp hcoord

theorem exists_optimal_frame (n : ℕ) :
    ∃ A : Fin n → Fin 3 → ℝ, Feasible (frameLevel A) A ∧
      OptimalValue n (frameLevel A) := by
  have hne : ({A : Fin n → Fin 3 → ℝ | Feasible (frameLevel A) A}).Nonempty := by
    refine ⟨fun _ _ => 0, ?_⟩
    simp [frameLevel, gramEntry, Feasible, RowBound]
  obtain ⟨A, hA, hmax⟩ :=
    (isCompact_feasible_frames n).exists_isMaxOn hne (continuous_frameLevel n).continuousOn
  refine ⟨A, hA, ⟨A, hA⟩, ?_⟩
  intro lam hlam
  rcases hlam with ⟨B, hB⟩
  have hlevel : frameLevel B = lam := by
    simpa [frameLevel, gramEntry] using hB.2 0 0
  have hmem : B ∈ {A : Fin n → Fin 3 → ℝ | Feasible (frameLevel A) A} := by
    rw [Set.mem_setOf_eq, hlevel]
    exact hB
  have hbound := hmax hmem
  change frameLevel B ≤ frameLevel A at hbound
  rwa [hlevel] at hbound

theorem frameValue_attained (n : ℕ) : FeasibleValue n (frameValue n) := by
  obtain ⟨A, hA, hopt⟩ := exists_optimal_frame n
  rw [frameValue_eq_of_optimal hopt]
  exact hopt.1

theorem frameValue_optimal (n : ℕ) : OptimalValue n (frameValue n) :=
  ⟨frameValue_attained n, fun _ h => feasible_le_frameValue h⟩

theorem geometricValue_attained (n : ℕ) : GeometricSide n (geometricValue n) := by
  rw [geometricSide_iff_feasibleValue, geometricValue_sq]
  exact ⟨geometricValue_nonneg n, frameValue_attained n⟩

end
end F3
