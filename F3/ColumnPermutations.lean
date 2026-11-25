import F3.MultiplierAlgebra

namespace F3
noncomputable section
open scoped BigOperators

def permuteColumns {ι : Type*} (A : ι → Fin 3 → ℝ) (e : Equiv.Perm (Fin 3)) :
    ι → Fin 3 → ℝ := fun i j => A i (e j)

theorem rowBound_permute {a : Fin 3 → ℝ} (ha : RowBound a)
    (e : Equiv.Perm (Fin 3)) : RowBound (fun j => a (e j)) := by
  have h : (∑ j : Fin 3, |a (e j)|) = ∑ j : Fin 3, |a j| :=
    Equiv.sum_comp e (fun j => |a j|)
  simp only [Fin.sum_univ_three] at h
  unfold RowBound at ha ⊢
  linarith

theorem feasible_permuteColumns {ι : Type*} [Fintype ι] {s : ℝ}
    {A : ι → Fin 3 → ℝ} (hA : Feasible s A) (e : Equiv.Perm (Fin 3)) :
    Feasible s (permuteColumns A e) := by
  constructor
  · intro i
    exact rowBound_permute (hA.1 i) e
  · intro j k
    have h := hA.2 (e j) (e k)
    simpa only [permuteColumns, e.injective.eq_iff] using h

def MultiplierSystem.permuteColumns {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A) (e : Equiv.Perm (Fin 3)) :
    MultiplierSystem (permuteColumns A e) where
  weight := M.weight
  gradient := fun i j => M.gradient i (e j)
  matrix := fun j k => M.matrix (e j) (e k)
  weight_nonneg := M.weight_nonneg
  weight_sum := M.weight_sum
  subgradient := by
    intro i
    constructor
    · intro j
      exact (M.subgradient i).1 (e j)
    · intro j
      exact (M.subgradient i).2 (e j)
  symmetric := by
    intro j k
    exact M.symmetric (e j) (e k)
  stationarity := by
    intro i j
    change (∑ k, A i (e k) * M.matrix (e k) (e j)) = M.weight i * M.gradient i (e j)
    rw [Equiv.sum_comp e (fun k => A i k * M.matrix k (e j))]
    exact M.stationarity i (e j)
  complementary := by
    intro i hi
    have h : (∑ j : Fin 3, |A i (e j)|) = ∑ j : Fin 3, |A i j| :=
      Equiv.sum_comp e (fun j => |A i j|)
    simp only [Fin.sum_univ_three] at h
    change |A i (e 0)| + |A i (e 1)| + |A i (e 2)| = 1
    rw [h]
    exact M.complementary i hi

@[simp] theorem permuteColumns_apply {ι : Type*} (A : ι → Fin 3 → ℝ)
    (e : Equiv.Perm (Fin 3)) (i : ι) (j : Fin 3) :
    permuteColumns A e i j = A i (e j) := rfl

@[simp] theorem MultiplierSystem.permuteColumns_weight {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A) (e : Equiv.Perm (Fin 3)) (i : ι) :
    (M.permuteColumns e).weight i = M.weight i := rfl

@[simp] theorem MultiplierSystem.permuteColumns_matrix {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A) (e : Equiv.Perm (Fin 3)) (j k : Fin 3) :
    (M.permuteColumns e).matrix j k = M.matrix (e j) (e k) := rfl

/-- Any three real labels can be ordered by a permutation of their indices. -/
theorem exists_sorted_columns (d : Fin 3 → ℝ) :
    ∃ e : Equiv.Perm (Fin 3), d (e 0) ≤ d (e 1) ∧ d (e 1) ≤ d (e 2) := by
  by_cases h01 : d 0 ≤ d 1
  · by_cases h12 : d 1 ≤ d 2
    · exact ⟨Equiv.refl _, h01, h12⟩
    · have h21 : d 2 ≤ d 1 := le_of_not_ge h12
      by_cases h02 : d 0 ≤ d 2
      · refine ⟨Equiv.swap 1 2, ?_, ?_⟩
        · simpa [Equiv.swap_apply_def] using h02
        · simpa [Equiv.swap_apply_def] using h21
      · have h20 : d 2 ≤ d 0 := le_of_not_ge h02
        refine ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1), ?_, ?_⟩
        · simpa [Equiv.swap_apply_def] using h20
        · simpa [Equiv.swap_apply_def] using h01
  · have h10 : d 1 ≤ d 0 := le_of_not_ge h01
    by_cases h02 : d 0 ≤ d 2
    · refine ⟨Equiv.swap 0 1, ?_, ?_⟩
      · simpa [Equiv.swap_apply_def] using h10
      · simpa [Equiv.swap_apply_def] using h02
    · have h20 : d 2 ≤ d 0 := le_of_not_ge h02
      by_cases h12 : d 1 ≤ d 2
      · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), ?_, ?_⟩
        · simpa [Equiv.swap_apply_def] using h12
        · simpa [Equiv.swap_apply_def] using h20
      · have h21 : d 2 ≤ d 1 := le_of_not_ge h12
        refine ⟨Equiv.swap 0 2, ?_, ?_⟩
        · simpa [Equiv.swap_apply_def] using h21
        · simpa [Equiv.swap_apply_def] using h10

end
end F3
