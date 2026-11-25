import F3.MultiplierAlgebra

namespace F3
noncomputable section
open scoped BigOperators

def signColumns {ι : Type*} (A : ι → Fin 3 → ℝ) (σ : Fin 3 → ℝ) :=
  fun i j => σ j * A i j

lemma abs_eq_one_of_sign_sq {σ : ℝ} (hσ : σ*σ=1) : |σ|=1 := by
  have h := sq_abs σ
  have hp := abs_nonneg σ
  nlinarith

theorem feasible_signColumns {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (σ : Fin 3 → ℝ) (hσ : ∀ j, σ j*σ j=1) :
    Feasible s (signColumns A σ) := by
  constructor
  · intro i
    simpa [RowBound, signColumns, abs_mul, abs_eq_one_of_sign_sq (hσ 0),
      abs_eq_one_of_sign_sq (hσ 1),abs_eq_one_of_sign_sq (hσ 2)] using hA.1 i
  · intro j k
    have hsum : (∑ i, signColumns A σ i j * signColumns A σ i k) =
        (σ j*σ k)*(∑ i, A i j*A i k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [signColumns]
      ring
    rw [hsum,hA.2]
    by_cases h : j=k
    · subst k; simp [hσ j]
    · simp [h]

def MultiplierSystem.signColumns {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A)
    (σ : Fin 3 → ℝ) (hσ : ∀ j, σ j*σ j=1) :
    MultiplierSystem (F3.signColumns A σ) where
  weight := M.weight
  gradient := fun i j => σ j*M.gradient i j
  matrix := fun j k => σ j*σ k*M.matrix j k
  weight_nonneg := M.weight_nonneg
  weight_sum := M.weight_sum
  subgradient := by
    intro i
    constructor
    · intro j
      simpa [abs_mul,abs_eq_one_of_sign_sq (hσ j)] using (M.subgradient i).1 j
    · intro j
      dsimp [F3.signColumns]
      calc
        (σ j*A i j)*(σ j*M.gradient i j) =
            (σ j*σ j)*(A i j*M.gradient i j) := by ring
        _ = |A i j| := by rw [hσ j,one_mul,(M.subgradient i).2 j]
        _ = |σ j*A i j| := by rw [abs_mul,abs_eq_one_of_sign_sq (hσ j),one_mul]
  symmetric := by intro j k; rw [M.symmetric j k]; ring
  stationarity := by
    intro i j
    calc
      (∑ k, F3.signColumns A σ i k*(σ k*σ j*M.matrix k j)) =
          σ j*(∑ k, A i k*M.matrix k j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        dsimp [F3.signColumns]
        calc
          (σ k*A i k)*(σ k*σ j*M.matrix k j) =
              (σ k*σ k)*(σ j*(A i k*M.matrix k j)) := by ring
          _ = _ := by rw [hσ k,one_mul]
      _ = M.weight i*(σ j*M.gradient i j) := by rw [M.stationarity]; ring
  complementary := by
    intro i hi
    simpa [F3.signColumns,abs_mul,abs_eq_one_of_sign_sq (hσ 0),
      abs_eq_one_of_sign_sq (hσ 1),abs_eq_one_of_sign_sq (hσ 2)]
      using M.complementary i hi

def quadraticThree (S : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∑ j, ∑ k, v j*S j k*v k

theorem quadraticThree_eq {S : Fin 3 → Fin 3 → ℝ}
    (hS : ∀ j k, S j k = S k j) (v : Fin 3 → ℝ) :
    quadraticThree S v = quadThree (S 0 0) (S 1 1) (S 2 2)
      (S 0 1) (S 0 2) (S 1 2) (v 0) (v 1) (v 2) := by
  simp only [quadraticThree,Fin.sum_univ_three,quadThree,
    hS 1 0,hS 2 0,hS 2 1]
  ring

theorem quadraticThree_sign_conjugation
    (S : Fin 3 → Fin 3 → ℝ) (v σ : Fin 3 → ℝ)
    (hσ : ∀ j, σ j*σ j=1) :
    quadraticThree (fun j k => σ j*σ k*S j k) (fun j => σ j*v j) =
      quadraticThree S v := by
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  calc
    (σ j*v j)*(σ j*σ k*S j k)*(σ k*v k) =
        (σ j*σ j)*(σ k*σ k)*(v j*S j k*v k) := by ring
    _ = _ := by rw [hσ j,hσ k]; ring

/-- Full-row positive definiteness, with arbitrary signs of the full row. -/
theorem full_row_posdef {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hs : 0 < s) (M : MultiplierSystem A)
    (hw : ∀ i, 0 < M.weight i) (i₀ : ι)
    (hu : ∀ j, A i₀ j ≠ 0) (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < quadraticThree M.matrix v := by
  classical
  let σ : Fin 3 → ℝ := fun j => if A i₀ j < 0 then -1 else 1
  have hσ (j : Fin 3) : σ j*σ j=1 := by dsimp [σ]; split_ifs <;> norm_num
  have hsign (j : Fin 3) : 0 < signColumns A σ i₀ j := by
    dsimp [signColumns,σ]
    split_ifs with hj
    · linarith
    · have hp := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm (hu j))
      simpa using hp
  have hnv : σ 0*v 0 ≠ 0 ∨ σ 1*v 1 ≠ 0 ∨ σ 2*v 2 ≠ 0 := by
    by_contra h
    push_neg at h
    have hvzero : ∀ j, v j = 0 := by
      intro j
      have hs0 : σ j ≠ 0 := by
        intro hz
        have hj := hσ j
        rw [hz,zero_mul] at hj
        norm_num at hj
      fin_cases j
      · exact (mul_eq_zero.mp h.1).resolve_left hs0
      · exact (mul_eq_zero.mp h.2.1).resolve_left hs0
      · exact (mul_eq_zero.mp h.2.2).resolve_left hs0
    exact hv (funext hvzero)
  let M' := M.signColumns σ hσ
  have hp := full_positive_row_posdef (feasible_signColumns hA σ hσ) hs M'
    hw i₀ hsign (σ 0*v 0) (σ 1*v 1) (σ 2*v 2) hnv
  rw [← quadraticThree_eq M'.symmetric (fun j => σ j*v j)] at hp
  change 0 < quadraticThree (fun j k => σ j*σ k*M.matrix j k)
    (fun j => σ j*v j) at hp
  rw [quadraticThree_sign_conjugation M.matrix v σ hσ] at hp
  exact hp

end
end F3
