import F3.Frames

/-!
# A geometric formulation independent of the row constraints

The unit cube is defined by membership of points. An affine image of it is
required to lie in the ambient unit cube. The linear part must multiply
Euclidean squared distances by the square of the prescribed side length.
Neither row budgets nor a Gram condition occur in `GeometricSide`.
-/

namespace F3

noncomputable section
open scoped BigOperators

def UnitCube {ι : Type*} (x : ι → ℝ) : Prop :=
  ∀ i, |x i| ≤ (1 : ℝ) / 2

def linearImage {n : ℕ} (A : Fin n → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) (i : Fin n) : ℝ :=
  A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2

def AffineCubeContained {n : ℕ} (A : Fin n → Fin 3 → ℝ)
    (c : Fin n → ℝ) : Prop :=
  ∀ x : Fin 3 → ℝ, UnitCube x → UnitCube (fun i => c i + linearImage A x i)

def ScalesSquaredDistances {n : ℕ} (side : ℝ)
    (A : Fin n → Fin 3 → ℝ) : Prop :=
  ∀ x y : Fin 3 → ℝ,
    (∑ i, (linearImage A x i - linearImage A y i)^2) =
      side^2 * ((x 0 - y 0)^2 + (x 1 - y 1)^2 + (x 2 - y 2)^2)

def GeometricSide (n : ℕ) (side : ℝ) : Prop :=
  0 ≤ side ∧ ∃ (A : Fin n → Fin 3 → ℝ) (c : Fin n → ℝ),
    ScalesSquaredDistances side A ∧ AffineCubeContained A c

private def endpoint (a : ℝ) : ℝ :=
  if 0 ≤ a then 1 / 2 else -(1 / 2)

private theorem endpoint_abs (a : ℝ) : |endpoint a| = (1 : ℝ) / 2 := by
  unfold endpoint
  split <;> norm_num

private theorem mul_endpoint (a : ℝ) : a * endpoint a = |a| / 2 := by
  unfold endpoint
  split_ifs with h
  · rw [abs_of_nonneg h]
    ring
  · rw [abs_of_neg (lt_of_not_ge h)]
    ring

theorem rowBound_of_affineCubeContained {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} {c : Fin n → ℝ}
    (h : AffineCubeContained A c) (i : Fin n) : RowBound (A i) := by
  let x : Fin 3 → ℝ := fun j => endpoint (A i j)
  have hx : UnitCube x := by
    intro j
    exact le_of_eq (endpoint_abs (A i j))
  have hnx : UnitCube (fun j => -x j) := by
    intro j
    simpa only [abs_neg] using hx j
  have hp := (abs_le.mp (h x hx i)).2
  have hm := (abs_le.mp (h (fun j => -x j) hnx i)).1
  change c i + linearImage A x i ≤ 1 / 2 at hp
  change -(1 / 2) ≤ c i + linearImage A (fun j => -x j) i at hm
  have he : linearImage A x i = (|A i 0| + |A i 1| + |A i 2|) / 2 := by
    dsimp [linearImage, x]
    rw [mul_endpoint, mul_endpoint, mul_endpoint]
    ring
  have hn : linearImage A (fun j => -x j) i = -linearImage A x i := by
    unfold linearImage
    ring
  rw [he] at hp
  rw [hn, he] at hm
  unfold RowBound
  linarith

theorem affineCubeContained_zero_of_rows {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} (h : ∀ i, RowBound (A i)) :
    AffineCubeContained A (fun _ => 0) := by
  intro x hx i
  simp only [zero_add, linearImage]
  have h0 := mul_le_mul_of_nonneg_left (hx 0) (abs_nonneg (A i 0))
  have h1 := mul_le_mul_of_nonneg_left (hx 1) (abs_nonneg (A i 1))
  have h2 := mul_le_mul_of_nonneg_left (hx 2) (abs_nonneg (A i 2))
  have hr := h i
  unfold RowBound at hr
  calc
    |A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2|
        ≤ |A i 0 * x 0| + |A i 1 * x 1| + |A i 2 * x 2| := by
          exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ (1 : ℝ) / 2 := by
      simp only [abs_mul]
      linarith

theorem exists_affineCubeContained_iff_rows {n : ℕ}
    (A : Fin n → Fin 3 → ℝ) :
    (∃ c, AffineCubeContained A c) ↔ ∀ i, RowBound (A i) := by
  constructor
  · rintro ⟨c, hc⟩ i
    exact rowBound_of_affineCubeContained hc i
  · intro h
    exact ⟨fun _ => 0, affineCubeContained_zero_of_rows h⟩

private theorem squaredImage_expansion {n : ℕ}
    (A : Fin n → Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    (∑ i, (linearImage A x i)^2) =
      (∑ i, A i 0 * A i 0) * (x 0)^2 +
      (∑ i, A i 1 * A i 1) * (x 1)^2 +
      (∑ i, A i 2 * A i 2) * (x 2)^2 +
      (∑ i, A i 0 * A i 1) * (2 * x 0 * x 1) +
      (∑ i, A i 0 * A i 2) * (2 * x 0 * x 2) +
      (∑ i, A i 1 * A i 2) * (2 * x 1 * x 2) := by
  calc
    (∑ i, (linearImage A x i)^2) =
        ∑ i, (A i 0 * A i 0 * (x 0)^2 +
          A i 1 * A i 1 * (x 1)^2 +
          A i 2 * A i 2 * (x 2)^2 +
          A i 0 * A i 1 * (2 * x 0 * x 1) +
          A i 0 * A i 2 * (2 * x 0 * x 2) +
          A i 1 * A i 2 * (2 * x 1 * x 2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            unfold linearImage
            ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_mul]

theorem scalesSquaredDistances_of_gram {n : ℕ} {side : ℝ}
    {A : Fin n → Fin 3 → ℝ}
    (h : ∀ j k, (∑ i, A i j * A i k) = if j = k then side^2 else 0) :
    ScalesSquaredDistances side A := by
  intro x y
  have he (i : Fin n) : linearImage A x i - linearImage A y i =
      linearImage A (fun j => x j - y j) i := by
    unfold linearImage
    ring
  simp_rw [he]
  rw [squaredImage_expansion]
  rw [h 0 0, h 1 1, h 2 2, h 0 1, h 0 2, h 1 2]
  norm_num [Fin.ext_iff]
  ring

theorem gram_of_scalesSquaredDistances {n : ℕ} {side : ℝ}
    {A : Fin n → Fin 3 → ℝ} (h : ScalesSquaredDistances side A) :
    ∀ j k, (∑ i, A i j * A i k) = if j = k then side^2 else 0 := by
  have he (x : Fin 3 → ℝ) :
      (∑ i, (linearImage A x i)^2) = side^2 * ((x 0)^2 + (x 1)^2 + (x 2)^2) := by
    simpa [linearImage] using h x (fun _ => 0)
  have h0 := he ![1, 0, 0]
  have h1 := he ![0, 1, 0]
  have h2 := he ![0, 0, 1]
  simp only [linearImage, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.head_fin_const,
    mul_one, mul_zero, add_zero, zero_add, one_pow, zero_pow (by decide : 2 ≠ 0)] at h0 h1 h2
  have h01 := he ![1, 1, 0]
  have h02 := he ![1, 0, 1]
  have h12 := he ![0, 1, 1]
  rw [squaredImage_expansion] at h01 h02 h12
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.head_fin_const] at h01 h02 h12
  simp only [pow_two] at h0 h1 h2
  rw [h0, h1, h2] at h01 h02 h12
  have hz01 : (∑ i, A i 0 * A i 1) = 0 := by nlinarith [h01]
  have hz02 : (∑ i, A i 0 * A i 2) = 0 := by nlinarith [h02]
  have hz12 : (∑ i, A i 1 * A i 2) = 0 := by nlinarith [h12]
  intro j k
  fin_cases j <;> fin_cases k
  · simpa [pow_two] using h0
  · simpa using hz01
  · simpa using hz02
  · change (∑ i, A i 1 * A i 0) = 0
    calc
      _ = ∑ i, A i 0 * A i 1 := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = 0 := hz01
  · simpa [pow_two] using h1
  · simpa using hz12
  · change (∑ i, A i 2 * A i 0) = 0
    calc
      _ = ∑ i, A i 0 * A i 2 := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = 0 := hz02
  · change (∑ i, A i 2 * A i 1) = 0
    calc
      _ = ∑ i, A i 1 * A i 2 := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = 0 := hz12
  · simpa [pow_two] using h2

theorem geometricSide_iff_feasibleValue {n : ℕ} {side : ℝ} :
    GeometricSide n side ↔ 0 ≤ side ∧ FeasibleValue n (side^2) := by
  constructor
  · rintro ⟨hs, A, c, hdist, hcube⟩
    exact ⟨hs, A, fun i => rowBound_of_affineCubeContained hcube i,
      gram_of_scalesSquaredDistances hdist⟩
  · rintro ⟨hs, A, hA⟩
    exact ⟨hs, A, fun _ => 0, scalesSquaredDistances_of_gram hA.2,
      affineCubeContained_zero_of_rows hA.1⟩

/-- Positive side length makes the geometric linear map an actual embedding. -/
theorem scalesSquaredDistances_injective {n : ℕ} {side : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hs : 0 < side)
    (h : ScalesSquaredDistances side A) : Function.Injective (linearImage A) := by
  intro x y hxy
  have he := h x y
  have hz : (∑ i, (linearImage A x i - linearImage A y i)^2) = 0 := by
    simp_rw [congrFun hxy]
    simp
  rw [hz] at he
  have hsum : (x 0 - y 0)^2 + (x 1 - y 1)^2 + (x 2 - y 2)^2 = 0 :=
    (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ (ne_of_gt hs))
  have h0 : x 0 - y 0 = 0 := by
    apply sq_eq_zero_iff.mp
    nlinarith [sq_nonneg (x 1 - y 1), sq_nonneg (x 2 - y 2)]
  have h1 : x 1 - y 1 = 0 := by
    apply sq_eq_zero_iff.mp
    nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 2 - y 2)]
  have h2 : x 2 - y 2 = 0 := by
    apply sq_eq_zero_iff.mp
    nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
  funext j
  fin_cases j
  · exact sub_eq_zero.mp h0
  · exact sub_eq_zero.mp h1
  · exact sub_eq_zero.mp h2

/-- Supremum of side lengths in the independent geometric containment problem. -/
def geometricValue (n : ℕ) : ℝ := sSup {side : ℝ | GeometricSide n side}

theorem geometricSide_zero (n : ℕ) : GeometricSide n 0 := by
  rw [geometricSide_iff_feasibleValue]
  exact ⟨le_rfl, by simpa using zero_feasible_value n⟩

theorem geometricSide_le_sqrt_frameValue {n : ℕ} {side : ℝ}
    (h : GeometricSide n side) : side ≤ Real.sqrt (frameValue n) := by
  exact Real.le_sqrt_of_sq_le
    (feasible_le_frameValue (geometricSide_iff_feasibleValue.mp h).2)

theorem geometric_values_bddAbove (n : ℕ) :
    BddAbove {side : ℝ | GeometricSide n side} := by
  exact ⟨Real.sqrt (frameValue n), fun _ h => geometricSide_le_sqrt_frameValue h⟩

theorem geometricValue_nonneg (n : ℕ) : 0 ≤ geometricValue n :=
  le_csSup (geometric_values_bddAbove n) (geometricSide_zero n)

theorem geometricValue_eq_frameSide (n : ℕ) : geometricValue n = frameSide n := by
  have hnonneg := geometricValue_nonneg n
  have hupper : geometricValue n ≤ Real.sqrt (frameValue n) := by
    exact csSup_le ⟨0, geometricSide_zero n⟩ (fun _ h => geometricSide_le_sqrt_frameValue h)
  have hlower : frameValue n ≤ (geometricValue n)^2 := by
    apply csSup_le (feasible_values_nonempty n)
    intro lam hlam
    have hlam0 : 0 ≤ lam := by
      rcases hlam with ⟨A, hA⟩
      exact feasible_nonneg hA
    have hg : GeometricSide n (Real.sqrt lam) := by
      rw [geometricSide_iff_feasibleValue, Real.sq_sqrt hlam0]
      exact ⟨Real.sqrt_nonneg lam, hlam⟩
    have hle : Real.sqrt lam ≤ geometricValue n :=
      le_csSup (geometric_values_bddAbove n) hg
    nlinarith [Real.sq_sqrt hlam0, Real.sqrt_nonneg lam]
  unfold frameSide
  apply le_antisymm hupper
  exact (Real.sqrt_le_iff).2 ⟨hnonneg, hlower⟩

theorem geometricValue_sq (n : ℕ) : (geometricValue n)^2 = frameValue n := by
  rw [geometricValue_eq_frameSide, frameSide_sq]

end
end F3
