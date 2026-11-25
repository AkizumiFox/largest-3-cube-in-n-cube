import F3.Dominance
import F3.MultiplierAlgebra
import F3.ColumnPermutations

/-!
# Active rows of actual normalized stationary systems

The statements use the original feasible matrix and an actual MultiplierSystem.
No sharp-value or all-active premise is introduced.
-/
namespace F3
noncomputable section
open scoped BigOperators

/-- A zero-weight row belongs to the multiplier kernel. -/
theorem zero_weight_row_kernel {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (M : MultiplierSystem A) (i : Fin n) (hi : M.weight i = 0) (j : Fin 3) :
    (∑ k, M.matrix j k * A i k) = 0 := by
  have h := M.stationarity i j
  rw [hi, zero_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [M.symmetric j k]
  ring

/-- Positive-weight subgradients are orthogonal to the multiplier kernel. -/
theorem positive_gradient_orthogonal {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (M : MultiplierSystem A) {x : Fin 3 → ℝ}
    (hx : ∀ j, (∑ k, M.matrix j k * x k) = 0)
    (i : Fin n) (hi : 0 < M.weight i) :
    (∑ j, M.gradient i j * x j) = 0 := by
  have h0 := M.stationarity i 0
  have h1 := M.stationarity i 1
  have h2 := M.stationarity i 2
  have hx0 := hx 0
  have hx1 := hx 1
  have hx2 := hx 2
  have h10 := M.symmetric 1 0
  have h20 := M.symmetric 2 0
  have h21 := M.symmetric 2 1
  simp only [Fin.sum_univ_three, h10, h20, h21] at h0 h1 h2 hx0 hx1 hx2
  have heq : M.weight i * (M.gradient i 0 * x 0 + M.gradient i 1 * x 1 + M.gradient i 2 * x 2) = 0 := by
    linear_combination A i 0 * hx0 + A i 1 * hx1 + A i 2 * hx2 - x 0 * h0 - x 1 * h1 - x 2 * h2
  have hz := (mul_eq_zero.mp heq).resolve_left (ne_of_gt hi)
  simpa only [Fin.sum_univ_three] using hz

theorem subgradient_coordinate_abs_one {a g : Fin 3 → ℝ}
    (hg : RowSubgradient a g) (j : Fin 3) (ha : a j ≠ 0) : |g j| = 1 := by
  have h := congrArg abs (hg.2 j)
  rw [abs_mul, abs_abs] at h
  have ha0 : 0 < |a j| := abs_pos.mpr ha
  nlinarith

/-- A subgradient orthogonal to a strictly dominant vector has zero primal
coordinate in the dominant column. -/
theorem dominant_subgradient_zero {a g x : Fin 3 → ℝ}
    (hg : RowSubgradient a g) (j : Fin 3)
    (hdom : Dominance.Dominant x j) (hortho : (∑ l, g l * x l) = 0) :
    a j = 0 := by
  by_contra ha
  have hgj := subgradient_coordinate_abs_one hg j ha
  have hcancel := Dominance.finite_cancellation (x := fun l => g l * x l) hortho j
  rw [abs_mul, hgj, one_mul] at hcancel
  have hsmall : (∑ l ∈ Finset.univ.erase j, |g l * x l|) ≤ Dominance.minorL1 x j := by
    apply Finset.sum_le_sum
    intro l _
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hg.1 l)
  exact (not_le_of_gt hdom) (hcancel.trans hsmall)

theorem zero_diagonal_row {n : ℕ} {s : ℝ} {A : Fin n → Fin 3 → ℝ}
    (hA : Feasible s A) (hs : 0 < s) (M : MultiplierSystem A)
    {j : Fin 3} (hj : M.matrix j j = 0) (k : Fin 3) : M.matrix j k = 0 := by
  have h := multiplier_entry_bound hA hs M j k
  rw [hj] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- A zero-weight row with a strictly dominant column forces that entire
multiplier row and column to vanish. -/
theorem dominant_zero_weight_diagonal {n : ℕ} {s : ℝ} {A : Fin n → Fin 3 → ℝ}
    (hA : Feasible s A) (hs : 0 < s) (M : MultiplierSystem A)
    (i : Fin n) (hi : M.weight i = 0) (j : Fin 3)
    (hdom : Dominance.Dominant (A i) j) : M.matrix j j = 0 := by
  have hkernel := zero_weight_row_kernel M i hi
  have hprimal (h : Fin n) (hh : 0 < M.weight h) : A h j = 0 :=
    dominant_subgradient_zero (M.subgradient h) j hdom
      (positive_gradient_orthogonal M hkernel h hh)
  have hdiag := multiplier_diagonal_identity hA M j
  have hsum : (∑ h, M.weight h * |A h j|) = 0 := by
    apply Finset.sum_eq_zero
    intro h _
    by_cases hw : M.weight h = 0
    · simp [hw]
    · have hp : 0 < M.weight h := lt_of_le_of_ne (M.weight_nonneg h) (Ne.symm hw)
      simp [hprimal h hp]
  rw [hsum] at hdiag
  exact (mul_eq_zero.mp hdiag).resolve_left (ne_of_gt hs)

theorem zero_diagonal_weight_of_nonzero_entry {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (hs : 0 < s)
    (M : MultiplierSystem A) {j : Fin 3} (hj : M.matrix j j = 0)
    (i : Fin n) (ha : A i j ≠ 0) : M.weight i = 0 := by
  have hz (k : Fin 3) : M.matrix k j = 0 := by
    rw [M.symmetric k j]
    exact zero_diagonal_row hA hs M hj k
  have h := M.stationarity i j
  simp only [hz, mul_zero, Finset.sum_const_zero] at h
  have hg := subgradient_coordinate_abs_one (M.subgradient i) j ha
  have hgn : M.gradient i j ≠ 0 := by intro he; simp [he] at hg
  exact (mul_eq_zero.mp h.symm).resolve_right hgn

theorem dominant_weight_zero_iff {n : ℕ} {s : ℝ} {A : Fin n → Fin 3 → ℝ}
    (hA : Feasible s A) (hs : 0 < s) (M : MultiplierSystem A)
    (i : Fin n) (j : Fin 3) (hdom : Dominance.Dominant (A i) j) :
    M.weight i = 0 ↔ M.matrix j j = 0 := by
  constructor
  · intro hi
    exact dominant_zero_weight_diagonal hA hs M i hi j hdom
  · intro hj
    apply zero_diagonal_weight_of_nonzero_entry hA hs M hj i
    intro ha
    have hn := Dominance.minorL1_nonneg (A i) j
    unfold Dominance.Dominant at hdom
    rw [ha, abs_zero] at hdom
    linarith

def activeCount {n : ℕ} {A : Fin n → Fin 3 → ℝ} (M : MultiplierSystem A) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => M.weight i ≠ 0)).card

def signedSupportCount (u : Fin 3 → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => u j ≠ 0)).card

/-- Quantization for an actual normalized multiplier whose matrix is a signed
rank-one outer product. The proof uses the actual row budgets and Gram equations. -/
theorem signed_rank_one_quantization {n : ℕ} {s τ : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A)
    (M : MultiplierSystem A) (hτ : 0 < τ) (u : Fin 3 → ℝ)
    (hu : ∀ j, u j = 0 ∨ u j = 1 ∨ u j = -1)
    (hun : ∃ j, u j ≠ 0)
    (hform : ∀ j k, M.matrix j k = τ * u j * u k) :
    1 ≤ signedSupportCount u ∧ signedSupportCount u ≤ 3 ∧
      (signedSupportCount u : ℝ) * s = (activeCount M : ℝ) := by
  classical
  let t : Fin n → ℝ := fun i => ∑ j, A i j * u j
  have huabs (j : Fin 3) : |u j| ≤ 1 := by
    rcases hu j with h | h | h <;> rw [h] <;> norm_num
  obtain ⟨j₀, hj₀⟩ := hun
  have huone : |u j₀| = 1 := by
    rcases hu j₀ with h | h | h
    · exact False.elim (hj₀ h)
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hstat (i : Fin n) (j : Fin 3) : τ * t i * u j = M.weight i * M.gradient i j := by
    calc
      _ = ∑ k, A i k * (τ * u k * u j) := by
        dsimp [t]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k, A i k * M.matrix k j := by simp_rw [hform]
      _ = _ := M.stationarity i j
  have henergy (i : Fin n) : τ * (t i)^2 = M.weight i * Dominance.l1 (A i) := by
    have h0 := hstat i 0
    have h1 := hstat i 1
    have h2 := hstat i 2
    have hg0 := (M.subgradient i).2 0
    have hg1 := (M.subgradient i).2 1
    have hg2 := (M.subgradient i).2 2
    have ht : t i = A i 0 * u 0 + A i 1 * u 1 + A i 2 * u 2 := by simp [t, Fin.sum_univ_three]
    simp only [Dominance.l1, Fin.sum_univ_three]
    linear_combination A i 0*h0 + A i 1*h1 + A i 2*h2 + τ*t i*ht + M.weight i*hg0 + M.weight i*hg1 + M.weight i*hg2
  have htbound (i : Fin n) : |t i| ≤ 1 := by
    calc
      _ ≤ ∑ j, |A i j * u j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |A i j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (huabs j)
      _ ≤ 1 := by simpa only [Fin.sum_univ_three] using hA.1 i
  have hrows (i : Fin n) : (t i)^2 = if M.weight i = 0 then 0 else 1 := by
    have he := henergy i
    by_cases hi : M.weight i = 0
    · rw [hi, zero_mul] at he
      simp only [hi, ite_true]
      exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hτ)
    · have hip : 0 < M.weight i := lt_of_le_of_ne (M.weight_nonneg i) (Ne.symm hi)
      have hl1 : Dominance.l1 (A i) = 1 := by
        simpa only [Dominance.l1, Fin.sum_univ_three] using M.complementary i hip
      rw [hl1, mul_one] at he
      have hs := congrArg abs (hstat i j₀)
      rw [abs_mul, abs_mul, abs_of_pos hτ, huone, mul_one,
        abs_mul, abs_of_nonneg (M.weight_nonneg i)] at hs
      have hbound : τ * |t i| ≤ M.weight i := by
        rw [hs]
        exact mul_le_of_le_one_right (M.weight_nonneg i) ((M.subgradient i).1 j₀)
      have hsq : |t i| ≤ (t i)^2 := (mul_le_mul_left hτ).mp (he ▸ hbound)
      have hnonneg := abs_nonneg (t i)
      have hupper := htbound i
      have hproduct : |t i| * (|t i| - 1) = 0 := by nlinarith [sq_abs (t i)]
      have hnonzero : |t i| ≠ 0 := by
        intro hz
        have hti : t i = 0 := abs_eq_zero.mp hz
        rw [hti] at he
        norm_num at he
        exact hi he.symm
      have hone : |t i| = 1 := by
        have h := (mul_eq_zero.mp hproduct).resolve_left hnonzero
        linarith
      simp only [hi, if_false]
      nlinarith [sq_abs (t i)]
  have htenergy : (∑ i, (t i)^2) = (activeCount M : ℝ) := by
    simp_rw [hrows]
    simp [activeCount, Finset.sum_ite]
  have huenergy : (∑ j, (u j)^2) = (signedSupportCount u : ℝ) := by
    have he (j : Fin 3) : (u j)^2 = if u j = 0 then 0 else 1 := by
      rcases hu j with h | h | h <;> rw [h] <;> norm_num
    simp_rw [he]
    simp [signedSupportCount, Finset.sum_ite]
  have hgram := Dominance.gram_quadratic (Dominance.feasibleK_three_iff.mpr hA) u
  change (∑ i, (t i)^2) = s * (∑ j, (u j)^2) at hgram
  rw [htenergy, huenergy] at hgram
  have hq1 : 1 ≤ signedSupportCount u := by
    apply Finset.card_pos.mpr
    exact ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀⟩⟩
  have hq3 : signedSupportCount u ≤ 3 := by
    have h := Finset.card_le_card (Finset.filter_subset (fun j => u j ≠ 0) (Finset.univ : Finset (Fin 3)))
    simpa [signedSupportCount] using h
  exact ⟨hq1, hq3, by nlinarith [hgram]⟩

/-- The quantized level is impossible in the first residue's open interval. -/
theorem signed_rank_one_excluded_residue_one {m : ℕ} {d τ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ) + d) A)
    (M : MultiplierSystem A) (hd : 0 < d) (hdhi : d < 1 / 3)
    (hτ : 0 < τ) (u : Fin 3 → ℝ)
    (hu : ∀ j, u j = 0 ∨ u j = 1 ∨ u j = -1)
    (hun : ∃ j, u j ≠ 0)
    (hform : ∀ j k, M.matrix j k = τ * u j * u k) : False := by
  obtain ⟨hq1, hq3, heq⟩ := signed_rank_one_quantization hA M hτ u hu hun hform
  have hqr1 : (1 : ℝ) ≤ signedSupportCount u := by exact_mod_cast hq1
  have hqr3 : (signedSupportCount u : ℝ) ≤ 3 := by exact_mod_cast hq3
  have hprod0 : 0 < (signedSupportCount u : ℝ) * d := mul_pos (by linarith) hd
  have hprod1 : (signedSupportCount u : ℝ) * d < 1 := by nlinarith
  have hrlo : ((signedSupportCount u * m : ℕ) : ℝ) < activeCount M := by
    push_cast
    nlinarith
  have hrhi : (activeCount M : ℝ) < (signedSupportCount u * m + 1 : ℕ) := by
    push_cast
    nlinarith
  have hnlo : signedSupportCount u * m < activeCount M := by exact_mod_cast hrlo
  have hnhi : activeCount M < signedSupportCount u * m + 1 := by exact_mod_cast hrhi
  omega

/-- A degenerate two-by-two block, together with the multiplier entry bounds,
forces one of the signed rank-one forms. -/
theorem zero_diagonal_degenerate_form {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (hs : 0 < s)
    (M : MultiplierSystem A) (h00 : M.matrix 0 0 = 0)
    (hdet : M.matrix 1 1 * M.matrix 2 2 - (M.matrix 1 2)^2 ≤ 0) :
    ∃ (τ : ℝ) (u : Fin 3 → ℝ), 0 < τ ∧
      (∀ j, u j = 0 ∨ u j = 1 ∨ u j = -1) ∧ (∃ j, u j ≠ 0) ∧
      (∀ j k, M.matrix j k = τ * u j * u k) := by
  have h01 := zero_diagonal_row hA hs M h00 1
  have h02 := zero_diagonal_row hA hs M h00 2
  have h10 : M.matrix 1 0 = 0 := (M.symmetric 1 0).trans h01
  have h20 : M.matrix 2 0 = 0 := (M.symmetric 2 0).trans h02
  have h21 := M.symmetric 2 1
  have ha := multiplier_diagonal_nonneg hA hs M 1
  have hc := multiplier_diagonal_nonneg hA hs M 2
  have hba := multiplier_entry_bound hA hs M 1 2
  have hbc : |M.matrix 1 2| ≤ M.matrix 2 2 := by
    rw [← M.symmetric 2 1]
    exact multiplier_entry_bound hA hs M 2 1
  have htrace := multiplier_trace_identity hA M
  rw [h00] at htrace
  have hsum : 0 < M.matrix 1 1 + M.matrix 2 2 := by nlinarith
  by_cases haz : M.matrix 1 1 = 0
  · have hbz : M.matrix 1 2 = 0 := abs_eq_zero.mp (le_antisymm (haz ▸ hba) (abs_nonneg _))
    refine ⟨M.matrix 2 2, ![0,0,1], by linarith, ?_, ⟨2, by norm_num [Matrix.cons_val_two]⟩, ?_⟩
    · intro j; fin_cases j <;> norm_num
    · intro j k; fin_cases j <;> fin_cases k <;> norm_num [Fin.isValue, Matrix.cons_val_two,h00,h01,h02,h10,h20,h21,haz,hbz] <;> try assumption <;> try rfl
      all_goals first | exact h21.trans hbz | exact h21.trans hbeq | exact Eq.refl (M.matrix 2 2)
  by_cases hcz : M.matrix 2 2 = 0
  · have hbz : M.matrix 1 2 = 0 := abs_eq_zero.mp (le_antisymm (hcz ▸ hbc) (abs_nonneg _))
    refine ⟨M.matrix 1 1, ![0,1,0], by linarith, ?_, ⟨1, by norm_num⟩, ?_⟩
    · intro j; fin_cases j <;> norm_num
    · intro j k; fin_cases j <;> fin_cases k <;> norm_num [Fin.isValue, Matrix.cons_val_two,h00,h01,h02,h10,h20,h21,hcz,hbz] <;> try assumption <;> try rfl
      all_goals first | exact h21.trans hbz | exact h21.trans hbeq | exact Eq.refl (M.matrix 2 2)
  have hap : 0 < M.matrix 1 1 := lt_of_le_of_ne ha (Ne.symm haz)
  have hcp : 0 < M.matrix 2 2 := lt_of_le_of_ne hc (Ne.symm hcz)
  have habsp : 0 < |M.matrix 1 2| := by
    have hp := mul_pos hap hcp
    nlinarith [sq_abs (M.matrix 1 2), abs_nonneg (M.matrix 1 2)]
  have hmul := mul_le_mul hba hbc (abs_nonneg _) ha
  have heq : M.matrix 1 1 * M.matrix 2 2 = |M.matrix 1 2|^2 := by
    nlinarith [sq_abs (M.matrix 1 2)]
  have hc_le : M.matrix 2 2 ≤ |M.matrix 1 2| := by
    have h := mul_le_mul_of_nonneg_right hba hc
    apply (mul_le_mul_left habsp).mp
    nlinarith
  have ha_le : M.matrix 1 1 ≤ |M.matrix 1 2| := by
    have h := mul_le_mul_of_nonneg_left hbc ha
    apply (mul_le_mul_right habsp).mp
    nlinarith
  have haeq : M.matrix 1 1 = |M.matrix 1 2| := le_antisymm ha_le hba
  have hceq : M.matrix 2 2 = M.matrix 1 1 := by linarith
  by_cases hbpos : 0 ≤ M.matrix 1 2
  · have hbeq : M.matrix 1 2 = M.matrix 1 1 := by rw [abs_of_nonneg hbpos] at haeq; linarith
    refine ⟨M.matrix 1 1, ![0,1,1], hap, ?_, ⟨1, by norm_num⟩, ?_⟩
    · intro j; fin_cases j <;> norm_num
    · intro j k; fin_cases j <;> fin_cases k <;> norm_num [Fin.isValue, Matrix.cons_val_two,h00,h01,h02,h10,h20,h21,hceq,hbeq] <;> try assumption <;> try rfl
      all_goals first | exact h21.trans hbz | exact h21.trans hbeq | exact Eq.refl (M.matrix 2 2)
  · have hbeq : M.matrix 1 2 = -M.matrix 1 1 := by rw [abs_of_neg (lt_of_not_ge hbpos)] at haeq; linarith
    refine ⟨M.matrix 1 1, ![0,1,-1], hap, ?_, ⟨1, by norm_num⟩, ?_⟩
    · intro j; fin_cases j <;> norm_num
    · intro j k; fin_cases j <;> fin_cases k <;> norm_num [Fin.isValue, Matrix.cons_val_two,h00,h01,h02,h10,h20,h21,hceq,hbeq] <;> try assumption <;> try rfl
      all_goals first | exact h21.trans hbz | exact h21.trans hbeq | exact Eq.refl (M.matrix 2 2)

/-- In the first residue a zero multiplier diagonal has a nonsingular
complementary block; otherwise quantization gives a contradiction. -/
theorem residue_one_zero_diagonal_block_positive {m : ℕ} {d : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 0 < d) (hdhi : d < 1/3)
    (h00 : M.matrix 0 0 = 0) :
    0 < M.matrix 1 1 * M.matrix 2 2 - (M.matrix 1 2)^2 := by
  by_contra hn
  have hs : 0 < (m : ℝ) + d := by positivity
  obtain ⟨τ,u,hτ,hu,hun,hform⟩ := zero_diagonal_degenerate_form hA hs M h00 (le_of_not_gt hn)
  exact signed_rank_one_excluded_residue_one hA M hd hdhi hτ u hu hun hform

theorem activeCount_sum {n : ℕ} {A : Fin n → Fin 3 → ℝ} (M : MultiplierSystem A) :
    (∑ i, if M.weight i = 0 then (0 : ℝ) else 1) = (activeCount M : ℝ) := by
  classical
  simp [activeCount, Finset.sum_ite]

theorem inactiveCount_sum {n : ℕ} {A : Fin n → Fin 3 → ℝ} (M : MultiplierSystem A) :
    (∑ i, if M.weight i = 0 then (1 : ℝ) else 0) = (n : ℝ) - (activeCount M : ℝ) := by
  classical
  have h : (∑ i, if M.weight i = 0 then (1 : ℝ) else 0) +
      (∑ i, if M.weight i = 0 then (0 : ℝ) else 1) = n := by
    rw [← Finset.sum_add_distrib]
    have hi (i : Fin n) : (if M.weight i = 0 then (1 : ℝ) else 0) +
        (if M.weight i = 0 then 0 else 1) = 1 := by split_ifs <;> norm_num
    simp_rw [hi]
    simp
  rw [activeCount_sum] at h
  linarith

theorem residue_one_no_zero_diagonal_at_zero {m : ℕ} {d : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 0 < d) (hdhi : d < 1/3)
    (h00 : M.matrix 0 0 = 0) : False := by
  classical
  have hs : 0 < (m : ℝ) + d := by positivity
  have hdet := residue_one_zero_diagonal_block_positive hA M hd hdhi h00
  have h10 : M.matrix 1 0 = 0 := by
    rw [M.symmetric 1 0]
    exact zero_diagonal_row hA hs M h00 1
  have h20 : M.matrix 2 0 = 0 := by
    rw [M.symmetric 2 0]
    exact zero_diagonal_row hA hs M h00 2
  have h21 := M.symmetric 2 1
  have haxis (i : Fin (3*m+1)) (hi : M.weight i = 0) : A i 1 = 0 ∧ A i 2 = 0 := by
    have h1 := zero_weight_row_kernel M i hi 1
    have h2 := zero_weight_row_kernel M i hi 2
    simp only [Fin.sum_univ_three, h10, h20, h21, zero_mul, zero_add] at h1 h2
    have he1 : (M.matrix 1 1 * M.matrix 2 2 - (M.matrix 1 2)^2) * A i 1 = 0 := by
      linear_combination M.matrix 2 2 * h1 - M.matrix 1 2 * h2
    have he2 : (M.matrix 1 1 * M.matrix 2 2 - (M.matrix 1 2)^2) * A i 2 = 0 := by
      linear_combination M.matrix 1 1 * h2 - M.matrix 1 2 * h1
    exact ⟨(mul_eq_zero.mp he1).resolve_left (ne_of_gt hdet),
      (mul_eq_zero.mp he2).resolve_left (ne_of_gt hdet)⟩
  have hposzero (i : Fin (3*m+1)) (hi : M.weight i ≠ 0) : A i 0 = 0 := by
    by_contra ha
    exact hi (zero_diagonal_weight_of_nonzero_entry hA hs M h00 i ha)
  have hcol0 : (m : ℝ) + d ≤ (3*m+1 : ℕ) - (activeCount M : ℝ) := by
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (f := fun i => (A i 0)^2) (g := fun i => if M.weight i = 0 then (1 : ℝ) else 0) (by
        intro i _
        dsimp
        by_cases hi : M.weight i = 0
        · rw [if_pos hi]
          exact Dominance.entry_sq_le_one (Dominance.feasibleK_three_iff.mpr hA) i 0
        · rw [if_neg hi, hposzero i hi]
          norm_num)
    have hg : (∑ i, (A i 0)^2) = (m : ℝ) + d := by simpa [pow_two] using hA.2 0 0
    rw [hg, inactiveCount_sum] at hsum
    exact hsum
  have hcol12 : 2 * ((m : ℝ) + d) ≤ (activeCount M : ℝ) := by
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (f := fun i => (A i 1)^2 + (A i 2)^2)
      (g := fun i => if M.weight i = 0 then (0 : ℝ) else 1) (by
        intro i _
        dsimp
        by_cases hi : M.weight i = 0
        · rw [if_pos hi, (haxis i hi).1, (haxis i hi).2]
          norm_num
        · rw [if_neg hi]
          have h := row_energy_le_one (hA.1 i)
          nlinarith [sq_nonneg (A i 0)])
    have hg1 : (∑ i, (A i 1)^2) = (m : ℝ) + d := by simpa [pow_two] using hA.2 1 1
    have hg2 : (∑ i, (A i 2)^2) = (m : ℝ) + d := by simpa [pow_two] using hA.2 2 2
    rw [Finset.sum_add_distrib, hg1, hg2, activeCount_sum] at hsum
    linarith
  have hr : (activeCount M : ℝ) < (2*m+1 : ℕ) := by
    push_cast at hcol0 ⊢
    linarith
  have hrnat : activeCount M < 2*m+1 := by exact_mod_cast hr
  have hrle : activeCount M ≤ 2*m := by omega
  have hrreal : (activeCount M : ℝ) ≤ 2*(m : ℝ) := by exact_mod_cast hrle
  linarith

theorem residue_one_no_zero_diagonal {m : ℕ} {d : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 0 < d) (hdhi : d < 1/3)
    (j : Fin 3) (hj : M.matrix j j = 0) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 j
  have hA' := feasible_permuteColumns hA e
  have h00 : (M.permuteColumns e).matrix 0 0 = 0 := by
    simpa [e] using hj
  exact residue_one_no_zero_diagonal_at_zero hA' (M.permuteColumns e) hd hdhi h00

/-- Every row weight in every genuine normalized multiplier system is positive
in residue one. This uses feasibility, and does not require a sharp-value premise. -/
theorem active_residue_one {m : ℕ} {d : ℝ} (hd : 0 < d)
    {A : Fin (3*m+1) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) : ∀ i, 0 < M.weight i := by
  have hcoarse := Dominance.three_column_coarse hd hA
  have hdhi : d < 1/3 := by linarith [Dominance.three_dimensional_bound_lt_72_div_1000]
  obtain ⟨dom,hdom,_,_,_,_⟩ := Dominance.dominance_summary (by norm_num : 2 ≤ 3) hd
    (Dominance.feasibleK_three_iff.mpr hA)
  intro i
  by_contra hn
  have hi : M.weight i = 0 := le_antisymm (le_of_not_gt hn) (M.weight_nonneg i)
  have hs : 0 < (m : ℝ) + d := by positivity
  have hj := dominant_zero_weight_diagonal hA hs M i hi (dom i) (hdom i)
  exact residue_one_no_zero_diagonal hA M hd hdhi (dom i) hj


end
end F3
