import F3.ActiveRows
import F3.ColumnBounds

namespace F3
noncomputable section
open scoped BigOperators

theorem multiplier_outer_stationarity {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (M : MultiplierSystem A) {τ : ℝ} {u : Fin 3 → ℝ}
    (hform : ∀ j k, M.matrix j k = τ * u j * u k) (i : Fin n) (j : Fin 3) :
    τ * (∑ k, A i k * u k) * u j = M.weight i * M.gradient i j := by
  calc
    _ = ∑ k, A i k * (τ * u k * u j) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ k, A i k * M.matrix k j := by simp_rw [hform]
    _ = _ := M.stationarity i j

theorem multiplier_outer_energy {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (M : MultiplierSystem A) {τ : ℝ} {u : Fin 3 → ℝ}
    (hform : ∀ j k, M.matrix j k = τ * u j * u k) (i : Fin n) :
    τ * (∑ k, A i k * u k)^2 = M.weight i * Dominance.l1 (A i) := by
  have h0 := multiplier_outer_stationarity M hform i 0
  have h1 := multiplier_outer_stationarity M hform i 1
  have h2 := multiplier_outer_stationarity M hform i 2
  have hg0 := (M.subgradient i).2 0
  have hg1 := (M.subgradient i).2 1
  have hg2 := (M.subgradient i).2 2
  simp only [Fin.sum_univ_three] at h0 h1 h2 ⊢
  simp only [Dominance.l1, Fin.sum_univ_three]
  linear_combination A i 0*h0 + A i 1*h1 + A i 2*h2 +
    M.weight i*hg0 + M.weight i*hg1 + M.weight i*hg2

/-- In every positive-weight row of a rank-one system, coordinate products
align with the signs of the defining outer-product vector. -/
theorem multiplier_outer_positive_products {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (M : MultiplierSystem A) {τ : ℝ} (hτ : 0 < τ) {u : Fin 3 → ℝ}
    (hform : ∀ j k, M.matrix j k = τ * u j * u k)
    (i : Fin n) (hi : 0 < M.weight i) (j k : Fin 3) :
    0 ≤ (A i j * u j) * (A i k * u k) := by
  let t : ℝ := ∑ l, A i l * u l
  have he := multiplier_outer_energy M hform i
  have hl1 : Dominance.l1 (A i) = 1 := by
    simpa only [Dominance.l1, Fin.sum_univ_three] using M.complementary i hi
  rw [hl1, mul_one] at he
  change τ * t^2 = M.weight i at he
  have ht : t ≠ 0 := by intro hz; rw [hz] at he; norm_num at he; linarith
  have hj := multiplier_outer_stationarity M hform i j
  have hk := multiplier_outer_stationarity M hform i k
  change τ * t * u j = M.weight i * M.gradient i j at hj
  change τ * t * u k = M.weight i * M.gradient i k at hk
  have hprod (l : Fin 3) : 0 ≤ (τ*t) * (A i l*u l) := by
    have hh := multiplier_outer_stationarity M hform i l
    change τ * t * u l = M.weight i * M.gradient i l at hh
    have hsg := (M.subgradient i).2 l
    have hid : (τ*t) * (A i l*u l) = M.weight i * |A i l| := by
      linear_combination A i l * hh + M.weight i * hsg
    rw [hid]
    positivity
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have hfactor : τ*t < 0 := mul_neg_of_pos_of_neg hτ htneg
    have hjn : A i j*u j ≤ 0 := by nlinarith [hprod j]
    have hkn : A i k*u k ≤ 0 := by nlinarith [hprod k]
    exact mul_nonneg_of_nonpos_of_nonpos hjn hkn
  · have hfactor : 0 < τ*t := mul_pos hτ htpos
    exact mul_nonneg ((mul_nonneg_iff_of_pos_left hfactor).mp (hprod j))
      ((mul_nonneg_iff_of_pos_left hfactor).mp (hprod k))

theorem signed_rank_one_residue_two_quantized {m : ℕ} {d τ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5 < d) (hdhi : d ≤ 4/9)
    (hτ : 0 < τ) (u : Fin 3 → ℝ)
    (hu : ∀ j, u j = 0 ∨ u j = 1 ∨ u j = -1) (hun : ∃ j, u j ≠ 0)
    (hform : ∀ j k, M.matrix j k = τ * u j * u k) :
    signedSupportCount u = 3 ∧ d = 1/3 ∧ activeCount M = 3*m+1 := by
  obtain ⟨hq1,hq3,heq⟩ := signed_rank_one_quantization hA M hτ u hu hun hform
  have hqr1 : (1 : ℝ) ≤ signedSupportCount u := by exact_mod_cast hq1
  have hqeq : signedSupportCount u = 3 := by
    by_contra hn
    have hq2 : signedSupportCount u ≤ 2 := by omega
    have hqr2 : (signedSupportCount u : ℝ) ≤ 2 := by exact_mod_cast hq2
    have hprod0 : 0 < (signedSupportCount u : ℝ) * d := by positivity
    have hprod1 : (signedSupportCount u : ℝ) * d < 1 := by nlinarith
    have hrlo : ((signedSupportCount u*m : ℕ) : ℝ) < activeCount M := by push_cast; nlinarith
    have hrhi : (activeCount M : ℝ) < (signedSupportCount u*m+1 : ℕ) := by push_cast; nlinarith
    have hnlo : signedSupportCount u*m < activeCount M := by exact_mod_cast hrlo
    have hnhi : activeCount M < signedSupportCount u*m+1 := by exact_mod_cast hrhi
    omega
  rw [hqeq] at heq
  norm_num only [Nat.cast_ofNat] at heq
  have hrlo : ((3*m : ℕ) : ℝ) < activeCount M := by push_cast; linarith
  have hrhi : (activeCount M : ℝ) < (3*m+2 : ℕ) := by push_cast; linarith
  have hnlo : 3*m < activeCount M := by exact_mod_cast hrlo
  have hnhi : activeCount M < 3*m+2 := by exact_mod_cast hrhi
  have hR : activeCount M = 3*m+1 := by omega
  refine ⟨hqeq,?_,hR⟩
  rw [hR] at heq
  push_cast at heq
  linarith

theorem signed_support_three {u : Fin 3 → ℝ} (hq : signedSupportCount u = 3) :
    ∀ j, u j ≠ 0 := by
  classical
  have heq : Finset.univ.filter (fun j => u j ≠ 0) = (Finset.univ : Finset (Fin 3)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    simpa [signedSupportCount] using hq.ge
  intro j
  have hj : j ∈ Finset.univ.filter (fun j => u j ≠ 0) := by rw [heq]; exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hj).2

theorem activeCount_pred_unique_zero {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (M : MultiplierSystem A) (hcard : activeCount M + 1 = n) :
    ∃ r, M.weight r = 0 ∧ ∀ i, i ≠ r → 0 < M.weight i := by
  classical
  have hzcard : (Finset.univ.filter (fun i => M.weight i = 0)).card = 1 := by
    have h := inactiveCount_sum M
    have he : ((Finset.univ.filter (fun i => M.weight i = 0)).card : ℝ) =
        (n : ℝ) - (activeCount M : ℝ) := by simpa [Finset.sum_ite] using h
    have hc : (activeCount M : ℝ) + 1 = n := by exact_mod_cast hcard
    have : ((Finset.univ.filter (fun i => M.weight i = 0)).card : ℝ) = 1 := by linarith
    exact_mod_cast this
  obtain ⟨r,hr⟩ := Finset.card_eq_one.mp hzcard
  refine ⟨r,?_,?_⟩
  · have hm : r ∈ Finset.univ.filter (fun i => M.weight i = 0) := by rw [hr]; simp
    exact (Finset.mem_filter.mp hm).2
  · intro i hir
    have hi : M.weight i ≠ 0 := by
      intro hz
      have hm : i ∈ Finset.univ.filter (fun i => M.weight i = 0) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
      rw [hr,Finset.mem_singleton] at hm
      exact hir hm
    exact lt_of_le_of_ne (M.weight_nonneg i) (Ne.symm hi)

/-- Three pairwise nonpositive products force a zero coordinate. -/
theorem three_nonpositive_products_zero (x : Fin 3 → ℝ)
    (hp : ∀ j k, j ≠ k → x j * x k ≤ 0) : ∃ j, x j = 0 := by
  by_contra hn
  have hx : ∀ j, x j ≠ 0 := by simpa using hn
  have h01 := hp 0 1 (by decide)
  have h02 := hp 0 2 (by decide)
  have h12 := hp 1 2 (by decide)
  rcases lt_or_gt_of_ne (hx 0) with h0 | h0
  · have h1 : 0 < x 1 := by
      have hn1 : 0 ≤ x 1 := by nlinarith
      exact lt_of_le_of_ne hn1 (Ne.symm (hx 1))
    have h2 : 0 < x 2 := by
      have hn2 : 0 ≤ x 2 := by nlinarith
      exact lt_of_le_of_ne hn2 (Ne.symm (hx 2))
    exact (not_lt_of_ge h12) (mul_pos h1 h2)
  · have h1 : x 1 < 0 := by
      have hn1 : x 1 ≤ 0 := by nlinarith
      exact lt_of_le_of_ne hn1 (hx 1)
    have h2 : x 2 < 0 := by
      have hn2 : x 2 ≤ 0 := by nlinarith
      exact lt_of_le_of_ne hn2 (hx 2)
    exact (not_lt_of_ge h12) (mul_pos_of_neg_of_neg h1 h2)

/-- If all but one saturated row have a common coordinate-product sign pattern,
orthogonality forces one column to consist entirely of unit pure rows. -/
theorem single_exception_products_integer {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (r : Fin n)
    (u : Fin 3 → ℝ) (hu : ∀ j, u j ≠ 0)
    (hprod : ∀ i, i ≠ r → ∀ j k, 0 ≤ (A i j*u j)*(A i k*u k))
    (hsat : ∀ i, i ≠ r → Dominance.l1 (A i) = 1) :
    ∃ q : ℕ, s = q := by
  classical
  let B : Fin n → Fin 3 → ℝ := fun i j => A i j*u j
  have hgram (j k : Fin 3) (hjk : j ≠ k) : (∑ i, B i j*B i k) = 0 := by
    calc
      _ = (∑ i, A i j*A i k)*u j*u k := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [B]
        ring
      _ = 0 := by rw [hA.2 j k, if_neg hjk]; ring
  have hrprod (j k : Fin 3) (hjk : j ≠ k) : B r j*B r k ≤ 0 := by
    have hnonneg : 0 ≤ ∑ i ∈ Finset.univ.erase r, B i j*B i k := by
      apply Finset.sum_nonneg
      intro i hi
      exact hprod i (Finset.mem_erase.mp hi).1 j k
    have he := Finset.sum_erase_add Finset.univ (fun i => B i j*B i k) (Finset.mem_univ r)
    rw [hgram j k hjk] at he
    dsimp at he
    linarith
  obtain ⟨j,hj⟩ := three_nonpositive_products_zero (B r) hrprod
  have haj : A r j = 0 := (mul_eq_zero.mp hj).resolve_right (hu j)
  have hzero (i : Fin n) (k : Fin 3) (hkj : k ≠ j) : B i j*B i k = 0 := by
    have hnonneg (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) : 0 ≤ B i j*B i k := by
      by_cases hir : i = r
      · rw [hir,hj,zero_mul]
      · exact hprod i hir j k
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (hgram j k (Ne.symm hkj)) i (Finset.mem_univ i)
  have hpure (i : Fin n) (hi : A i j ≠ 0) (k : Fin 3) (hkj : k ≠ j) : A i k = 0 := by
    have hbij : B i j ≠ 0 := mul_ne_zero hi (hu j)
    have hbk : B i k = 0 := (mul_eq_zero.mp (hzero i k hkj)).resolve_left hbij
    exact (mul_eq_zero.mp hbk).resolve_right (hu k)
  have hsq (i : Fin n) : (A i j)^2 = if A i j = 0 then 0 else 1 := by
    by_cases hi : A i j = 0
    · simp [hi]
    · have hir : i ≠ r := by intro he; apply hi; simpa [he] using haj
      have hsum : Dominance.l1 (A i) = |A i j| := by
        unfold Dominance.l1
        apply Finset.sum_eq_single j
        · intro k _ hkj
          rw [hpure i hi k hkj,abs_zero]
        · simp
      have habs : |A i j| = 1 := hsum.symm.trans (hsat i hir)
      simp only [hi,if_false]
      nlinarith [sq_abs (A i j)]
  refine ⟨(Finset.univ.filter (fun i => A i j ≠ 0)).card,?_⟩
  have hg : (∑ i, (A i j)^2) = s := by simpa [pow_two] using hA.2 j j
  rw [← hg]
  simp_rw [hsq]
  simp [Finset.sum_ite]

/-- Rank-one exclusion in residue two, for an actual signed outer-product
multiplier matrix. -/
theorem signed_rank_one_excluded_residue_two {m : ℕ} {d τ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5 < d) (hdhi : d ≤ 4/9)
    (hτ : 0 < τ) (u : Fin 3 → ℝ)
    (hu : ∀ j, u j = 0 ∨ u j = 1 ∨ u j = -1) (hun : ∃ j, u j ≠ 0)
    (hform : ∀ j k, M.matrix j k = τ * u j * u k) : False := by
  obtain ⟨hq,hdexact,hR⟩ := signed_rank_one_residue_two_quantized hA M hd hdhi hτ u hu hun hform
  have hcount : activeCount M + 1 = 3*m+2 := by omega
  obtain ⟨r,_,hr⟩ := activeCount_pred_unique_zero M hcount
  have hufull := signed_support_three hq
  obtain ⟨q,hq⟩ := single_exception_products_integer hA r u hufull
    (fun i hir j k => multiplier_outer_positive_products M hτ hform i (hr i hir) j k)
    (by intro i hir; simpa only [Dominance.l1,Fin.sum_univ_three] using M.complementary i (hr i hir))
  rw [hdexact] at hq
  have hqlo : (m : ℝ) < q := by linarith
  have hqhi : (q : ℝ) < (m+1 : ℕ) := by push_cast; linarith
  have hnlo : m < q := by exact_mod_cast hqlo
  have hnhi : q < m+1 := by exact_mod_cast hqhi
  omega

/-- Actual multiplier entry bounds turn vanishing two-by-two minors into a
signed outer-product representation. -/
theorem multiplier_minors_zero_signed_form {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (hs : 0 < s)
    (M : MultiplierSystem A)
    (hminor : ∀ j k a b, M.matrix j a*M.matrix k b=M.matrix j b*M.matrix k a) :
    ∃ (τ : ℝ) (u : Fin 3 → ℝ), 0 < τ ∧
      (∀ j, u j=0 ∨ u j=1 ∨ u j= -1) ∧ (∃ j, u j≠0) ∧
      (∀ j k, M.matrix j k=τ*u j*u k) := by
  have hp : ∃ p, 0 < M.matrix p p := by
    by_contra hn
    push_neg at hn
    have ht := multiplier_trace_identity hA M
    have hsum : M.matrix 0 0+M.matrix 1 1+M.matrix 2 2 ≤ 0 := by linarith [hn 0,hn 1,hn 2]
    have hm := mul_nonpos_of_nonneg_of_nonpos hs.le hsum
    linarith
  obtain ⟨p,hp⟩ := hp
  let τ : ℝ := M.matrix p p
  let u : Fin 3 → ℝ := fun j => M.matrix j p/τ
  have hτ : 0 < τ := hp
  have hτn : τ ≠ 0 := ne_of_gt hτ
  have hdiag (j : Fin 3) : M.matrix j j*τ=(M.matrix j p)^2 := by
    have h := hminor j p j p
    rw [M.symmetric p j] at h
    exact h.trans (by ring)
  have hb (j : Fin 3) (hj : M.matrix j p ≠ 0) : |M.matrix j p|=τ := by
    have h1 := multiplier_entry_bound hA hs M j p
    have h2 : |M.matrix j p| ≤ τ := by
      rw [M.symmetric j p]
      exact multiplier_entry_bound hA hs M p j
    have hbpos := abs_pos.mpr hj
    have hm := mul_le_mul_of_nonneg_right h1 hτ.le
    rw [hdiag j] at hm
    have hlo : τ ≤ |M.matrix j p| := by nlinarith [sq_abs (M.matrix j p)]
    exact le_antisymm h2 hlo
  have hu (j : Fin 3) : u j=0 ∨ u j=1 ∨ u j= -1 := by
    by_cases hj : M.matrix j p=0
    · left; simp [u,hj]
    · have he := hb j hj
      by_cases hpos : 0 ≤ M.matrix j p
      · right; left
        rw [abs_of_nonneg hpos] at he
        simp [u,he,hτn]
      · right; right
        rw [abs_of_neg (lt_of_not_ge hpos)] at he
        have he' : M.matrix j p= -τ := by linarith
        simp [u,he',hτn]
  refine ⟨τ,u,hτ,hu,⟨p,?_⟩,?_⟩
  · have huone : u p=1 := by simp [u,τ,ne_of_gt hp]
    rw [huone]; norm_num
  · intro j k
    have h := hminor j p k p
    rw [M.symmetric p k] at h
    dsimp [u]
    field_simp
    exact h

end
end F3
