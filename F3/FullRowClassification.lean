import F3.NormalFormConclusions
import F3.SignChanges

/-! Natural support conventions and finite-support classification.
The support cardinality bound is an explicit upstream hypothesis. -/
namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

def rowSupport {ι : Type*} (A : ι → Fin 3 → ℝ) (i : ι) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun j => A i j ≠ 0)

def pureRows {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (rowSupport A i).card=1)

def pairRows {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (rowSupport A i).card=2)

def fullRows {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (rowSupport A i).card=3)

@[simp] theorem mem_rowSupport {ι : Type*} (A : ι → Fin 3 → ℝ) (i : ι) (j : Fin 3) :
    j ∈ rowSupport A i ↔ A i j ≠ 0 := by
  classical
  simp [rowSupport]

@[simp] theorem mem_pureRows {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) (i : ι) :
    i∈pureRows A ↔ (rowSupport A i).card=1 := by
  classical
  simp [pureRows]

@[simp] theorem mem_pairRows {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) (i : ι) :
    i∈pairRows A ↔ (rowSupport A i).card=2 := by
  classical
  simp [pairRows]

@[simp] theorem mem_fullRows {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) (i : ι) :
    i∈fullRows A ↔ (rowSupport A i).card=3 := by
  classical
  simp [fullRows]

lemma rowSupport_card_cases {ι : Type*} (A : ι → Fin 3 → ℝ) (i : ι) :
    ((rowSupport A i).card=3 ↔ A i 0≠0 ∧ A i 1≠0 ∧ A i 2≠0) ∧
    ((rowSupport A i).card=2 ↔
      (A i 0≠0 ∧ A i 1≠0 ∧ A i 2=0) ∨
      (A i 0≠0 ∧ A i 1=0 ∧ A i 2≠0) ∨
      (A i 0=0 ∧ A i 1≠0 ∧ A i 2≠0)) := by
  classical
  have hu : (Finset.univ : Finset (Fin 3))={0,1,2} := by decide
  by_cases h0 : A i 0=0 <;> by_cases h1 : A i 1=0 <;> by_cases h2 : A i 2=0 <;>
    simp [rowSupport,hu,Finset.filter_insert,Finset.filter_singleton,h0,h1,h2]

lemma full_row_iff {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) (i : ι) :
    i∈fullRows A ↔ ∀ j, A i j≠0 := by
  rw [mem_fullRows,(rowSupport_card_cases A i).1]
  constructor
  · intro h j
    fin_cases j <;> tauto
  · intro h
    exact ⟨h 0,h 1,h 2⟩


lemma orthogonal_pair_has_other {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (i₀ : ι) {j k : Fin 3} (hjk : j≠k) (hprod : A i₀ j*A i₀ k≠0) :
    ∃ i, i≠i₀ ∧ A i j*A i k≠0 := by
  classical
  by_contra hn
  have hz (i : ι) (hi : i≠i₀) : A i j*A i k=0 := by
    by_contra h
    exact hn ⟨i,hi,h⟩
  have hsum : (∑ i, A i j*A i k)=A i₀ j*A i₀ k := by
    apply Finset.sum_eq_single i₀
    · intro i _ hi
      exact hz i hi
    · simp
  have ho : (∑ i, A i j*A i k)=0 := by simpa [hjk] using hA.2 j k
  exact hprod (hsum.symm.trans ho)

/-- Three distinct pair rows are necessary to cancel one full row. -/
theorem one_full_has_three_pair_rows {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hF : (fullRows A).card=1) : 3≤(pairRows A).card := by
  classical
  obtain ⟨i₀,hi₀⟩ := Finset.card_pos.mp (show 0<(fullRows A).card by omega)
  have hfull := (full_row_iff A i₀).mp hi₀
  have huniq (i : ι) (hi : i∈fullRows A) : i=i₀ :=
    Finset.card_le_one.mp (by omega) i hi i₀ hi₀
  obtain ⟨i₁,hne₁,hp₁⟩ := orthogonal_pair_has_other hA i₀
    (j:=0) (k:=1) (by decide) (mul_ne_zero (hfull 0) (hfull 1))
  obtain ⟨i₂,hne₂,hp₂⟩ := orthogonal_pair_has_other hA i₀
    (j:=0) (k:=2) (by decide) (mul_ne_zero (hfull 0) (hfull 2))
  obtain ⟨i₃,hne₃,hp₃⟩ := orthogonal_pair_has_other hA i₀
    (j:=1) (k:=2) (by decide) (mul_ne_zero (hfull 1) (hfull 2))
  have h₁0 : A i₁ 0≠0 := left_ne_zero_of_mul hp₁
  have h₁1 : A i₁ 1≠0 := right_ne_zero_of_mul hp₁
  have h₂0 : A i₂ 0≠0 := left_ne_zero_of_mul hp₂
  have h₂2 : A i₂ 2≠0 := right_ne_zero_of_mul hp₂
  have h₃1 : A i₃ 1≠0 := left_ne_zero_of_mul hp₃
  have h₃2 : A i₃ 2≠0 := right_ne_zero_of_mul hp₃
  have h₁2 : A i₁ 2=0 := by
    by_contra h
    apply hne₁
    apply huniq
    rw [mem_fullRows,(rowSupport_card_cases A i₁).1]
    exact ⟨h₁0,h₁1,h⟩
  have h₂1 : A i₂ 1=0 := by
    by_contra h
    apply hne₂
    apply huniq
    rw [mem_fullRows,(rowSupport_card_cases A i₂).1]
    exact ⟨h₂0,h,h₂2⟩
  have h₃0 : A i₃ 0=0 := by
    by_contra h
    apply hne₃
    apply huniq
    rw [mem_fullRows,(rowSupport_card_cases A i₃).1]
    exact ⟨h,h₃1,h₃2⟩
  have hm₁ : i₁∈pairRows A := by
    rw [mem_pairRows,(rowSupport_card_cases A i₁).2]
    exact Or.inl ⟨h₁0,h₁1,h₁2⟩
  have hm₂ : i₂∈pairRows A := by
    rw [mem_pairRows,(rowSupport_card_cases A i₂).2]
    exact Or.inr (Or.inl ⟨h₂0,h₂1,h₂2⟩)
  have hm₃ : i₃∈pairRows A := by
    rw [mem_pairRows,(rowSupport_card_cases A i₃).2]
    exact Or.inr (Or.inr ⟨h₃0,h₃1,h₃2⟩)
  have hn₁₂ : i₁≠i₂ := by intro h; subst i₂; exact h₁1 h₂1
  have hn₁₃ : i₁≠i₃ := by intro h; subst i₃; exact h₁0 h₃0
  have hn₂₃ : i₂≠i₃ := by intro h; subst i₃; exact h₂0 h₃0
  have hsub : ({i₁,i₂,i₃}:Finset ι)⊆pairRows A := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hm₁
    · exact hm₂
    · exact hm₃
  have hcount := Finset.card_le_card hsub
  simpa [hn₁₂,hn₁₃,hn₂₃] using hcount

lemma nonmixed_products_zero {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (i : ι)
    (hf : i∉fullRows A) (hp : i∉pairRows A) :
    A i 0*A i 1=0 ∧ A i 0*A i 2=0 ∧ A i 1*A i 2=0 := by
  classical
  rw [mem_fullRows,(rowSupport_card_cases A i).1] at hf
  rw [mem_pairRows,(rowSupport_card_cases A i).2] at hp
  by_cases h0 : A i 0=0 <;> by_cases h1 : A i 1=0 <;> by_cases h2 : A i 2=0 <;>
    simp_all


lemma rowSupport_card_le {ι : Type*} (A : ι → Fin 3 → ℝ) (i : ι) :
    (rowSupport A i).card≤3 := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = 3 := by simp

lemma pair_of_two_nonzero_of_not_full {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (i : ι) {j k : Fin 3}
    (hjk : j≠k) (hj : A i j≠0) (hk : A i k≠0) (hf : i∉fullRows A) :
    i∈pairRows A := by
  classical
  have hsub : ({j,k}:Finset (Fin 3))⊆rowSupport A i := by
    intro l hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simpa using hj
    · simpa using hk
  have hcard := Finset.card_le_card hsub
  simp [hjk] at hcard
  have hu := rowSupport_card_le A i
  rw [mem_fullRows] at hf
  rw [mem_pairRows]
  omega

lemma one_full_pair_witness {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hF : (fullRows A).card=1) (i₀ : ι) (hi₀ : i₀∈fullRows A)
    {j k : Fin 3} (hjk : j≠k) :
    ∃ i, i∈pairRows A ∧ i≠i₀ ∧ A i j≠0 ∧ A i k≠0 := by
  classical
  have hfull := (full_row_iff A i₀).mp hi₀
  obtain ⟨i,hne,hp⟩ := orthogonal_pair_has_other hA i₀ hjk
    (mul_ne_zero (hfull j) (hfull k))
  have hj := left_ne_zero_of_mul hp
  have hk := right_ne_zero_of_mul hp
  have hf : i∉fullRows A := by
    intro hi
    exact hne (Finset.card_le_one.mp (by omega) i hi i₀ hi₀)
  exact ⟨i,pair_of_two_nonzero_of_not_full A i hjk hj hk hf,hne,hj,hk⟩

/-- Two full rows cannot by themselves cancel all three off-diagonal entries. -/
theorem two_full_has_pair_row {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hF : (fullRows A).card=2) : 1≤(pairRows A).card := by
  classical
  by_contra hn
  have hQ : (pairRows A).card=0 := by omega
  have hempty : pairRows A=∅ := Finset.card_eq_zero.mp hQ
  obtain ⟨i₀,i₁,hne,hrows⟩ := Finset.card_eq_two.mp hF
  have hfull : ∀j,A i₀ j≠0 := (full_row_iff A i₀).mp (by simp [hrows])
  have hz (i : ι) (hi : i∉fullRows A) :
      A i 0*A i 1=0 ∧ A i 0*A i 2=0 ∧ A i 1*A i 2=0 :=
    nonmixed_products_zero A i hi (by simp [hempty])
  have hsum (f : ι → ℝ) (hf : ∀i,i∉fullRows A → f i=0) :
      (∑ i,f i)=f i₀+f i₁ := by
    calc
      _ = ∑ i ∈ fullRows A,f i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        exact hf i hi
      _ = _ := by simp [hrows,hne]
  have h01 := hsum (fun i => A i 0*A i 1) (fun i hi => (hz i hi).1)
  have h02 := hsum (fun i => A i 0*A i 2) (fun i hi => (hz i hi).2.1)
  have h12 := hsum (fun i => A i 1*A i 2) (fun i hi => (hz i hi).2.2)
  have he01 : (∑ i,A i 0*A i 1)=0 := by simpa using hA.2 0 1
  have he02 : (∑ i,A i 0*A i 2)=0 := by simpa using hA.2 0 2
  have he12 : (∑ i,A i 1*A i 2)=0 := by simpa using hA.2 1 2
  dsimp at h01 h02 h12
  exact two_full_rows_need_pair (d:=A i₁ 0) (e:=A i₁ 1) (f:=A i₁ 2)
    (hfull 0) (hfull 1) (hfull 2) (by linarith) (by linarith) (by linarith)

/-- The exact support counts at any feasible frame satisfying the proved
optimizer support bound and containing a full row. -/
theorem full_pair_count_classification {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hF : (fullRows A).Nonempty)
    (hbound : (pairRows A).card+2*(fullRows A).card≤5) :
    ((fullRows A).card=1 ∧ (pairRows A).card=3) ∨
    ((fullRows A).card=2 ∧ (pairRows A).card=1) := by
  have hpos := Finset.card_pos.mpr hF
  have hcases : (fullRows A).card=1 ∨ (fullRows A).card=2 := by omega
  rcases hcases with h1 | h2
  · have hQ := one_full_has_three_pair_rows hA h1
    exact Or.inl ⟨h1,by omega⟩
  · have hQ := two_full_has_pair_row hA h2
    exact Or.inr ⟨h2,by omega⟩


lemma saturated_support_nonempty {ι : Type*} (A : ι → Fin 3 → ℝ) (i : ι)
    (hs : |A i 0|+|A i 1|+|A i 2|=1) : (rowSupport A i).Nonempty := by
  classical
  by_contra hn
  have h0 : A i 0=0 := by
    by_contra h
    exact hn ⟨0,by simpa using h⟩
  have h1 : A i 1=0 := by
    by_contra h
    exact hn ⟨1,by simpa using h⟩
  have h2 : A i 2=0 := by
    by_contra h
    exact hn ⟨2,by simpa using h⟩
  simp [h0,h1,h2] at hs

lemma saturated_support_cases {ι : Type*} (A : ι → Fin 3 → ℝ) (i : ι)
    (hs : |A i 0|+|A i 1|+|A i 2|=1) :
    (rowSupport A i).card=1 ∨ (rowSupport A i).card=2 ∨ (rowSupport A i).card=3 := by
  have hl := Finset.card_pos.mpr (saturated_support_nonempty A i hs)
  have hu := rowSupport_card_le A i
  omega

theorem pure_pair_full_count {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) :
    (pureRows A).card+(pairRows A).card+(fullRows A).card=Fintype.card ι := by
  classical
  calc
    _ = ∑ i, ((if (rowSupport A i).card=1 then 1 else 0)+
        (if (rowSupport A i).card=2 then 1 else 0)+
        (if (rowSupport A i).card=3 then 1 else 0)) := by
      simp only [pureRows,pairRows,fullRows,Finset.card_eq_sum_ones,
        Finset.sum_filter,Finset.sum_add_distrib]
    _ = ∑ _i : ι, (1:ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases saturated_support_cases A i (hs i) with h | h | h <;> simp [h]
    _ = _ := by simp

theorem support_excess_count {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) :
    (∑ i, ((rowSupport A i).card-1))=(pairRows A).card+2*(fullRows A).card := by
  classical
  calc
    _ = ∑ i, ((if (rowSupport A i).card=2 then 1 else 0)+
        2*(if (rowSupport A i).card=3 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases saturated_support_cases A i (hs i) with h | h | h <;> simp [h]
    _ = _ := by
      simp only [pairRows,fullRows,Finset.card_eq_sum_ones,
        Finset.sum_filter,Finset.sum_add_distrib,Finset.mul_sum]

theorem zero_entry_count {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) :
    (∑ i, (3-(rowSupport A i).card))=2*(pureRows A).card+(pairRows A).card := by
  classical
  calc
    _ = ∑ i, (2*(if (rowSupport A i).card=1 then 1 else 0)+
        (if (rowSupport A i).card=2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases saturated_support_cases A i (hs i) with h | h | h <;> simp [h]
    _ = _ := by
      simp only [pureRows,pairRows,Finset.card_eq_sum_ones,
        Finset.sum_filter,Finset.sum_add_distrib,Finset.mul_sum]

theorem support_total_count {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) :
    (∑ i, (rowSupport A i).card)=
      (pureRows A).card+2*(pairRows A).card+3*(fullRows A).card := by
  classical
  calc
    _ = ∑ i, ((if (rowSupport A i).card=1 then 1 else 0)+
        2*(if (rowSupport A i).card=2 then 1 else 0)+
        3*(if (rowSupport A i).card=3 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases saturated_support_cases A i (hs i) with h | h | h <;> simp [h]
    _ = _ := by
      simp only [pureRows,pairRows,fullRows,Finset.card_eq_sum_ones,
        Finset.sum_filter,Finset.sum_add_distrib,Finset.mul_sum]

end
end F3
