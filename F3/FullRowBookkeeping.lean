import F3.FullRowClassification
import F3.ColumnPermutations

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

lemma rowSupport_card_permute {ι : Type*} (A : ι → Fin 3 → ℝ)
    (e : Equiv.Perm (Fin 3)) (i : ι) :
    (rowSupport (permuteColumns A e) i).card=(rowSupport A i).card := by
  classical
  apply Finset.card_bij (fun j _ => e j)
  · intro j hj
    simpa using hj
  · intro j hj k hk h
    exact e.injective h
  · intro j hj
    refine ⟨e.symm j,?_,by simp⟩
    simpa using hj

@[simp] lemma pureRows_permute {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (e : Equiv.Perm (Fin 3)) : pureRows (permuteColumns A e)=pureRows A := by
  ext i
  simp [rowSupport_card_permute]
@[simp] lemma pairRows_permute {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (e : Equiv.Perm (Fin 3)) : pairRows (permuteColumns A e)=pairRows A := by
  ext i
  simp [rowSupport_card_permute]
@[simp] lemma fullRows_permute {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (e : Equiv.Perm (Fin 3)) : fullRows (permuteColumns A e)=fullRows A := by
  ext i
  simp [rowSupport_card_permute]

lemma rowSupport_sign {ι : Type*} (A : ι → Fin 3 → ℝ)
    (σ : Fin 3 → ℝ) (hσ : ∀j,σ j*σ j=1) (i : ι) :
    rowSupport (signColumns A σ) i=rowSupport A i := by
  have hn (j : Fin 3) : σ j≠0 := by
    intro h
    have ht := hσ j
    rw [h,zero_mul] at ht
    norm_num at ht
  ext j
  simp [signColumns,hn]

@[simp] lemma pureRows_sign {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (σ : Fin 3 → ℝ) (hσ : ∀j,σ j*σ j=1) : pureRows (signColumns A σ)=pureRows A := by
  ext i
  simp [rowSupport_sign A σ hσ]
@[simp] lemma pairRows_sign {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (σ : Fin 3 → ℝ) (hσ : ∀j,σ j*σ j=1) : pairRows (signColumns A σ)=pairRows A := by
  ext i
  simp [rowSupport_sign A σ hσ]
@[simp] lemma fullRows_sign {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (σ : Fin 3 → ℝ) (hσ : ∀j,σ j*σ j=1) : fullRows (signColumns A σ)=fullRows A := by
  ext i
  simp [rowSupport_sign A σ hσ]

lemma saturated_permute {ι : Type*} (A : ι → Fin 3 → ℝ)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) (e : Equiv.Perm (Fin 3)) :
    ∀i,|permuteColumns A e i 0|+|permuteColumns A e i 1|+|permuteColumns A e i 2|=1 := by
  intro i
  have he := Equiv.sum_comp e (fun j => |A i j|)
  simpa [Fin.sum_univ_three,permuteColumns,hs i] using he

lemma saturated_sign {ι : Type*} (A : ι → Fin 3 → ℝ)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1)
    (σ : Fin 3 → ℝ) (hσ : ∀j,σ j*σ j=1) :
    ∀i,|signColumns A σ i 0|+|signColumns A σ i 1|+|signColumns A σ i 2|=1 := by
  intro i
  simpa [signColumns,abs_mul,abs_eq_one_of_sign_sq (hσ 0),
    abs_eq_one_of_sign_sq (hσ 1),abs_eq_one_of_sign_sq (hσ 2)] using hs i

def pureColumnRows {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) (j : Fin 3) : Finset ι := by
  classical
  exact (pureRows A).filter (fun i => A i j≠0)

lemma pure_entry_sq {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) (i : ι) (hi : i∈pureRows A) (j : Fin 3) :
    A i j^2=if A i j≠0 then 1 else 0 := by
  classical
  by_cases hj : A i j=0
  · simp [hj]
  obtain ⟨k,hk⟩ := Finset.card_eq_one.mp ((mem_pureRows A i).mp hi)
  have hjk : j=k := by
    have hm : j∈rowSupport A i := (mem_rowSupport A i j).mpr hj
    simpa [hk] using hm
  subst k
  have hz (l : Fin 3) (hl : l≠j) : A i l=0 := by
    by_contra hn
    have hm : l∈rowSupport A i := (mem_rowSupport A i l).mpr hn
    have he : l=j := by simpa [hk] using hm
    exact hl he
  have hsum : (∑l : Fin 3,|A i l|)=|A i j| := by
    apply Finset.sum_eq_single j
    · intro l _ hl
      simp [hz l hl]
    · simp
  have hab : |A i j|=1 := by
    rw [Fin.sum_univ_three,hs i] at hsum
    exact hsum.symm
  rw [if_pos hj]
  nlinarith [sq_abs (A i j)]

lemma pure_column_energy {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) (j : Fin 3) :
    (∑i∈pureRows A,A i j^2)=((pureColumnRows A j).card:ℝ) := by
  classical
  calc
    _ = ∑i∈pureRows A,if A i j≠0 then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pure_entry_sq A hs i hi j
    _ = _ := by rw [←Finset.sum_filter]; simp [pureColumnRows]

lemma pure_column_count {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) :
    (pureColumnRows A 0).card+(pureColumnRows A 1).card+(pureColumnRows A 2).card=
      (pureRows A).card := by
  classical
  have hrow (i : ι) (hi : i∈pureRows A) :
      (if A i 0≠0 then 1 else 0)+(if A i 1≠0 then 1 else 0)+(if A i 2≠0 then 1 else 0)=(1:ℕ) := by
    have hc := (mem_pureRows A i).mp hi
    simpa [rowSupport,Finset.card_filter,Fin.sum_univ_three] using hc
  simp only [pureColumnRows,Finset.card_filter]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  simp only [Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl hrow

lemma column_energy_partition {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) (j : Fin 3) :
    (∑i,A i j^2)=(∑i∈pureRows A,A i j^2)+(∑i∈pairRows A,A i j^2)+
      (∑i∈fullRows A,A i j^2) := by
  classical
  simp only [pureRows,pairRows,fullRows,Finset.sum_filter]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases saturated_support_cases A i (hs i) with h | h | h <;> simp [h]

end
end F3
