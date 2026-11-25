import F3.OrderedPairFrames
import F3.ColumnBounds
import F3.Dominance

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

@[simp] theorem mem_pairEdgeRows {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (i : ι) (j k : Fin 3) :
    i∈pairEdgeRows A j k ↔ A i j≠0 ∧ A i k≠0 := by
  classical
  simp [pairEdgeRows]

@[simp] theorem mem_largeColumnRows {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (i : ι) (j : Fin 3) :
    i∈largeColumnRows A j ↔ (1:ℝ)/2< |A i j| := by
  classical
  simp [largeColumnRows]

lemma OrderedPairFrame.support_cases {ι : Type*} {A : ι → Fin 3 → ℝ}
    (ho : OrderedPairFrame A) (i : ι) :
    (A i 0≠0 ∧ A i 1=0 ∧ A i 2=0) ∨
    (A i 0=0 ∧ A i 1≠0 ∧ A i 2=0) ∨
    (A i 0=0 ∧ A i 1=0 ∧ A i 2≠0) ∨
    (A i 0≠0 ∧ A i 1≠0 ∧ A i 2=0) ∨
    (A i 0≠0 ∧ A i 1=0 ∧ A i 2≠0) ∨
    (A i 0=0 ∧ A i 1≠0 ∧ A i 2≠0) := by
  have hn : A i 0≠0 ∨ A i 1≠0 ∨ A i 2≠0 := by
    by_contra h
    push_neg at h
    have hs := ho.saturated i
    simp [h.1,h.2.1,h.2.2] at hs
  have hz : A i 0=0 ∨ A i 1=0 ∨ A i 2=0 := by
    obtain ⟨j,hj⟩ := ho.not_full i
    fin_cases j <;> tauto
  tauto

lemma OrderedPairFrame.row_flow {ι : Type*} {A : ι → Fin 3 → ℝ}
    (ho : OrderedPairFrame A) (i : ι) :
    ((if (1:ℝ)/2< |A i 0| then 1 else 0)-A i 0^2=
      (if A i 0≠0 ∧ A i 1≠0 then 1-A i 0^2 else 0)+
      (if A i 0≠0 ∧ A i 2≠0 then 1-A i 0^2 else 0)) ∧
    (A i 1^2-(if (1:ℝ)/2< |A i 1| then 1 else 0)=
      (if A i 0≠0 ∧ A i 1≠0 then A i 1^2 else 0)-
      (if A i 1≠0 ∧ A i 2≠0 then 1-A i 1^2 else 0)) ∧
    (A i 2^2-(if (1:ℝ)/2< |A i 2| then 1 else 0)=
      (if A i 0≠0 ∧ A i 2≠0 then A i 2^2 else 0)+
      (if A i 1≠0 ∧ A i 2≠0 then A i 2^2 else 0)) := by
  classical
  rcases ho.support_cases i with h | h | h | h | h | h
  · have hab : |A i 0|=1 := by simpa [h.2.1,h.2.2] using ho.saturated i
    have hs : A i 0^2=1 := by nlinarith [sq_abs (A i 0)]
    norm_num [h.1,h.2.1,h.2.2,hab,hs]
  · have hab : |A i 1|=1 := by simpa [h.1,h.2.2] using ho.saturated i
    have hs : A i 1^2=1 := by nlinarith [sq_abs (A i 1)]
    norm_num [h.1,h.2.1,h.2.2,hab,hs]
  · have hab : |A i 2|=1 := by simpa [h.1,h.2.1] using ho.saturated i
    have hs : A i 2^2=1 := by nlinarith [sq_abs (A i 2)]
    norm_num [h.1,h.2.1,h.2.2,hab,hs]
  · have hb := ordered_pair_budget ho i (j:=0) (k:=1) (by decide) h.1 h.2.1
    norm_num [h.1,h.2.1,h.2.2,hb.2.1,not_lt.mpr hb.2.2.le]
  · have hb := ordered_pair_budget ho i (j:=0) (k:=2) (by decide) h.1 h.2.2
    norm_num [h.1,h.2.1,h.2.2,hb.2.1,not_lt.mpr hb.2.2.le]
  · have hb := ordered_pair_budget ho i (j:=1) (k:=2) (by decide) h.2.1 h.2.2
    norm_num [h.1,h.2.1,h.2.2,hb.2.1,not_lt.mpr hb.2.2.le]

theorem ordered_pair_energy_balances_of_diagonal {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) (s : Fin 3 → ℝ)
    (hg : ∀j,(∑i,A i j^2)=s j) :
    ((largeColumnRows A 0).card:ℝ)-s 0=pairEdgeDeficit A 0 1+pairEdgeDeficit A 0 2 ∧
    s 1-((largeColumnRows A 1).card:ℝ)=pairEdgeEnergy A 0 1-pairEdgeDeficit A 1 2 ∧
    s 2-((largeColumnRows A 2).card:ℝ)=pairEdgeEnergy A 0 2+pairEdgeEnergy A 1 2 := by
  classical
  have hc (j : Fin 3) : ((largeColumnRows A j).card:ℝ)=
      ∑i,if (1:ℝ)/2< |A i j| then (1:ℝ) else 0 := by
    exact Finset.natCast_card_filter _ _
  have h1 := congrArg (fun f : ι → ℝ => ∑i,f i) (funext (fun i => (ho.row_flow i).1))
  have h2 := congrArg (fun f : ι → ℝ => ∑i,f i) (funext (fun i => (ho.row_flow i).2.1))
  have h3 := congrArg (fun f : ι → ℝ => ∑i,f i) (funext (fun i => (ho.row_flow i).2.2))
  dsimp at h1 h2 h3
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←hc,hg] at h1 h2 h3
  constructor
  · simpa only [pairEdgeDeficit,pairEdgeRows,Finset.sum_filter] using h1
  constructor
  · simpa only [pairEdgeDeficit,pairEdgeEnergy,pairEdgeRows,Finset.sum_filter] using h2
  · simpa only [pairEdgeEnergy,pairEdgeRows,Finset.sum_filter] using h3

theorem ordered_pair_energy_balances {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (ho : OrderedPairFrame A) :
    ((largeColumnRows A 0).card:ℝ)-s=pairEdgeDeficit A 0 1+pairEdgeDeficit A 0 2 ∧
    s-((largeColumnRows A 1).card:ℝ)=pairEdgeEnergy A 0 1-pairEdgeDeficit A 1 2 ∧
    s-((largeColumnRows A 2).card:ℝ)=pairEdgeEnergy A 0 2+pairEdgeEnergy A 1 2 := by
  exact ordered_pair_energy_balances_of_diagonal ho (fun _ => s)
    (fun j => by simpa [pow_two] using hA.2 j j)

lemma OrderedPairFrame.large_unique {ι : Type*} {A : ι → Fin 3 → ℝ}
    (ho : OrderedPairFrame A) (i : ι) {j k : Fin 3}
    (hj : (1:ℝ)/2< |A i j|) (hk : (1:ℝ)/2< |A i k|) : j=k := by
  by_contra hne
  have hnj : A i j≠0 := by
    intro hz
    rw [hz,abs_zero] at hj
    norm_num at hj
  have hnk : A i k≠0 := by
    intro hz
    rw [hz,abs_zero] at hk
    norm_num at hk
  have ht := two_support_sum hne (third_zero_of_not_full hne hnj hnk (ho.not_full i))
  rw [Fin.sum_univ_three,ho.saturated] at ht
  linarith

lemma ordered_large_count_sum {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) :
    (largeColumnRows A 0).card+(largeColumnRows A 1).card+(largeColumnRows A 2).card=Fintype.card ι := by
  classical
  have hrow (i : ι) : (if (1:ℝ)/2< |A i 0| then 1 else 0)+
      (if (1:ℝ)/2< |A i 1| then 1 else 0)+(if (1:ℝ)/2< |A i 2| then 1 else 0)=(1:ℕ) := by
    obtain ⟨j,hj⟩ := ho.large i
    have hn (k : Fin 3) (hk : k≠j) : ¬(1:ℝ)/2< |A i k| := by
      intro h
      exact hk (ho.large_unique i h hj)
    have he : (∑k : Fin 3,if (1:ℝ)/2< |A i k| then (1:ℕ) else 0)=1 := by
      calc
        _ = (if (1:ℝ)/2< |A i j| then (1:ℕ) else 0) := by
          apply Finset.sum_eq_single j
          · intro k _ hk
            rw [if_neg (hn k hk)]
          · simp
        _ = 1 := if_pos hj
    simpa only [Fin.sum_univ_three] using he
  simp only [largeColumnRows,Finset.card_filter]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  calc
    _ = ∑_i : ι,(1:ℕ) := Finset.sum_congr rfl (fun i _ => hrow i)
    _ = _ := by simp

lemma pairEdgeRows_subset_large {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k) :
    pairEdgeRows A j k⊆largeColumnRows A j := by
  intro i hi
  have hp := (mem_pairEdgeRows A i j k).mp hi
  exact (mem_largeColumnRows A i j).mpr (ordered_pair_budget ho i hjk hp.1 hp.2).2.1

lemma edge01_edge02_disjoint {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) :
    Disjoint (pairEdgeRows A 0 1) (pairEdgeRows A 0 2) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i h01 h02
  obtain ⟨h0,h1⟩ := (mem_pairEdgeRows A i 0 1).mp h01
  have h2 := ((mem_pairEdgeRows A i 0 2).mp h02).2
  obtain ⟨j,hj⟩ := ho.not_full i
  fin_cases j <;> contradiction

lemma source_edge_count_le {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) :
    (pairEdgeRows A 0 1).card+(pairEdgeRows A 0 2).card≤(largeColumnRows A 0).card := by
  classical
  rw [←Finset.card_union_of_disjoint (edge01_edge02_disjoint ho)]
  apply Finset.card_le_card
  exact Finset.union_subset (pairEdgeRows_subset_large ho (by decide))
    (pairEdgeRows_subset_large ho (by decide))

end
end F3
