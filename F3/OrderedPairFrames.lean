import F3.PairGraph
import F3.FullRowBookkeeping

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

structure OrderedPairFrame {ι : Type*} (A : ι → Fin 3 → ℝ) : Prop where
  saturated : ∀ i, |A i 0|+|A i 1|+|A i 2|=1
  large : ∀ i, ∃ j, (1:ℝ)/2< |A i j|
  not_full : ∀ i, ∃ j, A i j=0
  ordered : ∀ i j k, j<k → A i j≠0 → A i k≠0 → |A i k|< |A i j|

theorem two_support_sum {a : Fin 3 → ℝ} {j k : Fin 3}
    (hjk : j≠k) (hz : ∀ l,l≠j → l≠k → a l=0) :
    (∑ l, |a l|)=|a j|+|a k| := by
  classical
  calc
    _ = ∑ l ∈ ({j,k}:Finset (Fin 3)),|a l| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro l _ hl
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hl
      simp [hz l hl.1 hl.2]
    _ = _ := by simp [hjk]

theorem third_zero_of_not_full {a : Fin 3 → ℝ} {j k : Fin 3}
    (hjk : j≠k) (hj : a j≠0) (hk : a k≠0) (hn : ∃ l,a l=0) :
    ∀ l,l≠j → l≠k → a l=0 := by
  obtain ⟨t,ht⟩ := hn
  have htj : t≠j := by intro h; subst t; exact hj ht
  have htk : t≠k := by intro h; subst t; exact hk ht
  intro l hlj hlk
  have hlt : l=t := by
    fin_cases j <;> fin_cases k <;> fin_cases t <;> fin_cases l <;>
      simp_all
  simpa only [hlt] using ht

theorem unequal_pair_of_large {a : Fin 3 → ℝ} (ha : RowBound a)
    (hlarge : ∃ l,(1:ℝ)/2< |a l|) {j k : Fin 3} (hjk : j≠k)
    (hz : ∀l,l≠j → l≠k → a l=0) : |a j|≠|a k| := by
  intro he
  have hsum := two_support_sum hjk hz
  rw [Fin.sum_univ_three] at hsum
  have hle : |a j|+|a k|≤1 := by unfold RowBound at ha; linarith
  obtain ⟨l,hl⟩ := hlarge
  by_cases hlj : l=j
  · subst l; linarith
  by_cases hlk : l=k
  · subst l; linarith
  rw [hz l hlj hlk,abs_zero] at hl
  norm_num at hl

theorem exists_ordered_pair_frame {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (hw : ∀ i,0<M.weight i)
    (hl : ∀ i,∃j,(1:ℝ)/2< |A i j|) (hn : ∀i,∃j,A i j=0) :
    ∃ e : Equiv.Perm (Fin 3), OrderedPairFrame (permuteColumns A e) := by
  obtain ⟨e,he01,he12⟩ := exists_sorted_columns (fun j => M.matrix j j)
  let B := permuteColumns A e
  let N := M.permuteColumns e
  have hB : Feasible s B := feasible_permuteColumns hA e
  have hNl : ∀i,0<N.weight i := hw
  have hBl (i : ι) : ∃j,(1:ℝ)/2< |B i j| := by
    obtain ⟨j,hj⟩ := hl i
    exact ⟨e.symm j,by simpa [B,permuteColumns] using hj⟩
  have hBn (i : ι) : ∃j,B i j=0 := by
    obtain ⟨j,hj⟩ := hn i
    exact ⟨e.symm j,by simpa [B,permuteColumns] using hj⟩
  refine ⟨e,⟨fun i => N.complementary i (hNl i),hBl,hBn,?_⟩⟩
  intro i j k hjk hj hk
  have hjkne : j≠k := ne_of_lt hjk
  have hz := third_zero_of_not_full hjkne hj hk (hBn i)
  have hneq := unequal_pair_of_large (hB.1 i) (hBl i) hjkne hz
  have horder : N.matrix j j≤N.matrix k k := by
    fin_cases j <;> fin_cases k <;> norm_num at hjk ⊢
    · exact he01
    · exact he01.trans he12
    · exact he12
  by_contra! hle
  have hlt : |B i j|< |B i k| := lt_of_le_of_ne hle hneq
  have hp := (actual_pair_orientation hB hs N hNl i hjkne.symm hk hj
    (fun l hlk hlj => hz l hlj hlk)).mp hlt
  exact (not_lt_of_ge horder) hp

def pairEdgeRows {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (j k : Fin 3) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => A i j≠0 ∧ A i k≠0)

def largeColumnRows {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (j : Fin 3) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (1:ℝ)/2< |A i j|)

def pairEdgeEnergy {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (j k : Fin 3) : ℝ := ∑ i ∈ pairEdgeRows A j k, (A i k)^2

def pairEdgeLoss {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (j k : Fin 3) : ℝ := ∑ i ∈ pairEdgeRows A j k, 2*|A i j| * |A i k|

def pairEdgeDeficit {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ)
    (j k : Fin 3) : ℝ := ∑ i ∈ pairEdgeRows A j k, (1-(A i j)^2)

theorem pairEdgeEnergy_nonneg {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (j k : Fin 3) : 0≤pairEdgeEnergy A j k :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem pairEdgeLoss_nonneg {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (j k : Fin 3) : 0≤pairEdgeLoss A j k :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _))

theorem ordered_pair_budget {ι : Type*} {A : ι → Fin 3 → ℝ}
    (ho : OrderedPairFrame A) (i : ι) {j k : Fin 3}
    (hjk : j<k) (hj : A i j≠0) (hk : A i k≠0) :
    |A i j|+|A i k|=1 ∧ (1:ℝ)/2< |A i j| ∧ |A i k|<1/2 := by
  have hsum := two_support_sum (ne_of_lt hjk)
    (third_zero_of_not_full (ne_of_lt hjk) hj hk (ho.not_full i))
  rw [Fin.sum_univ_three,ho.saturated] at hsum
  have hlt := ho.ordered i j k hjk hj hk
  exact ⟨hsum.symm,by linarith,by linarith⟩

theorem pairEdgeDeficit_eq {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A)
    {j k : Fin 3} (hjk : j<k) :
    pairEdgeDeficit A j k=pairEdgeLoss A j k+pairEdgeEnergy A j k := by
  classical
  rw [pairEdgeDeficit,pairEdgeLoss,pairEdgeEnergy,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hip := (Finset.mem_filter.mp hi).2
  have hsum := (ordered_pair_budget ho i hjk hip.1 hip.2).1
  nlinarith [sq_abs (A i j),sq_abs (A i k)]

end
end F3
