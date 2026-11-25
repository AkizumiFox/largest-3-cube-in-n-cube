import F3.OrderedPairBookkeeping
import F3.Transfer

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

def edgePositiveMinor {ι : Type*} (A : ι → Fin 3 → ℝ) (j k : Fin 3) (i : ι) : ℝ :=
  if 0<A i j*A i k then |A i k| else 0

def edgeNegativeMinor {ι : Type*} (A : ι → Fin 3 → ℝ) (j k : Fin 3) (i : ι) : ℝ :=
  if A i j*A i k<0 then |A i k| else 0

lemma pair_minor_product {ι : Type*} {A : ι → Fin 3 → ℝ}
    (ho : OrderedPairFrame A) (i : ι) {j k : Fin 3} (hjk : j<k)
    (hp : A i j*A i k≠0) :
    |A i k| * (1-|A i k|)=|A i j*A i k| := by
  have hb := (ordered_pair_budget ho i hjk (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)).1
  rw [show 1-|A i k|=|A i j| by linarith,mul_comm,abs_mul]

lemma edge_minor_bounds {ι : Type*} {A : ι → Fin 3 → ℝ}
    (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k) (i : ι) :
    (0≤edgePositiveMinor A j k i ∧ edgePositiveMinor A j k i≤1/2) ∧
    (0≤edgeNegativeMinor A j k i ∧ edgeNegativeMinor A j k i≤1/2) := by
  constructor
  · unfold edgePositiveMinor
    split_ifs with hp
    · exact ⟨abs_nonneg _,(ordered_pair_budget ho i hjk
        (left_ne_zero_of_mul (ne_of_gt hp)) (right_ne_zero_of_mul (ne_of_gt hp))).2.2.le⟩
    · norm_num
  · unfold edgeNegativeMinor
    split_ifs with hp
    · exact ⟨abs_nonneg _,(ordered_pair_budget ho i hjk
        (left_ne_zero_of_mul (ne_of_lt hp)) (right_ne_zero_of_mul (ne_of_lt hp))).2.2.le⟩
    · norm_num

lemma edge_minor_row_identities {ι : Type*} {A : ι → Fin 3 → ℝ}
    (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k) (i : ι) :
    (edgePositiveMinor A j k i*(1-edgePositiveMinor A j k i)-
      edgeNegativeMinor A j k i*(1-edgeNegativeMinor A j k i)=A i j*A i k) ∧
    (edgePositiveMinor A j k i^2+edgeNegativeMinor A j k i^2=
      if A i j≠0 ∧ A i k≠0 then A i k^2 else 0) ∧
    (edgePositiveMinor A j k i*(1-edgePositiveMinor A j k i)+
      edgeNegativeMinor A j k i*(1-edgeNegativeMinor A j k i)=
      if A i j≠0 ∧ A i k≠0 then |A i j| * |A i k| else 0) := by
  rcases lt_trichotomy (A i j*A i k) 0 with hn | hz | hp
  · have hj := left_ne_zero_of_mul (ne_of_lt hn)
    have hk := right_ne_zero_of_mul (ne_of_lt hn)
    have ht := pair_minor_product ho i hjk (ne_of_lt hn)
    rw [abs_of_neg hn] at ht
    simp only [edgePositiveMinor,edgeNegativeMinor,not_lt_of_ge hn.le,if_false,hn,if_true,
      hj,hk,not_false_eq_true,and_self,zero_mul,zero_pow,zero_add,sq_abs,zero_sub]
    refine ⟨by linarith, by simp [hj,hk], ?_⟩
    rw [if_pos ⟨hj,hk⟩,←abs_mul,abs_of_neg hn]
    exact ht
  · have he : ¬(A i j≠0 ∧ A i k≠0) := by
      rintro ⟨hj,hk⟩
      exact mul_ne_zero hj hk hz
    simp [edgePositiveMinor,edgeNegativeMinor,hz,he]
  · have hj := left_ne_zero_of_mul (ne_of_gt hp)
    have hk := right_ne_zero_of_mul (ne_of_gt hp)
    have ht := pair_minor_product ho i hjk (ne_of_gt hp)
    rw [abs_of_pos hp] at ht
    simp only [edgePositiveMinor,edgeNegativeMinor,not_lt_of_ge hp.le,if_false,hp,if_true,
      hj,hk,not_false_eq_true,and_self,zero_mul,zero_pow,add_zero,sq_abs,sub_zero]
    refine ⟨ht,by simp [hj,hk],?_⟩
    rw [if_pos ⟨hj,hk⟩,←abs_mul,abs_of_pos hp]
    exact ht

lemma actual_edge_sign_cancellation {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (ho : OrderedPairFrame A)
    {j k : Fin 3} (hjk : j<k) :
    Transfer.productMass (edgePositiveMinor A j k)=Transfer.productMass (edgeNegativeMinor A j k) := by
  have ht : Transfer.productMass (edgePositiveMinor A j k)-
      Transfer.productMass (edgeNegativeMinor A j k)=(∑i,A i j*A i k) := by
    unfold Transfer.productMass
    rw [←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => (edge_minor_row_identities ho hjk i).1)
  have hz : (∑i,A i j*A i k)=0 := by simpa [ne_of_lt hjk] using hA.2 j k
  linarith

lemma actual_edge_energy {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k) :
    Transfer.energy (edgePositiveMinor A j k)+Transfer.energy (edgeNegativeMinor A j k)=
      pairEdgeEnergy A j k := by
  classical
  unfold Transfer.energy pairEdgeEnergy pairEdgeRows
  rw [←Finset.sum_add_distrib,Finset.sum_filter]
  exact Finset.sum_congr rfl (fun i _ => (edge_minor_row_identities ho hjk i).2.1)

lemma actual_edge_loss {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k) :
    2*(Transfer.productMass (edgePositiveMinor A j k)+Transfer.productMass (edgeNegativeMinor A j k))=
      pairEdgeLoss A j k := by
  classical
  unfold Transfer.productMass pairEdgeLoss pairEdgeRows
  rw [←Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [(edge_minor_row_identities ho hjk i).2.2]
  split_ifs <;> ring

/-- Stable edge transfer for the actual rows of a finite feasible frame. -/
theorem actual_edge_transfer {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (ho : OrderedPairFrame A)
    {j k : Fin 3} (hjk : j<k) :
    2*pairEdgeEnergy A j k≤pairEdgeLoss A j k ∧
    Transfer.phi (pairEdgeEnergy A j k)≤pairEdgeLoss A j k ∧
    3*pairEdgeEnergy A j k≤pairEdgeDeficit A j k := by
  have ht := Transfer.edge_loss (edgePositiveMinor A j k) (edgeNegativeMinor A j k)
    (fun i => (edge_minor_bounds ho hjk i).1) (fun i => (edge_minor_bounds ho hjk i).2)
    (actual_edge_sign_cancellation hA ho hjk)
  dsimp at ht
  rw [actual_edge_energy ho hjk,actual_edge_loss ho hjk] at ht
  rw [pairEdgeDeficit_eq ho hjk]
  exact ht

end
end F3
