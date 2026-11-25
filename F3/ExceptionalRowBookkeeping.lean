import F3.KernelEdgeBounds
import F3.TwoCoordinateKernel

namespace F3
noncomputable section
open scoped BigOperators

def deleteRow {n : ℕ} (A : Fin n → Fin 3 → ℝ) (r : Fin n) :
    {i : Fin n // i≠r} → Fin 3 → ℝ := fun i => A i.1

theorem sum_deleted_index {n : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin n → α) (r : Fin n) :
    (∑ i : {i : Fin n // i≠r}, f i.1)=∑ i∈Finset.univ.erase r,f i := by
  classical
  exact (Finset.sum_subtype (Finset.univ.erase r) (by simp) f).symm

theorem deleteRow_gram_diagonal {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (r : Fin n) (j : Fin 3) :
    (∑ i, (deleteRow A r i j)^2)=s-(A r j)^2 := by
  have he := Finset.sum_erase_add Finset.univ (fun i => (A i j)^2) (Finset.mem_univ r)
  dsimp only at he
  have hg : (∑ i,(A i j)^2)=s := by simpa [pow_two] using hA.2 j j
  rw [hg] at he
  change (∑ i : {i : Fin n // i≠r},(A i.1 j)^2)=_
  rw [sum_deleted_index (fun i => (A i j)^2) r]
  linarith

theorem deleteRow_signed_product {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (r : Fin n)
    {j k : Fin 3} (hjk : j≠k) :
    pairEdgeSignedProduct (deleteRow A r) j k= -(A r j*A r k) := by
  rw [pairEdgeSignedProduct_eq_sum]
  change (∑ i : {i : Fin n // i≠r},A i.1 j*A i.1 k)=_
  rw [sum_deleted_index (fun i => A i j*A i k) r]
  have he := Finset.sum_erase_add Finset.univ (fun i => A i j*A i k) (Finset.mem_univ r)
  dsimp only at he
  rw [hA.2,if_neg hjk] at he
  linarith

theorem deleteRow_large_count {n : ℕ} (A : Fin n → Fin 3 → ℝ)
    (r : Fin n) (j : Fin 3) (hr : |A r j|≤1/2) :
    (largeColumnRows (deleteRow A r) j).card=largeCount A j := by
  classical
  simp only [largeColumnRows,largeCount,Finset.card_filter,deleteRow]
  rw [sum_deleted_index (fun i => if (1 : ℝ)/2 < |A i j| then (1 : ℕ) else 0) r]
  have he := Finset.sum_erase_add Finset.univ
    (fun i => if (1 : ℝ)/2 < |A i j| then (1 : ℕ) else 0) (Finset.mem_univ r)
  dsimp only at he
  simpa only [if_neg (not_lt_of_ge hr),add_zero] using he

theorem deleteRow_card {m : ℕ} (r : Fin (3*m+2)) :
    Fintype.card {i : Fin (3*m+2) // i≠r}=3*m+1 := by
  classical
  simp [Fintype.card_subtype,Finset.filter_ne']

theorem deleteRow_defect_identity {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (r : Fin (3*m+2)) (ho : OrderedPairFrame (deleteRow A r)) :
    2*(pairEdgeAbsProduct (deleteRow A r) 0 1+
      pairEdgeAbsProduct (deleteRow A r) 0 2+
      pairEdgeAbsProduct (deleteRow A r) 1 2)=
        1-3*d+(A r 0)^2+(A r 1)^2+(A r 2)^2 := by
  have hrest : (∑ i,rowDefect (deleteRow A r i))=
      2*(pairEdgeAbsProduct (deleteRow A r) 0 1+
        pairEdgeAbsProduct (deleteRow A r) 0 2+
        pairEdgeAbsProduct (deleteRow A r) 1 2) := by
    rw [pairEdgeAbsProduct_eq_sum,pairEdgeAbsProduct_eq_sum,pairEdgeAbsProduct_eq_sum]
    simp only [Finset.mul_sum,mul_add,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [saturated_row_defect (ho.saturated i)]
    ring
  have he := Finset.sum_erase_add Finset.univ (fun i => rowDefect (A i)) (Finset.mem_univ r)
  dsimp only at he
  rw [← sum_deleted_index (fun i => rowDefect (A i)) r,total_rowDefect hA] at he
  change (∑ i,rowDefect (deleteRow A r i))+rowDefect (A r)=(3*m+2 : ℕ)-3*((m : ℝ)+d) at he
  rw [hrest] at he
  simp only [rowDefect,rowEnergy,Fin.sum_univ_three] at he
  push_cast at he
  linarith

end
end F3
