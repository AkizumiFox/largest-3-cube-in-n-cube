import F3.ExceptionalRowBookkeeping
import F3.TriangleFlow
import F3.ActiveRows

/-! Elimination of the full positive zero-weight row after ordering the
remaining pair rows. Both strict and degenerate triangles are included. -/

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem subgradient_pair_nonpos {a g x : Fin 3 → ℝ}
    (hg : RowSubgradient a g) (j k l : Fin 3)
    (ho : g j*x j+g k*x k+g l*x l=0)
    (hl : 0≤x l) (htri : x l<x j+x k) : a j*a k≤0 := by
  by_contra hn
  have hp : 0<a j*a k := lt_of_not_ge hn
  have haj : a j≠0 := by intro hz; rw [hz,zero_mul] at hp; exact lt_irrefl _ hp
  have hj := hg.2 j
  have hk := hg.2 k
  rcases lt_or_gt_of_ne haj with hjneg | hjpos
  · have hkneg : a k<0 := by nlinarith
    rw [abs_of_neg hjneg] at hj
    rw [abs_of_neg hkneg] at hk
    have hgj : g j= -1 := mul_left_cancel₀ haj (by simpa only [mul_neg_one] using hj)
    have hgk : g k= -1 := mul_left_cancel₀ hkneg.ne (by simpa only [mul_neg_one] using hk)
    rw [hgj,hgk] at ho
    have hb := mul_le_mul_of_nonneg_right (abs_le.mp (hg.1 l)).2 hl
    nlinarith
  · have hkpos : 0<a k := by nlinarith
    rw [abs_of_pos hjpos] at hj
    rw [abs_of_pos hkpos] at hk
    have hgj : g j=1 := mul_left_cancel₀ haj (by simpa only [mul_one] using hj)
    have hgk : g k=1 := mul_left_cancel₀ hkpos.ne' (by simpa only [mul_one] using hk)
    rw [hgj,hgk] at ho
    have hb := mul_le_mul_of_nonneg_right (abs_le.mp (hg.1 l)).1 hl
    nlinarith

theorem no_three_coordinate_zero_weight_ordered {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (hd : 1/5<d) (M : MultiplierSystem A)
    (r : Fin (3*m+2)) (hwr : M.weight r=0)
    (hw : ∀ i, i≠r → 0<M.weight i)
    (hr : ∀ j, 0<A r j)
    (htri : A r 0≤A r 1+A r 2 ∧ A r 1≤A r 0+A r 2 ∧ A r 2≤A r 0+A r 1)
    (ho : OrderedPairFrame (deleteRow A r)) : False := by
  classical
  let B := deleteRow A r
  let u := A r
  have hu (j : Fin 3) : 0<u j := hr j
  have hsum : u 0+u 1+u 2≤1 := by
    simpa only [RowBound,abs_of_pos (hr 0),abs_of_pos (hr 1),abs_of_pos (hr 2)] using hA.1 r
  have htri₀ : u 0≤u 1+u 2 := htri.1
  have htri₁ : u 1≤u 0+u 2 := htri.2.1
  have htri₂ : u 2≤u 0+u 1 := htri.2.2
  have hhalf (j : Fin 3) : u j≤1/2 := by
    fin_cases j
    · change u 0≤(1:ℝ)/2
      linarith only [hsum,htri₀]
    · change u 1≤(1:ℝ)/2
      linarith only [hsum,htri₁]
    · change u 2≤(1:ℝ)/2
      linarith only [hsum,htri₂]
  have hsigned (j k : Fin 3) (hjk : j≠k) :
      pairEdgeSignedProduct B j k= -(u j*u k) := deleteRow_signed_product hA r hjk
  have hmasslower (j k : Fin 3) (hjk : j≠k) :
      u j*u k≤pairEdgeAbsProduct B j k := by
    have he := pairEdge_abs_signed_le B j k
    rw [hsigned j k hjk,abs_neg,abs_of_pos (mul_pos (hu j) (hu k))] at he
    exact he
  have hD (j k : Fin 3) (hjk : j<k) : 2*u j*u k≤pairEdgeDeficit B j k := by
    have h₁ := hmasslower j k (ne_of_lt hjk)
    have h₂ := ordered_edge_deficit_ge_two_abs ho hjk
    linarith
  have hbal := ordered_pair_energy_balances_of_diagonal ho
    (fun j => (m : ℝ)+d-(u j)^2) (deleteRow_gram_diagonal hA r)
  change ((largeColumnRows B 0).card : ℝ)-((m : ℝ)+d-(u 0)^2)=
      pairEdgeDeficit B 0 1+pairEdgeDeficit B 0 2 ∧
    ((m : ℝ)+d-(u 1)^2)-((largeColumnRows B 1).card : ℝ)=
      pairEdgeEnergy B 0 1-pairEdgeDeficit B 1 2 ∧
    ((m : ℝ)+d-(u 2)^2)-((largeColumnRows B 2).card : ℝ)=
      pairEdgeEnergy B 0 2+pairEdgeEnergy B 1 2 at hbal
  have hq (j : Fin 3) : m≤(largeColumnRows B j).card := by
    have hh : |A r j|≤1/2 := by rw [abs_of_pos (hr j)]; exact hhalf j
    rw [deleteRow_large_count A r j hh]
    exact residue_two_large_count (by linarith) hA j
  have hqsum : (largeColumnRows B 0).card+(largeColumnRows B 1).card+
      (largeColumnRows B 2).card=3*m+1 := by
    rw [ordered_large_count_sum ho,deleteRow_card r]
  have hsource : ((largeColumnRows B 0).card : ℝ)+(u 0)^2-
      pairEdgeDeficit B 0 1-pairEdgeDeficit B 0 2=(m : ℝ)+d := by linarith only [hbal.1]
  obtain ⟨hq₀,hq₁,hq₂⟩ := triangle_source_counts (by linarith : 0<d) (hu 0).le htri₀
    (hq 0) (hq 1) (hq 2) hqsum hsource (hD 0 1 (by decide)) (hD 0 2 (by decide))
  have hmiddle : d=(u 1)^2+pairEdgeEnergy B 0 1-pairEdgeDeficit B 1 2 := by
    have h := hbal.2.1
    rw [hq₁] at h
    linarith only [h]
  have hsink : d=(u 2)^2+pairEdgeEnergy B 0 2+pairEdgeEnergy B 1 2 := by
    have h := hbal.2.2
    rw [hq₂] at h
    linarith only [h]
  have horth (i : {i : Fin (3*m+2) // i≠r}) :
      M.gradient i.1 0*u 0+M.gradient i.1 1*u 1+M.gradient i.1 2*u 2=0 := by
    simpa only [Fin.sum_univ_three] using
      positive_gradient_orthogonal M (zero_weight_row_kernel M r hwr) i.1 (hw i.1 i.2)
  have hneg₀₁ (h : u 2<u 0+u 1) : ∀ i, B i 0*B i 1≤0 := by
    intro i
    exact subgradient_pair_nonpos (M.subgradient i.1) 0 1 2 (horth i) (hu 2).le h
  have hneg₀₂ (h : u 1<u 0+u 2) : ∀ i, B i 0*B i 2≤0 := by
    intro i
    apply subgradient_pair_nonpos (M.subgradient i.1) 0 2 1 _ (hu 1).le h
    linarith [horth i]
  have hneg₁₂ (h : u 0<u 1+u 2) : ∀ i, B i 1*B i 2≤0 := by
    intro i
    apply subgradient_pair_nonpos (M.subgradient i.1) 1 2 0 _ (hu 0).le h
    linarith [horth i]
  have habs₀₁ (h : u 2<u 0+u 1) : pairEdgeAbsProduct B 0 1=u 0*u 1 := by
    rw [pairEdgeAbsProduct_of_nonpos (hneg₀₁ h),hsigned 0 1 (by decide),neg_neg]
  have habs₀₂ (h : u 1<u 0+u 2) : pairEdgeAbsProduct B 0 2=u 0*u 2 := by
    rw [pairEdgeAbsProduct_of_nonpos (hneg₀₂ h),hsigned 0 2 (by decide),neg_neg]
  have habs₁₂ (h : u 0<u 1+u 2) : pairEdgeAbsProduct B 1 2=u 1*u 2 := by
    rw [pairEdgeAbsProduct_of_nonpos (hneg₁₂ h),hsigned 1 2 (by decide),neg_neg]
  have hdefect : 2*(pairEdgeAbsProduct B 0 1+pairEdgeAbsProduct B 0 2+
      pairEdgeAbsProduct B 1 2)=1-3*d+(u 0)^2+(u 1)^2+(u 2)^2 :=
    deleteRow_defect_identity hA r ho
  by_cases he₀ : u 0=u 1+u 2
  · have hQ₀₁ := habs₀₁ (by linarith [hu 1])
    have hQ₀₂ := habs₀₂ (by linarith [hu 2])
    have hsmall : u 1*u 2+pairEdgeAbsProduct B 1 2<1/5 := by
      rw [hQ₀₁,hQ₀₂,he₀] at hdefect
      nlinarith
    have hE₁₂ := ordered_edge_energy_lt_one_over_35 ho (j:=1) (k:=2) (by decide)
      (mul_nonneg (hu 1).le (hu 2).le) (hsigned 1 2 (by decide)) hsmall
    have hE₀₁ := ordered_edge_energy_le_square ho (j:=0) (k:=1) (by decide)
      (hu 0).le (hu 1).le (hhalf 1) (by linarith [hu 2] : u 0+u 1≤1) hQ₀₁
    have hE₀₂ := ordered_edge_energy_le_square ho (j:=0) (k:=2) (by decide)
      (hu 0).le (hu 2).le (hhalf 2) (by linarith [hu 1] : u 0+u 2≤1) hQ₀₂
    have hDnonneg : 0≤pairEdgeDeficit B 1 2 := by
      have hh := hD 1 2 (by decide)
      nlinarith [mul_pos (hu 1) (hu 2)]
    exact degenerate_source_flow_impossible hd (hu 1).le (hu 2).le he₀ (hhalf 0)
      hmiddle hsink hE₀₁ hE₀₂ hE₁₂ hDnonneg
  by_cases he₁ : u 1=u 0+u 2
  · have hQ₀₁ := habs₀₁ (by linarith [hu 0])
    have hQ₁₂ := habs₁₂ (by linarith [hu 2])
    have hsmall : u 0*u 2+pairEdgeAbsProduct B 0 2<1/5 := by
      rw [hQ₀₁,hQ₁₂,he₁] at hdefect
      nlinarith
    have hE₀₂ := ordered_edge_energy_lt_one_over_35 ho (j:=0) (k:=2) (by decide)
      (mul_nonneg (hu 0).le (hu 2).le) (hsigned 0 2 (by decide)) hsmall
    have hE₀₁ := ordered_edge_energy_le_square ho (j:=0) (k:=1) (by decide)
      (hu 1).le (hu 0).le (hhalf 0) (by linarith [hu 2] : u 1+u 0≤1)
      (by simpa only [mul_comm] using hQ₀₁)
    have hE₁₂ := ordered_edge_energy_le_square ho (j:=1) (k:=2) (by decide)
      (hu 1).le (hu 2).le (hhalf 2) (by linarith [hu 0] : u 1+u 2≤1) hQ₁₂
    exact degenerate_middle_flow_impossible hd (hu 0).le (hu 2).le he₁ (hhalf 1)
      hmiddle hsink hE₀₁ hE₀₂ hE₁₂ (hD 1 2 (by decide))
  by_cases he₂ : u 2=u 0+u 1
  · have hQ₀₂ := habs₀₂ (by linarith [hu 0])
    have hQ₁₂ := habs₁₂ (by linarith [hu 1])
    have hsmall : u 0*u 1+pairEdgeAbsProduct B 0 1<1/5 := by
      rw [hQ₀₂,hQ₁₂,he₂] at hdefect
      nlinarith
    have hE₀₁ := ordered_edge_energy_lt_one_over_35 ho (j:=0) (k:=1) (by decide)
      (mul_nonneg (hu 0).le (hu 1).le) (hsigned 0 1 (by decide)) hsmall
    exact degenerate_sink_flow_impossible hd (hu 0).le (hu 1).le he₂ hmiddle hE₀₁
      (hD 1 2 (by decide))
  · have hE₀₁ : pairEdgeEnergy B 0 1≤u 0*u 1 := by
      rw [← habs₀₁ (lt_of_le_of_ne htri₂ he₂)]
      exact ordered_edge_energy_le_abs ho (by decide)
    have hE₀₂ : pairEdgeEnergy B 0 2≤u 0*u 2 := by
      rw [← habs₀₂ (lt_of_le_of_ne htri₁ he₁)]
      exact ordered_edge_energy_le_abs ho (by decide)
    have hE₁₂ : pairEdgeEnergy B 1 2≤u 1*u 2 := by
      rw [← habs₁₂ (lt_of_le_of_ne htri₀ he₀)]
      exact ordered_edge_energy_le_abs ho (by decide)
    have hb := strict_triangle_flow_upper (by linarith : 0<d) (hu 0).le (hu 1) (hu 2).le
      hsum htri₁ hmiddle hsink hE₀₁ hE₀₂ hE₁₂ (hD 1 2 (by decide))
    linarith

end
end F3
