import F3.EdgeTransferActual

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

lemma pairEdgeDeficit_nonneg {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k) :
    0≤pairEdgeDeficit A j k := by
  rw [pairEdgeDeficit_eq ho hjk]
  exact add_nonneg (pairEdgeLoss_nonneg A j k) (pairEdgeEnergy_nonneg A j k)

lemma transfer_phi_subadd {E F : ℝ} (hE : 0≤E) (hF : 0≤F) :
    Transfer.phi (E+F)≤Transfer.phi E+Transfer.phi F := by
  have he := Real.sq_sqrt (show 0≤2*E by positivity)
  have hf := Real.sq_sqrt (show 0≤2*F by positivity)
  have hp := mul_nonneg (Real.sqrt_nonneg (2*E)) (Real.sqrt_nonneg (2*F))
  have hr : Real.sqrt (2*(E+F))≤Real.sqrt (2*E)+Real.sqrt (2*F) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity,by nlinarith⟩
  unfold Transfer.phi
  linarith

lemma grouped_transfer {E F L K : ℝ} (hE : 0≤E) (hF : 0≤F)
    (h1 : 2*E≤L ∧ Transfer.phi E≤L)
    (h2 : 2*F≤K ∧ Transfer.phi F≤K) :
    2*(E+F)≤L+K ∧ Transfer.phi (E+F)≤L+K := by
  constructor
  · linarith
  · exact (transfer_phi_subadd hE hF).trans (add_le_add h1.2 h2.2)

theorem ordered_total_edge_loss {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (ho : OrderedPairFrame A) :
    pairEdgeLoss A 0 1+pairEdgeLoss A 0 2+pairEdgeLoss A 1 2=(Fintype.card ι:ℝ)-3*s := by
  obtain ⟨h0,h1,h2⟩ := ordered_pair_energy_balances hA ho
  have hc := ordered_large_count_sum ho
  have hcr : ((largeColumnRows A 0).card:ℝ)+((largeColumnRows A 1).card:ℝ)+
      ((largeColumnRows A 2).card:ℝ)=(Fintype.card ι:ℝ) := by exact_mod_cast hc
  rw [pairEdgeDeficit_eq ho (by decide : (0:Fin 3)<1),
    pairEdgeDeficit_eq ho (by decide : (0:Fin 3)<2)] at h0
  rw [pairEdgeDeficit_eq ho (by decide : (1:Fin 3)<2)] at h1
  linarith

lemma ordered_two_deficient_columns {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {m : ℕ} {δ : ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (ho : OrderedPairFrame A) (hd : 0≤δ)
    (hc1 : (largeColumnRows A 1).card=m) (hc2 : (largeColumnRows A 2).card=m) :
    4*Real.sqrt (2*δ)-4*δ≤pairEdgeLoss A 0 1+pairEdgeLoss A 0 2+pairEdgeLoss A 1 2 := by
  obtain ⟨h0,h1,h2⟩ := ordered_pair_energy_balances hA ho
  rw [hc1] at h1
  rw [hc2] at h2
  have hd12 := pairEdgeDeficit_nonneg ho (by decide : (1:Fin 3)<2)
  have he01 := actual_edge_transfer hA ho (by decide : (0:Fin 3)<1)
  have he02 := actual_edge_transfer hA ho (by decide : (0:Fin 3)<2)
  have he12 := actual_edge_transfer hA ho (by decide : (1:Fin 3)<2)
  have hgroup := grouped_transfer (pairEdgeEnergy_nonneg A 0 2) (pairEdgeEnergy_nonneg A 1 2)
    ⟨he02.1,he02.2.1⟩ ⟨he12.1,he12.2.1⟩
  have hleft := Transfer.loss_of_energy_lower_bound hd (show δ≤pairEdgeEnergy A 0 1 by linarith)
    he01.1 he01.2.1
  have hright := Transfer.loss_of_energy_lower_bound hd
    (show δ≤pairEdgeEnergy A 0 2+pairEdgeEnergy A 1 2 by linarith) hgroup.1 hgroup.2
  unfold Transfer.phi at hleft hright
  linarith

lemma saturated_dominant_large {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) (dom : Fin n → Fin 3)
    (hdom : ∀i,Dominance.Dominant (A i) (dom i)) :
    ∀i,(1:ℝ)/2< |A i (dom i)| := by
  intro i
  have ht := Dominance.l1_decompose (A i) (dom i)
  have hd := hdom i
  unfold Dominance.Dominant at hd
  simp only [Dominance.l1,Fin.sum_univ_three,hs i] at ht
  linarith

lemma dominance_large_exists {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (hd : 0<δ)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) :
    ∀i,∃j,(1:ℝ)/2< |A i j| := by
  obtain ⟨dom,hdom,_⟩ := Dominance.dominance_summary (by decide : 2≤3) hd
    (Dominance.feasibleK_three_iff.mpr hA)
  intro i
  exact ⟨dom i,saturated_dominant_large hs dom hdom i⟩

lemma dominant_count_eq_large {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (ho : OrderedPairFrame A) (dom : Fin n → Fin 3)
    (hdom : ∀i,Dominance.Dominant (A i) (dom i)) (j : Fin 3) :
    Dominance.domCount dom j=(largeColumnRows A j).card := by
  classical
  have hl := saturated_dominant_large ho.saturated dom hdom
  unfold Dominance.domCount largeColumnRows
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro he
    simpa [he] using hl i
  · intro hi
    exact ho.large_unique i (hl i) hi

lemma ordered_residue_one_counts {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (ho : OrderedPairFrame A) (hd : 0<δ) :
    (largeColumnRows A 0).card=m+1 ∧ (largeColumnRows A 1).card=m ∧
      (largeColumnRows A 2).card=m := by
  obtain ⟨dom,hdom,_,_,_,j,hj,hothers⟩ := Dominance.dominance_summary (by decide : 2≤3) hd
    (Dominance.feasibleK_three_iff.mpr hA)
  have hc (k : Fin 3) := dominant_count_eq_large ho dom hdom k
  have hj0 : j=0 := by
    by_contra hn
    have hc0 := hothers 0 (Ne.symm hn)
    rw [hc 0] at hc0
    have hb := (ordered_pair_energy_balances hA ho).1
    rw [hc0] at hb
    have hd01 := pairEdgeDeficit_nonneg ho (by decide : (0:Fin 3)<1)
    have hd02 := pairEdgeDeficit_nonneg ho (by decide : (0:Fin 3)<2)
    linarith
  subst j
  exact ⟨(hc 0).symm.trans hj,(hc 1).symm.trans (hothers 1 (by decide)),
    (hc 2).symm.trans (hothers 2 (by decide))⟩

/-- The stable residue-one bound from the actual ordered pair frame. -/
theorem ordered_residue_one_bound {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (ho : OrderedPairFrame A) (hd : 0<δ) :
    δ≤15-4*Real.sqrt 14 := by
  obtain ⟨hc0,hc1,hc2⟩ := ordered_residue_one_counts hA ho hd
  have hl := ordered_two_deficient_columns hA ho hd.le hc1 hc2
  rw [ordered_total_edge_loss hA ho] at hl
  norm_num only [Fintype.card_fin,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at hl
  have hcoarse := Dominance.three_column_coarse hd hA
  have hhi := Dominance.three_dimensional_bound_lt_72_div_1000
  exact Transfer.residue_one_scalar hd.le (by linarith) (by linarith)

lemma ordered_source_cap {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {m : ℕ} {δ : ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (ho : OrderedPairFrame A)
    (hd0 : 0<δ) (hd1 : δ≤1) (hc0 : (largeColumnRows A 0).card=m+1) :
    pairEdgeEnergy A 0 1+pairEdgeEnergy A 0 2≤Transfer.B (1-δ) := by
  have hb := (ordered_pair_energy_balances hA ho).1
  rw [hc0] at hb
  push_cast at hb
  have ht1 := actual_edge_transfer hA ho (by decide : (0:Fin 3)<1)
  have ht2 := actual_edge_transfer hA ho (by decide : (0:Fin 3)<2)
  have ht := grouped_transfer (pairEdgeEnergy_nonneg A 0 1) (pairEdgeEnergy_nonneg A 0 2)
    ⟨ht1.1,ht1.2.1⟩ ⟨ht2.1,ht2.2.1⟩
  rw [pairEdgeDeficit_eq ho (by decide : (0:Fin 3)<1),
    pairEdgeDeficit_eq ho (by decide : (0:Fin 3)<2)] at hb
  have he : pairEdgeLoss A 0 1+pairEdgeLoss A 0 2+
      (pairEdgeEnergy A 0 1+pairEdgeEnergy A 0 2)=1-δ := by linarith
  have hi := Transfer.edge_inverse
    (add_nonneg (pairEdgeEnergy_nonneg A 0 1) (pairEdgeEnergy_nonneg A 0 2)) ht.1 ht.2
    (show pairEdgeLoss A 0 1+pairEdgeLoss A 0 2+
      (pairEdgeEnergy A 0 1+pairEdgeEnergy A 0 2)<3/2 by linarith)
  rwa [he] at hi

/-- The stable residue-two bound from the actual ordered pair frame and
actual large-coordinate counts. -/
theorem ordered_residue_two_bound {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (ho : OrderedPairFrame A)
    (hdlo : 10-4*Real.sqrt 6≤δ) (hdhi : δ≤4/9) : δ≤10-4*Real.sqrt 6 := by
  classical
  have hd : 1/5<δ := lt_of_lt_of_le Transfer.correction_two_bounds.1 hdlo
  have hd0 : 0<δ := by linarith
  have hcl (j : Fin 3) : m≤(largeColumnRows A j).card := by
    exact residue_two_large_count hd0 hA j
  have hcl0 := hcl 0
  have hcl1 := hcl 1
  have hcl2 := hcl 2
  have hct := ordered_large_count_sum ho
  simp only [Fintype.card_fin] at hct
  obtain ⟨hb0,hb1,hb2⟩ := ordered_pair_energy_balances hA ho
  have hd01 := pairEdgeDeficit_nonneg ho (by decide : (0:Fin 3)<1)
  have hd02 := pairEdgeDeficit_nonneg ho (by decide : (0:Fin 3)<2)
  have hd12 := pairEdgeDeficit_nonneg ho (by decide : (1:Fin 3)<2)
  have hc0gt : m<(largeColumnRows A 0).card := by
    have hr : (m:ℝ)<((largeColumnRows A 0).card:ℝ) := by linarith
    exact_mod_cast hr
  have hc0 : (largeColumnRows A 0).card=m+1 := by
    by_contra hn
    have hp0 : (largeColumnRows A 0).card=m+2 := by omega
    have hp1 : (largeColumnRows A 1).card=m := by omega
    have hp2 : (largeColumnRows A 2).card=m := by omega
    have hl := ordered_two_deficient_columns hA ho hd0.le hp1 hp2
    rw [ordered_total_edge_loss hA ho] at hl
    norm_num only [Fintype.card_fin,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hl
    exact Transfer.residue_two_surplus_exclusion hd hdhi (by linarith)
  have hsource := ordered_source_cap hA ho hd0 (by linarith) hc0
  have hcap := Transfer.B_source_cap hdlo (show δ≤1 by linarith)
  have hc1 : (largeColumnRows A 1).card=m+1 := by
    by_contra hn
    have hp1 : (largeColumnRows A 1).card=m := by omega
    rw [hp1] at hb1
    have he02 := pairEdgeEnergy_nonneg A 0 2
    linarith
  have hc2 : (largeColumnRows A 2).card=m := by omega
  rw [hc1] at hb1
  rw [hc2] at hb2
  push_cast at hb1 hb2
  have hmid : pairEdgeDeficit A 1 2=1-δ+pairEdgeEnergy A 0 1 := by linarith
  have hsink : δ=pairEdgeEnergy A 0 2+pairEdgeEnergy A 1 2 := by linarith
  have hd12hi : pairEdgeDeficit A 1 2<3/2 := by
    have h01 := pairEdgeEnergy_nonneg A 0 1
    have h02 := pairEdgeEnergy_nonneg A 0 2
    linarith
  have hte := actual_edge_transfer hA ho (by decide : (1:Fin 3)<2)
  have hinv := Transfer.edge_inverse (pairEdgeEnergy_nonneg A 1 2) hte.1 hte.2.1
    (show pairEdgeLoss A 1 2+pairEdgeEnergy A 1 2<3/2 by
      rw [←pairEdgeDeficit_eq ho (by decide : (1:Fin 3)<2)]; exact hd12hi)
  rw [←pairEdgeDeficit_eq ho (by decide : (1:Fin 3)<2)] at hinv
  exact Transfer.three_vertex_flow hdlo hdhi (pairEdgeEnergy_nonneg A 0 1)
    (pairEdgeEnergy_nonneg A 0 2) hsource hmid hsink hinv

end
end F3
