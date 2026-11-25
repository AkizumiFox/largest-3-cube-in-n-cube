import F3.OrderedFlow

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

lemma positive_edge_has_two_rows {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    {j k : Fin 3} (hjk : j≠k) (he : 0<pairEdgeEnergy A j k) :
    2≤(pairEdgeRows A j k).card := by
  classical
  have hn : (pairEdgeRows A j k).Nonempty := by
    by_contra h
    have hz : pairEdgeRows A j k=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [pairEdgeEnergy,hz] at he
  obtain ⟨i₀,hi₀⟩ := hn
  have hp₀ := (mem_pairEdgeRows A i₀ j k).mp hi₀
  obtain ⟨i₁,hne,hp₁⟩ := orthogonal_pair_has_other hA i₀ hjk (mul_ne_zero hp₀.1 hp₀.2)
  have hi₁ : i₁∈pairEdgeRows A j k := (mem_pairEdgeRows A i₁ j k).mpr
    ⟨left_ne_zero_of_mul hp₁,right_ne_zero_of_mul hp₁⟩
  have hsub : ({i₀,i₁}:Finset ι)⊆pairEdgeRows A j k := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hi₀
    · exact hi₁
  have ht := Finset.card_le_card hsub
  simpa [Ne.symm hne] using ht

lemma small_source_has_no_branch {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (ho : OrderedPairFrame A) (hd : 0<δ)
    (hm : m≤2) : pairEdgeEnergy A 0 2=0 := by
  classical
  obtain ⟨hc0,hc1,hc2⟩ := ordered_residue_one_counts hA ho hd
  have hb1 := (ordered_pair_energy_balances hA ho).2.1
  rw [hc1] at hb1
  have hD := pairEdgeDeficit_nonneg ho (by decide : (1:Fin 3)<2)
  have he01 : 0<pairEdgeEnergy A 0 1 := by linarith
  have hn01 := positive_edge_has_two_rows hA (by decide : (0:Fin 3)≠1) he01
  have hc := source_edge_count_le ho
  rw [hc0] at hc
  by_contra hn
  have he02 : 0<pairEdgeEnergy A 0 2 := lt_of_le_of_ne (pairEdgeEnergy_nonneg A 0 2) (Ne.symm hn)
  have hn02 := positive_edge_has_two_rows hA (by decide : (0:Fin 3)≠2) he02
  omega

/-- The no-full-row ordered branch cannot occur in dimension four. -/
theorem ordered_dimension_four_impossible {δ : ℝ} {A : Fin (3*1+1) → Fin 3 → ℝ}
    (hA : Feasible ((1:ℝ)+δ) A) (ho : OrderedPairFrame A) (hd : 0<δ) : False := by
  have hA' : Feasible (((1:ℕ):ℝ)+δ) A := by simpa using hA
  have he02 := small_source_has_no_branch hA' ho hd (by decide : 1≤2)
  obtain ⟨hc0,hc1,hc2⟩ := ordered_residue_one_counts hA' ho hd
  have hb2 := (ordered_pair_energy_balances hA ho).2.2
  rw [hc2,he02] at hb2
  norm_num at hb2
  have he12 : 0<pairEdgeEnergy A 1 2 := by linarith
  have hn12 := positive_edge_has_two_rows hA (by decide : (1:Fin 3)≠2) he12
  have hcount := Finset.card_le_card (pairEdgeRows_subset_large ho (by decide : (1:Fin 3)<2))
  rw [hc1] at hcount
  omega

lemma pair_deficit_energy_sum {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k) :
    pairEdgeDeficit A j k+pairEdgeEnergy A j k=2*(∑i∈pairEdgeRows A j k,|A i k|) := by
  unfold pairEdgeDeficit pairEdgeEnergy
  rw [←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := (mem_pairEdgeRows A i j k).mp hi
  have hb := (ordered_pair_budget ho i hjk hp.1 hp.2).1
  nlinarith [sq_abs (A i j),sq_abs (A i k)]

lemma chain_incoming_square_lower {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (ho : OrderedPairFrame A) (hd : 0<δ)
    (he02 : pairEdgeEnergy A 0 2=0) : 4*δ≤(pairEdgeEnergy A 0 1)^2 := by
  obtain ⟨hc0,hc1,hc2⟩ := ordered_residue_one_counts hA ho hd
  obtain ⟨hb0,hb1,hb2⟩ := ordered_pair_energy_balances hA ho
  rw [hc1] at hb1
  rw [hc2,he02] at hb2
  have hs := pair_deficit_energy_sum ho (by decide : (1:Fin 3)<2)
  have heq : pairEdgeEnergy A 0 1=2*(∑i∈pairEdgeRows A 1 2,|A i 2|) := by linarith
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s:=pairEdgeRows A 1 2)
    (f:=fun i => |A i 2|) (fun i _ => abs_nonneg (A i 2))
  simp only [sq_abs] at hsq
  change pairEdgeEnergy A 1 2≤(∑i∈pairEdgeRows A 1 2,|A i 2|)^2 at hsq
  rw [heq]
  nlinarith only [hb2,hsq]

lemma ordered_incoming_one {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (ho : OrderedPairFrame A) (dom : Fin n → Fin 3)
    (hdom : ∀i,Dominance.Dominant (A i) (dom i)) :
    Dominance.incoming A dom 1=pairEdgeEnergy A 0 1 := by
  classical
  have hl := saturated_dominant_large ho.saturated dom hdom
  unfold Dominance.incoming pairEdgeEnergy pairEdgeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : A i 1=0
  · simp [h1]
  by_cases h0 : A i 0=0
  · have hb : (1:ℝ)/2< |A i 1| := by
      by_cases h2 : A i 2=0
      · have he : |A i 1|=1 := by simpa [h0,h2] using ho.saturated i
        rw [he]
        norm_num
      · exact (ordered_pair_budget ho i (j:=1) (k:=2) (by decide) h1 h2).2.1
    have he : dom i=1 := ho.large_unique i (hl i) hb
    simp [he,h0]
  · have hb := (ordered_pair_budget ho i (j:=0) (k:=1) (by decide) h0 h1).2.1
    have he : dom i=0 := ho.large_unique i (hl i) hb
    simp [he,h0,h1]

lemma edge01_dominance_bound {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (ho : OrderedPairFrame A) (hd : 0<δ) :
    pairEdgeEnergy A 0 1≤(1-Real.sqrt (3*δ))^2/2 := by
  obtain ⟨dom,hdom,_,_,hE,_⟩ := Dominance.dominance_summary (by decide : 2≤3) hd
    (Dominance.feasibleK_three_iff.mpr hA)
  have ht := Dominance.incoming_le_total A dom 1
  rw [ordered_incoming_one ho dom hdom] at ht
  exact ht.trans hE

/-- The no-full-row ordered branch in dimension seven lies below 3/100. -/
theorem ordered_dimension_seven_bound {δ : ℝ} {A : Fin (3*2+1) → Fin 3 → ℝ}
    (hA : Feasible ((2:ℝ)+δ) A) (ho : OrderedPairFrame A) (hd : 0<δ) : δ<3/100 := by
  have hA' : Feasible (((2:ℕ):ℝ)+δ) A := by simpa using hA
  have he02 := small_source_has_no_branch hA' ho hd (by decide : 2≤2)
  have hlow := chain_incoming_square_lower hA' ho hd he02
  have hu := edge01_dominance_bound hA' ho hd
  have hc := Dominance.three_column_coarse hd hA'
  have hc' := Dominance.three_dimensional_bound_lt_72_div_1000
  have hroot := Real.sqrt_nonneg (3*δ)
  have hsroot := Real.sq_sqrt (show 0≤3*δ by positivity)
  have hrhi : Real.sqrt (3*δ)≤1 := Real.sqrt_le_one.mpr (by linarith)
  by_contra! hn
  have hrlo : 3/10≤Real.sqrt (3*δ) := by nlinarith
  have hf := mul_nonneg (show 0≤Real.sqrt (3*δ)-3/10 by linarith)
    (show 0≤17/10-Real.sqrt (3*δ) by linarith)
  have hupper : pairEdgeEnergy A 0 1≤49/200 := by nlinarith
  have hE0 := pairEdgeEnergy_nonneg A 0 1
  have hp := mul_nonneg hE0 (show 0≤49/200-pairEdgeEnergy A 0 1 by linarith)
  nlinarith

end
end F3
