import F3.PairGraph
import F3.ColumnBounds
import F3.FullRowBookkeeping
import F3.OrderedPairFrames

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem at_most_one_large_coordinate {a : Fin 3 → ℝ} (ha : RowBound a) :
    (if 1/2< |a 0| then (1:ℝ) else 0)+
    (if 1/2< |a 1| then (1:ℝ) else 0)+
    (if 1/2< |a 2| then (1:ℝ) else 0)≤1 := by
  unfold RowBound at ha
  by_cases h0 : 1/2< |a 0| <;> by_cases h1 : 1/2< |a 1| <;>
    by_cases h2 : 1/2< |a 2| <;> simp only [h0,h1,h2,ite_true,ite_false] <;>
      linarith [abs_nonneg (a 0),abs_nonneg (a 1),abs_nonneg (a 2)]

theorem largeCount_sum_real {n : ℕ} (A : Fin n → Fin 3 → ℝ) (j : Fin 3) :
    (∑i,if 1/2< |A i j| then (1:ℝ) else 0)=largeCount A j := by
  classical
  simp [largeCount,Finset.sum_ite]

theorem no_two_balanced_rows {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (hδ : 1/5<δ)
    (p q : Fin (3*m+2)) (hpq : p≠q)
    (hp : |A p 0|=1/2 ∧ |A p 1|=1/2 ∧ A p 2=0)
    (hq : |A q 0|=1/2 ∧ |A q 1|=1/2 ∧ A q 2=0) : False := by
  classical
  have hlarge (i : Fin (3*m+2)) :
      (if 1/2< |A i 0| then (1:ℝ) else 0)+
      (if 1/2< |A i 1| then (1:ℝ) else 0)+
      (if 1/2< |A i 2| then (1:ℝ) else 0)≤
        1-(if i=p then (1:ℝ) else 0)-(if i=q then (1:ℝ) else 0) := by
    by_cases hip : i=p
    · subst i; norm_num [hp.1,hp.2.1,hp.2.2,hpq]
    by_cases hiq : i=q
    · subst i; norm_num [hq.1,hq.2.1,hq.2.2,hpq.symm]
    simpa only [if_neg hip,if_neg hiq,sub_zero] using at_most_one_large_coordinate (hA.1 i)
  have hcounts := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hlarge i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    largeCount_sum_real,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcounts
  have hp0 := residue_two_large_count (by linarith : 0<δ) hA 0
  have hp1 := residue_two_large_count (by linarith : 0<δ) hA 1
  have hp0r : (m:ℝ)≤largeCount A 0 := by exact_mod_cast hp0
  have hp1r : (m:ℝ)≤largeCount A 1 := by exact_mod_cast hp1
  have hp2 : (largeCount A 2:ℝ)≤m := by
    push_cast at hcounts
    linarith
  have hdefp : rowDefect (A p)=1/2 := by
    have h0 : (A p 0)^2=1/4 := by nlinarith [sq_abs (A p 0),hp.1]
    have h1 : (A p 1)^2=1/4 := by nlinarith [sq_abs (A p 1),hp.2.1]
    norm_num [rowDefect,rowEnergy,Fin.sum_univ_three,h0,h1,hp.2.2]
  have hdefq : rowDefect (A q)=1/2 := by
    have h0 : (A q 0)^2=1/4 := by nlinarith [sq_abs (A q 0),hq.1]
    have h1 : (A q 1)^2=1/4 := by nlinarith [sq_abs (A q 1),hq.2.1]
    norm_num [rowDefect,rowEnergy,Fin.sum_univ_three,h0,h1,hq.2.2]
  have hthird (i : Fin (3*m+2)) :
      2*(A i 2)^2≤2*(if 1/2< |A i 2| then (1:ℝ) else 0)+rowDefect (A i)-
        (if i=p then (1:ℝ)/2 else 0)-(if i=q then (1:ℝ)/2 else 0) := by
    by_cases hip : i=p
    · subst i; norm_num [hp.2.2,hdefp,hpq]
    by_cases hiq : i=q
    · subst i; norm_num [hq.2.2,hdefq,hpq.symm]
    simp only [if_neg hip,if_neg hiq,sub_zero]
    by_cases hb : 1/2< |A i 2|
    · rw [if_pos hb]
      have he := Dominance.entry_sq_le_one (Dominance.feasibleK_three_iff.mpr hA) i 2
      have hl := rowDefect_nonneg (hA.1 i)
      linarith
    · rw [if_neg hb]
      simpa using small_coordinate_defect (hA.1 i) 2 (le_of_not_gt hb)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hthird i)
  have hcol : (∑i,(A i 2)^2)=(m:ℝ)+δ := by simpa [pow_two] using hA.2 2 2
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
    hcol,largeCount_sum_real,total_rowDefect hA,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hsum
  push_cast at hsum
  linarith

theorem actual_pair_diagonal_eq_of_balanced {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (hw : ∀i,0<M.weight i)
    (i : ι) {j k : Fin 3} (hjk : j≠k) (hj : A i j≠0) (hk : A i k≠0)
    (hz : ∀l,l≠j → l≠k → A i l=0) (he : |A i j|=|A i k|) :
    M.matrix j j=M.matrix k k := by
  apply le_antisymm
  · by_contra! h
    have hh := (actual_pair_orientation hA hs M hw i hjk.symm hk hj
      (fun l hlk hlj => hz l hlj hlk)).mpr h
    linarith
  · by_contra! h
    have hh := (actual_pair_orientation hA hs M hw i hjk hj hk hz).mpr h
    linarith

theorem actual_pair_balanced_of_diagonal_eq {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (hw : ∀i,0<M.weight i)
    (i : ι) {j k : Fin 3} (hjk : j≠k) (hj : A i j≠0) (hk : A i k≠0)
    (hz : ∀l,l≠j → l≠k → A i l=0) (he : M.matrix j j=M.matrix k k) :
    |A i j|=|A i k| := by
  apply le_antisymm
  · by_contra! h
    have hh := (actual_pair_orientation hA hs M hw i hjk hj hk hz).mp h
    linarith
  · by_contra! h
    have hh := (actual_pair_orientation hA hs M hw i hjk.symm hk hj
      (fun l hlk hlj => hz l hlj hlk)).mp h
    linarith

/-- A no-full-row second-residue stationary frame has a large coordinate in
every row. No optimum or graph representation is assumed. -/
theorem residue_two_no_full_large {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (hδ : 1/5<δ)
    (M : MultiplierSystem A) (hw : ∀i,0<M.weight i)
    (hn : ∀i,∃j,A i j=0) : ∀i,∃j,(1:ℝ)/2< |A i j| := by
  classical
  intro p
  by_contra! hsmall
  obtain ⟨l,hl⟩ := hn p
  let e : Equiv.Perm (Fin 3) := Equiv.swap 2 l
  let B := permuteColumns A e
  let N := M.permuteColumns e
  have hB : Feasible ((m:ℝ)+δ) B := feasible_permuteColumns hA e
  have hN : ∀i,0<N.weight i := hw
  have hs : 0<(m:ℝ)+δ := by positivity
  have hBn (i : Fin (3*m+2)) : ∃j,B i j=0 := by
    obtain ⟨j,hj⟩ := hn i
    exact ⟨e.symm j,by simpa [B,permuteColumns] using hj⟩
  have hz : B p 2=0 := by simpa [B,permuteColumns,e] using hl
  have hp0 : |B p 0|≤1/2 := hsmall (e 0)
  have hp1 : |B p 1|≤1/2 := hsmall (e 1)
  have hsat := N.complementary p (hN p)
  change |B p 0|+|B p 1|+|B p 2|=1 at hsat
  rw [hz,abs_zero,add_zero] at hsat
  have hp0e : |B p 0|=1/2 := by linarith
  have hp1e : |B p 1|=1/2 := by linarith
  have hp0n : B p 0≠0 := by intro h; rw [h,abs_zero] at hp0e; norm_num at hp0e
  have hp1n : B p 1≠0 := by intro h; rw [h,abs_zero] at hp1e; norm_num at hp1e
  obtain ⟨q,hqp,hprod⟩ := orthogonal_pair_has_other hB p
    (j:=0) (k:=1) (by decide) (mul_ne_zero hp0n hp1n)
  have hq0n := left_ne_zero_of_mul hprod
  have hq1n := right_ne_zero_of_mul hprod
  have hzq := third_zero_of_not_full (by decide : (0:Fin 3)≠1) hq0n hq1n (hBn q)
  have hq2 : B q 2=0 := hzq 2 (by decide) (by decide)
  have hdiag := actual_pair_diagonal_eq_of_balanced hB hs N hN p
    (by decide : (0:Fin 3)≠1) hp0n hp1n
    (third_zero_of_not_full (by decide) hp0n hp1n (hBn p)) (by linarith)
  have hbal := actual_pair_balanced_of_diagonal_eq hB hs N hN q
    (by decide : (0:Fin 3)≠1) hq0n hq1n hzq hdiag
  have hqs := N.complementary q (hN q)
  change |B q 0|+|B q 1|+|B q 2|=1 at hqs
  rw [hq2,abs_zero,add_zero] at hqs
  exact no_two_balanced_rows hB hδ p q hqp.symm ⟨hp0e,hp1e,hz⟩
    ⟨by linarith,by linarith,hq2⟩

end
end F3
