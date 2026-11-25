import F3.FullRowClassification
import F3.PairStationarity
import F3.FullRowBookkeeping

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

structure PairTriple {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) where
  i01 : ι
  i02 : ι
  i12 : ι
  row01 : A i01 0≠0 ∧ A i01 1≠0 ∧ A i01 2=0
  row02 : A i02 0≠0 ∧ A i02 1=0 ∧ A i02 2≠0
  row12 : A i12 0=0 ∧ A i12 1≠0 ∧ A i12 2≠0
  exhaustive : ∀i,i∈pairRows A ↔ i=i01 ∨ i=i02 ∨ i=i12

lemma PairTriple.distinct {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (t : PairTriple A) : t.i01≠t.i02 ∧ t.i01≠t.i12 ∧ t.i02≠t.i12 := by
  refine ⟨?_,?_,?_⟩
  · intro h
    exact t.row01.2.1 (by simpa [h] using t.row02.2.1)
  · intro h
    exact t.row01.1 (by simpa [h] using t.row12.1)
  · intro h
    exact t.row02.1 (by simpa [h] using t.row12.1)

lemma one_full_pair_triple {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hF : (fullRows A).card=1) (hQ : (pairRows A).card=3) : Nonempty (PairTriple A) := by
  classical
  obtain ⟨i₀,hi₀⟩ := Finset.card_pos.mp (show 0<(fullRows A).card by omega)
  obtain ⟨i01,hm01,hn01,h01a,h01b⟩ := one_full_pair_witness hA hF i₀ hi₀ (j:=0) (k:=1) (by decide)
  obtain ⟨i02,hm02,hn02,h02a,h02c⟩ := one_full_pair_witness hA hF i₀ hi₀ (j:=0) (k:=2) (by decide)
  obtain ⟨i12,hm12,hn12,h12b,h12c⟩ := one_full_pair_witness hA hF i₀ hi₀ (j:=1) (k:=2) (by decide)
  have h01c : A i01 2=0 := by
    have h := (rowSupport_card_cases A i01).2.mp ((mem_pairRows A i01).mp hm01)
    tauto
  have h02b : A i02 1=0 := by
    have h := (rowSupport_card_cases A i02).2.mp ((mem_pairRows A i02).mp hm02)
    tauto
  have h12a : A i12 0=0 := by
    have h := (rowSupport_card_cases A i12).2.mp ((mem_pairRows A i12).mp hm12)
    tauto
  have hn1 : i01≠i02 := by intro h; subst i02; exact h01b h02b
  have hn2 : i01≠i12 := by intro h; subst i12; exact h01a h12a
  have hn3 : i02≠i12 := by intro h; subst i12; exact h02a h12a
  have hsub : ({i01,i02,i12}:Finset ι)⊆pairRows A := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hm01
    · exact hm02
    · exact hm12
  have heq : ({i01,i02,i12}:Finset ι)=pairRows A :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hQ,hn1,hn2,hn3])
  exact ⟨⟨i01,i02,i12,⟨h01a,h01b,h01c⟩,⟨h02a,h02b,h02c⟩,
    ⟨h12a,h12b,h12c⟩,by intro i; rw [←heq]; simp⟩⟩

lemma sum_two_of_zero {ι : Type*} [Fintype ι] (f : ι → ℝ) (i₀ i₁ : ι)
    (hne : i₀≠i₁) (hz : ∀i,i≠i₀ → i≠i₁ → f i=0) :
    (∑ i,f i)=f i₀+f i₁ := by
  classical
  calc
    _ = ∑ i ∈ ({i₀,i₁}:Finset ι),f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      exact hz i hi.1 hi.2
    _ = _ := by simp [hne]

lemma one_full_pair_cancellation {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hF : (fullRows A).card=1) (i₀ : ι) (hi₀ : i₀∈fullRows A)
    (t : PairTriple A) :
    A t.i01 0*A t.i01 1 = -(A i₀ 0*A i₀ 1) ∧
    A t.i02 0*A t.i02 2 = -(A i₀ 0*A i₀ 2) ∧
    A t.i12 1*A t.i12 2 = -(A i₀ 1*A i₀ 2) := by
  classical
  have hunique (i : ι) (hi : i∈fullRows A) : i=i₀ :=
    Finset.card_le_one.mp (by omega) i hi i₀ hi₀
  have hfull := (full_row_iff A i₀).mp hi₀
  have hn01 : i₀≠t.i01 := by intro h; exact hfull 2 (by simpa [h] using t.row01.2.2)
  have hn02 : i₀≠t.i02 := by intro h; exact hfull 1 (by simpa [h] using t.row02.2.1)
  have hn12 : i₀≠t.i12 := by intro h; exact hfull 0 (by simpa [h] using t.row12.1)
  have hz01 (i : ι) (hn0 : i≠i₀) (hn1 : i≠t.i01) : A i 0*A i 1=0 := by
    by_cases hf : i∈fullRows A
    · exact False.elim (hn0 (hunique i hf))
    by_cases hp : i∈pairRows A
    · rcases (t.exhaustive i).mp hp with h | h | h
      · exact False.elim (hn1 h)
      · rw [h,t.row02.2.1,mul_zero]
      · rw [h,t.row12.1,zero_mul]
    · exact (nonmixed_products_zero A i hf hp).1
  have hz02 (i : ι) (hn0 : i≠i₀) (hn1 : i≠t.i02) : A i 0*A i 2=0 := by
    by_cases hf : i∈fullRows A
    · exact False.elim (hn0 (hunique i hf))
    by_cases hp : i∈pairRows A
    · rcases (t.exhaustive i).mp hp with h | h | h
      · rw [h,t.row01.2.2,mul_zero]
      · exact False.elim (hn1 h)
      · rw [h,t.row12.1,zero_mul]
    · exact (nonmixed_products_zero A i hf hp).2.1
  have hz12 (i : ι) (hn0 : i≠i₀) (hn1 : i≠t.i12) : A i 1*A i 2=0 := by
    by_cases hf : i∈fullRows A
    · exact False.elim (hn0 (hunique i hf))
    by_cases hp : i∈pairRows A
    · rcases (t.exhaustive i).mp hp with h | h | h
      · rw [h,t.row01.2.2,mul_zero]
      · rw [h,t.row02.2.1,zero_mul]
      · exact False.elim (hn1 h)
    · exact (nonmixed_products_zero A i hf hp).2.2
  have hs01 := sum_two_of_zero (fun i => A i 0*A i 1) i₀ t.i01 hn01 hz01
  have hs02 := sum_two_of_zero (fun i => A i 0*A i 2) i₀ t.i02 hn02 hz02
  have hs12 := sum_two_of_zero (fun i => A i 1*A i 2) i₀ t.i12 hn12 hz12
  have he01 : (∑ i,A i 0*A i 1)=0 := by simpa using hA.2 0 1
  have he02 : (∑ i,A i 0*A i 2)=0 := by simpa using hA.2 0 2
  have he12 : (∑ i,A i 1*A i 2)=0 := by simpa using hA.2 1 2
  dsimp at hs01 hs02 hs12
  exact ⟨by linarith,by linarith,by linarith⟩

lemma smaller_coordinate_half {a b u v : ℝ}
    (ha : 0<a) (hb : 0<b) (hab : a+b<1)
    (hu : 0<u) (hv : 0<v) (hsum : u+v=1) (hprod : u*v=a*b)
    (horder : v≤u) : v<1/2 := by
  have hp := mul_pos (show 0<1-(a+b) by linarith) (show 0<1+(a+b) by linarith)
  have habp : a*b<1/4 := by nlinarith [sq_nonneg (a-b)]
  by_contra! hn
  have hveq : v=1/2 := by linarith
  rw [hveq] at hsum hprod
  nlinarith

lemma one_full_sorted_data {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hsp : 0<s)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1)
    (M : MultiplierSystem A) (hw : ∀i,0<M.weight i)
    (hF : (fullRows A).card=1) (i₀ : ι) (hi₀ : i₀∈fullRows A)
    (hpos : ∀j,0<A i₀ j) (t : PairTriple A)
    (h01 : M.matrix 0 0≤M.matrix 1 1) (h12 : M.matrix 1 1≤M.matrix 2 2) :
    ∃d : OneFullData,
      d.a=A i₀ 0 ∧ d.b=A i₀ 1 ∧ d.c=A i₀ 2 ∧
      d.x=|A t.i01 1| ∧ d.y=|A t.i02 2| ∧ d.z=|A t.i12 2| := by
  have hsum : A i₀ 0+A i₀ 1+A i₀ 2=1 := by
    simpa [abs_of_pos (hpos 0),abs_of_pos (hpos 1),abs_of_pos (hpos 2)] using hs i₀
  have hb01 : |A t.i01 0|+|A t.i01 1|=1 := by simpa [t.row01.2.2] using hs t.i01
  have hb02 : |A t.i02 0|+|A t.i02 2|=1 := by simpa [t.row02.2.1] using hs t.i02
  have hb12 : |A t.i12 1|+|A t.i12 2|=1 := by simpa [t.row12.1] using hs t.i12
  obtain ⟨hc01,hc02,hc12⟩ := one_full_pair_cancellation hA hF i₀ hi₀ t
  have hn01 : A t.i01 0*A t.i01 1<0 := by rw [hc01]; exact neg_neg_of_pos (mul_pos (hpos 0) (hpos 1))
  have hn02 : A t.i02 0*A t.i02 2<0 := by rw [hc02]; exact neg_neg_of_pos (mul_pos (hpos 0) (hpos 2))
  have hn12 : A t.i12 1*A t.i12 2<0 := by rw [hc12]; exact neg_neg_of_pos (mul_pos (hpos 1) (hpos 2))
  have hp01 : |A t.i01 0| * |A t.i01 1|=A i₀ 0*A i₀ 1 := by
    rw [←abs_mul,hc01,abs_neg,abs_of_pos (mul_pos (hpos 0) (hpos 1))]
  have hp02 : |A t.i02 0| * |A t.i02 2|=A i₀ 0*A i₀ 2 := by
    rw [←abs_mul,hc02,abs_neg,abs_of_pos (mul_pos (hpos 0) (hpos 2))]
  have hp12 : |A t.i12 1| * |A t.i12 2|=A i₀ 1*A i₀ 2 := by
    rw [←abs_mul,hc12,abs_neg,abs_of_pos (mul_pos (hpos 1) (hpos 2))]
  have hpd := full_row_posdef hA hsp M hw i₀ ((full_row_iff A i₀).mp hi₀)
  have ho01 := negative_pair_orientation_le hA hsp M hpd t.i01 (j:=0) (k:=1) (by decide)
    (by intro l hl0 hl1; fin_cases l <;> simp_all [t.row01.2.2]) hn01 h01
  have ho02 := negative_pair_orientation_le hA hsp M hpd t.i02 (j:=0) (k:=2) (by decide)
    (by intro l hl0 hl2; fin_cases l <;> simp_all [t.row02.2.1]) hn02 (h01.trans h12)
  have ho12 := negative_pair_orientation_le hA hsp M hpd t.i12 (j:=1) (k:=2) (by decide)
    (by intro l hl1 hl2; fin_cases l <;> simp_all [t.row12.1]) hn12 h12
  have ha01 := abs_pos.mpr t.row01.1
  have hb01p := abs_pos.mpr t.row01.2.1
  have ha02 := abs_pos.mpr t.row02.1
  have hc02p := abs_pos.mpr t.row02.2.2
  have hb12p := abs_pos.mpr t.row12.2.1
  have hc12p := abs_pos.mpr t.row12.2.2
  have hxhalf := smaller_coordinate_half (hpos 0) (hpos 1) (by linarith [hpos 2])
    ha01 hb01p hb01 hp01 ho01
  have hyhalf := smaller_coordinate_half (hpos 0) (hpos 2) (by linarith [hpos 1])
    ha02 hc02p hb02 hp02 ho02
  have hzhalf := smaller_coordinate_half (hpos 1) (hpos 2) (by linarith [hpos 0])
    hb12p hc12p hb12 hp12 ho12
  let d : OneFullData := {
    a:=A i₀ 0, b:=A i₀ 1, c:=A i₀ 2,
    x:=|A t.i01 1|, y:=|A t.i02 2|, z:=|A t.i12 2|,
    ha:=hpos 0, hb:=hpos 1, hc:=hpos 2,
    hx:=hb01p,hy:=hc02p,hz:=hc12p,hsum:=hsum,
    hxhalf:=hxhalf,hyhalf:=hyhalf,hzhalf:=hzhalf,
    hprodxy:=by rw [show 1-|A t.i01 1|=|A t.i01 0| by linarith]; nlinarith only [hp01],
    hprodxz:=by rw [show 1-|A t.i02 2|=|A t.i02 0| by linarith]; nlinarith only [hp02],
    hprodyz:=by rw [show 1-|A t.i12 2|=|A t.i12 1| by linarith]; nlinarith only [hp12] }
  exact ⟨d,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end F3
