import F3.OneFullExtraction

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

structure TwoFullSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Fin 3 → ℝ) where
  i₀ : ι
  i₁ : ι
  ip : ι
  distinct : i₀≠i₁
  fullSet : fullRows A={i₀,i₁}
  pairSet : pairRows A={ip}
  full₀ : ∀j,A i₀ j≠0
  full₁ : ∀j,A i₁ j≠0
  pair : A ip 0≠0 ∧ A ip 1=0 ∧ A ip 2≠0

lemma exists_twoFullSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Fin 3 → ℝ} (hF : (fullRows A).card=2) (hQ : (pairRows A).card=1)
    (ip : ι) (hip : ip∈pairRows A)
    (hp : A ip 0≠0 ∧ A ip 1=0 ∧ A ip 2≠0) : Nonempty (TwoFullSupport A) := by
  classical
  obtain ⟨i₀,i₁,hne,hset⟩ := Finset.card_eq_two.mp hF
  have hpSet : pairRows A={ip} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hip,fun i hi => Finset.card_le_one.mp (by omega) i hi ip hip⟩
  have hfull₀ : ∀j,A i₀ j≠0 := (full_row_iff A i₀).mp (by simp [hset])
  have hfull₁ : ∀j,A i₁ j≠0 := (full_row_iff A i₁).mp (by simp [hset])
  exact ⟨⟨i₀,i₁,ip,hne,hset,hpSet,hfull₀,hfull₁,hp⟩⟩

lemma TwoFullSupport.distinct_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Fin 3 → ℝ} (t : TwoFullSupport A) : t.i₀≠t.ip ∧ t.i₁≠t.ip := by
  constructor
  · intro h
    exact t.full₀ 1 (by simpa [h] using t.pair.2.1)
  · intro h
    exact t.full₁ 1 (by simpa [h] using t.pair.2.1)

lemma nonmixed_offdiag_zero {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (i : ι) (hf : i∉fullRows A) (hp : i∉pairRows A)
    {j k : Fin 3} (hjk : j≠k) : A i j*A i k=0 := by
  by_contra h
  exact hp (pair_of_two_nonzero_of_not_full A i hjk (left_ne_zero_of_mul h)
    (right_ne_zero_of_mul h) hf)

lemma sum_three_of_zero {ι : Type*} [Fintype ι] (f : ι → ℝ) (i₀ i₁ ip : ι)
    (h01 : i₀≠i₁) (h0p : i₀≠ip) (h1p : i₁≠ip)
    (hz : ∀i,i≠i₀ → i≠i₁ → i≠ip → f i=0) :
    (∑i,f i)=f i₀+f i₁+f ip := by
  classical
  calc
    _ = ∑i∈({i₀,i₁,ip}:Finset ι),f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      exact hz i hi.1 hi.2.1 hi.2.2
    _ = _ := by simp [h01,h0p,h1p]; ring

lemma TwoFullSupport.offdiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (t : TwoFullSupport A) (hA : Feasible s A)
    {j k : Fin 3} (hjk : j≠k) :
    A t.i₀ j*A t.i₀ k+A t.i₁ j*A t.i₁ k+A t.ip j*A t.ip k=0 := by
  have hz (i : ι) (h0 : i≠t.i₀) (h1 : i≠t.i₁) (hp : i≠t.ip) : A i j*A i k=0 := by
    apply nonmixed_offdiag_zero A i
    · simp [t.fullSet,h0,h1]
    · simp [t.pairSet,hp]
    · exact hjk
  have he := sum_three_of_zero (fun i => A i j*A i k) t.i₀ t.i₁ t.ip
    t.distinct t.distinct_pair.1 t.distinct_pair.2 hz
  have hg : (∑i,A i j*A i k)=0 := by simpa [hjk] using hA.2 j k
  dsimp at he
  linarith

lemma TwoFullSupport.column_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (t : TwoFullSupport A) (hA : Feasible s A)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1) (j : Fin 3) :
    ((pureColumnRows A j).card:ℝ)+A t.i₀ j^2+A t.i₁ j^2+A t.ip j^2=s := by
  have hg : (∑i,A i j^2)=s := by simpa [pow_two] using hA.2 j j
  rw [column_energy_partition A hs j,pure_column_energy A hs j,t.fullSet,t.pairSet] at hg
  simp [t.distinct] at hg
  linarith

lemma equal_abs_remaining_product {a b c d e f : ℝ}
    (hb : b≠0) (hbe : |e|=|b|)
    (h01 : a*b+d*e=0) (h12 : b*c+e*f=0) : d*f=a*c := by
  have h01' : d*e=-(a*b) := by linarith
  have h12' : e*f=-(b*c) := by linarith
  have hes : e^2=b^2 := by rw [←sq_abs e,←sq_abs b,hbe]
  have ht : (d*f)*b^2=(a*c)*b^2 := by
    calc
      _ = (d*e)*(e*f) := by rw [←hes]; ring
      _ = (-(a*b))*(-(b*c)) := by rw [h01',h12']
      _ = _ := by ring
  exact mul_right_cancel₀ (pow_ne_zero 2 hb) ht

lemma two_full_fixed_normal_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Fin 3 → ℝ} {m : ℕ} {δ : ℝ}
    (hA : Feasible ((m:ℝ)+δ) A)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1)
    (t : TwoFullSupport A) (hd0 : 0<δ) (hd1 : δ<1/2) :
    ∃(d : TwoFullData) (p₀ p₁ p₂ : ℕ),
      p₀+p₁+p₂+3=Fintype.card ι ∧
      (p₀:ℝ)+d.energyOne=(m:ℝ)+δ ∧
      (p₁:ℝ)+d.energyTwo=(m:ℝ)+δ ∧
      (p₂:ℝ)+d.energyThree=(m:ℝ)+δ := by
  have hc01 : A t.i₀ 0*A t.i₀ 1+A t.i₁ 0*A t.i₁ 1=0 := by
    simpa [t.pair.2.1] using t.offdiag hA (j:=0) (k:=1) (by decide)
  have hc12 : A t.i₀ 1*A t.i₀ 2+A t.i₁ 1*A t.i₁ 2=0 := by
    simpa [t.pair.2.1] using t.offdiag hA (j:=1) (k:=2) (by decide)
  have hp01 : |A t.i₀ 0| * |A t.i₀ 1|=|A t.i₁ 0| * |A t.i₁ 1| := by
    rw [←abs_mul,←abs_mul,show A t.i₀ 0*A t.i₀ 1=-(A t.i₁ 0*A t.i₁ 1) by linarith,abs_neg]
  have hp12 : |A t.i₀ 1| * |A t.i₀ 2|=|A t.i₁ 1| * |A t.i₁ 2| := by
    rw [←abs_mul,←abs_mul,show A t.i₀ 1*A t.i₀ 2=-(A t.i₁ 1*A t.i₁ 2) by linarith,abs_neg]
  have hemid : ((pureColumnRows A 1).card:ℝ)+|A t.i₀ 1|^2+|A t.i₁ 1|^2=(m:ℝ)+δ := by
    simpa [sq_abs,t.pair.2.1] using t.column_energy hA hs 1
  obtain ⟨haeq,hbeq,hceq⟩ := two_full_equal_scale m (pureColumnRows A 1).card
    (abs_pos.mpr (t.full₀ 0)) (abs_pos.mpr (t.full₀ 1)) (abs_pos.mpr (t.full₀ 2))
    (abs_pos.mpr (t.full₁ 0)) (abs_pos.mpr (t.full₁ 1)) (abs_pos.mpr (t.full₁ 2))
    (hs t.i₀) (hs t.i₁) hp01 hp12 hd0 hd1 hemid
  have hprod02 : A t.i₁ 0*A t.i₁ 2=A t.i₀ 0*A t.i₀ 2 :=
    equal_abs_remaining_product (t.full₀ 1) hbeq hc01 hc12
  have hc02 := t.offdiag hA (j:=0) (k:=2) (by decide)
  rw [hprod02] at hc02
  have hp02 : 2*|A t.i₀ 0| * |A t.i₀ 2|=|A t.ip 0| * |A t.ip 2| := by
    have ht : A t.ip 0*A t.ip 2= -2*(A t.i₀ 0*A t.i₀ 2) := by linarith
    rw [←abs_mul,ht,abs_mul,abs_mul]
    norm_num
    ring
  have hpbudget : |A t.ip 0|+|A t.ip 2|=1 := by simpa [t.pair.2.1] using hs t.ip
  let d : TwoFullData := {
    a:=|A t.i₀ 0|, b:=|A t.i₀ 1|, c:=|A t.i₀ 2|,
    g:=|A t.ip 0|, h:=|A t.ip 2|,
    ha:=abs_pos.mpr (t.full₀ 0),hb:=abs_pos.mpr (t.full₀ 1),hc:=abs_pos.mpr (t.full₀ 2),
    hg:=abs_pos.mpr t.pair.1,hh:=abs_pos.mpr t.pair.2.2,
    hsum:=hs t.i₀,hsum':=hpbudget,horth:=hp02 }
  have he0 := t.column_energy hA hs 0
  have he1 := t.column_energy hA hs 1
  have he2 := t.column_energy hA hs 2
  have hs0 : A t.i₁ 0^2=A t.i₀ 0^2 := by rw [←sq_abs (A t.i₁ 0),haeq,sq_abs]
  have hs1 : A t.i₁ 1^2=A t.i₀ 1^2 := by rw [←sq_abs (A t.i₁ 1),hbeq,sq_abs]
  have hs2 : A t.i₁ 2^2=A t.i₀ 2^2 := by rw [←sq_abs (A t.i₁ 2),hceq,sq_abs]
  rw [hs0] at he0
  rw [hs1,t.pair.2.1] at he1
  rw [hs2] at he2
  refine ⟨d,(pureColumnRows A 0).card,(pureColumnRows A 1).card,(pureColumnRows A 2).card,?_,?_,?_,?_⟩
  · have hF : (fullRows A).card=2 := by simp [t.fullSet,t.distinct]
    have hQ : (pairRows A).card=1 := by simp [t.pairSet]
    have ht := pure_pair_full_count A hs
    have hp := pure_column_count A
    omega
  · dsimp [d,TwoFullData.energyOne]
    simp only [sq_abs]
    linarith
  · dsimp [d,TwoFullData.energyTwo]
    simp only [sq_abs]
    linarith
  · dsimp [d,TwoFullData.energyThree]
    simp only [sq_abs]
    linarith

lemma pair_zero_middle_permutation {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ip : ι) (hip : ip∈pairRows A) :
    ∃e : Equiv.Perm (Fin 3),
      permuteColumns A e ip 0≠0 ∧ permuteColumns A e ip 1=0 ∧ permuteColumns A e ip 2≠0 := by
  have ht := (rowSupport_card_cases A ip).2.mp ((mem_pairRows A ip).mp hip)
  rcases ht with h | h | h
  · refine ⟨Equiv.swap 1 2,?_⟩
    simpa [permuteColumns,Equiv.swap_apply_def] using ⟨h.1,h.2.2,h.2.1⟩
  · exact ⟨Equiv.refl _,h⟩
  · refine ⟨Equiv.swap 0 1,?_⟩
    simpa [permuteColumns,Equiv.swap_apply_def] using ⟨h.2.1,h.1,h.2.2⟩

/-- A saturated frame with F=2,Q=1 yields the genuine two-full-row normal form.
Only the fractional isotropy level is used; no multiplier normal form is assumed. -/
theorem two_full_normal_form {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {m : ℕ} {δ : ℝ}
    (hA : Feasible ((m:ℝ)+δ) A)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1)
    (hF : (fullRows A).card=2) (hQ : (pairRows A).card=1)
    (hd0 : 0<δ) (hd1 : δ<1/2) :
    ∃(d : TwoFullData) (p₀ p₁ p₂ : ℕ),
      p₀+p₁+p₂+3=Fintype.card ι ∧
      (p₀:ℝ)+d.energyOne=(m:ℝ)+δ ∧
      (p₁:ℝ)+d.energyTwo=(m:ℝ)+δ ∧
      (p₂:ℝ)+d.energyThree=(m:ℝ)+δ := by
  classical
  obtain ⟨ip,hip⟩ := Finset.card_pos.mp (show 0<(pairRows A).card by omega)
  obtain ⟨e,he⟩ := pair_zero_middle_permutation ip hip
  let B := permuteColumns A e
  have hB := feasible_permuteColumns hA e
  have hBF : (fullRows B).card=2 := by simpa [B] using hF
  have hBQ : (pairRows B).card=1 := by simpa [B] using hQ
  have hiB : ip∈pairRows B := by simpa [B] using hip
  obtain ⟨t⟩ := exists_twoFullSupport hBF hBQ ip hiB he
  exact two_full_fixed_normal_form hB (saturated_permute A hs e) t hd0 hd1

end
end F3
