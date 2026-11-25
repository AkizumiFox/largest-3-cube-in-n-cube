import F3.OneFullExtraction
import F3.TwoFullExtraction
import F3.Dominance

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem signUnit_mul_of_negative_product {x y : ℝ} (h : x*y<0) :
    Dominance.signUnit x*y= -|y| := by
  by_cases hx : 0≤x
  · have hp : 0<x := lt_of_le_of_ne hx (Ne.symm (left_ne_zero_of_mul (ne_of_lt h)))
    have hy : y<0 := by nlinarith
    simp [Dominance.signUnit,hx,abs_of_neg hy]
  · have hx' : x<0 := lt_of_not_ge hx
    have hy : 0<y := by nlinarith
    simp [Dominance.signUnit,hx,abs_of_pos hy]

theorem signUnit_mul_of_positive_product {x y : ℝ} (h : 0<x*y) :
    Dominance.signUnit x*y=|y| := by
  by_cases hx : 0≤x
  · have hp : 0<x := lt_of_le_of_ne hx (Ne.symm (left_ne_zero_of_mul (ne_of_gt h)))
    have hy : 0<y := by nlinarith
    simp [Dominance.signUnit,hx,abs_of_pos hy]
  · have hx' : x<0 := lt_of_not_ge hx
    have hy : y<0 := by nlinarith
    simp [Dominance.signUnit,hx,abs_of_neg hy]

/-- Literal realized one-full-row normal form. The three scalar signs are
row sign changes, while PairTriple records the actual indices and support. -/
def OneFullWitness {ι : Type*} [Fintype ι] (A : ι → Fin 3 → ℝ) : Prop :=
  ∃ (i₀ : ι) (t : PairTriple A) (d : OneFullData) (u v w : ℝ),
    fullRows A={i₀} ∧ u^2=1 ∧ v^2=1 ∧ w^2=1 ∧
    A i₀=![d.a,d.b,d.c] ∧
    (fun j=>u*A t.i01 j)=![1-d.x,-d.x,0] ∧
    (fun j=>v*A t.i02 j)=![1-d.y,0,-d.y] ∧
    (fun j=>w*A t.i12 j)=![0,1-d.z,-d.z]

theorem one_full_sorted_witness {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (hw : ∀i,0<M.weight i)
    (hF : (fullRows A).card=1) (i₀ : ι) (hi₀ : i₀∈fullRows A)
    (hpos : ∀j,0<A i₀ j) (t : PairTriple A)
    (h01 : M.matrix 0 0≤M.matrix 1 1) (h12 : M.matrix 1 1≤M.matrix 2 2) :
    OneFullWitness A := by
  have hsat := fun i=>M.complementary i (hw i)
  obtain ⟨d,ha,hb,hc,hx,hy,hz⟩ := one_full_sorted_data hA hs hsat M hw hF i₀ hi₀ hpos t h01 h12
  obtain ⟨hp01,hp02,hp12⟩ := one_full_pair_cancellation hA hF i₀ hi₀ t
  have hn01 : A t.i01 0*A t.i01 1<0 := by rw [hp01]; exact neg_neg_of_pos (mul_pos (hpos 0) (hpos 1))
  have hn02 : A t.i02 0*A t.i02 2<0 := by rw [hp02]; exact neg_neg_of_pos (mul_pos (hpos 0) (hpos 2))
  have hn12 : A t.i12 1*A t.i12 2<0 := by rw [hp12]; exact neg_neg_of_pos (mul_pos (hpos 1) (hpos 2))
  have hs01 : |A t.i01 0|=1-d.x := by have h:=hsat t.i01; simp only [t.row01.2.2,abs_zero,add_zero] at h; linarith
  have hs02 : |A t.i02 0|=1-d.y := by have h:=hsat t.i02; simp only [t.row02.2.1,abs_zero,add_zero] at h; linarith
  have hs12 : |A t.i12 1|=1-d.z := by have h:=hsat t.i12; simp only [t.row12.1,abs_zero,zero_add] at h; linarith
  refine ⟨i₀,t,d,Dominance.signUnit (A t.i01 0),Dominance.signUnit (A t.i02 0),
    Dominance.signUnit (A t.i12 1),fullRows_eq_singleton hF i₀ hi₀,
    Dominance.signUnit_sq _,Dominance.signUnit_sq _,Dominance.signUnit_sq _,?_,?_,?_,?_⟩
  · funext j; fin_cases j
    · exact ha.symm
    · exact hb.symm
    · exact hc.symm
  · funext j; fin_cases j
    · change Dominance.signUnit (A t.i01 0)*A t.i01 0=1-d.x
      simpa only [mul_comm,Dominance.signUnit_mul] using hs01
    · change Dominance.signUnit (A t.i01 0)*A t.i01 1= -d.x
      simpa only [hx] using signUnit_mul_of_negative_product hn01
    · change Dominance.signUnit (A t.i01 0)*A t.i01 2=0
      rw [t.row01.2.2,mul_zero]
  · funext j; fin_cases j
    · change Dominance.signUnit (A t.i02 0)*A t.i02 0=1-d.y
      simpa only [mul_comm,Dominance.signUnit_mul] using hs02
    · change Dominance.signUnit (A t.i02 0)*A t.i02 1=0
      rw [t.row02.2.1,mul_zero]
    · change Dominance.signUnit (A t.i02 0)*A t.i02 2= -d.y
      simpa only [hy] using signUnit_mul_of_negative_product hn02
  · funext j; fin_cases j
    · change Dominance.signUnit (A t.i12 1)*A t.i12 0=0
      rw [t.row12.1,mul_zero]
    · change Dominance.signUnit (A t.i12 1)*A t.i12 1=1-d.z
      simpa only [mul_comm,Dominance.signUnit_mul] using hs12
    · change Dominance.signUnit (A t.i12 1)*A t.i12 2= -d.z
      simpa only [hz] using signUnit_mul_of_negative_product hn12


/-- A complete coordinate-level realization of the one-full normal form,
after an actual column permutation and column sign changes. -/
theorem one_full_realized_normal_form {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hsp : 0<s)
    (M : MultiplierSystem A) (hw : ∀i,0<M.weight i)
    (hF : (fullRows A).card=1) (hQ : (pairRows A).card=3) :
    ∃ (e : Equiv.Perm (Fin 3)) (σ : Fin 3 → ℝ),
      (∀j,σ j*σ j=1) ∧ OneFullWitness (signColumns (permuteColumns A e) σ) := by
  classical
  obtain ⟨e,he01,he12⟩ := exists_sorted_columns (fun j => M.matrix j j)
  let B := permuteColumns A e
  let N := M.permuteColumns e
  have hB := feasible_permuteColumns hA e
  have hBF : (fullRows B).card=1 := by simpa [B] using hF
  have hBQ : (pairRows B).card=3 := by simpa [B] using hQ
  obtain ⟨i₀,hi₀⟩ := Finset.card_pos.mp (show 0<(fullRows B).card by omega)
  have hfull := (full_row_iff B i₀).mp hi₀
  let σ : Fin 3 → ℝ := fun j => if B i₀ j<0 then -1 else 1
  have hσ (j : Fin 3) : σ j*σ j=1 := by dsimp [σ]; split_ifs <;> norm_num
  let C := signColumns B σ
  let P := N.signColumns σ hσ
  have hC := feasible_signColumns hB σ hσ
  have hCF : (fullRows C).card=1 := by simpa [C,fullRows_sign B σ hσ] using hBF
  have hCQ : (pairRows C).card=3 := by simpa [C,pairRows_sign B σ hσ] using hBQ
  have hiC : i₀∈fullRows C := by simpa [C,fullRows_sign B σ hσ] using hi₀
  have hwC (i : ι) : 0<P.weight i := hw i
  have hsC (i : ι) : |C i 0|+|C i 1|+|C i 2|=1 := P.complementary i (hwC i)
  have hpos (j : Fin 3) : 0<C i₀ j := by
    dsimp [C,signColumns,σ]
    split_ifs with hj
    · linarith
    · simpa using lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm (hfull j))
  have hsort01 : P.matrix 0 0≤P.matrix 1 1 := by
    change σ 0*σ 0*M.matrix (e 0) (e 0)≤σ 1*σ 1*M.matrix (e 1) (e 1)
    simpa [hσ] using he01
  have hsort12 : P.matrix 1 1≤P.matrix 2 2 := by
    change σ 1*σ 1*M.matrix (e 1) (e 1)≤σ 2*σ 2*M.matrix (e 2) (e 2)
    simpa [hσ] using he12
  obtain ⟨t⟩ := one_full_pair_triple hC hCF hCQ
  exact ⟨e,σ,hσ,one_full_sorted_witness hC hsp P hwC hCF i₀ hiC hpos t hsort01 hsort12⟩

/-- Coordinate-level realization of the two-full normal form, with genuine
support indices, column signs, and row signs. -/
def TwoFullWitness {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Fin 3 → ℝ) : Prop :=
  ∃ (t : TwoFullSupport A) (d : TwoFullData) (σ : Fin 3 → ℝ) (u v : ℝ),
    (∀j,σ j*σ j=1) ∧ u^2=1 ∧ v^2=1 ∧
    (fun j=>σ j*A t.i₀ j)=![d.a,d.b,d.c] ∧
    (fun j=>u*(σ j*A t.i₁ j))=![d.a,-d.b,d.c] ∧
    (fun j=>v*(σ j*A t.ip j))=![d.g,0,-d.h]

theorem two_full_fixed_witness {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Fin 3 → ℝ} {m : ℕ} {δ : ℝ}
    (hA : Feasible ((m:ℝ)+δ) A)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1)
    (t : TwoFullSupport A) (hd0 : 0<δ) (hd1 : δ<1/2) :
    TwoFullWitness A := by
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

  let σ : Fin 3 → ℝ := fun j=>Dominance.signUnit (A t.i₀ j)
  have hσ (j : Fin 3) : σ j*σ j=1 := by
    simpa only [σ,pow_two] using Dominance.signUnit_sq (A t.i₀ j)
  have hx (j : Fin 3) : σ j*A t.i₀ j=|A t.i₀ j| := by
    simpa only [σ,mul_comm] using Dominance.signUnit_mul (A t.i₀ j)
  have habs (i : ι) (j : Fin 3) : |σ j*A i j|=|A i j| := by
    simpa only [σ,mul_comm] using Dominance.abs_mul_signUnit (A i j) (A t.i₀ j)
  have hy01 : (σ 0*A t.i₁ 0)*(σ 1*A t.i₁ 1)<0 := by
    have hh : (σ 0*A t.i₁ 0)*(σ 1*A t.i₁ 1)= -(|A t.i₀ 0| * |A t.i₀ 1|) := by
      calc
        _ = (σ 0*σ 1)*(A t.i₁ 0*A t.i₁ 1) := by ring
        _ = (σ 0*σ 1)*(-(A t.i₀ 0*A t.i₀ 1)) := by congr 1; linarith
        _ = -((σ 0*A t.i₀ 0)*(σ 1*A t.i₀ 1)) := by ring
        _ = _ := by rw [hx,hx]
    rw [hh]
    exact neg_neg_of_pos (mul_pos (abs_pos.mpr (t.full₀ 0)) (abs_pos.mpr (t.full₀ 1)))
  have hy02 : 0<(σ 0*A t.i₁ 0)*(σ 2*A t.i₁ 2) := by
    have hh : (σ 0*A t.i₁ 0)*(σ 2*A t.i₁ 2)=|A t.i₀ 0| * |A t.i₀ 2| := by
      calc
        _ = (σ 0*σ 2)*(A t.i₁ 0*A t.i₁ 2) := by ring
        _ = (σ 0*σ 2)*(A t.i₀ 0*A t.i₀ 2) := by rw [hprod02]
        _ = (σ 0*A t.i₀ 0)*(σ 2*A t.i₀ 2) := by ring
        _ = _ := by rw [hx,hx]
    rw [hh]
    exact mul_pos (abs_pos.mpr (t.full₀ 0)) (abs_pos.mpr (t.full₀ 2))
  have hz02 : (σ 0*A t.ip 0)*(σ 2*A t.ip 2)<0 := by
    have hh : (σ 0*A t.ip 0)*(σ 2*A t.ip 2)= -2*(|A t.i₀ 0| * |A t.i₀ 2|) := by
      calc
        _ = (σ 0*σ 2)*(A t.ip 0*A t.ip 2) := by ring
        _ = (σ 0*σ 2)*(-2*(A t.i₀ 0*A t.i₀ 2)) := by congr 1; linarith
        _ = -2*((σ 0*A t.i₀ 0)*(σ 2*A t.i₀ 2)) := by ring
        _ = _ := by rw [hx,hx]
    rw [hh]
    have hp := mul_pos (abs_pos.mpr (t.full₀ 0)) (abs_pos.mpr (t.full₀ 2))
    linarith
  refine ⟨t,d,σ,Dominance.signUnit (σ 0*A t.i₁ 0),Dominance.signUnit (σ 0*A t.ip 0),
    hσ,Dominance.signUnit_sq _,Dominance.signUnit_sq _,?_,?_,?_⟩
  · funext j; fin_cases j <;> exact hx _
  · funext j; fin_cases j
    · change Dominance.signUnit (σ 0*A t.i₁ 0)*(σ 0*A t.i₁ 0)=|A t.i₀ 0|
      rw [mul_comm (Dominance.signUnit _) _,Dominance.signUnit_mul,habs,haeq]
    · change Dominance.signUnit (σ 0*A t.i₁ 0)*(σ 1*A t.i₁ 1)= -|A t.i₀ 1|
      simpa only [habs,hbeq] using signUnit_mul_of_negative_product hy01
    · change Dominance.signUnit (σ 0*A t.i₁ 0)*(σ 2*A t.i₁ 2)=|A t.i₀ 2|
      simpa only [habs,hceq] using signUnit_mul_of_positive_product hy02
  · funext j; fin_cases j
    · change Dominance.signUnit (σ 0*A t.ip 0)*(σ 0*A t.ip 0)=|A t.ip 0|
      rw [mul_comm (Dominance.signUnit _) _,Dominance.signUnit_mul,habs]
    · change Dominance.signUnit (σ 0*A t.ip 0)*(σ 1*A t.ip 1)=0
      rw [t.pair.2.1,mul_zero,mul_zero]
    · change Dominance.signUnit (σ 0*A t.ip 0)*(σ 2*A t.ip 2)= -|A t.ip 2|
      simpa only [habs] using signUnit_mul_of_negative_product hz02

/-- Saturated two-full frames have the literal three mixed rows displayed in
the paper, after column permutation and row/column sign changes. -/
theorem two_full_realized_normal_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Fin 3 → ℝ} {m : ℕ} {δ : ℝ}
    (hA : Feasible ((m:ℝ)+δ) A)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1)
    (hF : (fullRows A).card=2) (hQ : (pairRows A).card=1)
    (hd0 : 0<δ) (hd1 : δ<1/2) :
    ∃e : Equiv.Perm (Fin 3), TwoFullWitness (permuteColumns A e) := by
  classical
  obtain ⟨ip,hip⟩ := Finset.card_pos.mp (show 0<(pairRows A).card by omega)
  obtain ⟨e,he⟩ := pair_zero_middle_permutation ip hip
  let B := permuteColumns A e
  have hB := feasible_permuteColumns hA e
  have hBF : (fullRows B).card=2 := by simpa [B] using hF
  have hBQ : (pairRows B).card=1 := by simpa [B] using hQ
  have hiB : ip∈pairRows B := by simpa [B] using hip
  obtain ⟨t⟩ := exists_twoFullSupport hBF hBQ ip hiB he
  exact ⟨e,two_full_fixed_witness hB (saturated_permute A hs e) t hd0 hd1⟩

end
end F3
