import F3.FullRowExtraction

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

lemma PairTriple.pairRows_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Fin 3 → ℝ}
    (t : PairTriple A) : pairRows A={t.i01,t.i02,t.i12} := by
  classical
  ext i
  simp [t.exhaustive i]

lemma fullRows_eq_singleton {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (hF : (fullRows A).card=1) (i₀ : ι) (hi₀ : i₀∈fullRows A) :
    fullRows A={i₀} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hi₀,?_⟩
  intro i hi
  exact Finset.card_le_one.mp (by omega) i hi i₀ hi₀

lemma one_full_mixed_energy {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (hF : (fullRows A).card=1) (i₀ : ι) (hi₀ : i₀∈fullRows A)
    (t : PairTriple A) (j : Fin 3) :
    (∑i∈pairRows A,A i j^2)+(∑i∈fullRows A,A i j^2)=
      A i₀ j^2+A t.i01 j^2+A t.i02 j^2+A t.i12 j^2 := by
  classical
  rw [t.pairRows_eq,fullRows_eq_singleton hF i₀ hi₀]
  simp [t.distinct.1,t.distinct.2.1,t.distinct.2.2]
  ring

lemma one_full_sorted_normal_form {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hsp : 0<s)
    (hs : ∀i,|A i 0|+|A i 1|+|A i 2|=1)
    (M : MultiplierSystem A) (hw : ∀i,0<M.weight i)
    (hF : (fullRows A).card=1) (hQ : (pairRows A).card=3)
    (i₀ : ι) (hi₀ : i₀∈fullRows A) (hpos : ∀j,0<A i₀ j)
    (h01 : M.matrix 0 0≤M.matrix 1 1) (h12 : M.matrix 1 1≤M.matrix 2 2) :
    ∃(d : OneFullData) (p₀ p₁ p₂ : ℕ),
      p₀+p₁+p₂+4=Fintype.card ι ∧
      (p₀:ℝ)+d.energyOne=s ∧ (p₁:ℝ)+d.energyTwo=s ∧ (p₂:ℝ)+d.energyThree=s := by
  classical
  obtain ⟨t⟩ := one_full_pair_triple hA hF hQ
  obtain ⟨d,ha,hb,hc,hx,hy,hz⟩ := one_full_sorted_data hA hsp hs M hw hF i₀ hi₀ hpos t h01 h12
  have he (j : Fin 3) : ((pureColumnRows A j).card:ℝ)+
      (A i₀ j^2+A t.i01 j^2+A t.i02 j^2+A t.i12 j^2)=s := by
    have hg : (∑i,A i j^2)=s := by simpa [pow_two] using hA.2 j j
    rw [column_energy_partition A hs j,pure_column_energy A hs j,
      add_assoc,one_full_mixed_energy hF i₀ hi₀ t j] at hg
    exact hg
  have hb01 : |A t.i01 0|+|A t.i01 1|=1 := by simpa [t.row01.2.2] using hs t.i01
  have hb02 : |A t.i02 0|+|A t.i02 2|=1 := by simpa [t.row02.2.1] using hs t.i02
  have hb12 : |A t.i12 1|+|A t.i12 2|=1 := by simpa [t.row12.1] using hs t.i12
  have h01a : A t.i01 0^2=(1-d.x)^2 := by
    rw [←sq_abs (A t.i01 0)]
    congr 1
    linarith
  have h02a : A t.i02 0^2=(1-d.y)^2 := by
    rw [←sq_abs (A t.i02 0)]
    congr 1
    linarith
  have h12b : A t.i12 1^2=(1-d.z)^2 := by
    rw [←sq_abs (A t.i12 1)]
    congr 1
    linarith
  have h01b : A t.i01 1^2=d.x^2 := by rw [hx,sq_abs]
  have h02c : A t.i02 2^2=d.y^2 := by rw [hy,sq_abs]
  have h12c : A t.i12 2^2=d.z^2 := by rw [hz,sq_abs]
  refine ⟨d,(pureColumnRows A 0).card,(pureColumnRows A 1).card,(pureColumnRows A 2).card,?_,?_,?_,?_⟩
  · have ht := pure_pair_full_count A hs
    have hp := pure_column_count A
    omega
  · have ht := he 0
    simpa [OneFullData.energyOne,←ha,h01a,h02a,t.row12.1] using ht
  · have ht := he 1
    simpa [OneFullData.energyTwo,←hb,h01b,h12b,t.row02.2.1] using ht
  · have ht := he 2
    simpa [OneFullData.energyThree,←hc,h02c,h12c,t.row01.2.2] using ht

/-- Actual one-full-row extraction, including sign changes and diagonal sorting. -/
theorem one_full_normal_form {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hsp : 0<s)
    (M : MultiplierSystem A) (hw : ∀i,0<M.weight i)
    (hF : (fullRows A).card=1) (hQ : (pairRows A).card=3) :
    ∃(d : OneFullData) (p₀ p₁ p₂ : ℕ),
      p₀+p₁+p₂+4=Fintype.card ι ∧
      (p₀:ℝ)+d.energyOne=s ∧ (p₁:ℝ)+d.energyTwo=s ∧ (p₂:ℝ)+d.energyThree=s := by
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
  exact one_full_sorted_normal_form hC hsp hsC P hwC hCF hCQ i₀ hiC hpos hsort01 hsort12

end
end F3
