import F3.ColumnBounds
import F3.ActiveRows

/-! The two-coordinate zero-weight row is excluded by two integer count
alternatives.  The proof does not require a classification of dominant rows. -/

namespace F3
noncomputable section
open scoped BigOperators

def thirdPairMass {n : ℕ} (A : Fin n → Fin 3 → ℝ) (r : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.erase r, |A i 2| *(|A i 0|+|A i 1|)

theorem saturated_row_defect {a : Fin 3 → ℝ}
    (hs : |a 0|+|a 1|+|a 2|=1) :
    rowDefect a = 2*(|a 0| *|a 1|)+2*(|a 2| *(|a 0|+|a 1|)) := by
  have he : (|a 0|+|a 1|+|a 2|)^2=1 := by rw [hs]; norm_num
  simp only [rowDefect,rowEnergy,Fin.sum_univ_three]
  nlinarith [sq_abs (a 0),sq_abs (a 1),sq_abs (a 2)]

theorem two_coordinate_kernel_mass_identity {m : ℕ} {d t : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (r : Fin (3*m+2))
    (hr0 : A r 0=t) (hr1 : A r 1=t) (hr2 : A r 2=0)
    (hsat : ∀ i, i≠r → |A i 0|+|A i 1|+|A i 2|=1)
    (hprod : ∀ i, i≠r → A i 0*A i 1≤0) :
    2*thirdPairMass A r=1-3*d := by
  classical
  have hcross := hA.2 0 1
  norm_num at hcross
  have hcrossErase := Finset.sum_erase_add Finset.univ
    (fun i => A i 0*A i 1) (Finset.mem_univ r)
  dsimp only at hcrossErase
  rw [hcross,hr0,hr1] at hcrossErase
  have habs : (∑ i ∈ Finset.univ.erase r, |A i 0| *|A i 1|)=t^2 := by
    have he : (∑ i ∈ Finset.univ.erase r, |A i 0| *|A i 1|)=
        -(∑ i ∈ Finset.univ.erase r, A i 0*A i 1) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← abs_mul,abs_of_nonpos (hprod i (Finset.mem_erase.mp hi).1)]
    rw [he]
    nlinarith
  have heach (i : Fin (3*m+2)) (hi : i ∈ Finset.univ.erase r) :=
    saturated_row_defect (hsat i (Finset.mem_erase.mp hi).1)
  have hrest : (∑ i ∈ Finset.univ.erase r, rowDefect (A i))=
      2*t^2+2*thirdPairMass A r := by
    rw [Finset.sum_congr rfl heach]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,habs,thirdPairMass]
  have hrdef : rowDefect (A r)=1-2*t^2 := by
    simp only [rowDefect,rowEnergy,Fin.sum_univ_three,hr0,hr1,hr2]
    ring
  have htotal := Finset.sum_erase_add Finset.univ
    (fun i => rowDefect (A i)) (Finset.mem_univ r)
  dsimp only at htotal
  rw [hrest,hrdef,total_rowDefect hA] at htotal
  push_cast at htotal
  linarith

theorem two_coordinate_kernel_energy_bounds {m : ℕ} {d t : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (r : Fin (3*m+2))
    (hr0 : A r 0=t) (hr1 : A r 1=t) (hr2 : A r 2=0)
    (hsat : ∀ i, i≠r → |A i 0|+|A i 1|+|A i 2|=1)
    (hprod : ∀ i, i≠r → A i 0*A i 1≤0) :
    ∃ p : ℕ, (m : ℝ)+d ≤ p+thirdPairMass A r ∧
      2*((m : ℝ)+d) ≤ 3*m+1-p+thirdPairMass A r := by
  classical
  let T := Finset.univ.erase r
  let p : ℕ := (T.filter (fun i => 1/2< |A i 2|)).card
  have hcount : (∑ i ∈ T, if 1/2< |A i 2| then (1 : ℝ) else 0)=(p : ℝ) := by
    simp [p,Finset.sum_ite]
  have hcompl : (∑ i ∈ T, if 1/2< |A i 2| then (0 : ℝ) else 1)=3*m+1-(p : ℝ) := by
    have he : (∑ i ∈ T, if 1/2< |A i 2| then (1 : ℝ) else 0)+
        (∑ i ∈ T, if 1/2< |A i 2| then (0 : ℝ) else 1)=(T.card : ℝ) := by
      rw [← Finset.sum_add_distrib]
      simp only [ite_add_ite,add_zero,zero_add,ite_self,Finset.sum_const,
        nsmul_eq_mul,mul_one]
    have hc : T.card=3*m+1 := by simp [T]
    rw [hcount,hc] at he
    push_cast at he
    linarith
  have hthird : (∑ i ∈ T, (A i 2)^2)=(m : ℝ)+d := by
    have he := Finset.sum_erase_add Finset.univ (fun i => (A i 2)^2) (Finset.mem_univ r)
    dsimp only at he
    have hg : (∑ i, (A i 2)^2)=(m : ℝ)+d := by simpa [pow_two] using hA.2 2 2
    rw [hr2,zero_pow (by decide : (2 : ℕ)≠0),add_zero,hg] at he
    exact he
  have hpair : (∑ i ∈ T, (|A i 0|+|A i 1|)^2)=2*((m : ℝ)+d) := by
    have hgram0 : (∑ i, (A i 0)^2)=(m : ℝ)+d := by simpa [pow_two] using hA.2 0 0
    have hgram1 : (∑ i, (A i 1)^2)=(m : ℝ)+d := by simpa [pow_two] using hA.2 1 1
    have he0 := Finset.sum_erase_add Finset.univ (fun i => (A i 0)^2) (Finset.mem_univ r)
    have he1 := Finset.sum_erase_add Finset.univ (fun i => (A i 1)^2) (Finset.mem_univ r)
    dsimp only at he0 he1
    rw [hr0,hgram0] at he0
    rw [hr1,hgram1] at he1
    have he01 := Finset.sum_erase_add Finset.univ (fun i => A i 0*A i 1) (Finset.mem_univ r)
    dsimp only at he01
    have hg01 : (∑ i, A i 0*A i 1)=0 := by simpa using hA.2 0 1
    rw [hr0,hr1,hg01] at he01
    have hexp : (∑ i ∈ T, (|A i 0|+|A i 1|)^2)=
        (∑ i ∈ T, (A i 0)^2)+(∑ i ∈ T, (A i 1)^2)-
          2*(∑ i ∈ T, A i 0*A i 1) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have habs : |A i 0| *|A i 1|= -(A i 0*A i 1) := by
        rw [← abs_mul,abs_of_nonpos (hprod i (Finset.mem_erase.mp hi).1)]
      nlinarith [sq_abs (A i 0),sq_abs (A i 1)]
    rw [hexp]
    dsimp [T] at *
    nlinarith
  have hsmall (i : Fin (3*m+2)) (hi : i ∈ T) :
      (A i 2)^2 ≤ (if 1/2< |A i 2| then (1 : ℝ) else 0)+
        |A i 2| *(|A i 0|+|A i 1|) := by
    have hs := hsat i (Finset.mem_erase.mp hi).1
    have hc := abs_nonneg (A i 2)
    have hab : 0≤|A i 0|+|A i 1| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    by_cases hbig : 1/2< |A i 2|
    · rw [if_pos hbig]
      have he := Dominance.entry_sq_le_one (Dominance.feasibleK_three_iff.mpr hA) i 2
      nlinarith [mul_nonneg hc hab]
    · rw [if_neg hbig]
      have hb := le_of_not_gt hbig
      nlinarith [sq_abs (A i 2)]
  have hlarge (i : Fin (3*m+2)) (hi : i ∈ T) :
      (|A i 0|+|A i 1|)^2 ≤ (if 1/2< |A i 2| then (0 : ℝ) else 1)+
        |A i 2| *(|A i 0|+|A i 1|) := by
    have hs := hsat i (Finset.mem_erase.mp hi).1
    have hc := abs_nonneg (A i 2)
    have hab : 0≤|A i 0|+|A i 1| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    by_cases hbig : 1/2< |A i 2|
    · rw [if_pos hbig]
      nlinarith
    · rw [if_neg hbig]
      have hb : |A i 0|+|A i 1|≤1 := by linarith
      nlinarith [mul_nonneg hc hab]
  have hsumSmall := Finset.sum_le_sum hsmall
  have hsumLarge := Finset.sum_le_sum hlarge
  rw [hthird,Finset.sum_add_distrib,hcount] at hsumSmall
  rw [hpair,Finset.sum_add_distrib,hcompl] at hsumLarge
  exact ⟨p,hsumSmall,hsumLarge⟩

theorem two_coordinate_kernel_upper {m : ℕ} {d t : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (r : Fin (3*m+2))
    (hr0 : A r 0=t) (hr1 : A r 1=t) (hr2 : A r 2=0)
    (hsat : ∀ i, i≠r → |A i 0|+|A i 1|+|A i 2|=1)
    (hprod : ∀ i, i≠r → A i 0*A i 1≤0) : d≤1/5 := by
  have hmass := two_coordinate_kernel_mass_identity hA r hr0 hr1 hr2 hsat hprod
  obtain ⟨p,hsmall,hlarge⟩ := two_coordinate_kernel_energy_bounds hA r hr0 hr1 hr2 hsat hprod
  by_cases hp : p≤m
  · have hp' : (p : ℝ)≤m := by exact_mod_cast hp
    linarith
  · have hp' : (m : ℝ)+1≤p := by exact_mod_cast (show m+1≤p by omega)
    linarith

theorem subgradient_opposite_pair {a g : Fin 3 → ℝ}
    (hg : RowSubgradient a g) (horth : g 0+g 1=0) : a 0*a 1≤0 := by
  by_cases hzero : a 0=0
  · simp [hzero]
  have hgsq : (g 0)^2=1 := by
    have ha := subgradient_coordinate_abs_one hg 0 hzero
    nlinarith [sq_abs (g 0)]
  have hg1 : g 1= -g 0 := by linarith
  have he : a 0*a 1= -(a 0*g 0)*(a 1*g 1) := by
    rw [hg1]
    calc
      a 0*a 1=(a 0*a 1)*(g 0)^2 := by rw [hgsq,mul_one]
      _ = _ := by ring
  rw [he,hg.2 0,hg.2 1]
  nlinarith [mul_nonneg (abs_nonneg (a 0)) (abs_nonneg (a 1))]

theorem no_two_coordinate_zero_weight {m : ℕ} {d t : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (hd : 1/5<d) (M : MultiplierSystem A)
    (r : Fin (3*m+2)) (hwr : M.weight r=0)
    (hw : ∀ i, i≠r → 0<M.weight i)
    (ht : 0<t) (hr0 : A r 0=t) (hr1 : A r 1=t) (hr2 : A r 2=0) : False := by
  have hsat (i) (hi : i≠r) := M.complementary i (hw i hi)
  have hprod (i) (hi : i≠r) : A i 0*A i 1≤0 := by
    have ho := positive_gradient_orthogonal M
      (zero_weight_row_kernel M r hwr) i (hw i hi)
    simp only [Fin.sum_univ_three,hr0,hr1,hr2,mul_zero,add_zero] at ho
    have hg : M.gradient i 0+M.gradient i 1=0 := by nlinarith
    exact subgradient_opposite_pair (M.subgradient i) hg
  have hbound := two_coordinate_kernel_upper hA r hr0 hr1 hr2 hsat hprod
  linarith

end
end F3
