import F3.TwoFull

/-!
# Consequences of the complete scalar normal forms

This module includes the integer pure-row counts. The remaining upstream
obligation is to obtain these forms from an arbitrary maximizing frame.
-/
namespace F3
noncomputable section
set_option maxHeartbeats 1000000

lemma pure_count_le {m p : ℕ} {E δ : ℝ} (hE : 0<E) (hd : δ<1)
    (he : (p:ℝ)+E=(m:ℝ)+δ) : p≤m := by
  have h : (p:ℝ)<m+1 := by linarith
  have hn : p<m+1 := by exact_mod_cast h
  omega

lemma pure_count_lower {m p k : ℕ} {E δ : ℝ} (hE : E<k) (hd : 0<δ)
    (he : (p:ℝ)+E=(m:ℝ)+δ) : m<p+k := by
  have h : (m:ℝ)<p+k := by linarith
  exact_mod_cast h

lemma pure_count_eq {m p : ℕ} {E δ : ℝ} (hE0 : 0<E) (hE1 : E<1)
    (hd0 : 0<δ) (hd1 : δ<1) (he : (p:ℝ)+E=(m:ℝ)+δ) : p=m := by
  have hu := pure_count_le hE0 hd1 he
  have hl := pure_count_lower (k:=1) (by simpa using hE1) hd0 he
  omega

lemma adjusted_diagonal {m p k : ℕ} {E δ : ℝ}
    (hc : p+k=m) (he : (p:ℝ)+E=(m:ℝ)+δ) : E=(k:ℝ)+δ := by
  have hcr : (p:ℝ)+(k:ℝ)=(m:ℝ) := by exact_mod_cast hc
  linarith

namespace OneFullData

def energyOne (d : OneFullData) : ℝ := d.a^2+(1-d.x)^2+(1-d.y)^2
def energyTwo (d : OneFullData) : ℝ := d.b^2+d.x^2+(1-d.z)^2
def energyThree (d : OneFullData) : ℝ := d.c^2+d.y^2+d.z^2

lemma energy_bounds (d : OneFullData) :
    0<d.energyOne ∧ d.energyOne<3 ∧ 0<d.energyTwo ∧ d.energyTwo<2 ∧
    0<d.energyThree ∧ d.energyThree<1 := by
  have ha1 : d.a<1 := by linarith [d.hsum,d.hb,d.hc]
  have hb1 : d.b<1 := by linarith [d.hsum,d.ha,d.hc]
  have hc1 : d.c<1 := by linarith [d.hsum,d.ha,d.hb]
  have hax := mul_pos d.ha (show 0<1-d.a by linarith)
  have hx := mul_pos d.hx (show 0<1-d.x by linarith [d.hxhalf])
  have hy := mul_pos d.hy (show 0<1-d.y by linarith [d.hyhalf])
  have hz := mul_pos d.hz (show 0<1-d.z by linarith [d.hzhalf])
  have hx' := mul_pos d.hx (show 0<1-2*d.x by linarith [d.hxhalf])
  have hy' := mul_pos d.hy (show 0<1-2*d.y by linarith [d.hyhalf])
  have hz' := mul_pos d.hz (show 0<1-2*d.z by linarith [d.hzhalf])
  have hsumb := congrArg (fun t : ℝ => d.b*t) d.hsum
  have hsumc := congrArg (fun t : ℝ => d.c*t) d.hsum
  dsimp at hsumb hsumc
  dsimp [energyOne,energyTwo,energyThree]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · nlinarith only [sq_pos_of_pos d.ha,sq_nonneg (1-d.x),sq_nonneg (1-d.y)]
  · have hp := mul_pos (show 0<1-d.a by linarith) (show 0<1+d.a by linarith [d.ha])
    have hq := mul_pos d.hx (show 0<2-d.x by linarith [d.hxhalf])
    have hr := mul_pos d.hy (show 0<2-d.y by linarith [d.hyhalf])
    nlinarith only [hp,hq,hr]
  · nlinarith only [sq_pos_of_pos d.hb,sq_nonneg d.x,sq_nonneg (1-d.z)]
  · have hbc := mul_pos d.hb d.hc
    have hz1 := mul_pos d.hz (show 0<2-d.z by linarith [d.hzhalf])
    nlinarith only [hx',d.hprodxy,hsumb,hbc,hz1,hb1]
  · nlinarith only [sq_pos_of_pos d.hc,sq_nonneg d.y,sq_nonneg d.z]
  · nlinarith only [hy',hz',d.hprodxz,d.hprodyz,hsumc,hc1]

lemma diagonal_identities (d : OneFullData) :
    d.energyOne=2+3*d.a^2-2*d.a-d.x^2-d.y^2 ∧
    d.energyTwo=1+d.b^2+d.x^2-2*d.b*d.c-d.z^2 := by
  have hsuma := congrArg (fun t : ℝ => d.a*t) d.hsum
  dsimp at hsuma
  dsimp [energyOne,energyTwo]
  constructor
  · nlinarith only [hsuma,d.hprodxy,d.hprodxz]
  · nlinarith only [d.hprodyz]

/-- Full consequence of the first-residue one-full-row normal form,
including the pure-row count obstruction at m=1. -/
theorem residue_one (d : OneFullData) {m p₁ p₂ p₃ : ℕ} {δ : ℝ}
    (hd0 : 0<δ) (hd1 : δ<1)
    (ht : p₁+p₂+p₃+4=3*m+1)
    (he₁ : (p₁:ℝ)+d.energyOne=(m:ℝ)+δ)
    (he₂ : (p₂:ℝ)+d.energyTwo=(m:ℝ)+δ)
    (he₃ : (p₃:ℝ)+d.energyThree=(m:ℝ)+δ) :
    2≤m ∧ δ<3/100 := by
  obtain ⟨h10,h11,h20,h21,h30,h31⟩ := d.energy_bounds
  have hp₃ := pure_count_eq h30 h31 hd0 hd1 he₃
  have hp₁ := pure_count_lower (k:=3) (by simpa using h11) hd0 he₁
  have hp₂ := pure_count_lower (k:=2) (by simpa using h21) hd0 he₂
  obtain ⟨hc₁,hc₂,hc₃⟩ := one_full_pure_counts_residue_one (by omega) (by omega) hp₃ ht
  have h1 := adjusted_diagonal hc₁ he₁
  have h2 := adjusted_diagonal hc₂ he₂
  have h3 := adjusted_diagonal (k:=0) (by omega) he₃
  obtain ⟨hi₁,hi₂⟩ := d.diagonal_identities
  refine ⟨by omega,d.residue_one_correction_lt hd0 ?_ ?_ ?_⟩
  · norm_num at h1
    linarith
  · norm_num at h2
    linarith
  · simpa [energyThree] using h3.symm

/-- No one-full-row normal form is feasible in the relevant residue-two range. -/
theorem residue_two_impossible (d : OneFullData) {m p₁ p₂ p₃ : ℕ} {δ : ℝ}
    (hdl : (1:ℝ)/5<δ) (hdu : δ≤4/9)
    (ht : p₁+p₂+p₃+4=3*m+2)
    (he₁ : (p₁:ℝ)+d.energyOne=(m:ℝ)+δ)
    (he₂ : (p₂:ℝ)+d.energyTwo=(m:ℝ)+δ)
    (he₃ : (p₃:ℝ)+d.energyThree=(m:ℝ)+δ) : False := by
  have hd0 : 0<δ := by linarith
  have hd1 : δ<1 := by linarith
  obtain ⟨h10,h11,h20,h21,h30,h31⟩ := d.energy_bounds
  have hp₃ := pure_count_eq h30 h31 hd0 hd1 he₃
  have hp₁ := pure_count_lower (k:=3) (by simpa using h11) hd0 he₁
  have hp₂ := pure_count_lower (k:=2) (by simpa using h21) hd0 he₂
  have hu₁ := pure_count_le h10 hd1 he₁
  have hu₂ := pure_count_le h20 hd1 he₂
  have h3 := adjusted_diagonal (k:=0) (by omega) he₃
  obtain ⟨hi₁,hi₂⟩ := d.diagonal_identities
  rcases one_full_pure_counts_residue_two (by omega) (by omega) hp₃ hu₁ hu₂ ht with h | h
  · have h1 := adjusted_diagonal h.1 he₁
    apply d.residue_two_first_impossible hdl
    · norm_num at h1
      linarith
    · simpa [energyThree] using h3.symm
  · have h1 := adjusted_diagonal h.1 he₁
    have h2 := adjusted_diagonal h.2 he₂
    apply d.residue_two_second_impossible hdl hdu
    · norm_num at h1
      linarith
    · norm_num at h2
      linarith
    · simpa [energyThree] using h3.symm

end OneFullData

namespace TwoFullData

def swap (d : TwoFullData) : TwoFullData where
  a := d.c
  b := d.b
  c := d.a
  g := d.h
  h := d.g
  ha := d.hc
  hb := d.hb
  hc := d.ha
  hg := d.hh
  hh := d.hg
  hsum := by linarith [d.hsum]
  hsum' := by linarith [d.hsum']
  horth := by nlinarith only [d.horth]

def energyOne (d : TwoFullData) : ℝ := 2*d.a^2+d.g^2
def energyTwo (d : TwoFullData) : ℝ := 2*d.b^2
def energyThree (d : TwoFullData) : ℝ := 2*d.c^2+d.h^2

lemma energy_bounds (d : TwoFullData) :
    0<d.energyOne ∧ 0<d.energyTwo ∧ d.energyTwo<2 ∧ 0<d.energyThree := by
  have hb1 : d.b<1 := by linarith [d.hsum,d.ha,d.hc]
  dsimp [energyOne,energyTwo,energyThree]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [sq_pos_of_pos d.ha,sq_nonneg d.g]
  · exact mul_pos (by norm_num) (sq_pos_of_pos d.hb)
  · nlinarith [mul_pos (show 0<1-d.b by linarith) (show 0<1+d.b by linarith [d.hb])]
  · nlinarith only [sq_pos_of_pos d.hc,sq_nonneg d.h]

/-- The complete two-full-row normal form in residue one gives exactly one
of the two exceptional corrections. This includes all pure-count alternatives. -/
theorem residue_one (d : TwoFullData) {m p₁ p₂ p₃ : ℕ} {δ : ℝ}
    (hd : 0<δ) (hdu : δ≤72/1000)
    (ht : p₁+p₂+p₃+3=3*m+1)
    (he₁ : (p₁:ℝ)+d.energyOne=(m:ℝ)+δ)
    (he₂ : (p₂:ℝ)+d.energyTwo=(m:ℝ)+δ)
    (he₃ : (p₃:ℝ)+d.energyThree=(m:ℝ)+δ) :
    δ=firstExceptionalRoot^2 ∨ (2≤m ∧ δ=secondExceptionalRoot^2) := by
  have hd1 : δ<1 := by linarith
  obtain ⟨h10,h20,h21,h30⟩ := d.energy_bounds
  have hu₁ := pure_count_le h10 hd1 he₁
  have hu₂ := pure_count_le h20 hd1 he₂
  have hu₃ := pure_count_le h30 hd1 he₃
  have hl₂ := pure_count_lower (k:=2) (by simpa using h21) hd he₂
  have hE₁ {k : ℕ} (hk : p₁+k=m) : 2*d.a^2+d.g^2=(k:ℝ)+δ := by
    simpa [energyOne] using adjusted_diagonal hk he₁
  have hE₂ {k : ℕ} (hk : p₂+k=m) : 2*d.b^2=(k:ℝ)+δ := by
    simpa [energyTwo] using adjusted_diagonal hk he₂
  have hE₃ {k : ℕ} (hk : p₃+k=m) : 2*d.c^2+d.h^2=(k:ℝ)+δ := by
    simpa [energyThree] using adjusted_diagonal hk he₃
  rcases two_full_pure_counts_residue_one hu₁ hu₂ hu₃ (by omega) ht with
    ⟨hc₂,hcase⟩ | ⟨hc₂,hcase⟩
  · rcases hcase with ⟨hc₁,hc₃⟩ | ⟨hc₁,hc₃⟩
    · exact Or.inl (d.residue_one_first hd hdu (by simpa using hE₁ hc₁)
        (by simpa using hE₂ hc₂) (by simpa using hE₃ (k:=0) (by omega)))
    · exact Or.inl (d.swap.residue_one_first hd hdu
        (by simpa [swap] using hE₃ hc₃) (by simpa [swap] using hE₂ hc₂)
        (by simpa [swap] using hE₁ (k:=0) (by omega)))
  · rcases hcase with ⟨hc₁,hc₃⟩ | ⟨hc₁,hc₃⟩ | ⟨hc₁,hc₃⟩
    · exact False.elim (d.residue_one_equal_columns_impossible hd
        (by simpa using hE₁ hc₁) (by simpa using hE₃ hc₃))
    · exact Or.inr ⟨by omega,d.residue_one_second hd hdu (by simpa using hE₁ hc₁)
        (by simpa using hE₂ (k:=0) (by omega)) (by simpa using hE₃ (k:=0) (by omega))⟩
    · exact Or.inr ⟨by omega,d.swap.residue_one_second hd hdu
        (by simpa [swap] using hE₃ hc₃) (by simpa [swap] using hE₂ (k:=0) (by omega))
        (by simpa [swap] using hE₁ (k:=0) (by omega))⟩

/-- All pure-count alternatives in the two-full-row second-residue form
are impossible in the optimizer's proved correction range. -/
theorem residue_two_impossible (d : TwoFullData) {m p₁ p₂ p₃ : ℕ} {δ : ℝ}
    (hdl : (1:ℝ)/5<δ) (hdu : δ≤4/9)
    (ht : p₁+p₂+p₃+3=3*m+2)
    (he₁ : (p₁:ℝ)+d.energyOne=(m:ℝ)+δ)
    (he₂ : (p₂:ℝ)+d.energyTwo=(m:ℝ)+δ)
    (he₃ : (p₃:ℝ)+d.energyThree=(m:ℝ)+δ) : False := by
  have hd : 0<δ := by linarith
  have hd1 : δ<1 := by linarith
  obtain ⟨h10,h20,h21,h30⟩ := d.energy_bounds
  have hu₁ := pure_count_le h10 hd1 he₁
  have hu₂ := pure_count_le h20 hd1 he₂
  have hu₃ := pure_count_le h30 hd1 he₃
  have hl₂ := pure_count_lower (k:=2) (by simpa using h21) hd he₂
  have hE₁ {k : ℕ} (hk : p₁+k=m) : 2*d.a^2+d.g^2=(k:ℝ)+δ := by
    simpa [energyOne] using adjusted_diagonal hk he₁
  have hE₂ {k : ℕ} (hk : p₂+k=m) : 2*d.b^2=(k:ℝ)+δ := by
    simpa [energyTwo] using adjusted_diagonal hk he₂
  have hE₃ {k : ℕ} (hk : p₃+k=m) : 2*d.c^2+d.h^2=(k:ℝ)+δ := by
    simpa [energyThree] using adjusted_diagonal hk he₃
  rcases two_full_pure_counts_residue_two hu₁ hu₂ hu₃ (by omega) ht with
    ⟨hc₂,hc₁,hc₃⟩ | ⟨hc₂,hcase⟩
  · exact d.residue_two_equal_columns_impossible hd (by linarith)
      (by simpa using hE₁ (k:=0) (by omega)) (by simpa using hE₃ (k:=0) (by omega))
  · rcases hcase with ⟨hc₁,hc₃⟩ | ⟨hc₁,hc₃⟩
    · exact d.residue_two_unequal_columns_impossible hdl hdu
        (by simpa using hE₁ hc₁) (by simpa using hE₂ (k:=0) (by omega))
        (by simpa using hE₃ (k:=0) (by omega))
    · exact d.swap.residue_two_unequal_columns_impossible hdl hdu
        (by simpa [swap] using hE₃ hc₃) (by simpa [swap] using hE₂ (k:=0) (by omega))
        (by simpa [swap] using hE₁ (k:=0) (by omega))

end TwoFullData
end
end F3
