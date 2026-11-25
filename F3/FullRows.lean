import F3.Exceptional

/-!
# Algebra of full-row normal forms

These statements prove the scalar exclusions used after the manuscript's
full-row classification. They do not assume an optimizer or sharp-value
formula. The combinatorial reduction from an arbitrary frame to these
normal forms is a separate formalization obligation.
-/
namespace F3
noncomputable section
set_option maxHeartbeats 1000000

lemma small_pair_coordinate {a b x : ℝ}
    (ha : 0<a) (hb : 0<b) (hab : a+b<1)
    (hx : 0<x) (hxh : x<1/2) (he : x*(1-x)=a*b) :
    x<a ∧ x<b := by
  have aux : ∀ p q : ℝ, 0<p → 0<q → p+q<1 → x*(1-x)=p*q → x<p := by
    intro p q hp hq hpq heq
    by_contra! hpx
    have h1 := mul_pos hp (show 0<1-p-q by linarith)
    have h2 := mul_nonneg (show 0≤x-p by linarith)
      (show 0≤1-x-p by linarith)
    nlinarith
  exact ⟨aux a b ha hb hab he,aux b a hb ha (by linarith) (by nlinarith [he])⟩

lemma unequal_scale_fraction_excluded (m p : ℕ) {b δ : ℝ}
    (hb0 : 0<b) (hb1 : b<1) (hd0 : 0<δ) (hd1 : δ<1/2)
    (he : (p:ℝ)+b^2+(1-b)^2=(m:ℝ)+δ) : False := by
  have htlo : (1:ℝ)/2 ≤ b^2+(1-b)^2 := by nlinarith [sq_nonneg (b-1/2)]
  have hthi : b^2+(1-b)^2 < 1 := by
    have := mul_pos hb0 (show 0<1-b by linarith)
    nlinarith
  have hpm : (p:ℝ)<m := by linarith
  have hpmNat : p<m := by exact_mod_cast hpm
  have hpm' : (p:ℝ)+1≤m := by exact_mod_cast hpmNat
  linarith

structure OneFullData where
  a : ℝ
  b : ℝ
  c : ℝ
  x : ℝ
  y : ℝ
  z : ℝ
  ha : 0<a
  hb : 0<b
  hc : 0<c
  hx : 0<x
  hy : 0<y
  hz : 0<z
  hsum : a+b+c=1
  hxhalf : x<1/2
  hyhalf : y<1/2
  hzhalf : z<1/2
  hprodxy : x*(1-x)=a*b
  hprodxz : y*(1-y)=a*c
  hprodyz : z*(1-z)=b*c

namespace OneFullData

lemma small_x (d : OneFullData) : d.x<d.a ∧ d.x<d.b :=
  small_pair_coordinate d.ha d.hb (by linarith [d.hsum,d.hc]) d.hx d.hxhalf d.hprodxy
lemma small_y (d : OneFullData) : d.y<d.a ∧ d.y<d.c :=
  small_pair_coordinate d.ha d.hc (by linarith [d.hsum,d.hb]) d.hy d.hyhalf d.hprodxz
lemma small_z (d : OneFullData) : d.z<d.b ∧ d.z<d.c :=
  small_pair_coordinate d.hb d.hc (by linarith [d.hsum,d.ha]) d.hz d.hzhalf d.hprodyz

lemma second_energy_bound (d : OneFullData) :
    d.b^2+d.x^2-2*d.b*d.c-d.z^2 < 2*d.b*(d.b-d.c) := by
  have h := mul_pos (sub_pos.mpr d.small_x.2) (add_pos d.hb d.hx)
  nlinarith [sq_nonneg d.z]

lemma third_energy_bound (d : OneFullData) :
    d.c^2+d.y^2+d.z^2 < 3*d.c^2 := by
  have h1 := mul_pos (sub_pos.mpr d.small_y.2) (add_pos d.hc d.hy)
  have h2 := mul_pos (sub_pos.mpr d.small_z.2) (add_pos d.hc d.hz)
  nlinarith

/-- The one-full-row branch in residue one is below 3/100. -/
theorem residue_one_correction_lt (d : OneFullData) {δ : ℝ}
    (hd : 0<δ)
    (hfirst : δ=3*d.a^2-2*d.a-d.x^2-d.y^2)
    (hsecond : δ=d.b^2+d.x^2-2*d.b*d.c-d.z^2)
    (hthird : δ=d.c^2+d.y^2+d.z^2) : δ<3/100 := by
  have ha : (2:ℝ)/3<d.a := by
    by_contra! h
    have hp := mul_nonneg d.ha.le (show 0≤(2:ℝ)/3-d.a by linarith)
    nlinarith [sq_nonneg d.x,sq_nonneg d.y]
  have hbc : d.b+d.c<1/3 := by linarith [d.hsum]
  have hzsmall : d.z<1/6 := by linarith [d.small_z.1,d.small_z.2]
  have hzc : d.z < (2:ℝ)/5*d.c := by
    have hp := mul_nonneg d.hz.le (show 0≤(1:ℝ)/6-d.z by linarith)
    have hq := mul_pos d.hc (show 0<(1:ℝ)/3-d.b by linarith [d.hc])
    nlinarith [d.hprodyz]
  have hy2 := mul_pos (sub_pos.mpr d.small_y.2) (add_pos d.hc d.hy)
  have hz2 := mul_pos (show 0<(2:ℝ)/5*d.c-d.z by linarith)
    (show 0<(2:ℝ)/5*d.c+d.z by linarith [d.hc,d.hz])
  have hdelta : δ<(54:ℝ)/25*d.c^2 := by nlinarith only [hthird,hy2,hz2]
  by_contra! hlarge
  have hc : (117:ℝ)/1000<d.c := by
    by_contra! h
    have hp := mul_nonneg d.hc.le (show 0≤(117:ℝ)/1000-d.c by linarith)
    nlinarith
  have hb : (193:ℝ)/1000<d.b := by
    by_contra! h
    have hp := mul_nonneg d.hb.le (show 0≤(193:ℝ)/1000-d.b by linarith)
    have hq := mul_pos d.hb (show 0<d.c-(117:ℝ)/1000 by linarith)
    have ht := d.second_energy_bound
    nlinarith
  have hau : d.a<69/100 := by linarith [d.hsum]
  have hbcl : (31:ℝ)/100<d.b+d.c := by linarith
  have hx : (2:ℝ)/3*d.b<d.x := by
    have hp := mul_pos (show 0<d.a-(2:ℝ)/3 by linarith) d.hb
    nlinarith [d.hprodxy,sq_pos_of_pos d.hx]
  have hy : (2:ℝ)/3*d.c<d.y := by
    have hp := mul_pos (show 0<d.a-(2:ℝ)/3 by linarith) d.hc
    nlinarith [d.hprodxz,sq_pos_of_pos d.hy]
  have hx2 := mul_pos (show 0<d.x-(2:ℝ)/3*d.b by linarith)
    (show 0<d.x+(2:ℝ)/3*d.b by linarith [d.hx,d.hb])
  have hy2' := mul_pos (show 0<d.y-(2:ℝ)/3*d.c by linarith)
    (show 0<d.y+(2:ℝ)/3*d.c by linarith [d.hy,d.hc])
  have hbc2 := mul_pos (show 0<d.b+d.c-(31:ℝ)/100 by linarith)
    (show 0<d.b+d.c+(31:ℝ)/100 by linarith [d.hb,d.hc])
  have ha2 := mul_pos (show 0<(69:ℝ)/100-d.a by linarith)
    (show 0<3*((69:ℝ)/100+d.a)-2 by linarith)
  nlinarith only [hfirst,hlarge,hx2,hy2',hbc2,ha2,sq_nonneg (d.b-d.c)]

/-- First pure-count alternative in the residue-two one-full-row branch. -/
theorem residue_two_first_impossible (d : OneFullData) {δ : ℝ}
    (hd : (1:ℝ)/5<δ)
    (hfirst : δ=3*d.a^2-2*d.a-d.x^2-d.y^2)
    (hthird : δ=d.c^2+d.y^2+d.z^2) : False := by
  have ha : (3:ℝ)/4<d.a := by
    by_contra! h
    have hp := mul_nonneg d.ha.le (show 0≤(3:ℝ)/4-d.a by linarith)
    nlinarith [sq_nonneg d.x,sq_nonneg d.y]
  have hc : d.c<1/4 := by linarith [d.hsum,d.hb]
  have hp := mul_nonneg d.hc.le (show 0≤(1:ℝ)/4-d.c by linarith)
  have ht := d.third_energy_bound
  nlinarith

/-- Second pure-count alternative in the residue-two one-full-row branch. -/
theorem residue_two_second_impossible (d : OneFullData) {δ : ℝ}
    (hd : (1:ℝ)/5<δ) (hdu : δ≤4/9)
    (hfirst : δ=1+3*d.a^2-2*d.a-d.x^2-d.y^2)
    (hsecond : δ=d.b^2+d.x^2-2*d.b*d.c-d.z^2)
    (hthird : δ=d.c^2+d.y^2+d.z^2) : False := by
  have hc : (1:ℝ)/4<d.c := by
    by_contra! h
    have hp := mul_nonneg d.hc.le (show 0≤(1:ℝ)/4-d.c by linarith)
    have ht := d.third_energy_bound
    nlinarith
  have hb : (9:ℝ)/20<d.b := by
    by_contra! h
    have hp := mul_nonneg d.hb.le (show 0≤(9:ℝ)/20-d.b by linarith)
    have hq := mul_pos d.hb (show 0<d.c-(1:ℝ)/4 by linarith)
    have ht := d.second_energy_bound
    nlinarith
  have ha : d.a<3/10 := by linarith [d.hsum]
  have hx2 := mul_pos (sub_pos.mpr d.small_x.1) (add_pos d.ha d.hx)
  have hy2 := mul_pos (sub_pos.mpr d.small_y.1) (add_pos d.ha d.hy)
  have hp := mul_pos (show 0<(3:ℝ)/10-d.a by linarith)
    (show 0<(17:ℝ)/10-d.a by linarith)
  nlinarith only [hfirst,hdu,hx2,hy2,hp]

end OneFullData

lemma two_positive_sum_one_squares_lt {g h : ℝ} (hg : 0<g) (hh : 0<h)
    (hs : g+h=1) : g^2+h^2<1 := by
  nlinarith [mul_pos hg hh]

lemma sum_one_squares_ge_half {g h : ℝ} (hs : g+h=1) :
    (1:ℝ)/2≤g^2+h^2 := by
  nlinarith [sq_nonneg (g-h)]

/-- Elementary replacement for the derivative estimates in the last
residue-two full-row case. It proves the same inequalities in the manuscript. -/
lemma two_full_residue_two_component_bounds {x y : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hxs : x^2=1+y^2)
    (hyl : (1:ℝ)/5<y^2) (hyu : y≤2/3) :
    x*(Real.sqrt 2-y)-y < 16/25 ∧
    x-y*(Real.sqrt 2-y) < 18/25 := by
  have hylo : (4:ℝ)/9<y := by
    by_contra! h
    have hp := mul_nonneg hy (show 0≤(4:ℝ)/9-y by linarith)
    nlinarith
  rcases sqrt_two_bounds with ⟨hrlo,hrhi⟩
  have hrupper : Real.sqrt 2 < (10:ℝ)/7 := by
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hxcap : x≤1+y^2/2 := by nlinarith [sq_nonneg (x-1)]
  have hp := mul_nonneg (show 0≤1+y^2/2-x by linarith)
    (show 0≤Real.sqrt 2-y by linarith)
  have hq := mul_nonneg (show 0≤1+y^2/2 by positivity)
    (show 0≤(10:ℝ)/7-Real.sqrt 2 by linarith)
  have hcubic := mul_nonneg (show 0≤y-(4:ℝ)/9 by linarith) (sq_nonneg y)
  have hslope := mul_nonneg (show 0≤y-(4:ℝ)/9 by linarith)
    (show 0≤(10:ℝ)/9-y-(4:ℝ)/9 by linarith)
  constructor
  · nlinarith only [hp,hq,hcubic,hslope,hylo]
  · have hxlinear : x≤1+(31:ℝ)/100*y := by
      by_contra! h
      have ht := mul_pos (show 0<x-(1+(31:ℝ)/100*y) by linarith)
        (show 0<x+(1+(31:ℝ)/100*y) by linarith)
      have hyy := mul_nonneg hy (show 0≤(2:ℝ)/3-y by linarith)
      nlinarith only [ht,hyy,hxs,hy]
    have hprod := mul_nonneg hy (show 0≤Real.sqrt 2-(7:ℝ)/5 by linarith)
    have hint := mul_nonneg (show 0≤y-(4:ℝ)/9 by linarith)
      (show 0≤(2:ℝ)/3-y by linarith)
    nlinarith only [hxlinear,hprod,hint,hyu]

/-- The remaining two-full-row residue-two case is impossible. -/
theorem two_full_residue_two_impossible {x y C S : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hxs : x^2=1+y^2)
    (hyl : (1:ℝ)/5<y^2) (hyu : y≤2/3)
    (hC : C=x*(Real.sqrt 2-y)-y)
    (hS : S=x-y*(Real.sqrt 2-y))
    (hCp : 0<C) (hSp : 0<S) (hcs : C^2+S^2=1) : False := by
  obtain ⟨hc,hs⟩ := two_full_residue_two_component_bounds hx hy hxs hyl hyu
  rw [←hC] at hc
  rw [←hS] at hs
  nlinarith only [hc,hs,hCp,hSp,hcs]


/-- The two full rows in the normal form must have equal magnitudes. -/
theorem two_full_equal_scale (m p : ℕ) {a b c a' b' c' δ : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (ha' : 0<a') (hb' : 0<b') (hc' : 0<c')
    (hs : a+b+c=1) (hs' : a'+b'+c'=1)
    (h12 : a*b=a'*b') (h23 : b*c=b'*c')
    (hd0 : 0<δ) (hd1 : δ<1/2)
    (he : (p:ℝ)+b^2+b'^2=(m:ℝ)+δ) : a'=a ∧ b'=b ∧ c'=c := by
  have hrow := congrArg (fun t : ℝ => t*b) hs
  have hrow' := congrArg (fun t : ℝ => t*b') hs'
  dsimp at hrow hrow'
  have hfactor : (b-b')*(1-b-b')=0 := by nlinarith only [hrow,hrow',h12,h23]
  have hbb : b'=b := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · have hh : b'=1-b := by linarith
      have hbhi : b<1 := by linarith
      rw [hh] at he
      exact False.elim (unequal_scale_fraction_excluded m p hb hbhi hd0 hd1 he)
  subst b'
  have haa : a=a' := mul_right_cancel₀ (ne_of_gt hb) h12
  have hcc : c=c' := mul_left_cancel₀ (ne_of_gt hb) h23
  exact ⟨haa.symm,rfl,hcc.symm⟩

lemma one_full_pure_counts_residue_one {m p₁ p₂ p₃ : ℕ}
    (h₁ : m≤p₁+2) (h₂ : m≤p₂+1) (h₃ : p₃=m)
    (ht : p₁+p₂+p₃+4=3*m+1) :
    p₁+2=m ∧ p₂+1=m ∧ p₃=m := by omega

lemma one_full_pure_counts_residue_two {m p₁ p₂ p₃ : ℕ}
    (h₁ : m≤p₁+2) (h₂ : m≤p₂+1) (h₃ : p₃=m)
    (hu₁ : p₁≤m) (hu₂ : p₂≤m)
    (ht : p₁+p₂+p₃+4=3*m+2) :
    (p₁+2=m ∧ p₂=m) ∨ (p₁+1=m ∧ p₂+1=m) := by omega

lemma two_full_pure_counts_residue_one {m p₁ p₂ p₃ : ℕ}
    (hu₁ : p₁≤m) (hu₂ : p₂≤m) (hu₃ : p₃≤m) (hl₂ : m≤p₂+1)
    (ht : p₁+p₂+p₃+3=3*m+1) :
    (p₂+1=m ∧ ((p₁+1=m ∧ p₃=m) ∨ (p₁=m ∧ p₃+1=m))) ∨
    (p₂=m ∧ ((p₁+1=m ∧ p₃+1=m) ∨ (p₁+2=m ∧ p₃=m) ∨
      (p₁=m ∧ p₃+2=m))) := by omega

lemma two_full_pure_counts_residue_two {m p₁ p₂ p₃ : ℕ}
    (hu₁ : p₁≤m) (hu₂ : p₂≤m) (hu₃ : p₃≤m) (hl₂ : m≤p₂+1)
    (ht : p₁+p₂+p₃+3=3*m+2) :
    (p₂+1=m ∧ p₁=m ∧ p₃=m) ∨
    (p₂=m ∧ ((p₁+1=m ∧ p₃=m) ∨ (p₁=m ∧ p₃+1=m))) := by omega

lemma two_full_rows_need_pair {a b c d e f : ℝ}
    (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (h12 : a*b+d*e=0) (h13 : a*c+d*f=0) (h23 : b*c+e*f=0) : False := by
  have h1 : a*b=-(d*e) := by linarith
  have h2 : a*c=-(d*f) := by linarith
  have h3 : e*f=-(b*c) := by linarith
  have he : a^2*(b*c) = -(d^2*(b*c)) := by
    calc
      _ = (a*b)*(a*c) := by ring
      _ = (-(d*e))*(-(d*f)) := by rw [h1,h2]
      _ = d^2*(e*f) := by ring
      _ = _ := by rw [h3]; ring
  have hz : (a^2+d^2)*(b*c)=0 := by nlinarith only [he]
  have hpos : 0<a^2+d^2 := by nlinarith [sq_pos_of_ne_zero ha,sq_nonneg d]
  exact mul_ne_zero (ne_of_gt hpos) (mul_ne_zero hb hc) hz

/-- Positive parametrization of a two-by-two matrix with orthogonal columns. -/
lemma positive_two_column_parameterization {p q u v x y : ℝ}
    (hp : 0<p) (hq : 0<q) (hu : 0<u) (hv : 0<v)
    (hx : 0<x) (hy : 0<y)
    (ho : p*q=u*v) (h1 : p^2+u^2=x^2) (h2 : q^2+v^2=y^2) :
    ∃ C S : ℝ, 0<C ∧ 0<S ∧ C^2+S^2=1 ∧
      x*C=p ∧ y*S=q ∧ x*S=u ∧ y*C=v := by
  have he : (x*q)^2=(y*u)^2 := by
    calc
      _ = (p^2+u^2)*q^2 := by rw [mul_pow, ←h1]
      _ = (p*q)^2+(u*q)^2 := by ring
      _ = (u*v)^2+(u*q)^2 := by rw [ho]
      _ = u^2*(q^2+v^2) := by ring
      _ = _ := by rw [h2]; ring
  have he' : x*q=y*u := by
    have hr := congrArg Real.sqrt he
    simpa only [Real.sqrt_sq (mul_pos hx hq).le,Real.sqrt_sq (mul_pos hy hu).le] using hr
  have hf : (x*v)^2=(y*p)^2 := by
    calc
      _ = (p^2+u^2)*v^2 := by rw [mul_pow, ←h1]
      _ = (p*v)^2+(u*v)^2 := by ring
      _ = (p*v)^2+(p*q)^2 := by rw [ho]
      _ = p^2*(q^2+v^2) := by ring
      _ = _ := by rw [h2]; ring
  have hf' : x*v=y*p := by
    have hr := congrArg Real.sqrt hf
    simpa only [Real.sqrt_sq (mul_pos hx hv).le,Real.sqrt_sq (mul_pos hy hp).le] using hr
  refine ⟨p/x,u/x,div_pos hp hx,div_pos hu hx,?_,?_,?_,?_,?_⟩
  · field_simp
    nlinarith only [h1]
  · field_simp
  · field_simp
    nlinarith only [he']
  · field_simp
  · field_simp
    nlinarith only [hf']

end
end F3
