import F3.FullRows

/-! Exact identification of the two-full-row residue-one normal forms. -/
namespace F3
noncomputable section
set_option maxHeartbeats 1000000

lemma first_root_identification {x y C S : ℝ}
    (hx : 0≤x) (hy : y ∈ Set.Icc (0:ℝ) (27/100))
    (hxs : x^2=1+y^2) (hcs : C^2+S^2=1)
    (hrow : x*C+y*S=Real.sqrt 2-x) (hrow' : x*S+y*C=1) :
    y=firstExceptionalRoot := by
  have hxdef : x=exceptionalX 1 y := by
    unfold exceptionalX
    rw [←hxs,Real.sqrt_sq hx]
  have hrowx := congrArg (fun t : ℝ => x*t) hrow
  have hrowy := congrArg (fun t : ℝ => y*t) hrow'
  have hxc := congrArg (fun t : ℝ => t*C) hxs
  have hrowx' := congrArg (fun t : ℝ => x*t) hrow'
  have hrowy' := congrArg (fun t : ℝ => y*t) hrow
  have hxs' := congrArg (fun t : ℝ => t*S) hxs
  dsimp at hrowx hrowy hxc hrowx' hrowy' hxs'
  have hc : C=x*(Real.sqrt 2-x)-y := by nlinarith only [hrowx,hrowy,hxc]
  have hs : S=x-y*(Real.sqrt 2-x) := by nlinarith only [hrowx',hrowy',hxs']
  have hroot : rootOneEquation y=1 := by
    change (exceptionalCOne y)^2+(exceptionalSOne y)^2=1
    dsimp [exceptionalCOne,exceptionalSOne]
    rw [←hxdef,←hc,←hs]
    exact hcs
  exact rootOneEquation_strictAntiOn.injOn hy firstExceptionalRoot_spec.1
    (hroot.trans firstExceptionalRoot_spec.2.symm)

lemma second_root_identification {x y C S : ℝ}
    (hx : 0≤x) (hy : y ∈ Set.Icc (0:ℝ) (27/100))
    (hxs : x^2=2+y^2) (hcs : C^2+S^2=1)
    (hrow : x*C+y*S=Real.sqrt 2-y) (hrow' : x*S+y*C=1) :
    y=secondExceptionalRoot := by
  have hxdef : x=exceptionalX 2 y := by
    unfold exceptionalX
    rw [←hxs,Real.sqrt_sq hx]
  have hrowx := congrArg (fun t : ℝ => x*t) hrow
  have hrowy := congrArg (fun t : ℝ => y*t) hrow'
  have hxc := congrArg (fun t : ℝ => t*C) hxs
  have hrowx' := congrArg (fun t : ℝ => x*t) hrow'
  have hrowy' := congrArg (fun t : ℝ => y*t) hrow
  have hxs' := congrArg (fun t : ℝ => t*S) hxs
  dsimp at hrowx hrowy hxc hrowx' hrowy' hxs'
  have hc : C=(x*(Real.sqrt 2-y)-y)/2 := by nlinarith only [hrowx,hrowy,hxc]
  have hs : S=(x-y*(Real.sqrt 2-y))/2 := by nlinarith only [hrowx',hrowy',hxs']
  have hroot : rootTwoEquation y=1 := by
    change (exceptionalCTwo y)^2+(exceptionalSTwo y)^2=1
    dsimp [exceptionalCTwo,exceptionalSTwo]
    rw [←hxdef,←hc,←hs]
    exact hcs
  exact rootTwoEquation_strictAntiOn.injOn hy secondExceptionalRoot_spec.1
    (hroot.trans secondExceptionalRoot_spec.2.symm)

structure TwoFullData where
  a : ℝ
  b : ℝ
  c : ℝ
  g : ℝ
  h : ℝ
  ha : 0<a
  hb : 0<b
  hc : 0<c
  hg : 0<g
  hh : 0<h
  hsum : a+b+c=1
  hsum' : g+h=1
  horth : 2*a*c=g*h

namespace TwoFullData

lemma parametrization (d : TwoFullData) {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hfirst : 2*d.a^2+d.g^2=x^2) (hthird : 2*d.c^2+d.h^2=y^2) :
    ∃ C S : ℝ, 0<C ∧ 0<S ∧ C^2+S^2=1 ∧
      x*C=Real.sqrt 2*d.a ∧ y*S=Real.sqrt 2*d.c ∧ x*S=d.g ∧ y*C=d.h := by
  have hr := Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)
  have hrs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  apply positive_two_column_parameterization
    (mul_pos hr d.ha) (mul_pos hr d.hc) d.hg d.hh hx hy
  · calc
      _ = (Real.sqrt 2)^2*d.a*d.c := by ring
      _ = _ := by rw [hrs]; exact d.horth
  · rw [mul_pow,hrs]
    exact hfirst
  · rw [mul_pow,hrs]
    exact hthird

lemma equal_column_energy_row_energy (d : TwoFullData) {s : ℝ} (hs : 0<s)
    (hfirst : 2*d.a^2+d.g^2=s) (hthird : 2*d.c^2+d.h^2=s) :
    d.g^2+d.h^2=s := by
  have hx := Real.sqrt_pos.mpr hs
  have hxs := Real.sq_sqrt hs.le
  obtain ⟨C,S,hC,hS,hcs,hxc,hys,hxs',hyc⟩ :=
    d.parametrization hx hx (by rwa [hxs]) (by rwa [hxs])
  calc
    _ = (Real.sqrt s*S)^2+(Real.sqrt s*C)^2 := by rw [hxs',hyc]
    _ = (Real.sqrt s)^2*(C^2+S^2) := by ring
    _ = s := by rw [hcs,hxs]; ring

lemma residue_one_equal_columns_impossible (d : TwoFullData) {δ : ℝ} (hd : 0<δ)
    (hfirst : 2*d.a^2+d.g^2=1+δ) (hthird : 2*d.c^2+d.h^2=1+δ) : False := by
  have he := d.equal_column_energy_row_energy (by linarith) hfirst hthird
  have hl := two_positive_sum_one_squares_lt d.hg d.hh d.hsum'
  linarith

lemma residue_two_equal_columns_impossible (d : TwoFullData) {δ : ℝ}
    (hd : 0<δ) (hdu : δ<1/2)
    (hfirst : 2*d.a^2+d.g^2=δ) (hthird : 2*d.c^2+d.h^2=δ) : False := by
  have he := d.equal_column_energy_row_energy hd hfirst hthird
  have hl := sum_one_squares_ge_half d.hsum'
  linarith

/-- The first normal-form pure-count alternative identifies the four-row root. -/
theorem residue_one_first (d : TwoFullData) {δ : ℝ} (hd : 0<δ) (hdu : δ≤72/1000)
    (hfirst : 2*d.a^2+d.g^2=1+δ) (hsecond : 2*d.b^2=1+δ)
    (hthird : 2*d.c^2+d.h^2=δ) : δ=firstExceptionalRoot^2 := by
  let x := Real.sqrt (1+δ)
  let y := Real.sqrt δ
  have hx : 0<x := Real.sqrt_pos.mpr (by linarith)
  have hy : 0<y := Real.sqrt_pos.mpr hd
  have hxs : x^2=1+δ := Real.sq_sqrt (by linarith)
  have hys : y^2=δ := Real.sq_sqrt hd.le
  have hyI : y ∈ Set.Icc (0:ℝ) (27/100) := ⟨hy.le,by nlinarith⟩
  have hr := Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)
  have hrs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  obtain ⟨C,S,hC,hS,hcs,hxc,hys',hxs',hyc⟩ :=
    d.parametrization hx hy (by rwa [hxs]) (by rwa [hys])
  have hb : Real.sqrt 2*d.b=x := by
    have he : (Real.sqrt 2*d.b)^2=x^2 := by rw [mul_pow,hrs,hsecond,hxs]
    have he' := congrArg Real.sqrt he
    simpa only [Real.sqrt_sq (mul_pos hr d.hb).le,Real.sqrt_sq hx.le] using he'
  have hrow : x*C+y*S=Real.sqrt 2-x := by
    have hm := congrArg (fun t : ℝ => Real.sqrt 2*t) d.hsum
    dsimp at hm
    nlinarith only [hxc,hys',hb,hm]
  have hrow' : x*S+y*C=1 := by rw [hxs',hyc]; exact d.hsum'
  have hid := first_root_identification hx.le hyI (by linarith) hcs hrow hrow'
  rw [hid] at hys
  exact hys.symm

/-- The second normal-form pure-count alternative identifies the seven-row root. -/
theorem residue_one_second (d : TwoFullData) {δ : ℝ} (hd : 0<δ) (hdu : δ≤72/1000)
    (hfirst : 2*d.a^2+d.g^2=2+δ) (hsecond : 2*d.b^2=δ)
    (hthird : 2*d.c^2+d.h^2=δ) : δ=secondExceptionalRoot^2 := by
  let x := Real.sqrt (2+δ)
  let y := Real.sqrt δ
  have hx : 0<x := Real.sqrt_pos.mpr (by linarith)
  have hy : 0<y := Real.sqrt_pos.mpr hd
  have hxs : x^2=2+δ := Real.sq_sqrt (by linarith)
  have hys : y^2=δ := Real.sq_sqrt hd.le
  have hyI : y ∈ Set.Icc (0:ℝ) (27/100) := ⟨hy.le,by nlinarith⟩
  have hr := Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)
  have hrs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  obtain ⟨C,S,hC,hS,hcs,hxc,hys',hxs',hyc⟩ :=
    d.parametrization hx hy (by rwa [hxs]) (by rwa [hys])
  have hb : Real.sqrt 2*d.b=y := by
    have he : (Real.sqrt 2*d.b)^2=y^2 := by rw [mul_pow,hrs,hsecond,hys]
    have he' := congrArg Real.sqrt he
    simpa only [Real.sqrt_sq (mul_pos hr d.hb).le,Real.sqrt_sq hy.le] using he'
  have hrow : x*C+y*S=Real.sqrt 2-y := by
    have hm := congrArg (fun t : ℝ => Real.sqrt 2*t) d.hsum
    dsimp at hm
    nlinarith only [hxc,hys',hb,hm]
  have hrow' : x*S+y*C=1 := by rw [hxs',hyc]; exact d.hsum'
  have hid := second_root_identification hx.le hyI (by linarith) hcs hrow hrow'
  rw [hid] at hys
  exact hys.symm

/-- The unequal-column normal form in residue two is excluded directly. -/
theorem residue_two_unequal_columns_impossible (d : TwoFullData) {δ : ℝ}
    (hdl : (1:ℝ)/5<δ) (hdu : δ≤4/9)
    (hfirst : 2*d.a^2+d.g^2=1+δ) (hsecond : 2*d.b^2=δ)
    (hthird : 2*d.c^2+d.h^2=δ) : False := by
  have hd : 0<δ := by linarith
  let x := Real.sqrt (1+δ)
  let y := Real.sqrt δ
  have hx : 0<x := Real.sqrt_pos.mpr (by linarith)
  have hy : 0<y := Real.sqrt_pos.mpr hd
  have hxs : x^2=1+δ := Real.sq_sqrt (by linarith)
  have hys : y^2=δ := Real.sq_sqrt hd.le
  have hr := Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)
  have hrs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  obtain ⟨C,S,hC,hS,hcs,hxc,hys',hxs',hyc⟩ :=
    d.parametrization hx hy (by rwa [hxs]) (by rwa [hys])
  have hb : Real.sqrt 2*d.b=y := by
    have he : (Real.sqrt 2*d.b)^2=y^2 := by rw [mul_pow,hrs,hsecond,hys]
    have he' := congrArg Real.sqrt he
    simpa only [Real.sqrt_sq (mul_pos hr d.hb).le,Real.sqrt_sq hy.le] using he'
  have hrow : x*C+y*S=Real.sqrt 2-y := by
    have hm := congrArg (fun t : ℝ => Real.sqrt 2*t) d.hsum
    dsimp at hm
    nlinarith only [hxc,hys',hb,hm]
  have hrow' : x*S+y*C=1 := by rw [hxs',hyc]; exact d.hsum'
  have hrowx := congrArg (fun t : ℝ => x*t) hrow
  have hrowy := congrArg (fun t : ℝ => y*t) hrow'
  have hxys : x^2=1+y^2 := by linarith
  have hxC := congrArg (fun t : ℝ => t*C) hxys
  have hrowx' := congrArg (fun t : ℝ => x*t) hrow'
  have hrowy' := congrArg (fun t : ℝ => y*t) hrow
  have hxS := congrArg (fun t : ℝ => t*S) hxys
  dsimp at hrowx hrowy hxC hrowx' hrowy' hxS
  have hc : C=x*(Real.sqrt 2-y)-y := by nlinarith only [hrowx,hrowy,hxC]
  have hs : S=x-y*(Real.sqrt 2-y) := by nlinarith only [hrowx',hrowy',hxS]
  exact two_full_residue_two_impossible hx.le hy.le hxys (by linarith)
    (by nlinarith) hc hs hC hS hcs

end TwoFullData
end
end F3
