import F3.Frames
import Mathlib.Tactic.LinearCombination

/-!
# Algebraic part of the normalized multiplier argument

This file proves finite-sum identities and a three-dimensional positive-kernel
lemma used in the manuscript. It does not assume or assert the optimization
theorem, or the existence of a multiplier system at an optimizer.
-/

namespace F3
noncomputable section
open scoped BigOperators

/-- The coordinate characterization of the subgradient of the l1 norm. -/
def RowSubgradient (a g : Fin 3 → ℝ) : Prop :=
  (∀ j, |g j| ≤ 1) ∧ ∀ j, a j * g j = |a j|

/-- An actual normalized stationary tuple. Existence is a separate target. -/
structure MultiplierSystem {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) where
  weight : ι → ℝ
  gradient : ι → Fin 3 → ℝ
  matrix : Fin 3 → Fin 3 → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  subgradient : ∀ i, RowSubgradient (A i) (gradient i)
  symmetric : ∀ j k, matrix j k = matrix k j
  stationarity : ∀ i j,
    (∑ k, A i k * matrix k j) = weight i * gradient i j
  complementary : ∀ i, 0 < weight i →
    |A i 0| + |A i 1| + |A i 2| = 1

theorem multiplier_column_identity {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (M : MultiplierSystem A) (j k : Fin 3) :
    s * M.matrix j k = ∑ i, M.weight i * A i j * M.gradient i k := by
  classical
  have h : (∑ i, A i j * (∑ l, A i l * M.matrix l k)) =
      s * M.matrix j k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, hA.2]
    simp
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [M.stationarity]
  ring

theorem multiplier_diagonal_identity {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (M : MultiplierSystem A) (j : Fin 3) :
    s * M.matrix j j = ∑ i, M.weight i * |A i j| := by
  rw [multiplier_column_identity hA M j j]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, (M.subgradient i).2 j]

theorem multiplier_diagonal_nonneg {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hs : 0 < s) (M : MultiplierSystem A) (j : Fin 3) :
    0 ≤ M.matrix j j := by
  have h : 0 ≤ s * M.matrix j j := by
    rw [multiplier_diagonal_identity hA M]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (M.weight_nonneg i) (abs_nonneg _)
  nlinarith

theorem multiplier_entry_bound {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hs : 0 < s) (M : MultiplierSystem A) (j k : Fin 3) :
    |M.matrix j k| ≤ M.matrix j j := by
  have h : |s * M.matrix j k| ≤ s * M.matrix j j := by
    rw [multiplier_column_identity hA M, multiplier_diagonal_identity hA M]
    calc
      |∑ i, M.weight i * A i j * M.gradient i k| ≤
          ∑ i, |M.weight i * A i j * M.gradient i k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, M.weight i * |A i j| := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_mul, abs_of_nonneg (M.weight_nonneg i)]
        exact mul_le_of_le_one_right
          (mul_nonneg (M.weight_nonneg i) (abs_nonneg _)) ((M.subgradient i).1 k)
  rw [abs_mul, abs_of_pos hs] at h
  exact (mul_le_mul_left hs).mp h

theorem multiplier_trace_identity {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (M : MultiplierSystem A) :
    s * (M.matrix 0 0 + M.matrix 1 1 + M.matrix 2 2) = 1 := by
  rw [mul_add, mul_add, multiplier_diagonal_identity hA M,
    multiplier_diagonal_identity hA M, multiplier_diagonal_identity hA M,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i, M.weight i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : M.weight i = 0
      · simp [hi]
      · have hpos := lt_of_le_of_ne (M.weight_nonneg i) (Ne.symm hi)
        have hc := M.complementary i hpos
        nlinarith
    _ = 1 := M.weight_sum

/-- The quadratic form of a real symmetric three by three matrix. -/
def quadThree (a b c d e f x y z : ℝ) : ℝ :=
  a*x^2 + b*y^2 + c*z^2 + 2*d*x*y + 2*e*x*z + 2*f*y*z

private theorem quadThree_nonneg_positive_edge
    {a b c d e f u v w : ℝ}
    (hw : 0 < w) (hd : 0 ≤ d) (hda : d ≤ a) (hdb : d ≤ b)
    (h0 : a*u+d*v+e*w=0) (h1 : d*u+b*v+f*w=0)
    (h2 : e*u+f*v+c*w=0) (x y z : ℝ) :
    0 ≤ quadThree a b c d e f x y z := by
  have hblock : 0 ≤ a*(w*x-u*z)^2 + b*(w*y-v*z)^2 +
      2*d*(w*x-u*z)*(w*y-v*z) := by
    have ha := mul_nonneg (sub_nonneg.mpr hda) (sq_nonneg (w*x-u*z))
    have hb := mul_nonneg (sub_nonneg.mpr hdb) (sq_nonneg (w*y-v*z))
    have hd' := mul_nonneg hd (sq_nonneg ((w*x-u*z)+(w*y-v*z)))
    nlinarith
  have heq : w^2 * quadThree a b c d e f x y z =
      a*(w*x-u*z)^2 + b*(w*y-v*z)^2 +
        2*d*(w*x-u*z)*(w*y-v*z) := by
    unfold quadThree
    linear_combination (2*w*x*z-u*z^2)*h0 +
      (2*w*y*z-v*z^2)*h1 + w*z^2*h2
  have hwsq : 0 < w^2 := sq_pos_of_pos hw
  rw [← heq] at hblock
  exact nonneg_of_mul_nonneg_right hblock hwsq

/-- The positive-kernel PSD lemma in the manuscript, stated as a scalar
quadratic-form inequality and proved without an optimization premise. -/
theorem positive_kernel_quadThree_nonneg
    {a b c d e f u v w : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hda : d ≤ a) (hdb : d ≤ b)
    (hea : e ≤ a) (hec : e ≤ c)
    (hfb : f ≤ b) (hfc : f ≤ c)
    (h0 : a*u+d*v+e*w=0) (h1 : d*u+b*v+f*w=0)
    (h2 : e*u+f*v+c*w=0) (x y z : ℝ) :
    0 ≤ quadThree a b c d e f x y z := by
  by_cases hd : 0 ≤ d
  · exact quadThree_nonneg_positive_edge hw hd hda hdb h0 h1 h2 x y z
  by_cases he : 0 ≤ e
  · have h := quadThree_nonneg_positive_edge
      (a:=a) (b:=c) (c:=b) (d:=e) (e:=d) (f:=f)
      (u:=u) (v:=w) (w:=v) hv he hea hec
      (by linarith) (by linarith) (by linarith) x z y
    dsimp [quadThree] at h ⊢
    nlinarith
  by_cases hf : 0 ≤ f
  · have h := quadThree_nonneg_positive_edge
      (a:=b) (b:=c) (c:=a) (d:=f) (e:=d) (f:=e)
      (u:=v) (v:=w) (w:=u) hu hf hfb hfc
      (by linarith) (by linarith) (by linarith) y z x
    dsimp [quadThree] at h ⊢
    nlinarith
  have hdn : 0 ≤ -d := by linarith
  have hen : 0 ≤ -e := by linarith
  have hfn : 0 ≤ -f := by linarith
  have hsum : 0 ≤ -w*d*(v*x-u*y)^2 - v*e*(w*x-u*z)^2 -
      u*f*(w*y-v*z)^2 := by
    have hA := mul_nonneg (mul_nonneg hw.le hdn) (sq_nonneg (v*x-u*y))
    have hB := mul_nonneg (mul_nonneg hv.le hen) (sq_nonneg (w*x-u*z))
    have hC := mul_nonneg (mul_nonneg hu.le hfn) (sq_nonneg (w*y-v*z))
    nlinarith
  have heq : u*v*w*quadThree a b c d e f x y z =
      -w*d*(v*x-u*y)^2 - v*e*(w*x-u*z)^2 -
        u*f*(w*y-v*z)^2 := by
    unfold quadThree
    linear_combination v*w*x^2*h0 + u*w*y^2*h1 + u*v*z^2*h2
  rw [← heq] at hsum
  exact nonneg_of_mul_nonneg_right hsum (mul_pos (mul_pos hu hv) hw)

theorem quadThree_kernel_of_zero
    {a b c d e f x y z : ℝ}
    (hn : ∀ X Y Z, 0 ≤ quadThree a b c d e f X Y Z)
    (hz : quadThree a b c d e f x y z = 0) :
    a*x+d*y+e*z=0 ∧ d*x+b*y+f*z=0 ∧ e*x+f*y+c*z=0 := by
  have scalar : ∀ A B : ℝ, 0 ≤ A →
      (∀ t : ℝ, 0 ≤ A*t^2+2*B*t) → B=0 := by
    intro A B hA h
    let t : ℝ := -B/(A+1)
    have hden : A+1 ≠ 0 := by linarith
    have ht : (A+1)*t = -B := by dsimp [t]; field_simp; ring
    have ht2 : (A+1)*t^2 = -B*t := by nlinarith [congrArg (fun q : ℝ => q*t) ht]
    have hq := h t
    have ht0 : t=0 := by nlinarith [sq_nonneg t, mul_nonneg hA (sq_nonneg t)]
    rw [ht0, mul_zero] at ht
    linarith
  have ha : 0 ≤ a := by simpa [quadThree] using hn 1 0 0
  have hb : 0 ≤ b := by simpa [quadThree] using hn 0 1 0
  have hc : 0 ≤ c := by simpa [quadThree] using hn 0 0 1
  refine ⟨scalar a (a*x+d*y+e*z) ha ?_,
    scalar b (d*x+b*y+f*z) hb ?_, scalar c (e*x+f*y+c*z) hc ?_⟩
  · intro t
    have h := hn (x+t) y z
    dsimp [quadThree] at hz h
    nlinarith
  · intro t
    have h := hn x (y+t) z
    dsimp [quadThree] at hz h
    nlinarith
  · intro t
    have h := hn x y (z+t)
    dsimp [quadThree] at hz h
    nlinarith

/-- A full positive saturated stationary row gives a PSD matrix and the
stronger lower bound used to exclude its singular case. -/
theorem full_row_quad_lower_bound
    {a b c d e f u v w lam : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (huvw : u+v+w=1)
    (hda : d ≤ a) (hdb : d ≤ b)
    (hea : e ≤ a) (hec : e ≤ c)
    (hfb : f ≤ b) (hfc : f ≤ c)
    (h0 : a*u+d*v+e*w=lam) (h1 : d*u+b*v+f*w=lam)
    (h2 : e*u+f*v+c*w=lam) (x y z : ℝ) :
    lam*(x+y+z)^2 ≤ quadThree a b c d e f x y z := by
  have h := positive_kernel_quadThree_nonneg
    (a:=a-lam) (b:=b-lam) (c:=c-lam)
    (d:=d-lam) (e:=e-lam) (f:=f-lam)
    hu hv hw (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linear_combination h0-lam*huvw)
    (by linear_combination h1-lam*huvw)
    (by linear_combination h2-lam*huvw) x y z
  dsimp [quadThree] at h ⊢
  nlinarith

private theorem three_signs_product_nonneg
    {r t gr gt gv x y z : ℝ}
    (hgr : r*gr=|r|) (hgt : t*gt=|t|) (hgv : |gv| ≤ 1)
    (hxy : x*y<0) (hxyz : x+y+z=0)
    (horth : gr*x+gt*y+gv*z=0) : 0 ≤ r*t := by
  by_contra hneg
  have hrt : r*t<0 := lt_of_not_ge hneg
  have opposite : ∀ R T GR GT X Y Z : ℝ,
      0<R → T<0 → R*GR=|R| → T*GT=|T| →
      X*Y<0 → X+Y+Z=0 → GR*X+GT*Y+gv*Z=0 → False := by
    intro R T GR GT X Y Z hR hT hGR hGT hXY hXYZ hO
    rw [abs_of_pos hR] at hGR
    rw [abs_of_neg hT] at hGT
    have hGR1 : GR=1 := by nlinarith
    have hGT1 : GT= -1 := by nlinarith
    rw [hGR1,hGT1] at hO
    have hl : -1 ≤ gv := (abs_le.mp hgv).1
    have hh : gv ≤ 1 := (abs_le.mp hgv).2
    have hx : X ≠ 0 := by intro hx; rw [hx,zero_mul] at hXY; linarith
    rcases lt_or_gt_of_ne hx with hX | hX
    · have hY : 0<Y := by nlinarith
      by_cases hZ : 0≤Z
      · have hg := mul_le_mul_of_nonneg_right hh hZ
        nlinarith
      · have hg := mul_le_mul_of_nonpos_right hl (le_of_not_ge hZ)
        nlinarith
    · have hY : Y<0 := by nlinarith
      by_cases hZ : 0≤Z
      · have hg := mul_le_mul_of_nonneg_right hl hZ
        nlinarith
      · have hg := mul_le_mul_of_nonpos_right hh (le_of_not_ge hZ)
        nlinarith
  have hr : r ≠ 0 := by intro hr; rw [hr,zero_mul] at hrt; linarith
  rcases lt_or_gt_of_ne hr with hr | hr
  · have ht : 0<t := by nlinarith
    exact opposite t r gt gr y x z ht hr hgt hgr
      (by nlinarith) (by linarith) (by nlinarith)
  · have ht : t<0 := by nlinarith
    exact opposite r t gr gt x y z hr ht hgr hgt hxy hxyz horth

/-- Zero total coordinate sum forces an opposite-sign coordinate pair. -/
private theorem opposite_pair_of_sum_zero {x y z : ℝ}
    (h : x+y+z=0) (hnz : x≠0 ∨ y≠0 ∨ z≠0) :
    x*y<0 ∨ x*z<0 ∨ y*z<0 := by
  by_contra hh
  push_neg at hh
  have hxy := hh.1
  have hxz := hh.2.1
  have hyz := hh.2.2
  have hsum : x^2+y^2+z^2=0 := by nlinarith [sq_nonneg x,sq_nonneg y,sq_nonneg z]
  have hx : x=0 := by nlinarith [sq_nonneg y,sq_nonneg z]
  have hy : y=0 := by nlinarith [sq_nonneg x,sq_nonneg z]
  have hz : z=0 := by nlinarith [sq_nonneg x,sq_nonneg y]
  exact hnz.elim (fun h => h hx) (fun h => h.elim (fun h => h hy) (fun h => h hz))


/-- Algebraic positive definiteness of every stationary system with positive
row weights and a full positive row. The proof does not assume that the frame
is globally maximizing. Column sign changes give the other full-row signs. -/
theorem full_positive_row_posdef {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (hs : 0 < s) (M : MultiplierSystem A)
    (hw : ∀ i, 0 < M.weight i) (i₀ : ι)
    (hu : ∀ j, 0 < A i₀ j) (x y z : ℝ)
    (hnz : x≠0 ∨ y≠0 ∨ z≠0) :
    0 < quadThree (M.matrix 0 0) (M.matrix 1 1) (M.matrix 2 2)
      (M.matrix 0 1) (M.matrix 0 2) (M.matrix 1 2) x y z := by
  classical
  have h10 := M.symmetric 1 0
  have h20 := M.symmetric 2 0
  have h21 := M.symmetric 2 1
  have hg : ∀ j, M.gradient i₀ j = 1 := by
    intro j
    have h := (M.subgradient i₀).2 j
    rw [abs_of_pos (hu j)] at h
    nlinarith [hu j]
  have huvw : A i₀ 0 + A i₀ 1 + A i₀ 2 = 1 := by
    simpa only [abs_of_pos (hu 0),abs_of_pos (hu 1),abs_of_pos (hu 2)]
      using M.complementary i₀ (hw i₀)
  have h0 := M.stationarity i₀ 0
  have h1 := M.stationarity i₀ 1
  have h2 := M.stationarity i₀ 2
  simp only [Fin.sum_univ_three,h10,h20,h21,hg,mul_one] at h0 h1 h2
  have hb (j k : Fin 3) : M.matrix j k ≤ M.matrix j j :=
    le_trans (le_abs_self _) (multiplier_entry_bound hA hs M j k)
  have hlower (X Y Z : ℝ) : M.weight i₀*(X+Y+Z)^2 ≤
      quadThree (M.matrix 0 0) (M.matrix 1 1) (M.matrix 2 2)
        (M.matrix 0 1) (M.matrix 0 2) (M.matrix 1 2) X Y Z := by
    apply full_row_quad_lower_bound (hu 0) (hu 1) (hu 2) huvw
      (hb 0 1) (h10 ▸ hb 1 0) (hb 0 2) (h20 ▸ hb 2 0)
      (hb 1 2) (h21 ▸ hb 2 1)
    all_goals nlinarith
  have hpsd (X Y Z : ℝ) : 0 ≤
      quadThree (M.matrix 0 0) (M.matrix 1 1) (M.matrix 2 2)
        (M.matrix 0 1) (M.matrix 0 2) (M.matrix 1 2) X Y Z :=
    le_trans (mul_nonneg (hw i₀).le (sq_nonneg _)) (hlower X Y Z)
  by_contra hnot
  have hzero : quadThree (M.matrix 0 0) (M.matrix 1 1) (M.matrix 2 2)
      (M.matrix 0 1) (M.matrix 0 2) (M.matrix 1 2) x y z = 0 :=
    le_antisymm (le_of_not_gt hnot) (hpsd x y z)
  have hsum : x+y+z=0 := by
    have hl := hlower x y z
    rw [hzero] at hl
    by_contra hne
    have hp : 0 < (x+y+z)^2 := sq_pos_of_ne_zero hne
    exact not_lt_of_ge hl (mul_pos (hw i₀) hp)
  obtain ⟨hk0,hk1,hk2⟩ := quadThree_kernel_of_zero hpsd hzero
  have horth (i : ι) : M.gradient i 0*x+M.gradient i 1*y+M.gradient i 2*z=0 := by
    have he0 := M.stationarity i 0
    have he1 := M.stationarity i 1
    have he2 := M.stationarity i 2
    simp only [Fin.sum_univ_three,h10,h20,h21] at he0 he1 he2
    have he : M.weight i *
        (M.gradient i 0*x+M.gradient i 1*y+M.gradient i 2*z)=0 := by
      linear_combination A i 0*hk0 + A i 1*hk1 + A i 2*hk2 -
        x*he0-y*he1-z*he2
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (hw i))
  rcases opposite_pair_of_sum_zero hsum hnz with hxy | hxz | hyz
  · have hp (i : ι) : 0 ≤ A i 0*A i 1 :=
      three_signs_product_nonneg ((M.subgradient i).2 0)
        ((M.subgradient i).2 1) ((M.subgradient i).1 2) hxy hsum (horth i)
    have hpos : 0 < ∑ i, A i 0*A i 1 :=
      Finset.sum_pos' (fun i _ => hp i) ⟨i₀,Finset.mem_univ _,mul_pos (hu 0) (hu 1)⟩
    have hcancel := hA.2 0 1
    norm_num [Fin.ext_iff] at hcancel
    linarith
  · have hp (i : ι) : 0 ≤ A i 0*A i 2 := by
      apply three_signs_product_nonneg (x:=x) (y:=z) (z:=y) ((M.subgradient i).2 0)
        ((M.subgradient i).2 2) ((M.subgradient i).1 1) hxz
      · linarith
      · nlinarith [horth i]
    have hpos : 0 < ∑ i, A i 0*A i 2 :=
      Finset.sum_pos' (fun i _ => hp i) ⟨i₀,Finset.mem_univ _,mul_pos (hu 0) (hu 2)⟩
    have hcancel := hA.2 0 2
    norm_num [Fin.ext_iff] at hcancel
    linarith
  · have hp (i : ι) : 0 ≤ A i 1*A i 2 := by
      apply three_signs_product_nonneg (x:=y) (y:=z) (z:=x) ((M.subgradient i).2 1)
        ((M.subgradient i).2 2) ((M.subgradient i).1 0) hyz
      · linarith
      · nlinarith [horth i]
    have hpos : 0 < ∑ i, A i 1*A i 2 :=
      Finset.sum_pos' (fun i _ => hp i) ⟨i₀,Finset.mem_univ _,mul_pos (hu 1) (hu 2)⟩
    have hcancel := hA.2 1 2
    norm_num [Fin.ext_iff] at hcancel
    linarith

end
end F3
