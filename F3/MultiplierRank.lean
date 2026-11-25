import F3.RankOne
import F3.SignChanges
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace F3
noncomputable section
open scoped BigOperators Matrix

/-- A matrix of rank at most one has all two-by-two minors zero. -/
theorem matrix_rank_le_one_minors_zero (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hS : S.rank≤1) (j k a b : Fin 3) : S j a*S k b=S j b*S k a := by
  have hdim : Module.finrank ℝ (LinearMap.range S.mulVecLin)≤1 := hS
  obtain ⟨v,hv⟩ := finrank_le_one_iff.mp hdim
  have hcol (c : Fin 3) : (fun i=>S i c)∈LinearMap.range S.mulVecLin := by
    refine ⟨Pi.single c 1,?_⟩
    change S *ᵥ Pi.single c 1=(fun i=>S i c)
    rw [Matrix.mulVec_single_one]
    rfl
  have hrep (c : Fin 3) : ∃t : ℝ,∀i,S i c=t*v.1 i := by
    obtain ⟨t,ht⟩ := hv ⟨(fun i=>S i c),hcol c⟩
    refine ⟨t,?_⟩
    intro i
    have he := congrArg (fun w : LinearMap.range S.mulVecLin=>w.1 i) ht
    exact he.symm
  obtain ⟨ta,ha⟩ := hrep a
  obtain ⟨tb,hb⟩ := hrep b
  rw [ha j,ha k,hb j,hb k]
  ring

theorem multiplier_rank_ge_two_residue_one {m : ℕ} {d : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 0<d) (hdhi : d<1/3) : 2≤Matrix.rank M.matrix := by
  by_contra hn
  have hrank : Matrix.rank M.matrix≤1 := by omega
  have hs : 0<(m : ℝ)+d := by positivity
  obtain ⟨τ,u,hτ,hu,hun,hform⟩ := multiplier_minors_zero_signed_form hA hs M
    (matrix_rank_le_one_minors_zero M.matrix hrank)
  exact signed_rank_one_excluded_residue_one hA M hd hdhi hτ u hu hun hform

theorem multiplier_rank_ge_two_residue_two {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (hdhi : d≤4/9) : 2≤Matrix.rank M.matrix := by
  by_contra hn
  have hrank : Matrix.rank M.matrix≤1 := by omega
  have hs : 0<(m : ℝ)+d := by positivity
  obtain ⟨τ,u,hτ,hu,hun,hform⟩ := multiplier_minors_zero_signed_form hA hs M
    (matrix_rank_le_one_minors_zero M.matrix hrank)
  exact signed_rank_one_excluded_residue_two hA M hd hdhi hτ u hu hun hform

theorem matrix_rank_le_two_of_det_zero (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hdet : S.det=0) : S.rank≤2 := by
  obtain ⟨x,hx,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hxker : x∈LinearMap.ker S.mulVecLin := by
    simpa only [LinearMap.mem_ker,Matrix.mulVecLin_apply] using hker
  have hpositive : 0<Module.finrank ℝ (LinearMap.ker S.mulVecLin) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨x,hxker⟩,?_⟩
    intro hz
    apply hx
    exact congrArg Subtype.val hz
  have hnull := S.mulVecLin.finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ (Fin 3→ℝ)=3 := by simp
  rw [hdim] at hnull
  change S.rank+Module.finrank ℝ (LinearMap.ker S.mulVecLin)=3 at hnull
  omega

private theorem two_block_nonneg {a b c : ℝ} (hca : |c|≤a) (hcb : |c|≤b)
    (x y : ℝ) : 0≤a*x^2+b*y^2+2*c*x*y := by
  by_cases hc : 0≤c
  · rw [abs_of_nonneg hc] at hca hcb
    have h1 := mul_nonneg (sub_nonneg.mpr hca) (sq_nonneg x)
    have h2 := mul_nonneg (sub_nonneg.mpr hcb) (sq_nonneg y)
    have h3 := mul_nonneg hc (sq_nonneg (x+y))
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hc)] at hca hcb
    have h1 := mul_nonneg (sub_nonneg.mpr hca) (sq_nonneg x)
    have h2 := mul_nonneg (sub_nonneg.mpr hcb) (sq_nonneg y)
    have h3 := mul_nonneg (show 0≤ -c by linarith) (sq_nonneg (x-y))
    nlinarith

private theorem kernel_reduce_quad_nonneg {a b c d e f u v w : ℝ}
    (hw : w≠0) (hda : |d|≤a) (hdb : |d|≤b)
    (h0 : a*u+d*v+e*w=0) (h1 : d*u+b*v+f*w=0) (h2 : e*u+f*v+c*w=0)
    (x y z : ℝ) : 0≤quadThree a b c d e f x y z := by
  have hblock := two_block_nonneg hda hdb (w*x-u*z) (w*y-v*z)
  have heq : w^2*quadThree a b c d e f x y z=
      a*(w*x-u*z)^2+b*(w*y-v*z)^2+2*d*(w*x-u*z)*(w*y-v*z) := by
    unfold quadThree
    linear_combination (2*w*x*z-u*z^2)*h0+(2*w*y*z-v*z^2)*h1+w*z^2*h2
  rw [←heq] at hblock
  have hw2 : 0<w^2 := by nlinarith [sq_pos_of_ne_zero hw]
  exact nonneg_of_mul_nonneg_right hblock hw2

/-- Any singular real symmetric three-by-three matrix satisfying the
multiplier entry bounds is positive semidefinite. -/
theorem singular_entry_bounded_posSemidef (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : ∀j k,S j k=S k j) (hbound : ∀j k,|S j k|≤S j j)
    (hdet : S.det=0) : S.PosSemidef := by
  obtain ⟨r,hr,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h0 := congrFun hker 0
  have h1 := congrFun hker 1
  have h2 := congrFun hker 2
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_three,Pi.zero_apply,
    hsym 1 0,hsym 2 0,hsym 2 1] at h0 h1 h2
  have h01 := hbound 0 1
  have h10 : |S 0 1|≤S 1 1 := by simpa only [hsym 1 0] using hbound 1 0
  have h02 := hbound 0 2
  have h20 : |S 0 2|≤S 2 2 := by simpa only [hsym 2 0] using hbound 2 0
  have h12 := hbound 1 2
  have h21 : |S 1 2|≤S 2 2 := by simpa only [hsym 2 1] using hbound 2 1
  have hquad (x y z : ℝ) : 0≤quadThree (S 0 0) (S 1 1) (S 2 2)
      (S 0 1) (S 0 2) (S 1 2) x y z := by
    by_cases hr2 : r 2≠0
    · exact kernel_reduce_quad_nonneg hr2 h01 h10 h0 h1 h2 x y z
    by_cases hr1 : r 1≠0
    · have h := kernel_reduce_quad_nonneg hr1 h02 h20
        (by linarith : S 0 0*r 0+S 0 2*r 2+S 0 1*r 1=0)
        (by linarith : S 0 2*r 0+S 2 2*r 2+S 1 2*r 1=0)
        (by linarith : S 0 1*r 0+S 1 2*r 2+S 1 1*r 1=0) x z y
      dsimp [quadThree] at h ⊢
      nlinarith
    · have hr0 : r 0≠0 := by
        intro hz
        apply hr
        funext j
        fin_cases j <;> simp_all
      have h := kernel_reduce_quad_nonneg hr0 h12 h21
        (by linarith : S 1 1*r 1+S 1 2*r 2+S 0 1*r 0=0)
        (by linarith : S 1 2*r 1+S 2 2*r 2+S 0 2*r 0=0)
        (by linarith : S 0 1*r 1+S 0 2*r 2+S 0 0*r 0=0) y z x
      dsimp [quadThree] at h ⊢
      nlinarith
  constructor
  · ext j k
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hsym k j
  · intro x
    have h := hquad (x 0) (x 1) (x 2)
    rw [←quadraticThree_eq hsym] at h
    simpa only [quadraticThree,dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
      Finset.mul_sum,mul_assoc] using h

theorem singular_multiplier_posSemidef {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (hdet : Matrix.det M.matrix=0) : Matrix.PosSemidef M.matrix :=
  singular_entry_bounded_posSemidef M.matrix M.symmetric (multiplier_entry_bound hA hs M) hdet

theorem singular_multiplier_rank_two_psd_residue_one {m : ℕ} {d : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 0<d) (hdhi : d<1/3)
    (hdet : Matrix.det M.matrix=0) : Matrix.rank M.matrix=2 ∧ Matrix.PosSemidef M.matrix := by
  constructor
  · exact le_antisymm (matrix_rank_le_two_of_det_zero M.matrix hdet)
      (multiplier_rank_ge_two_residue_one hA M hd hdhi)
  · exact singular_multiplier_posSemidef hA (by positivity) M hdet

theorem singular_multiplier_rank_two_psd_residue_two {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (hdhi : d≤4/9)
    (hdet : Matrix.det M.matrix=0) : Matrix.rank M.matrix=2 ∧ Matrix.PosSemidef M.matrix := by
  constructor
  · exact le_antisymm (matrix_rank_le_two_of_det_zero M.matrix hdet)
      (multiplier_rank_ge_two_residue_two hA M hd hdhi)
  · exact singular_multiplier_posSemidef hA (by positivity) M hdet

end
end F3
