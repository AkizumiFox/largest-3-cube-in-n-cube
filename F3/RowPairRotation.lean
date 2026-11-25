import F3.SecondOrderBridge
import F3.Dominance
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! A rational orthogonal rotation makes a saturated full row and a positive
full row simultaneously slack when the former's sign vector annihilates the latter. -/

namespace F3
noncomputable section
open scoped BigOperators Topology
open Filter
open Dominance

def RowPairIndependent (u r : Fin 3 → ℝ) : Prop :=
  ∀ a b : ℝ, (∀ j, a*u j+b*r j=0) → a=0 ∧ b=0

theorem RowPairIndependent.linearIndependent {u r : Fin 3 → ℝ}
    (h : RowPairIndependent u r) : LinearIndependent ℝ ![u,r] := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro hr
    have hh := h 0 1 (by intro j; simpa only [zero_mul,zero_add,one_mul] using congrFun hr j)
    norm_num at hh
  · intro a ha
    have hh := h 1 (-a) (by
      intro j
      have he := congrFun ha j
      change a*r j=u j at he
      nlinarith)
    norm_num at hh

def rotationCos (t : ℝ) : ℝ := (1-t^2)/(1+t^2)
def rotationSin (e t : ℝ) : ℝ := e*(2*t)/(1+t^2)

theorem rotation_denom_pos (t : ℝ) : 0<1+t^2 := by positivity

theorem continuous_rotationCos : Continuous rotationCos :=
  (continuous_const.sub (continuous_id.pow 2)).div
    (continuous_const.add (continuous_id.pow 2))
    (fun t => (rotation_denom_pos t).ne')

theorem continuous_rotationSin (e : ℝ) : Continuous (rotationSin e) :=
  (continuous_const.mul (continuous_const.mul continuous_id)).div
    (continuous_const.add (continuous_id.pow 2))
    (fun t => (rotation_denom_pos t).ne')

theorem rotation_circle {e t : ℝ} (he : e^2=1) :
    rotationCos t ^ 2+rotationSin e t ^ 2=1 := by
  unfold rotationCos rotationSin
  field_simp [(rotation_denom_pos t).ne']
  nlinarith [sq_nonneg (t^2)]

def rotateFirst (u r : Fin 3 → ℝ) (c d : ℝ) := fun j => c*u j+d*r j
def rotateSecond (u r : Fin 3 → ℝ) (c d : ℝ) := fun j => c*r j-d*u j

theorem rotated_pair_independent {u r : Fin 3 → ℝ} {c d : ℝ}
    (h : RowPairIndependent u r) (hcd : c^2+d^2=1) :
    RowPairIndependent (rotateFirst u r c d) (rotateSecond u r c d) := by
  intro a b hab
  have hcoef := h (a*c-b*d) (a*d+b*c) (by
    intro j
    have he := hab j
    dsimp [rotateFirst,rotateSecond] at he
    nlinarith [he])
  constructor
  · linear_combination -a*hcd+c*hcoef.1+d*hcoef.2
  · linear_combination -b*hcd-d*hcoef.1+c*hcoef.2

theorem rotated_pair_gram {u r : Fin 3 → ℝ} {c d : ℝ}
    (hcd : c^2+d^2=1) (j k : Fin 3) :
    rotateFirst u r c d j*rotateFirst u r c d k+
      rotateSecond u r c d j*rotateSecond u r c d k = u j*u k+r j*r k := by
  dsimp [rotateFirst,rotateSecond]
  calc
    _ = (c^2+d^2)*(u j*u k+r j*r k) := by ring
    _ = _ := by rw [hcd,one_mul]

theorem saturated_positive_pair_independent {u r : Fin 3 → ℝ}
    (hu : l1 u=1) (hr : ∀ j, 0<r j)
    (horth : facetValue r (canonicalFacet u)=0) : RowPairIndependent u r := by
  have huf : facetValue u (canonicalFacet u)=1 := by
    simpa only [facetValue_canonical,l1,Fin.sum_univ_three] using hu
  intro a b hab
  have hdot : a*facetValue u (canonicalFacet u)+b*facetValue r (canonicalFacet u)=0 := by
    simp only [facetValue,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    calc
      _ = (a*u j+b*r j)*facetSign (canonicalFacet u) j := by ring
      _ = 0 := by rw [hab j,zero_mul]
  have ha : a=0 := by simpa [huf,horth] using hdot
  refine ⟨ha,?_⟩
  have hb := hab 0
  rw [ha,zero_mul,zero_add] at hb
  exact (mul_eq_zero.mp hb).resolve_right (hr 0).ne'

theorem exists_slack_pair_rotation {u r : Fin 3 → ℝ}
    (hu : l1 u=1) (hufull : ∀ j, u j≠0)
    (hr : ∀ j, 0<r j) (hrbound : l1 r≤1)
    (horth : facetValue r (canonicalFacet u)=0) :
    ∃ c d : ℝ, c^2+d^2=1 ∧
      l1 (rotateFirst u r c d)<1 ∧ l1 (rotateSecond u r c d)<1 ∧
      RowPairIndependent (rotateFirst u r c d) (rotateSecond u r c d) := by
  classical
  let U : ℝ := ∑ j, u j
  let e : ℝ := if 0≤U then 1 else -1
  have he : e^2=1 := by dsimp [e]; split_ifs <;> norm_num
  have heU : 0≤e*U := by
    dsimp [e]
    split_ifs with h
    · simpa using h
    · simp only [neg_mul,one_mul]
      linarith
  let v : ℝ → Fin 3 → ℝ := fun t => rotateFirst u r (rotationCos t) (rotationSin e t)
  let w : ℝ → Fin 3 → ℝ := fun t => rotateSecond u r (rotationCos t) (rotationSin e t)
  have hv0 (j : Fin 3) : v 0 j=u j := by simp [v,rotateFirst,rotationCos,rotationSin]
  have hw0 (j : Fin 3) : w 0 j=r j := by simp [w,rotateSecond,rotationCos,rotationSin]
  have hvcont (j : Fin 3) : Continuous (fun t => v t j) :=
    (continuous_rotationCos.mul continuous_const).add
      ((continuous_rotationSin e).mul continuous_const)
  have hwcont (j : Fin 3) : Continuous (fun t => w t j) :=
    (continuous_rotationCos.mul continuous_const).sub
      ((continuous_rotationSin e).mul continuous_const)
  have hsignj (j : Fin 3) :
      ∀ᶠ t in 𝓝 (0 : ℝ), 0<facetSign (canonicalFacet u) j*v t j := by
    have hprod : facetSign (canonicalFacet u) j*u j=|u j| := by
      simpa [canonicalSubgradient,facetSign,canonicalFacet,mul_comm]
        using (canonicalSubgradient_spec u).2 j
    have hpos : 0<facetSign (canonicalFacet u) j*v 0 j := by
      rw [hv0,hprod]
      exact abs_pos.mpr (hufull j)
    exact (continuous_const.mul (hvcont j)).continuousAt.eventually
      (eventually_gt_nhds hpos)
  have hposj (j : Fin 3) : ∀ᶠ t in 𝓝 (0 : ℝ), 0<w t j := by
    have hpos : 0<w 0 j := by rw [hw0]; exact hr j
    exact (hwcont j).continuousAt.eventually (eventually_gt_nhds hpos)
  have hsign : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j,
      0<facetSign (canonicalFacet u) j*v t j :=
    (eventually_all.2 hsignj).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, 0<w t j :=
    (eventually_all.2 hposj).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t<1 :=
    (eventually_lt_nhds (show (0 : ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,hsign,hpos,ht1,ht0⟩ :=
    (hsign.and (hpos.and (hlt.and self_mem_nhdsWithin))).exists
  have hc0 : 0≤rotationCos t := by
    unfold rotationCos
    apply div_nonneg _ (rotation_denom_pos t).le
    nlinarith
  have hc1 : rotationCos t<1 := by
    apply (div_lt_one (rotation_denom_pos t)).2
    nlinarith [sq_pos_of_pos ht0]
  have hdU : 0≤rotationSin e t*U := by
    have heq : rotationSin e t*U=(e*U)*(2*t)/(1+t^2) := by
      unfold rotationSin
      ring
    rw [heq]
    positivity
  have hvnorm : l1 (v t)=rotationCos t := by
    have habs (j : Fin 3) : |v t j|=v t j*facetSign (canonicalFacet u) j := by
      have ha := abs_of_pos (hsign j)
      rw [abs_mul,facetSign_abs,one_mul] at ha
      simpa only [mul_comm] using ha
    unfold l1
    simp_rw [habs]
    change facetValue (v t) (canonicalFacet u)=rotationCos t
    have hu' : facetValue u (canonicalFacet u)=1 := by
      simpa only [facetValue_canonical,l1,Fin.sum_univ_three] using hu
    calc
      _ = rotationCos t*facetValue u (canonicalFacet u)+
          rotationSin e t*facetValue r (canonicalFacet u) := by
        simp only [facetValue,v,rotateFirst,add_mul,Finset.sum_add_distrib,
          ← Finset.mul_sum,mul_assoc]
      _ = _ := by rw [hu',horth]; ring
  have hwnorm : l1 (w t)=rotationCos t*l1 r-rotationSin e t*U := by
    unfold l1
    simp_rw [abs_of_pos (hpos _),abs_of_pos (hr _)]
    simp only [w,rotateSecond,Finset.sum_sub_distrib,← Finset.mul_sum,U]
  have hwlt : l1 (w t)<1 := by
    rw [hwnorm]
    have hmul := mul_le_mul_of_nonneg_left hrbound hc0
    nlinarith
  refine ⟨rotationCos t,rotationSin e t,rotation_circle he,?_,hwlt,?_⟩
  · change l1 (v t)<1
    rw [hvnorm]
    exact hc1
  · exact rotated_pair_independent (saturated_positive_pair_independent hu hr horth)
      (rotation_circle he)

def replaceTwoRows {ι : Type*} [DecidableEq ι]
    (A : ι → Fin 3 → ℝ) (i k : ι) (u r : Fin 3 → ℝ) :=
  fun l => if l=i then u else if l=k then r else A l

private theorem sum_eq_two_add_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) {i k : ι} (hik : i≠k) :
    (∑ l, f l)=f i+f k+∑ l ∈ (Finset.univ.erase i).erase k, f l := by
  have hi := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hk := Finset.sum_erase_add (Finset.univ.erase i) f
    (Finset.mem_erase.mpr ⟨Ne.symm hik,Finset.mem_univ k⟩)
  linarith

theorem replaceTwoRows_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Fin 3 → ℝ) {i k : ι} (hik : i≠k) {c d : ℝ}
    (hcd : c^2+d^2=1) (j l : Fin 3) :
    crossGram
      (replaceTwoRows A i k (rotateFirst (A i) (A k) c d) (rotateSecond (A i) (A k) c d))
      (replaceTwoRows A i k (rotateFirst (A i) (A k) c d) (rotateSecond (A i) (A k) c d)) j l =
      crossGram A A j l := by
  unfold crossGram
  rw [sum_eq_two_add_erase _ hik,sum_eq_two_add_erase (fun q => A q j*A q l) hik]
  have hfirst := rotated_pair_gram (u := A i) (r := A k) hcd j l
  simp only [replaceTwoRows,if_pos rfl,if_neg (Ne.symm hik),ite_true]
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hqi : q≠i := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
  have hqk : q≠k := (Finset.mem_erase.mp hq).1
  simp [hqi,hqk]

theorem exists_feasible_slack_independent_rows {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A)
    (i k : ι) (hik : i≠k)
    (hu : l1 (A i)=1) (hufull : ∀ j, A i j≠0)
    (hr : ∀ j, 0<A k j)
    (horth : facetValue (A k) (canonicalFacet (A i))=0) :
    ∃ B : ι → Fin 3 → ℝ, Feasible s B ∧
      l1 (B i)<1 ∧ l1 (B k)<1 ∧ RowPairIndependent (B i) (B k) ∧
      ∀ q, q≠i → q≠k → B q=A q := by
  classical
  have hrb : l1 (A k)≤1 := by simpa only [l1,Fin.sum_univ_three] using hA.1 k
  obtain ⟨c,d,hcd,hv,hw,hind⟩ := exists_slack_pair_rotation hu hufull hr hrb horth
  let B := replaceTwoRows A i k (rotateFirst (A i) (A k) c d) (rotateSecond (A i) (A k) c d)
  have hBi : B i=rotateFirst (A i) (A k) c d := by simp [B,replaceTwoRows]
  have hBk : B k=rotateSecond (A i) (A k) c d := by simp [B,replaceTwoRows,Ne.symm hik]
  have hrows : ∀ q, RowBound (B q) := by
    intro q
    by_cases hqi : q=i
    · subst q
      rw [hBi]
      simpa only [l1,Fin.sum_univ_three] using hv.le
    by_cases hqk : q=k
    · subst q
      rw [hBk]
      simpa only [l1,Fin.sum_univ_three] using hw.le
    · simpa [B,replaceTwoRows,hqi,hqk] using hA.1 q
  refine ⟨B,⟨hrows,?_⟩,?_,?_,?_,?_⟩
  · intro j l
    exact (replaceTwoRows_gram A hik hcd j l).trans (hA.2 j l)
  · simpa only [hBi] using hv
  · simpa only [hBk] using hw
  · simpa only [hBi,hBk] using hind
  · intro q hqi hqk
    simp [B,replaceTwoRows,hqi,hqk]

theorem multiplier_annihilates_slack_row {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A) (i : ι)
    (hslack : l1 (A i)<1) :
    M.weight i=0 ∧ ∀ j, (∑ k, A i k*M.matrix k j)=0 := by
  have hw : M.weight i=0 := by
    by_contra hne
    have hp : 0<M.weight i := lt_of_le_of_ne (M.weight_nonneg i) (Ne.symm hne)
    have hs := M.complementary i hp
    have hs' : l1 (A i)=1 := by simpa only [l1,Fin.sum_univ_three] using hs
    linarith
  refine ⟨hw,?_⟩
  intro j
  rw [M.stationarity,hw,zero_mul]

theorem exists_optimal_independent_kernel_rows {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s)
    (i k : Fin n) (hik : i≠k)
    (hu : l1 (A i)=1) (hufull : ∀ j, A i j≠0)
    (hr : ∀ j, 0<A k j)
    (horth : facetValue (A k) (canonicalFacet (A i))=0) :
    ∃ B : Fin n → Fin 3 → ℝ, ∃ M : MultiplierSystem B,
      Feasible s B ∧ l1 (B i)<1 ∧ l1 (B k)<1 ∧
      RowPairIndependent (B i) (B k) ∧
      (∀ j, (∑ l, B i l*M.matrix l j)=0) ∧
      (∀ j, (∑ l, B k l*M.matrix l j)=0) := by
  obtain ⟨B,hB,hi,hk,hind,_⟩ :=
    exists_feasible_slack_independent_rows hA i k hik hu hufull hr horth
  obtain ⟨M⟩ := exists_multiplier_at_optimum hB hs hopt
  exact ⟨B,M,hB,hi,hk,hind,(multiplier_annihilates_slack_row M i hi).2,
    (multiplier_annihilates_slack_row M k hk).2⟩

end
end F3
