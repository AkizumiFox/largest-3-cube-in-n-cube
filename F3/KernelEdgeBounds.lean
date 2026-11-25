import F3.OrderedPairBookkeeping

/-! Exact product and energy estimates for pair rows with a nonzero exceptional
row contribution to column orthogonality. -/

namespace F3
noncomputable section
open scoped BigOperators

def pairEdgeAbsProduct {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (j k : Fin 3) : ℝ :=
  ∑ i ∈ pairEdgeRows A j k, |A i j| * |A i k|

def pairEdgeSignedProduct {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (j k : Fin 3) : ℝ :=
  ∑ i ∈ pairEdgeRows A j k, A i j*A i k

theorem pairEdgeAbsProduct_eq_sum {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (j k : Fin 3) :
    pairEdgeAbsProduct A j k=∑ i, |A i j| * |A i k| := by
  classical
  unfold pairEdgeAbsProduct pairEdgeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hj : A i j=0 <;> by_cases hk : A i k=0 <;> simp [hj,hk]

theorem pairEdgeSignedProduct_eq_sum {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (j k : Fin 3) :
    pairEdgeSignedProduct A j k=∑ i, A i j*A i k := by
  classical
  unfold pairEdgeSignedProduct pairEdgeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hj : A i j=0 <;> by_cases hk : A i k=0 <;> simp [hj,hk]

theorem pairEdgeAbsProduct_nonneg {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (j k : Fin 3) : 0≤pairEdgeAbsProduct A j k :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem pairEdgeLoss_eq_two_abs {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (j k : Fin 3) :
    pairEdgeLoss A j k=2*pairEdgeAbsProduct A j k := by
  simp only [pairEdgeLoss,pairEdgeAbsProduct,Finset.mul_sum,mul_assoc]

theorem pairEdge_abs_signed_le {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (j k : Fin 3) :
    |pairEdgeSignedProduct A j k|≤pairEdgeAbsProduct A j k := by
  simpa only [pairEdgeSignedProduct,pairEdgeAbsProduct,abs_mul] using
    Finset.abs_sum_le_sum_abs (fun i => A i j*A i k) (pairEdgeRows A j k)

theorem pairEdgeAbsProduct_of_nonpos {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {j k : Fin 3}
    (hneg : ∀ i, A i j*A i k≤0) :
    pairEdgeAbsProduct A j k= -pairEdgeSignedProduct A j k := by
  unfold pairEdgeAbsProduct pairEdgeSignedProduct
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← abs_mul,abs_of_nonpos (hneg i)]

theorem ordered_edge_energy_le_abs {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k) :
    pairEdgeEnergy A j k≤pairEdgeAbsProduct A j k := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  have hip := (mem_pairEdgeRows A i j k).mp hi
  have hlt := (ordered_pair_budget ho i hjk hip.1 hip.2).2.2
  have hsum := (ordered_pair_budget ho i hjk hip.1 hip.2).1
  nlinarith [sq_abs (A i k),abs_nonneg (A i k)]

theorem ordered_edge_deficit_ge_two_abs {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k) :
    2*pairEdgeAbsProduct A j k≤pairEdgeDeficit A j k := by
  rw [pairEdgeDeficit_eq ho hjk,pairEdgeLoss_eq_two_abs]
  exact le_add_of_nonneg_right (pairEdgeEnergy_nonneg A j k)

theorem ordered_edge_energy_le_square {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hbhalf : b≤1/2) (hab : a+b≤1)
    (hmass : pairEdgeAbsProduct A j k=a*b) : pairEdgeEnergy A j k≤b^2 := by
  classical
  have hsmall (i : ι) (hi : i∈pairEdgeRows A j k) : |A i k|≤b := by
    have hip := (mem_pairEdgeRows A i j k).mp hi
    have hbudget := ordered_pair_budget ho i hjk hip.1 hip.2
    have hp : |A i j| * |A i k|≤a*b := by
      rw [← hmass]
      change |A i j| * |A i k|≤∑ l∈pairEdgeRows A j k,|A l j| * |A l k|
      exact Finset.single_le_sum
        (fun l _ => mul_nonneg (abs_nonneg (A l j)) (abs_nonneg (A l k))) hi
    have habprod : a*b≤b*(1-b) := by nlinarith
    by_cases hle : |A i k|≤b
    · exact hle
    exfalso
    have hgt := lt_of_not_ge hle
    have hpositive : 0<(|A i k|-b)*(1-b-|A i k|) := by
      apply mul_pos (sub_pos.mpr hgt)
      linarith
    nlinarith
  have hweighted : (1-b)*pairEdgeEnergy A j k≤b*pairEdgeAbsProduct A j k := by
    unfold pairEdgeEnergy pairEdgeAbsProduct
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hip := (mem_pairEdgeRows A i j k).mp hi
    have hbudget := (ordered_pair_budget ho i hjk hip.1 hip.2).1
    have hsmall' := hsmall i hi
    have hprod := mul_nonneg (abs_nonneg (A i k)) (sub_nonneg.mpr hsmall')
    nlinarith [sq_abs (A i k)]
  rw [hmass] at hweighted
  have hupper : a*b^2≤(1-b)*b^2 := by
    exact mul_le_mul_of_nonneg_right (by linarith : a≤1-b) (sq_nonneg b)
  have hfactor : 0<1-b := by linarith
  nlinarith

theorem twice_abs_term_le_abs_sum_add_abs_sum {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (x : ι → ℝ) {i : ι} (hi : i∈T) :
    2*|x i|≤|∑ j∈T,x j|+∑ j∈T,|x j| := by
  have hs := Finset.sum_erase_add T x hi
  have ha := Finset.sum_erase_add T (fun j => |x j|) hi
  dsimp only at hs ha
  have htri : |x i|≤|∑ j∈T,x j|+|∑ j∈T.erase i,x j| := by
    calc
      |x i| = |(∑ j∈T,x j)-(∑ j∈T.erase i,x j)| := by congr 1; linarith
      _ ≤ _ := abs_sub _ _
  have habs := Finset.abs_sum_le_sum_abs x (T.erase i)
  linarith

theorem ordered_edge_energy_lt_one_over_35 {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (ho : OrderedPairFrame A) {j k : Fin 3} (hjk : j<k)
    {q : ℝ} (hq : 0≤q) (hsigned : pairEdgeSignedProduct A j k= -q)
    (hsmall : q+pairEdgeAbsProduct A j k<1/5) : pairEdgeEnergy A j k<1/35 := by
  classical
  have hterm (i : ι) (hi : i∈pairEdgeRows A j k) : |A i k|<1/8 := by
    have htwice := twice_abs_term_le_abs_sum_add_abs_sum
      (pairEdgeRows A j k) (fun l => A l j*A l k) hi
    have habs : 2*(|A i j| * |A i k|)≤q+pairEdgeAbsProduct A j k := by
      have htwice' : 2*|A i j*A i k|≤|pairEdgeSignedProduct A j k|+
          pairEdgeAbsProduct A j k := by
        simpa only [pairEdgeSignedProduct,pairEdgeAbsProduct,abs_mul] using htwice
      simpa only [abs_mul,hsigned,abs_neg,abs_of_nonneg hq] using htwice'
    have hip := (mem_pairEdgeRows A i j k).mp hi
    have hb := ordered_pair_budget ho i hjk hip.1 hip.2
    by_cases hlt : |A i k|<1/8
    · exact hlt
    exfalso
    have hle := le_of_not_gt hlt
    have hm : 0≤(|A i k|-1/8)*(7/8-|A i k|) := by
      apply mul_nonneg
      · linarith
      · linarith
    nlinarith
  have hsum : 7*pairEdgeEnergy A j k≤pairEdgeAbsProduct A j k := by
    unfold pairEdgeEnergy pairEdgeAbsProduct
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hip := (mem_pairEdgeRows A i j k).mp hi
    have hb := (ordered_pair_budget ho i hjk hip.1 hip.2).1
    have hs := hterm i hi
    nlinarith [sq_abs (A i k),abs_nonneg (A i k)]
  linarith

end
end F3
