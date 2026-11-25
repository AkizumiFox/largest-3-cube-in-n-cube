import F3.PairStationarity
import F3.ColumnPermutations
import F3.Dominance
import F3.Transfer

/-! Pair-supported rows of actual stationary frames.  All edge directions
are derived from the multiplier equations and column orthogonality. -/
namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem multiplier_no_signed_entry_equality {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s ε : ℝ}
    (hA : Feasible s A) (M : MultiplierSystem A)
    (hw : ∀ i, 0<M.weight i) (hε : ε^2=1) {j k : Fin 3} (hjk : j≠k)
    (hover : ∃ i, A i j≠0 ∧ A i k≠0) :
    ε*M.matrix j k≠M.matrix j j := by
  intro he
  have hεabs : |ε|=1 := by nlinarith [sq_abs ε,abs_nonneg ε]
  let gap : ι → ℝ := fun i => |A i j|-ε*A i j*M.gradient i k
  have hgap (i : ι) : 0≤gap i := by
    have hbound : |ε*A i j*M.gradient i k|≤|A i j| := by
      rw [abs_mul,abs_mul,hεabs,one_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) ((M.subgradient i).1 k)
    have hh := (le_abs_self (ε*A i j*M.gradient i k)).trans hbound
    exact sub_nonneg.mpr hh
  have hsum : (∑ i, M.weight i*gap i)=0 := by
    have hdiag := multiplier_diagonal_identity hA M j
    have hcross := multiplier_column_identity hA M j k
    calc
      _ = (∑ i, M.weight i*|A i j|)-ε*(∑ i, M.weight i*A i j*M.gradient i k) := by
        simp only [gap,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = s*M.matrix j j-ε*(s*M.matrix j k) := by rw [← hdiag,← hcross]
      _ = 0 := by rw [← he]; ring
  have hz (i : ι) : gap i=0 := by
    have hm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hw i).le (hgap i))).mp hsum i (Finset.mem_univ _)
    exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt (hw i))
  have hprod (i : ι) : ε*(A i j*A i k)=|A i j| * |A i k| := by
    by_cases hk : A i k=0
    · simp [hk]
    have hg := (M.subgradient i).2 k
    have ha := congrArg abs hg
    rw [abs_mul,abs_abs] at ha
    have hb : 0< |A i k| := abs_pos.mpr hk
    have hgabs : |M.gradient i k|=1 := by nlinarith
    have hgsq : (M.gradient i k)^2=1 := by nlinarith [sq_abs (M.gradient i k)]
    have hgapzero : ε*A i j*M.gradient i k=|A i j| := by
      have hh := hz i
      dsimp [gap] at hh
      linarith
    calc
      _ = ε*A i j*A i k*(M.gradient i k)^2 := by rw [hgsq]; ring
      _ = (ε*A i j*M.gradient i k)*(A i k*M.gradient i k) := by ring
      _ = _ := by rw [hgapzero,hg]
  have hcancel : (∑ i, |A i j| * |A i k|)=0 := by
    simp_rw [← hprod]
    rw [← Finset.mul_sum,hA.2,if_neg hjk,mul_zero]
  obtain ⟨i,hi,hk⟩ := hover
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))).mp hcancel i
      (Finset.mem_univ _)
  exact (ne_of_gt (mul_pos (abs_pos.mpr hi) (abs_pos.mpr hk))) hzero

theorem multiplier_entry_strict_on_overlap {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (hw : ∀ i, 0<M.weight i)
    {j k : Fin 3} (hjk : j≠k) (hover : ∃ i, A i j≠0 ∧ A i k≠0) :
    |M.matrix j k|<M.matrix j j := by
  have hb := multiplier_entry_bound hA hs M j k
  apply lt_of_le_of_ne hb
  intro he
  have hsign := Dominance.signUnit_mul (M.matrix j k)
  have hn := multiplier_no_signed_entry_equality hA M hw
    (Dominance.signUnit_sq (M.matrix j k)) hjk hover
  apply hn
  rw [mul_comm,hsign,he]

theorem actual_pair_orientation {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (hw : ∀ i, 0<M.weight i)
    (i : ι) {j k : Fin 3} (hjk : j≠k)
    (hj : A i j≠0) (hk : A i k≠0)
    (hz : ∀ l,l≠j → l≠k → A i l=0) :
    (|A i k|< |A i j| ↔ M.matrix j j<M.matrix k k) := by
  have hb1 := multiplier_entry_strict_on_overlap hA hs M hw hjk ⟨i,hj,hk⟩
  have hb2 := multiplier_entry_strict_on_overlap hA hs M hw hjk.symm ⟨i,hk,hj⟩
  rw [M.symmetric k j] at hb2
  have ha := abs_pos.mpr hj
  have hb := abs_pos.mpr hk
  have ht1 := abs_lt.mp hb1
  have ht2 := abs_lt.mp hb2
  have hp : A i j*A i k≠0 := mul_ne_zero hj hk
  rcases lt_or_gt_of_ne hp with hn | hn
  · have he := multiplier_negative_pair_stationarity M i hjk hz hn
    simpa only [add_lt_add_iff_right] using
      positive_pair_orientation (by linarith) (by linarith) ha hb he
  · have he := multiplier_positive_pair_stationarity M i hjk hz hn
    simpa only [sub_lt_sub_iff_right] using
      positive_pair_orientation (by linarith) (by linarith) ha hb he

end
end F3
