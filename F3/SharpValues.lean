import F3.FullBranchConclusions
import F3.NoFullConclusions
import F3.SupportBound
import F3.Attainment
import F3.ActiveResidueTwo

/-! Sharp values of the actual finite-frame optimization problem.
All root and frame constructions, optimization reductions, and branch
estimates used below are proved in the imported modules. -/
namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

def firstResidueCorrection (m : ℕ) : ℝ :=
  if m=1 then firstExceptionalRoot^2
  else if m=2 then secondExceptionalRoot^2
  else 15-4*Real.sqrt 14

lemma first_residue_correction_positive (m : ℕ) : 0<firstResidueCorrection m := by
  obtain ⟨h1,h12,h2,h23,h3⟩ := canonical_exceptional_correction_order
  unfold firstResidueCorrection
  split_ifs <;> linarith

lemma stable_first_residue_feasible {m : ℕ} (hm : 3≤m) :
    FeasibleValue (3*m+1) ((m:ℝ)+(15-4*Real.sqrt 14)) := by
  have hn : 10+3*(m-3)=3*m+1 := by omega
  have hmr : ((m-3:ℕ):ℝ)+3=(m:ℝ) := by exact_mod_cast Nat.sub_add_cancel hm
  have ht := mod_one_stable_construction (m-3)
  rw [hn] at ht
  convert ht using 1 <;> linarith

lemma second_residue_feasible {m : ℕ} (hm : 1≤m) :
    FeasibleValue (3*m+2) ((m:ℝ)+(10-4*Real.sqrt 6)) := by
  have hn : 5+3*(m-1)=3*m+2 := by omega
  have hmr : ((m-1:ℕ):ℝ)+1=(m:ℝ) := by exact_mod_cast Nat.sub_add_cancel hm
  have ht := mod_two_construction (m-1)
  rw [hn] at ht
  convert ht using 1 <;> linarith

lemma first_residue_feasible {m : ℕ} (hm : 1≤m) :
    FeasibleValue (3*m+1) ((m:ℝ)+firstResidueCorrection m) := by
  by_cases h1 : m=1
  · subst m
    simpa [firstResidueCorrection] using canonical_exceptional_frames.1
  by_cases h2 : m=2
  · subst m
    simpa [firstResidueCorrection] using canonical_exceptional_frames.2
  · simpa [firstResidueCorrection,h1,h2] using stable_first_residue_feasible (show 3≤m by omega)

lemma first_residue_upper_at_optimum {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ} (hd : 0<δ)
    (hA : Feasible ((m:ℝ)+δ) A) (hopt : OptimalValue (3*m+1) ((m:ℝ)+δ)) :
    δ≤firstResidueCorrection m := by
  classical
  obtain ⟨M⟩ := exists_multiplier_at_optimum hA (by positivity) hopt
  have hw := active_residue_one hd hA M
  have hcoarse := Dominance.three_column_coarse hd hA
  have hcoarsehi := Dominance.three_dimensional_bound_lt_72_div_1000
  have hdhi : δ≤72/1000 := by linarith
  obtain ⟨hr1,hr12,hr2,hr23,hr3⟩ := canonical_exceptional_correction_order
  by_cases hf : ∃i,∀j,A i j≠0
  · have hF : (fullRows A).Nonempty := by
      obtain ⟨i,hi⟩ := hf
      exact ⟨i,(full_row_iff A i).mpr hi⟩
    have hb := residue_one_full_support_bound hd hA hopt hf
    have ht := full_rows_residue_one hA M hw hF hb hd hdhi
    by_cases h1 : m=1
    · simp only [firstResidueCorrection,h1,ite_true]
      rcases ht with h | h | h
      · omega
      · exact h.le
      · omega
    by_cases h2 : m=2
    · simp [firstResidueCorrection,h1,h2]
      rcases ht with h | h | h <;> linarith
    · simp only [firstResidueCorrection,h1,h2,ite_false]
      rcases ht with h | h | h <;> linarith
  · have hn : ∀i,∃j,A i j=0 := by
      push_neg at hf
      exact hf
    by_cases h1 : m=1
    · subst m
      have hA' : Feasible ((1:ℝ)+δ) A := by simpa using hA
      exact False.elim (no_full_dimension_four_impossible hA' M hw hn hd)
    by_cases h2 : m=2
    · subst m
      have hA' : Feasible ((2:ℝ)+δ) A := by simpa using hA
      have ht := no_full_dimension_seven_bound hA' M hw hn hd
      simp only [firstResidueCorrection,show (2:ℕ)≠1 by decide,ite_false,ite_true]
      linarith
    · simpa only [firstResidueCorrection,h1,h2,ite_false] using no_full_residue_one_bound hA M hw hn hd

/-- The complete first-residue sharp-value theorem for the actual supremum. -/
theorem frameValue_first_residue {m : ℕ} (hm : 1≤m) :
    frameValue (3*m+1)=(m:ℝ)+firstResidueCorrection m := by
  have hlo := feasible_le_frameValue (first_residue_feasible hm)
  have hcorr := first_residue_correction_positive m
  let δ := frameValue (3*m+1)-(m:ℝ)
  have hd : 0<δ := by dsimp [δ]; linarith
  obtain ⟨A,hA⟩ := frameValue_attained (3*m+1)
  have hA' : Feasible ((m:ℝ)+δ) A := by simpa [δ] using hA
  have hopt : OptimalValue (3*m+1) ((m:ℝ)+δ) := by simpa [δ] using frameValue_optimal (3*m+1)
  have hu := first_residue_upper_at_optimum hd hA' hopt
  dsimp [δ] at hu
  linarith

theorem frameValue_four : frameValue 4=1+firstExceptionalRoot^2 := by
  simpa [firstResidueCorrection] using frameValue_first_residue (m:=1) (by decide)

theorem frameValue_seven : frameValue 7=2+secondExceptionalRoot^2 := by
  simpa [firstResidueCorrection] using frameValue_first_residue (m:=2) (by decide)

theorem frameValue_stable_first_residue {m : ℕ} (hm : 3≤m) :
    frameValue (3*m+1)=(m:ℝ)+(15-4*Real.sqrt 14) := by
  simpa [firstResidueCorrection,show m≠1 by omega,show m≠2 by omega] using
    frameValue_first_residue (show 1≤m by omega)

/-- Lower bounds for every residue, built from the actual finite frames. -/
theorem formula_feasible {n : ℕ} (hn : 3≤n) :
    FeasibleValue n (formula (firstExceptionalRoot^2) (secondExceptionalRoot^2) n) := by
  have hmod := Nat.mod_lt n (by decide : 0<3)
  have hdiv := Nat.mod_add_div n 3
  rcases (show n%3=0 ∨ n%3=1 ∨ n%3=2 by omega) with h0 | h1 | h2
  · have he : n=3*(n/3) := by omega
    rw [he,formula_at_three_mul _ _ (show 1≤n/3 by omega)]
    exact divisible_feasible _
  · have he : n=3*(n/3)+1 := by omega
    have hm : 1≤n/3 := by omega
    have hf : formula (firstExceptionalRoot^2) (secondExceptionalRoot^2) (3*(n/3)+1)=
        (n/3:ℕ)+firstResidueCorrection (n/3) := by
      by_cases hq1 : n/3=1
      · simp [hq1,formula,firstResidueCorrection]
      by_cases hq2 : n/3=2
      · simp [hq2,formula,firstResidueCorrection]
      · rw [formula_at_mod_one _ _ (show 3≤n/3 by omega)]
        simp [firstResidueCorrection,hq1,hq2]
    rw [he,hf]
    exact first_residue_feasible hm
  · have he : n=3*(n/3)+2 := by omega
    have hm : 1≤n/3 := by omega
    rw [he,formula_at_mod_two _ _ hm]
    exact second_residue_feasible hm

lemma second_residue_upper_at_optimum {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ}
    (hdlo : 10-4*Real.sqrt 6≤δ)
    (hA : Feasible ((m:ℝ)+δ) A) (hopt : OptimalValue (3*m+2) ((m:ℝ)+δ)) :
    δ≤10-4*Real.sqrt 6 := by
  classical
  have hd : 1/5<δ := lt_of_lt_of_le Transfer.correction_two_bounds.1 hdlo
  have hd0 : 0<δ := by linarith
  have hsp : 0<(m:ℝ)+δ := by positivity
  obtain ⟨M⟩ := exists_multiplier_at_optimum hA hsp hopt
  have hw := active_residue_two hA hopt M hd
  have hdhi := residue_two_preliminary_upper hd0.le hA
  by_cases hf : ∃i,∀j,A i j≠0
  · have hF : (fullRows A).Nonempty := by
      obtain ⟨i,hi⟩ := hf
      exact ⟨i,(full_row_iff A i).mpr hi⟩
    have hb := full_support_bound_at_optimum hA hsp hopt
      (fun N => active_residue_two hA hopt N hd) hf
    exact False.elim (full_rows_residue_two_impossible hA M hw hF hb hd hdhi)
  · have hn : ∀i,∃j,A i j=0 := by
      push_neg at hf
      exact hf
    exact no_full_residue_two_bound hA M hw hn hdlo hdhi

/-- The complete second-residue sharp-value theorem for the actual supremum. -/
theorem frameValue_second_residue {m : ℕ} (hm : 1≤m) :
    frameValue (3*m+2)=(m:ℝ)+(10-4*Real.sqrt 6) := by
  have hlo := feasible_le_frameValue (second_residue_feasible hm)
  let δ := frameValue (3*m+2)-(m:ℝ)
  have hdlo : 10-4*Real.sqrt 6≤δ := by dsimp [δ]; linarith
  obtain ⟨A,hA⟩ := frameValue_attained (3*m+2)
  have hA' : Feasible ((m:ℝ)+δ) A := by simpa [δ] using hA
  have hopt : OptimalValue (3*m+2) ((m:ℝ)+δ) := by simpa [δ] using frameValue_optimal (3*m+2)
  have hu := second_residue_upper_at_optimum hdlo hA' hopt
  dsimp [δ] at hu
  linarith

theorem frameValue_five : frameValue 5=11-4*Real.sqrt 6 := by
  have ht := frameValue_second_residue (m:=1) (by decide)
  norm_num at ht
  linarith

/-- The manuscript's complete piecewise formula, proved for the genuine
optimization value and the canonically isolated exceptional roots. -/
theorem frameValue_eq_formula {n : ℕ} (hn : 3≤n) :
    frameValue n=formula (firstExceptionalRoot^2) (secondExceptionalRoot^2) n := by
  have hmod := Nat.mod_lt n (by decide : 0<3)
  have hdiv := Nat.mod_add_div n 3
  rcases (show n%3=0 ∨ n%3=1 ∨ n%3=2 by omega) with h0 | h1 | h2
  · have he : n=3*(n/3) := by omega
    rw [he,frameValue_three_mul,formula_at_three_mul _ _ (show 1≤n/3 by omega)]
  · have he : n=3*(n/3)+1 := by omega
    have hm : 1≤n/3 := by omega
    rw [he,frameValue_first_residue hm]
    by_cases hq1 : n/3=1
    · simp [hq1,formula,firstResidueCorrection]
    by_cases hq2 : n/3=2
    · simp [hq2,formula,firstResidueCorrection]
    · rw [formula_at_mod_one _ _ (show 3≤n/3 by omega)]
      simp [firstResidueCorrection,hq1,hq2]
  · have he : n=3*(n/3)+2 := by omega
    have hm : 1≤n/3 := by omega
    rw [he,frameValue_second_residue hm,formula_at_mod_two _ _ hm]

theorem canonical_sharp_values :
    SharpValues frameValue (firstExceptionalRoot^2) (secondExceptionalRoot^2) :=
  fun _ hn => frameValue_eq_formula hn

theorem frameValue_recurrence {n : ℕ} (hn : 8≤n) :
    frameValue (n+3)=frameValue n+1 :=
  frameValue_recurrence_of_sharp_values canonical_sharp_values hn

theorem frameSide_squared_recurrence {n : ℕ} (hn : 8≤n) :
    (frameSide (n+3))^2=(frameSide n)^2+1 :=
  frameSide_squared_recurrence_of_sharp_values canonical_sharp_values hn

theorem frameValue_recurrence_except {n : ℕ}
    (hn : 3≤n) (h4 : n≠4) (h7 : n≠7) :
    frameValue (n+3)=frameValue n+1 := by
  rw [frameValue_eq_formula (show 3≤n+3 by omega),frameValue_eq_formula hn]
  exact formula_recurrence_except _ _ hn h4 h7

theorem frameValue_exceptional_gaps :
    frameValue 4+1<frameValue 7 ∧ frameValue 7+1<frameValue 10 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := canonical_exceptional_correction_order
  constructor
  · rw [frameValue_four,frameValue_seven]
    linarith
  · have ht := frameValue_stable_first_residue (m:=3) (by decide)
    norm_num at ht
    rw [frameValue_seven,ht]
    linarith

theorem frameValue_recurrence_iff {n : ℕ} (hn : 3≤n) :
    (frameValue (n+3)=frameValue n+1) ↔ n≠4 ∧ n≠7 := by
  constructor
  · intro he
    constructor
    · intro h
      subst n
      have hg := frameValue_exceptional_gaps.1
      norm_num at he
      linarith
    · intro h
      subst n
      have hg := frameValue_exceptional_gaps.2
      norm_num at he
      linarith
  · rintro ⟨h4,h7⟩
    exact frameValue_recurrence_except hn h4 h7

theorem frameSide_squared_recurrence_iff {n : ℕ} (hn : 3≤n) :
    ((frameSide (n+3))^2=(frameSide n)^2+1) ↔ n≠4 ∧ n≠7 := by
  rw [frameSide_sq,frameSide_sq]
  exact frameValue_recurrence_iff hn

theorem geometricValue_sq_eq_formula {n : ℕ} (hn : 3≤n) :
    (geometricValue n)^2=formula (firstExceptionalRoot^2) (secondExceptionalRoot^2) n := by
  rw [geometricValue_sq,frameValue_eq_formula hn]

theorem geometricValue_squared_recurrence_iff {n : ℕ} (hn : 3≤n) :
    ((geometricValue (n+3))^2=(geometricValue n)^2+1) ↔ n≠4 ∧ n≠7 := by
  rw [geometricValue_sq,geometricValue_sq]
  exact frameValue_recurrence_iff hn

end
end F3
