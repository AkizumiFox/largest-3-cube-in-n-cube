import F3.OrderedSmallDimensions
import F3.BalancedExclusion

namespace F3
noncomputable section
open scoped BigOperators

lemma ordered_frame_of_residue_one {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hn : ∀i,∃j,A i j=0) (hd : 0<δ) :
    ∃e : Equiv.Perm (Fin 3), OrderedPairFrame (permuteColumns A e) := by
  have hs := fun i => M.complementary i (hw i)
  have hl := dominance_large_exists hA hd hs
  exact exists_ordered_pair_frame hA (by positivity) M hw hl hn

theorem no_full_residue_one_bound {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hn : ∀i,∃j,A i j=0) (hd : 0<δ) :
    δ≤15-4*Real.sqrt 14 := by
  obtain ⟨e,he⟩ := ordered_frame_of_residue_one hA M hw hn hd
  exact ordered_residue_one_bound (feasible_permuteColumns hA e) he hd

theorem no_full_dimension_four_impossible {δ : ℝ} {A : Fin (3*1+1) → Fin 3 → ℝ}
    (hA : Feasible ((1:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hn : ∀i,∃j,A i j=0) (hd : 0<δ) : False := by
  obtain ⟨e,he⟩ := ordered_frame_of_residue_one (m:=1) (by simpa using hA) M hw hn hd
  exact ordered_dimension_four_impossible (feasible_permuteColumns hA e) he hd

theorem no_full_dimension_seven_bound {δ : ℝ} {A : Fin (3*2+1) → Fin 3 → ℝ}
    (hA : Feasible ((2:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hn : ∀i,∃j,A i j=0) (hd : 0<δ) : δ<3/100 := by
  obtain ⟨e,he⟩ := ordered_frame_of_residue_one (m:=2) (by simpa using hA) M hw hn hd
  exact ordered_dimension_seven_bound (feasible_permuteColumns hA e) he hd

/-- Sharp residue-two no-full-row flow after the balanced-row exclusion has
provided an actual large coordinate in every row. -/
theorem no_full_large_residue_two_bound {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hn : ∀i,∃j,A i j=0)
    (hl : ∀i,∃j,(1:ℝ)/2< |A i j|)
    (hdlo : 10-4*Real.sqrt 6≤δ) (hdhi : δ≤4/9) : δ≤10-4*Real.sqrt 6 := by
  have hd0 : 0<δ := lt_of_lt_of_le (by linarith [Transfer.correction_two_bounds.1]) hdlo
  obtain ⟨e,he⟩ := exists_ordered_pair_frame hA (by positivity) M hw hl hn
  exact ordered_residue_two_bound (feasible_permuteColumns hA e) he hdlo hdhi

/-- The complete actual no-full-row branch in residue two. -/
theorem no_full_residue_two_bound {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hn : ∀i,∃j,A i j=0)
    (hdlo : 10-4*Real.sqrt 6≤δ) (hdhi : δ≤4/9) : δ≤10-4*Real.sqrt 6 := by
  have hd : 1/5<δ := lt_of_lt_of_le Transfer.correction_two_bounds.1 hdlo
  exact no_full_large_residue_two_bound hA M hw hn
    (residue_two_no_full_large hA hd M hw hn) hdlo hdhi

end
end F3
