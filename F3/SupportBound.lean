import F3.SupportDimension
import F3.SecondOrderBridge
import F3.ActiveRows

/-! The genuine optimizer support bound, with all multiplier quantifiers
retained exactly as in the manuscript. -/
namespace F3
noncomputable section

theorem full_support_bound_at_optimum {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s)
    (hw : ∀ M : MultiplierSystem A, ∀ i, 0<M.weight i)
    (hfull : ∃ i, ∀ j, A i j≠0) :
    (pairRows A).card+2*(fullRows A).card≤5 := by
  obtain ⟨M⟩ := exists_multiplier_at_optimum hA hs hopt
  exact support_bound_of_no_face_tangent hA hs M
    (fun i => M.complementary i (hw M i))
    (no_face_tangent_at_full_optimum hA hs hopt hw hfull)

theorem residue_one_full_support_bound {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hδ : 0<δ) (hA : Feasible ((m:ℝ)+δ) A)
    (hopt : OptimalValue (3*m+1) ((m:ℝ)+δ))
    (hfull : ∃ i, ∀ j, A i j≠0) :
    (pairRows A).card+2*(fullRows A).card≤5 :=
  full_support_bound_at_optimum hA (by positivity) hopt
    (fun M => active_residue_one hδ hA M) hfull

theorem residue_one_full_count_classification {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hδ : 0<δ) (hA : Feasible ((m:ℝ)+δ) A)
    (hopt : OptimalValue (3*m+1) ((m:ℝ)+δ))
    (hfull : ∃ i, ∀ j, A i j≠0) :
    ((fullRows A).card=1 ∧ (pairRows A).card=3) ∨
    ((fullRows A).card=2 ∧ (pairRows A).card=1) := by
  apply full_pair_count_classification hA
  · obtain ⟨i,hi⟩ := hfull
    exact ⟨i,(full_row_iff A i).mpr hi⟩
  · exact residue_one_full_support_bound hδ hA hopt hfull

end
end F3
