import F3.TwoFullExtraction

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Complete first-residue full-row classification from an actual finite frame,
positive multiplier weights, and the support bound. -/
theorem full_rows_residue_one {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hf : (fullRows A).Nonempty)
    (hb : (pairRows A).card+2*(fullRows A).card≤5)
    (hd0 : 0<δ) (hdhi : δ≤72/1000) :
    (2≤m ∧ δ<3/100) ∨ δ=firstExceptionalRoot^2 ∨
      (2≤m ∧ δ=secondExceptionalRoot^2) := by
  have hsp : 0<(m:ℝ)+δ := by positivity
  rcases full_pair_count_classification hA hf hb with h | h
  · obtain ⟨d,p₀,p₁,p₂,ht,he0,he1,he2⟩ := one_full_normal_form hA hsp M hw h.1 h.2
    have ht' : p₀+p₁+p₂+4=3*m+1 := by simpa using ht
    exact Or.inl (d.residue_one hd0 (by linarith) ht' he0 he1 he2)
  · obtain ⟨d,p₀,p₁,p₂,ht,he0,he1,he2⟩ := two_full_normal_form hA
      (fun i => M.complementary i (hw i)) h.1 h.2 hd0 (by linarith)
    have ht' : p₀+p₁+p₂+3=3*m+1 := by simpa using ht
    exact Or.inr (d.residue_one hd0 hdhi ht' he0 he1 he2)

/-- Complete second-residue full-row exclusion from an actual finite frame. -/
theorem full_rows_residue_two_impossible {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hf : (fullRows A).Nonempty)
    (hb : (pairRows A).card+2*(fullRows A).card≤5)
    (hdlo : 1/5<δ) (hdhi : δ≤4/9) : False := by
  have hd0 : 0<δ := by linarith
  have hsp : 0<(m:ℝ)+δ := by positivity
  rcases full_pair_count_classification hA hf hb with h | h
  · obtain ⟨d,p₀,p₁,p₂,ht,he0,he1,he2⟩ := one_full_normal_form hA hsp M hw h.1 h.2
    have ht' : p₀+p₁+p₂+4=3*m+2 := by simpa using ht
    exact d.residue_two_impossible hdlo hdhi ht' he0 he1 he2
  · obtain ⟨d,p₀,p₁,p₂,ht,he0,he1,he2⟩ := two_full_normal_form hA
      (fun i => M.complementary i (hw i)) h.1 h.2 hd0 (by linarith)
    have ht' : p₀+p₁+p₂+3=3*m+2 := by simpa using ht
    exact d.residue_two_impossible hdlo hdhi ht' he0 he1 he2

theorem full_rows_dimension_four {δ : ℝ} {A : Fin (3*1+1) → Fin 3 → ℝ}
    (hA : Feasible ((1:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hf : (fullRows A).Nonempty)
    (hb : (pairRows A).card+2*(fullRows A).card≤5)
    (hd0 : 0<δ) (hdhi : δ≤72/1000) : δ=firstExceptionalRoot^2 := by
  have ht := full_rows_residue_one (m:=1) (by simpa using hA) M hw hf hb hd0 hdhi
  rcases ht with h | h | h
  · omega
  · exact h
  · omega

theorem full_rows_later_residue_one_bound {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+1) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (M : MultiplierSystem A)
    (hw : ∀i,0<M.weight i) (hf : (fullRows A).Nonempty)
    (hb : (pairRows A).card+2*(fullRows A).card≤5)
    (hd0 : 0<δ) (hdhi : δ≤72/1000) : δ≤secondExceptionalRoot^2 := by
  have ht := full_rows_residue_one hA M hw hf hb hd0 hdhi
  obtain ⟨h10,h12,h20,h21,h22⟩ := canonical_exceptional_correction_order
  rcases ht with h | h | h
  · linarith
  · linarith
  · exact h.2.le

end
end F3
