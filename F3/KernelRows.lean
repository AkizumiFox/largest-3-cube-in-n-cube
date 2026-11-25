import F3.RankOne
import F3.RowKernelMinors
import F3.FiniteRowPadding

namespace F3
noncomputable section
open scoped BigOperators

theorem residue_two_independent_kernel_impossible {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5 < d) (hdhi : d ≤ 4/9)
    {u r : Fin 3 → ℝ} (hind : RowPairIndependent u r)
    (hu : ∀ j, (∑ k, u k*M.matrix k j)=0)
    (hr : ∀ j, (∑ k, r k*M.matrix k j)=0) : False := by
  have hs : 0 < (m : ℝ)+d := by positivity
  obtain ⟨τ,v,hτ,hv,hvn,hform⟩ := multiplier_minors_zero_signed_form hA hs M
    (two_kernel_rows_all_minors_zero hind hu hr)
  exact signed_rank_one_excluded_residue_two hA M hd hdhi hτ v hv hvn hform

theorem row_minor_nonzero_independent {u r : Fin 3 → ℝ} {p j : Fin 3}
    (hminor : u j*r p ≠ u p*r j) : RowPairIndependent u r := by
  intro a b h
  have hp := h p
  have hj := h j
  have ha : a*(u j*r p-u p*r j)=0 := by linear_combination r p*hj-r j*hp
  have ha0 : a=0 := (mul_eq_zero.mp ha).resolve_right (sub_ne_zero.mpr hminor)
  have hnonzero : r p ≠ 0 ∨ r j ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hminor
    simp [hn.1,hn.2]
  refine ⟨ha0,?_⟩
  rcases hnonzero with hrp | hrj
  · rw [ha0,zero_mul,zero_add] at hp
    exact (mul_eq_zero.mp hp).resolve_right hrp
  · rw [ha0,zero_mul,zero_add] at hj
    exact (mul_eq_zero.mp hj).resolve_right hrj

/-- All zero-weight rows in residue two lie on one line, proved without an
unproved rank assumption. -/
theorem residue_two_zero_rows_parallel {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5 < d) (hdhi : d ≤ 4/9)
    (i r : Fin (3*m+2)) (hi : M.weight i=0) (hr : M.weight r=0)
    (p j : Fin 3) : A i j*A r p=A i p*A r j := by
  by_contra hn
  apply residue_two_independent_kernel_impossible hA M hd hdhi (row_minor_nonzero_independent hn)
  · intro k; simpa [hi] using M.stationarity i k
  · intro k; simpa [hr] using M.stationarity r k

theorem residue_two_zero_rows_scalar {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5 < d) (hdhi : d ≤ 4/9)
    (i r : Fin (3*m+2)) (hi : M.weight i=0) (hr : M.weight r=0)
    (p : Fin 3) (hp : A r p ≠ 0) : ∃ t : ℝ, ∀ j, A i j=t*A r j := by
  refine ⟨A i p/A r p,?_⟩
  intro j
  have h := residue_two_zero_rows_parallel hA M hd hdhi i r hi hr p j
  field_simp
  exact h

theorem nondominant_energy_gap {k : ℕ} (a : Fin k → ℝ)
    (hn : ∀ j, ¬ Dominance.Dominant a j) :
    2*Dominance.en a ≤ (Dominance.l1 a)^2 := by
  have hc (j : Fin k) : 2*|a j| ≤ Dominance.l1 a := by
    have h := le_of_not_gt (hn j)
    have he := Dominance.l1_decompose a j
    change |a j| ≤ Dominance.minorL1 a j at h
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (f := fun j => 2*(a j)^2) (g := fun j => |a j| *Dominance.l1 a) (by
      intro j _
      dsimp
      have hm := mul_le_mul_of_nonneg_left (hc j) (abs_nonneg (a j))
      nlinarith [sq_abs (a j)])
  simpa only [← Finset.mul_sum,← Finset.sum_mul,Dominance.en,Dominance.l1,pow_two] using hs

theorem signed_row_energy_bound {a x : Fin 3 → ℝ} (ha : RowBound a) :
    2*Dominance.en a-(∑ j, a j*Dominance.signUnit (x j))^2 ≤ 1 := by
  have h := Dominance.two_energy_le Finset.univ (fun j => a j*Dominance.signUnit (x j))
  simp only [mul_pow,Dominance.signUnit_sq,mul_one,Dominance.abs_mul_signUnit] at h
  have hn : 0 ≤ Dominance.l1 a := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb : Dominance.l1 a ≤ 1 := by simpa only [Dominance.l1,Fin.sum_univ_three] using ha
  change 2*Dominance.en a ≤ (Dominance.l1 a)^2+(∑ j, a j*Dominance.signUnit (x j))^2 at h
  nlinarith

theorem scalar_signed_energy_nonpos {a r : Fin 3 → ℝ} (t : ℝ)
    (ha : ∀ j, a j=t*r j) (hn : ∀ j, ¬ Dominance.Dominant r j) :
    2*Dominance.en a-(∑ j, a j*Dominance.signUnit (r j))^2 ≤ 0 := by
  have hgap := nondominant_energy_gap r hn
  have he : Dominance.en a=t^2*Dominance.en r := by
    simp only [Dominance.en,ha,mul_pow,Finset.mul_sum]
  have hs : (∑ j, a j*Dominance.signUnit (r j))=t*Dominance.l1 r := by
    simp only [ha,mul_assoc,Dominance.signUnit_mul,Dominance.l1,Finset.mul_sum]
  rw [he,hs]
  have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (sub_nonpos.mpr hgap)
  nlinarith

/-- If the common zero-weight direction is not dominant, the loss budget
allows exactly one zero-weight row. -/
theorem residue_two_nondominant_unique_zero {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5 < d) (r : Fin (3*m+2))
    (hr : M.weight r=0) (hn : ∀ j, ¬ Dominance.Dominant (A r) j) :
    ∀ i, i ≠ r → 0 < M.weight i := by
  classical
  have hd0 : 0 ≤ d := by linarith
  have hdhi := residue_two_preliminary_upper hd0 hA
  obtain ⟨p,hp⟩ := residue_two_no_zero_row hd hA r
  let v : Fin 3 → ℝ := fun j => Dominance.signUnit (A r j)
  let R : Fin (3*m+2) → ℝ := fun i => 2*Dominance.en (A i)-(∑ j, A i j*v j)^2
  have hR (i : Fin (3*m+2)) : R i ≤ if M.weight i=0 then 0 else 1 := by
    by_cases hi : M.weight i=0
    · rw [if_pos hi]
      obtain ⟨t,ht⟩ := residue_two_zero_rows_scalar hA M hd hdhi i r hi hr p hp
      exact scalar_signed_energy_nonpos t ht hn
    · rw [if_neg hi]
      exact signed_row_energy_bound (x := A r) (hA.1 i)
  have hsum : (∑ i, R i)=3*((m : ℝ)+d) := by
    simp only [R,Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [Dominance.trace_identity (Dominance.feasibleK_three_iff.mpr hA),
      Dominance.gram_quadratic (Dominance.feasibleK_three_iff.mpr hA) v]
    have hv : (∑ j, (v j)^2)=(3 : ℝ) := by simp [v,Dominance.signUnit_sq]
    rw [hv]
    norm_num
    ring
  have hsumle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hR i)
  rw [hsum,activeCount_sum] at hsumle
  have haclo : (3*m : ℕ) < activeCount M := by
    have hreal : ((3*m : ℕ) : ℝ) < activeCount M := by push_cast; linarith
    exact_mod_cast hreal
  have hacup : activeCount M ≤ 3*m+1 := by
    have hsub : Finset.univ.filter (fun i => M.weight i ≠ 0) ⊆ Finset.univ.erase r := by
      intro i hi
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_univ _⟩
      intro hir
      exact (Finset.mem_filter.mp hi).2 (hir ▸ hr)
    have hc := Finset.card_le_card hsub
    simpa [activeCount] using hc
  have hcount : activeCount M+1=3*m+2 := by omega
  obtain ⟨r',hr',hrest⟩ := activeCount_pred_unique_zero M hcount
  have hrr : r=r' := by
    by_contra hh
    have h := hrest r hh
    rw [hr] at h
    linarith
  simpa [hrr] using hrest

theorem residue_two_zero_diagonal_block_positive {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (h00 : M.matrix 0 0=0) :
    0<M.matrix 1 1*M.matrix 2 2-(M.matrix 1 2)^2 := by
  by_contra hn
  have hd0 : 0≤d := by linarith
  have hs : 0<(m : ℝ)+d := by positivity
  have hdhi := residue_two_preliminary_upper hd0 hA
  obtain ⟨τ,u,hτ,hu,hun,hform⟩ := zero_diagonal_degenerate_form hA hs M h00 (le_of_not_gt hn)
  exact signed_rank_one_excluded_residue_two hA M hd hdhi hτ u hu hun hform

theorem residue_two_no_zero_diagonal_at_zero {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (h00 : M.matrix 0 0=0) : False := by
  classical
  have hs : 0<(m : ℝ)+d := by positivity
  have hdet := residue_two_zero_diagonal_block_positive hA M hd h00
  have h10 : M.matrix 1 0=0 := by rw [M.symmetric 1 0]; exact zero_diagonal_row hA hs M h00 1
  have h20 : M.matrix 2 0=0 := by rw [M.symmetric 2 0]; exact zero_diagonal_row hA hs M h00 2
  have h21 := M.symmetric 2 1
  have haxis (i : Fin (3*m+2)) (hi : M.weight i=0) : A i 1=0 ∧ A i 2=0 := by
    have h1 := zero_weight_row_kernel M i hi 1
    have h2 := zero_weight_row_kernel M i hi 2
    simp only [Fin.sum_univ_three,h10,h20,h21,zero_mul,zero_add] at h1 h2
    have he1 : (M.matrix 1 1*M.matrix 2 2-(M.matrix 1 2)^2)*A i 1=0 := by
      linear_combination M.matrix 2 2*h1-M.matrix 1 2*h2
    have he2 : (M.matrix 1 1*M.matrix 2 2-(M.matrix 1 2)^2)*A i 2=0 := by
      linear_combination M.matrix 1 1*h2-M.matrix 1 2*h1
    exact ⟨(mul_eq_zero.mp he1).resolve_left (ne_of_gt hdet),
      (mul_eq_zero.mp he2).resolve_left (ne_of_gt hdet)⟩
  let P := Finset.univ.filter (fun i => M.weight i≠0)
  have hin (i : Fin (3*m+2)) (hi : i∈P) : A i 0=0 := by
    by_contra ha
    have hz := zero_diagonal_weight_of_nonzero_entry hA hs M h00 i ha
    exact (Finset.mem_filter.mp hi).2 hz
  have hout (i : Fin (3*m+2)) (hi : i∉P) : A i 1=0 ∧ A i 2=0 := by
    have hwi : M.weight i=0 := by simpa [P] using hi
    exact haxis i hwi
  have hb := axis_plane_two_dimensional_bound hA (by linarith) P hin hout
  linarith

theorem residue_two_diagonal_positive {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (j : Fin 3) : 0<M.matrix j j := by
  have hs : 0<(m : ℝ)+d := by positivity
  have hn := multiplier_diagonal_nonneg hA hs M j
  by_contra hh
  have hj : M.matrix j j=0 := le_antisymm (le_of_not_gt hh) hn
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 j
  have hA' := feasible_permuteColumns hA e
  have h00 : (M.permuteColumns e).matrix 0 0=0 := by simpa [e] using hj
  exact residue_two_no_zero_diagonal_at_zero hA' (M.permuteColumns e) hd h00

theorem residue_two_zero_row_nondominant {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (r : Fin (3*m+2))
    (hr : M.weight r=0) : ∀j, ¬Dominance.Dominant (A r) j := by
  intro j hj
  have hs : 0<(m : ℝ)+d := by positivity
  have he := dominant_zero_weight_diagonal hA hs M r hr j hj
  have hp := residue_two_diagonal_positive hA M hd j
  rw [he] at hp
  linarith

theorem residue_two_unique_zero {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (r : Fin (3*m+2))
    (hr : M.weight r=0) : ∀i,i≠r→0<M.weight i :=
  residue_two_nondominant_unique_zero hA M hd r hr (residue_two_zero_row_nondominant hA M hd r hr)

/-- A full zero-weight row rules out every other full row at the optimum. -/
theorem residue_two_full_kernel_other_not_full {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (hopt : OptimalValue (3*m+2) ((m : ℝ)+d))
    (M : MultiplierSystem A) (hd : 1/5<d) (r : Fin (3*m+2))
    (hr : M.weight r=0) (hrpos : ∀j,0<A r j) :
    ∀i,i≠r→∃j,A i j=0 := by
  intro i hir
  by_contra hn
  have hfull : ∀j,A i j≠0 := by simpa using hn
  have hi := residue_two_unique_zero hA M hd r hr i hir
  have hs : 0<(m : ℝ)+d := by positivity
  have hsat : Dominance.l1 (A i)=1 := by
    simpa only [Dominance.l1,Fin.sum_univ_three] using M.complementary i hi
  have hgrad : ∀j,M.gradient i j=facetSign (canonicalFacet (A i)) j := by
    intro j
    have hcan := (canonicalSubgradient_spec (A i)).2 j
    have he : M.gradient i j=canonicalSubgradient (A i) j := by
      apply mul_left_cancel₀ (hfull j)
      exact ((M.subgradient i).2 j).trans hcan.symm
    simpa [canonicalSubgradient,facetSign,canonicalFacet] using he
  have hg := positive_gradient_orthogonal M (zero_weight_row_kernel M r hr) i hi
  have horth : facetValue (A r) (canonicalFacet (A i))=0 := by
    simpa only [hgrad,facetValue,mul_comm] using hg
  obtain ⟨B,N,hB,_,_,hind,hu,hv⟩ := exists_optimal_independent_kernel_rows hA hs hopt i r hir
    hsat hfull hrpos horth
  have hdhi := residue_two_preliminary_upper (by linarith) hA
  exact residue_two_independent_kernel_impossible hB N hd hdhi hind hu hv

end
end F3
