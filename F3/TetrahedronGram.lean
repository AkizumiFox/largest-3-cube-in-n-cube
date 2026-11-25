import F3.Frames

namespace F3
noncomputable section
open scoped BigOperators

/-- The Gram matrix of any centered regular tetrahedron, derived from its
actual vertex coordinates and equal squared edge lengths. -/
theorem centered_regular_tetrahedron_gram {n : ℕ}
    (V : Fin n → Fin 4 → ℝ) (ell : ℝ)
    (hcent : ∀ i, (∑ p, V i p)=0)
    (hedge : ∀ p q, p≠q → (∑ i, (V i p-V i q)^2)=ell^2)
    (p q : Fin 4) :
    (∑ i, V i p*V i q)=(ell^2/2)*((if p=q then (1 : ℝ) else 0)-1/4) := by
  let G : Fin 4 → Fin 4 → ℝ := fun a b=>∑ i,V i a*V i b
  have hGsum (a : Fin 4) : (∑ b,G a b)=0 := by
    dsimp [G]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.mul_sum,hcent i,mul_zero]
  have hexpand (a b : Fin 4) :
      (∑ i,(V i a-V i b)^2)=G a a+G b b-2*G a b := by
    dsimp [G]
    rw [← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdist (a b : Fin 4) : G a a+G b b-2*G a b=
      if a=b then 0 else ell^2 := by
    by_cases hab : a=b
    · subst b; simp; ring
    · rw [if_neg hab,← hexpand a b]
      exact hedge a b hab
  have hsumif (a : Fin 4) :
      (∑ b : Fin 4, if a=b then (0 : ℝ) else ell^2)=3*ell^2 := by
    have hid (b : Fin 4) : (if a=b then (0 : ℝ) else ell^2)=
        ell^2-(if a=b then ell^2 else 0) := by split_ifs <;> ring
    simp_rw [hid]
    rw [Finset.sum_sub_distrib]
    simp
    ring
  have hrow (a : Fin 4) : 4*G a a+(∑ b,G b b)=3*ell^2 := by
    have h : (∑ b : Fin 4,(G a a+G b b-2*G a b))=∑ b : Fin 4,if a=b then 0 else ell^2 :=
      Finset.sum_congr rfl (fun b _=>hdist a b)
    rw [hsumif] at h
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hGsum] at h
    simpa using h
  have htrace : (∑ a,G a a)=3*ell^2/2 := by
    have h : (∑ a : Fin 4,(4*G a a+(∑ b,G b b)))=∑ a : Fin 4,3*ell^2 :=
      Finset.sum_congr rfl (fun a _=>hrow a)
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
    simp at h
    linarith
  have hdiag (a : Fin 4) : G a a=3*ell^2/8 := by
    have h := hrow a
    rw [htrace] at h
    linarith
  change G p q=_
  have h := hdist p q
  by_cases hpq : p=q
  · subst q
    simp only [ite_true]
    rw [hdiag]
    ring
  · rw [if_neg hpq] at h ⊢
    rw [hdiag p,hdiag q] at h
    linarith

end
end F3
