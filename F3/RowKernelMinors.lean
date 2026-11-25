import F3.RowPairRotation

/-! Two independent right-annihilated rows force every order-two minor to vanish. -/

namespace F3
noncomputable section
open scoped BigOperators

def rowCross (u r : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1*r 2-u 2*r 1,u 2*r 0-u 0*r 2,u 0*r 1-u 1*r 0]

theorem rowCross_nonzero {u r : Fin 3 → ℝ} (hind : RowPairIndependent u r) :
    ∃ j, rowCross u r j≠0 := by
  by_contra h
  push_neg at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [rowCross,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons] at h0 h1 h2
  have hdet : ∀ j k : Fin 3, u j*r k-u k*r j=0 := by
    intro j k
    fin_cases j <;> fin_cases k <;> simp_all <;> linarith
  have hr : ∃ j, r j≠0 := by
    by_contra hh
    push_neg at hh
    have he := hind 0 1 (by intro j; simp [hh j])
    norm_num at he
  obtain ⟨j,hj⟩ := hr
  have he := hind (r j) (-u j) (by
    intro k
    have hk := hdet k j
    nlinarith [hk])
  exact hj he.1

theorem rowCross_proportional {u r z : Fin 3 → ℝ}
    (hu : (∑ j, u j*z j)=0) (hr : (∑ j, r j*z j)=0)
    (j k : Fin 3) : rowCross u r j*z k=rowCross u r k*z j := by
  simp only [Fin.sum_univ_three] at hu hr
  fin_cases j <;> fin_cases k
  · rfl
  · change (u 1*r 2-u 2*r 1)*z 1=(u 2*r 0-u 0*r 2)*z 0
    linear_combination r 2*hu-u 2*hr
  · change (u 1*r 2-u 2*r 1)*z 2=(u 0*r 1-u 1*r 0)*z 0
    linear_combination u 1*hr-r 1*hu
  · change (u 2*r 0-u 0*r 2)*z 0=(u 1*r 2-u 2*r 1)*z 1
    linear_combination u 2*hr-r 2*hu
  · rfl
  · change (u 2*r 0-u 0*r 2)*z 2=(u 0*r 1-u 1*r 0)*z 1
    linear_combination r 0*hu-u 0*hr
  · change (u 0*r 1-u 1*r 0)*z 0=(u 1*r 2-u 2*r 1)*z 2
    linear_combination r 1*hu-u 1*hr
  · change (u 0*r 1-u 1*r 0)*z 1=(u 2*r 0-u 0*r 2)*z 2
    linear_combination u 0*hr-r 0*hu
  · rfl

theorem two_kernel_rows_all_minors_zero
    {u r : Fin 3 → ℝ} {S : Fin 3 → Fin 3 → ℝ}
    (hind : RowPairIndependent u r)
    (hu : ∀ j, (∑ k, u k*S k j)=0)
    (hr : ∀ j, (∑ k, r k*S k j)=0)
    (j k a b : Fin 3) : S j a*S k b=S j b*S k a := by
  obtain ⟨p,hp⟩ := rowCross_nonzero hind
  have hja := rowCross_proportional (hu a) (hr a) p j
  have hkb := rowCross_proportional (hu b) (hr b) p k
  have hjb := rowCross_proportional (hu b) (hr b) p j
  have hka := rowCross_proportional (hu a) (hr a) p k
  have he : (rowCross u r p)^2*(S j a*S k b-S j b*S k a)=0 := by
    calc
      _ = (rowCross u r p*S j a)*(rowCross u r p*S k b)-
          (rowCross u r p*S j b)*(rowCross u r p*S k a) := by ring
      _ = 0 := by rw [hja,hkb,hjb,hka]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hp))

theorem two_kernel_rows_principal_minors_zero
    {u r : Fin 3 → ℝ} {S : Fin 3 → Fin 3 → ℝ}
    (hind : RowPairIndependent u r)
    (hu : ∀ j, (∑ k, u k*S k j)=0)
    (hr : ∀ j, (∑ k, r k*S k j)=0)
    (j k : Fin 3) : S j j*S k k-S j k*S k j=0 := by
  exact sub_eq_zero.mpr (two_kernel_rows_all_minors_zero hind hu hr j k j k)

end
end F3
