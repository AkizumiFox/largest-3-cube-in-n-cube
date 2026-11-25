import F3.Dominance

/-! Zero padding and row restriction for finite feasible frames. -/
namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

def FiniteFeasible {ι : Type*} [Fintype ι] (k : ℕ) (s : ℝ)
    (A : ι → Fin k → ℝ) : Prop :=
  (∀ i, (∑ j, |A i j|)≤1) ∧
  (∀ j l, (∑ i,A i j*A i l)=if j=l then s else 0)

theorem finiteFeasible_pad {ι : Type*} [Fintype ι] {N k : ℕ} {s : ℝ}
    {A : ι → Fin k → ℝ} (hA : FiniteFeasible k s A)
    (hcard : Fintype.card ι≤N) :
    ∃ B : Fin N → Fin k → ℝ, Dominance.FeasibleK N k s B := by
  classical
  let A' : (ι ⊕ Fin (N-Fintype.card ι)) → Fin k → ℝ := Sum.elim A (fun _ _ => 0)
  have heq : Fintype.card (ι ⊕ Fin (N-Fintype.card ι))=Fintype.card (Fin N) := by
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  let e := Fintype.equivOfCardEq heq
  refine ⟨fun i => A' (e.symm i),?_,?_⟩
  · intro i
    cases h : e.symm i with
    | inl a => simpa [A',h] using hA.1 a
    | inr b => simp [A',h]
  · intro j l
    have he := Equiv.sum_comp e.symm (fun i => A' i j*A' i l)
    rw [he,Fintype.sum_sum_type]
    simp only [A',Sum.elim_inl,Sum.elim_inr,mul_zero,Finset.sum_const_zero,add_zero]
    exact hA.2 j l

theorem restricted_two_column_frame {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A)
    (P : Finset (Fin n))
    (houtside : ∀i,i∉P → A i 1=0 ∧ A i 2=0) :
    FiniteFeasible 2 s (fun i : P => ![A i 1,A i 2]) := by
  classical
  constructor
  · intro i
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
    have h := hA.1 i
    unfold RowBound at h
    linarith [abs_nonneg (A i 0)]
  · intro j k
    have hp (a b : Fin 3) (ha : a=1 ∨ a=2) (hb : b=1 ∨ b=2) :
        (∑ i : P,A i a*A i b)=if a=b then s else 0 := by
      calc
        _ = ∑ i ∈ P,A i a*A i b := Finset.sum_attach P (fun i => A i a*A i b)
        _ = ∑ i,A i a*A i b := by
          apply Finset.sum_subset (Finset.subset_univ P)
          intro i _ hi
          obtain ⟨h1,h2⟩ := houtside i hi
          rcases ha with rfl | rfl <;> simp [h1,h2]
        _ = _ := hA.2 a b
    fin_cases j <;> fin_cases k <;>
      simpa using hp _ _ (by simp) (by simp)

theorem axis_plane_two_dimensional_bound {m : ℕ} {δ : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ}
    (hA : Feasible ((m:ℝ)+δ) A) (hδ : 0<δ)
    (P : Finset (Fin (3*m+2)))
    (hin : ∀i,i∈P → A i 0=0)
    (hout : ∀i,i∉P → A i 1=0 ∧ A i 2=0) : δ≤1/8 := by
  classical
  have hentry (i : Fin (3*m+2)) : (A i 0)^2≤1 := by
    have h := row_energy_le_one (hA.1 i)
    nlinarith [sq_nonneg (A i 1),sq_nonneg (A i 2)]
  have hcol : (m:ℝ)+δ≤((3*m+2)-P.card:ℕ) := by
    have hs := Finset.sum_le_sum (s:=Finset.univ)
      (f:=fun i => (A i 0)^2) (g:=fun i => if i∈P then (0:ℝ) else 1) (by
        intro i _
        by_cases hi : i∈P
        · simp [hi,hin i hi]
        · simpa [hi] using hentry i)
    have he : (∑i,(A i 0)^2)=(m:ℝ)+δ := by simpa [pow_two] using hA.2 0 0
    rw [he] at hs
    have hc : (∑i : Fin (3*m+2),if i∈P then (0:ℝ) else 1)=
        ((3*m+2)-P.card:ℕ) := by
      have heq (i : Fin (3*m+2)) :
          (if i∈P then (0:ℝ) else 1)=(if i∉P then (1:ℝ) else 0) := by
        by_cases hi : i∈P <;> simp [hi]
      simp_rw [heq]
      rw [←Finset.sum_filter]
      simp [Finset.filter_not,Finset.card_sdiff (Finset.subset_univ P)]
    rwa [hc] at hs
  have hlt : (m:ℝ)<((3*m+2)-P.card:ℕ) := by linarith
  have hnat : m<(3*m+2)-P.card := by exact_mod_cast hlt
  have hP : P.card≤2*m+1 := by omega
  have hPf : Fintype.card P≤2*m+1 := by simpa using hP
  obtain ⟨B,hB⟩ := finiteFeasible_pad (restricted_two_column_frame hA P hout) hPf
  have hb := Dominance.two_dimensional_bound hB
  linarith

end
end F3
