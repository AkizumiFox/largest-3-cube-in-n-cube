import F3.GeneralCores

namespace F3.General
noncomputable section
open scoped BigOperators
open F3.Dominance

/-- Equality of the Euclidean energy and the unit row budget forces a signed
coordinate vector, in arbitrary positive dimension. -/
theorem unit_energy_signed_coordinate {k : ℕ} (hk : 0<k) {a : Fin k → ℝ}
    (ha : (∑j,|a j|)≤1) (he : (∑j,(a j)^2)=1) : SignedCoordinate a := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0,hk⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ (fun j=>|a j|) hnonempty
  have hsum : (∑l,(a l)^2)≤|a j| *(∑l,|a l|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    have hl := hmax l (Finset.mem_univ l)
    have hm := mul_le_mul_of_nonneg_right hl (abs_nonneg (a l))
    nlinarith [sq_abs (a l)]
  have hjle : |a j|≤1 := (Finset.single_le_sum (fun l _=>abs_nonneg (a l)) hj).trans ha
  have hj0 := abs_nonneg (a j)
  have hjone : |a j|=1 := by
    rw [he] at hsum
    have hmul := mul_le_mul_of_nonneg_left ha hj0
    nlinarith
  refine ⟨j,hjone,?_⟩
  intro l hlj
  have hd := Dominance.l1_decompose a j
  have hminor := Dominance.minorL1_nonneg a j
  have hl := Dominance.other_entry_le_minorL1 a hlj
  have hl1 : Dominance.l1 a≤1 := ha
  rw [hjone] at hd
  have hz : |a l|=0 := by apply le_antisymm _ (abs_nonneg _); linarith
  exact abs_eq_zero.mp hz

theorem trace_equality_signed_rows {n k : ℕ} (hk : 0<k) {s : ℝ}
    {A : Fin n → Fin k → ℝ} (hA : FeasibleK n k s A)
    (heq : (k : ℝ)*s=n) : ∀i,SignedCoordinate (A i) := by
  have hnonneg (i : Fin n) (_ : i∈(Finset.univ : Finset (Fin n))) :
      0≤1-Dominance.en (A i) := sub_nonneg.mpr (row_energy_bound (hA.1 i))
  have hz : (∑i,(1-Dominance.en (A i)))=0 := by
    rw [Finset.sum_sub_distrib,Dominance.trace_identity hA,heq]
    simp
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz i (Finset.mem_univ i)
  apply unit_energy_signed_coordinate hk (hA.1 i)
  change Dominance.en (A i)=1
  linarith

theorem signed_rows_column_energy {n k : ℕ} (A : Fin n → Fin k → ℝ)
    (hrows : ∀i,SignedCoordinate (A i)) (j : Fin k) :
    (∑i,(A i j)^2)=((coordinateRows A j).card : ℝ) := by
  classical
  rw [←coordinate_column_energy A j]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  obtain ⟨l,hl⟩ := hrows i
  have hjl : j≠l := by
    intro he
    apply hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hl⟩
  rw [hl.2 j hjl]
  norm_num

theorem trace_equality_forces_divisibility {n k : ℕ} (hk : 0<k) {s : ℝ}
    {A : Fin n → Fin k → ℝ} (hA : FeasibleK n k s A)
    (heq : (k : ℝ)*s=n) : k∣n := by
  let j : Fin k := ⟨0,hk⟩
  have he := signed_rows_column_energy A (trace_equality_signed_rows hk hA heq) j
  have hg : (∑i,(A i j)^2)=s := by simpa [pow_two] using hA.2 j j
  rw [hg] at he
  refine ⟨(coordinateRows A j).card,?_⟩
  have hn : (n : ℝ)=(k : ℝ)*(coordinateRows A j).card := by rw [←he]; exact heq.symm
  exact_mod_cast hn

/-- The equality characterization in the general matrix-model proposition. -/
theorem value_trace_equality_iff {k : ℕ} (hk : 0<k) (n : ℕ) :
    value k n=(n : ℝ)/k ↔ k∣n := by
  have hkr : (k : ℝ)≠0 := by exact_mod_cast (ne_of_gt hk)
  constructor
  · intro he
    obtain ⟨A,hA⟩ := value_attained hk n
    apply trace_equality_forces_divisibility hk hA
    rw [he]
    field_simp
  · rintro ⟨m,rfl⟩
    rw [value_divisible hk]
    push_cast
    field_simp

def stackFrames {n₁ n₂ k : ℕ} (A : Fin n₁ → Fin k → ℝ) (B : Fin n₂ → Fin k → ℝ) :
    Fin (n₁+n₂) → Fin k → ℝ := fun i=>Sum.elim A B (finSumFinEquiv.symm i)

theorem stackFrames_feasible {n₁ n₂ k : ℕ} {s t : ℝ}
    {A : Fin n₁ → Fin k → ℝ} {B : Fin n₂ → Fin k → ℝ}
    (hA : FeasibleK n₁ k s A) (hB : FeasibleK n₂ k t B) :
    FeasibleK (n₁+n₂) k (s+t) (stackFrames A B) := by
  constructor
  · intro i
    rcases h : finSumFinEquiv.symm i with a|b
    · simpa [stackFrames,h] using hA.1 a
    · simpa [stackFrames,h] using hB.1 b
  · intro j l
    have he : (∑i : Fin (n₁+n₂),stackFrames A B i j*stackFrames A B i l)=
        ∑i : Fin n₁ ⊕ Fin n₂,Sum.elim A B i j*Sum.elim A B i l :=
      Equiv.sum_comp finSumFinEquiv.symm (fun i : Fin n₁ ⊕ Fin n₂=>Sum.elim A B i j*Sum.elim A B i l)
    rw [he,Fintype.sum_sum_type]
    simp only [Sum.elim_inl,Sum.elim_inr,hA.2,hB.2]
    split_ifs <;> ring

/-- Arbitrary vertical stacking gives superadditivity of the genuine optimum,
including degenerate ambient dimensions. -/
theorem value_superadditive {k : ℕ} (hk : 0<k) (n₁ n₂ : ℕ) :
    value k n₁+value k n₂≤value k (n₁+n₂) := by
  obtain ⟨A,hA⟩ := value_attained hk n₁
  obtain ⟨B,hB⟩ := value_attained hk n₂
  exact feasible_le_value hk ⟨stackFrames A B,stackFrames_feasible hA hB⟩

end
end F3.General
