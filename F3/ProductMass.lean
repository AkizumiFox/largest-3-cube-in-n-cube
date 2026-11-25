import F3.Dominance

/-! The row product masses and aggregate cancellation identities in the
general-dimensional matrix model. -/
namespace F3.Dominance
noncomputable section
open scoped BigOperators

/-- The absolute mass of the unordered coordinate products of a row. -/
def productMass {k : ℕ} (a : Fin k → ℝ) : ℝ :=
  ∑j, ∑l ∈ Finset.univ.filter (fun l => j<l), |a j*a l|

theorem productMass_nonneg {k : ℕ} (a : Fin k → ℝ) : 0≤productMass a := by
  apply Finset.sum_nonneg
  intro j _
  exact Finset.sum_nonneg (fun l _ => abs_nonneg _)

theorem l1_sq_eq_energy_add_twice_productMass {k : ℕ} (a : Fin k → ℝ) :
    (l1 a)^2=en a+2*productMass a := by
  classical
  have hsplit (j l : Fin k) :
      |a j| * |a l|=(if j=l then (a j)^2 else 0)+
        (if j<l then |a j*a l| else 0)+(if l<j then |a j*a l| else 0) := by
    rcases lt_trichotomy j l with h | h | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le,abs_mul]
    · subst l
      simp [←pow_two,sq_abs]
    · simp [h,ne_of_gt h,not_lt_of_ge h.le,abs_mul]
  have hswap : (∑j : Fin k,∑l : Fin k,if l<j then |a j*a l| else 0)=
      ∑j : Fin k,∑l : Fin k,if j<l then |a j*a l| else 0 := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  calc
    (l1 a)^2=∑j : Fin k,∑l : Fin k,|a j| * |a l| := by
      simp only [l1,pow_two,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = en a+productMass a+productMass a := by
      simp only [hsplit,Finset.sum_add_distrib,hswap]
      simp [en,productMass,Finset.sum_filter]
    _ = en a+2*productMass a := by ring

/-- The unit row budget bounds twice the absolute product mass by row loss. -/
theorem row_loss_ge_twice_productMass {k : ℕ} {a : Fin k → ℝ}
    (ha : l1 a≤1) : 2*productMass a≤1-en a := by
  have hn : 0≤l1 a := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have he := l1_sq_eq_energy_add_twice_productMass a
  nlinarith

/-- Orthogonality cancels each row's total unordered product mass against
the product masses of all remaining rows. -/
theorem productMass_cancellation {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) (i : Fin n) :
    productMass (A i)≤∑h ∈ Finset.univ.erase i,productMass (A h) := by
  classical
  calc
    productMass (A i) ≤ ∑j : Fin k,∑l ∈ Finset.univ.filter (fun l => j<l),
        ∑h ∈ Finset.univ.erase i,|A h j*A h l| := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l hl
      exact gram_cancellation hA i (ne_of_lt (Finset.mem_filter.mp hl).2)
    _ = ∑h ∈ Finset.univ.erase i,productMass (A h) := by
      simp only [productMass]
      conv_lhs =>
        arg 2
        ext j
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]

theorem total_row_loss {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) : (∑i : Fin n,(1-en (A i)))=(n:ℝ)-(k:ℝ)*s := by
  rw [Finset.sum_sub_distrib,trace_identity hA]
  simp

theorem total_loss_ge_row_loss_add_twice_productMass {n k : ℕ} {s : ℝ}
    {A : Fin n → Fin k → ℝ} (hA : FeasibleK n k s A) (i : Fin n) :
    1-en (A i)+2*productMass (A i)≤(n:ℝ)-(k:ℝ)*s := by
  have hcancel := productMass_cancellation hA i
  have hrest : 2*(∑h ∈ Finset.univ.erase i,productMass (A h))≤
      ∑h ∈ Finset.univ.erase i,(1-en (A h)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun h _ => row_loss_ge_twice_productMass (hA.1 h))
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun h => (1:ℝ)-en (A h)) (Finset.mem_univ i)
  dsimp only at he
  rw [total_row_loss hA] at he
  linarith

end
end F3.Dominance
