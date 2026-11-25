import F3.CenteredTetrahedron
import F3.GeneralGeometry
import F3.GeneralTraceStacking
import F3.FiniteCoreStabilization
import F3.LocalVariational
import F3.MultiplierRank
import F3.TransferDerivative

/-! Direct geometric formulations of the manuscript's principal conclusions.
The geometric quantities below are independent suprema over actual contained
cube images and tetrahedral vertex configurations. -/
namespace F3
noncomputable section

theorem geometricValue_eq_sqrt_formula {n : ℕ} (hn : 3≤n) :
    geometricValue n =
      Real.sqrt (formula (firstExceptionalRoot^2) (secondExceptionalRoot^2) n) := by
  rw [geometricValue_eq_frameSide,frameSide,frameValue_eq_formula hn]

theorem geometricValue_five : geometricValue 5=Real.sqrt (11-4*Real.sqrt 6) := by
  rw [geometricValue_eq_frameSide,frameSide,frameValue_five]

theorem geometricValue_squared_recurrence {n : ℕ} (hn : 8≤n) :
    (geometricValue (n+3))^2=(geometricValue n)^2+1 := by
  rw [geometricValue_sq,geometricValue_sq]
  exact frameValue_recurrence hn

namespace General

theorem geometricValue_three_eq (n : ℕ) :
    geometricValue 3 n=F3.geometricValue n := by
  rw [geometricValue_eq_sqrt (by decide : 0<3),value_three_eq_frameValue,
    F3.geometricValue_eq_frameSide,F3.frameSide]

theorem geometricValue_attained {k : ℕ} (hk : 0<k) (n : ℕ) :
    GeometricSide k n (geometricValue k n) := by
  rw [geometricSide_iff_feasibleValue,geometricValue_sq hk]
  exact ⟨by rw [geometricValue_eq_sqrt hk]; exact Real.sqrt_nonneg _,value_attained hk n⟩

theorem geometricValue_trace_equality_iff {k : ℕ} (hk : 0<k) (n : ℕ) :
    (geometricValue k n)^2=(n : ℝ)/k ↔ k∣n := by
  rw [geometricValue_sq hk]
  exact value_trace_equality_iff hk n

theorem geometricValue_squared_superadditive {k : ℕ} (hk : 0<k) (n₁ n₂ : ℕ) :
    (geometricValue k n₁)^2+(geometricValue k n₂)^2≤
      (geometricValue k (n₁+n₂))^2 := by
  simp only [geometricValue_sq hk]
  exact value_superadditive hk n₁ n₂

theorem value_two_dimensional_bound (m : ℕ) :
    value 2 (2*m+1)≤(m : ℝ)+1/8 := by
  obtain ⟨A,hA⟩ := value_attained (by decide : 0<2) (2*m+1)
  exact Dominance.two_dimensional_bound hA

end General
end
end F3
