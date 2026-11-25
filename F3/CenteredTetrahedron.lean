import F3.TetrahedronHadamard
import F3.TetrahedronGram

/-! Centered regular tetrahedra in the unit cube. The nonnegative edge
parameter includes the collapsed zero configuration, as does GeometricSide;
this convention leaves every positive maximum unchanged. -/
namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- A centered tetrahedral configuration in [-1/2,1/2]^n with common
nonnegative edge length. All constraints are on its actual vertex coordinates. -/
def CenteredTetrahedronEdge (n : ℕ) (ell : ℝ) : Prop :=
  0≤ell ∧ ∃V : Fin n → Fin 4 → ℝ,
    (∀i,(∑p,V i p)=0) ∧
    (∀i p,|V i p|≤1/2) ∧
    (∀p q,p≠q → (∑i,(V i p-V i q)^2)=ell^2)

lemma tetraFrame_gram {n : ℕ} (V : Fin n → Fin 4 → ℝ) (ell : ℝ)
    (hG : ∀p q,(∑i,V i p*V i q)=(ell^2/2)*((if p=q then (1:ℝ) else 0)-1/4))
    (j k : Fin 3) :
    (∑i,tetraFrame V i j*tetraFrame V i k)=if j=k then ell^2/2 else 0 := by
  classical
  have ht := gram_transform V (fun p j => tetraSign j p) j k
  have hscaled : (∑i,tetraFrame V i j*tetraFrame V i k)=
      (∑i,(∑p,V i p*tetraSign j p)*(∑q,V i q*tetraSign k q))/4 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [tetraFrame]
    ring
  rw [hscaled,ht]
  simp only [hG]
  fin_cases j <;> fin_cases k <;>
    norm_num [tetraSign,Fin.sum_univ_four,Fin.sum_univ_three,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.reduceFinMk,
      show (0:Fin 4)≠1 by decide,
      show (0:Fin 4)≠2 by decide,
      show (0:Fin 4)≠3 by decide,
      show (1:Fin 4)≠0 by decide,
      show (1:Fin 4)≠2 by decide,
      show (1:Fin 4)≠3 by decide,
      show (2:Fin 4)≠0 by decide,
      show (2:Fin 4)≠1 by decide,
      show (2:Fin 4)≠3 by decide,
      show (3:Fin 4)≠0 by decide,
      show (3:Fin 4)≠1 by decide,
      show (3:Fin 4)≠2 by decide] <;> ring

theorem centeredTetrahedronEdge_iff_feasibleValue {n : ℕ} {ell : ℝ} :
    CenteredTetrahedronEdge n ell ↔ 0≤ell ∧ FeasibleValue n (ell^2/2) := by
  constructor
  · rintro ⟨hell,V,hcent,hcube,hedge⟩
    refine ⟨hell,tetraFrame V,tetraFrame_row_bound V hcent hcube,?_⟩
    exact tetraFrame_gram V ell (centered_regular_tetrahedron_gram V ell hcent hedge)
  · rintro ⟨hell,A,hA⟩
    refine ⟨hell,tetraVertices A,tetraVertices_centered A,tetraVertices_contained A hA.1,?_⟩
    intro p q hpq
    have ht := tetraVertices_edge hA hpq
    nlinarith

def tetrahedronValue (n : ℕ) : ℝ := sSup {ell : ℝ | CenteredTetrahedronEdge n ell}

lemma centeredTetrahedronEdge_zero (n : ℕ) : CenteredTetrahedronEdge n 0 := by
  rw [centeredTetrahedronEdge_iff_feasibleValue]
  exact ⟨le_rfl,by simpa using zero_feasible_value n⟩

lemma centeredTetrahedronEdge_upper {n : ℕ} {ell : ℝ}
    (h : CenteredTetrahedronEdge n ell) : ell≤Real.sqrt (2*frameValue n) := by
  have ht := feasible_le_frameValue (centeredTetrahedronEdge_iff_feasibleValue.mp h).2
  exact Real.le_sqrt_of_sq_le (by linarith)

lemma centeredTetrahedron_values_bddAbove (n : ℕ) :
    BddAbove {ell : ℝ | CenteredTetrahedronEdge n ell} :=
  ⟨Real.sqrt (2*frameValue n),fun _ h => centeredTetrahedronEdge_upper h⟩

lemma centeredTetrahedron_sqrt_attained (n : ℕ) :
    CenteredTetrahedronEdge n (Real.sqrt (2*frameValue n)) := by
  rw [centeredTetrahedronEdge_iff_feasibleValue]
  refine ⟨Real.sqrt_nonneg _,?_⟩
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) (frameValue_nonneg n))]
  convert frameValue_attained n using 1 <;> ring

theorem tetrahedronValue_eq_sqrt (n : ℕ) : tetrahedronValue n=Real.sqrt (2*frameValue n) := by
  apply le_antisymm
  · exact csSup_le ⟨0,centeredTetrahedronEdge_zero n⟩ (fun _ h => centeredTetrahedronEdge_upper h)
  · exact le_csSup (centeredTetrahedron_values_bddAbove n) (centeredTetrahedron_sqrt_attained n)

theorem tetrahedronValue_attained (n : ℕ) : CenteredTetrahedronEdge n (tetrahedronValue n) := by
  rw [tetrahedronValue_eq_sqrt]
  exact centeredTetrahedron_sqrt_attained n

theorem tetrahedronValue_eq_frameSide (n : ℕ) : tetrahedronValue n=Real.sqrt 2*frameSide n := by
  rw [tetrahedronValue_eq_sqrt,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  rfl

theorem tetrahedronValue_eq_geometricValue (n : ℕ) :
    tetrahedronValue n=Real.sqrt 2*geometricValue n := by
  rw [geometricValue_eq_frameSide,tetrahedronValue_eq_frameSide]

theorem tetrahedronValue_sq (n : ℕ) : (tetrahedronValue n)^2=2*frameValue n := by
  rw [tetrahedronValue_eq_sqrt]
  exact Real.sq_sqrt (mul_nonneg (by norm_num) (frameValue_nonneg n))

theorem tetrahedronValue_sq_eq_formula {n : ℕ} (hn : 3≤n) :
    (tetrahedronValue n)^2=2*formula (firstExceptionalRoot^2) (secondExceptionalRoot^2) n := by
  rw [tetrahedronValue_sq,frameValue_eq_formula hn]

/-- The maximum centered regular tetrahedron edge in the five-dimensional
unit cube, proved from the complete sharp frame theorem. -/
theorem tetrahedronValue_five : tetrahedronValue 5=4-Real.sqrt 6 := by
  have hr := Real.sqrt_nonneg (6:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ)≤6 by norm_num)
  have hp : 0≤4-Real.sqrt 6 := by nlinarith
  rw [tetrahedronValue_eq_sqrt,frameValue_five,
    show 2*(11-4*Real.sqrt 6)=(4-Real.sqrt 6)^2 by nlinarith,Real.sqrt_sq hp]

theorem centeredTetrahedron_five_attained :
    CenteredTetrahedronEdge 5 (4-Real.sqrt 6) := by
  rw [←tetrahedronValue_five]
  exact tetrahedronValue_attained 5

theorem centeredTetrahedron_five_optimal {ell : ℝ}
    (h : CenteredTetrahedronEdge 5 ell) : ell≤4-Real.sqrt 6 := by
  have ht := le_csSup (centeredTetrahedron_values_bddAbove 5) h
  change ell≤tetrahedronValue 5 at ht
  rwa [tetrahedronValue_five] at ht

end
end F3
