import F3.GeneralFrames

/-! Cube containment and the arbitrary-dimensional finite-frame model. -/
namespace F3.General
noncomputable section
open scoped BigOperators
open F3.Dominance

def linearImage {n k : ℕ} (A : Fin n → Fin k → ℝ) (x : Fin k → ℝ) : Fin n → ℝ :=
  fun i => ∑j,A i j*x j

def Contained {n k : ℕ} (A : Fin n → Fin k → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀x : Fin k → ℝ,F3.UnitCube x → F3.UnitCube (fun i => c i+linearImage A x i)

def ScalesDistances {n k : ℕ} (a : ℝ) (A : Fin n → Fin k → ℝ) : Prop :=
  ∀x y : Fin k → ℝ,
    (∑i,(linearImage A x i-linearImage A y i)^2)=a^2*(∑j,(x j-y j)^2)

def GeometricSide (k n : ℕ) (a : ℝ) : Prop :=
  0≤a ∧ ∃ (A : Fin n → Fin k → ℝ) (c : Fin n → ℝ),
    ScalesDistances a A ∧ Contained A c

theorem rows_of_contained {n k : ℕ} {A : Fin n → Fin k → ℝ} {c : Fin n → ℝ}
    (hc : Contained A c) : ∀i,(∑j,|A i j|)≤1 := by
  intro i
  let x : Fin k → ℝ := fun j => signUnit (A i j)/2
  have hx : F3.UnitCube x := by
    intro j
    have h : |signUnit (A i j)|=1 := by
      unfold signUnit
      split <;> norm_num
    simpa [x,abs_div,h]
  have hnx : F3.UnitCube (fun j => -x j) := by
    intro j; simpa only [abs_neg] using hx j
  have hp := (abs_le.mp (hc x hx i)).2
  have hm := (abs_le.mp (hc (fun j => -x j) hnx i)).1
  change c i+linearImage A x i≤1/2 at hp
  change -(1/2)≤c i+linearImage A (fun j => -x j) i at hm
  have he : linearImage A x i=(∑j,|A i j|)/2 := by
    simp only [linearImage,x,div_eq_mul_inv,←mul_assoc,signUnit_mul,←Finset.sum_mul]
  have hn : linearImage A (fun j => -x j) i= -linearImage A x i := by
    simp [linearImage,Finset.sum_neg_distrib]
  rw [he] at hp
  rw [hn,he] at hm
  linarith

theorem contained_of_rows {n k : ℕ} {A : Fin n → Fin k → ℝ}
    (hA : ∀i,(∑j,|A i j|)≤1) : Contained A (fun _ => 0) := by
  intro x hx i
  simp only [zero_add,linearImage]
  calc
    |∑j,A i j*x j| ≤ ∑j,|A i j*x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑j,|A i j|/2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,div_eq_mul_inv]
      simpa only [one_div] using mul_le_mul_of_nonneg_left (hx j) (abs_nonneg (A i j))
    _ = (∑j,|A i j|)/2 := by simp only [div_eq_mul_inv,Finset.sum_mul]
    _ ≤ 1/2 := by linarith [hA i]

theorem distances_of_feasible {n k : ℕ} {a : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k (a^2) A) : ScalesDistances a A := by
  intro x y
  have he (i : Fin n) : linearImage A x i-linearImage A y i=
      ∑j,A i j*(x j-y j) := by
    simp [linearImage,mul_sub,Finset.sum_sub_distrib]
  simp_rw [he]
  exact gram_quadratic hA (fun j => x j-y j)

theorem gram_of_distances {n k : ℕ} {a : ℝ} {A : Fin n → Fin k → ℝ}
    (hd : ScalesDistances a A) :
    ∀j l,(∑i,A i j*A i l)=if j=l then a^2 else 0 := by
  classical
  have hdiag (j : Fin k) : (∑i,(A i j)^2)=a^2 := by
    have h := hd (coordinateRow j) (fun _ => 0)
    simpa [linearImage,coordinateRow,mul_ite] using h
  intro j l
  by_cases hjl : j=l
  · subst l
    simpa only [ite_true,pow_two] using hdiag j
  · rw [if_neg hjl]
    let x : Fin k → ℝ := fun p => coordinateRow j p+coordinateRow l p
    have hxs (p : Fin k) : (x p)^2=
        (if p=j then (1:ℝ) else 0)+(if p=l then 1 else 0) := by
      by_cases hpj : p=j
      · subst p; simp [x,coordinateRow,hjl,Ne.symm hjl]
      by_cases hpl : p=l
      · subst p; simp [x,coordinateRow,hjl,Ne.symm hjl]
      simp [x,coordinateRow,hpj,Ne.symm hpj,hpl,Ne.symm hpl]
    have hxnorm : (∑p,(x p)^2)=2 := by
      simp only [hxs,Finset.sum_add_distrib]
      norm_num
    have hlin (i : Fin n) : linearImage A x i=A i j+A i l := by
      simp [linearImage,x,coordinateRow,mul_add,Finset.sum_add_distrib,mul_ite]
    have h := hd x (fun _ => 0)
    have hz (i : Fin n) : linearImage A (fun _ => 0) i=0 := by simp [linearImage]
    simp only [hlin,hz,sub_zero,hxnorm] at h
    have hex : (∑i,(A i j+A i l)^2)=
        (∑i,(A i j)^2)+(∑i,(A i l)^2)+2*(∑i,A i j*A i l) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hex,hdiag j,hdiag l] at h
    linarith

theorem geometricSide_iff_feasibleValue {k n : ℕ} {a : ℝ} :
    GeometricSide k n a ↔ 0≤a ∧ FeasibleValue k n (a^2) := by
  constructor
  · rintro ⟨ha,A,c,hd,hc⟩
    exact ⟨ha,A,rows_of_contained hc,gram_of_distances hd⟩
  · rintro ⟨ha,A,hA⟩
    exact ⟨ha,A,fun _ => 0,distances_of_feasible hA,contained_of_rows hA.1⟩

theorem distances_injective {n k : ℕ} {a : ℝ} {A : Fin n → Fin k → ℝ}
    (ha : 0<a) (hA : ScalesDistances a A) : Function.Injective (linearImage A) := by
  intro x y he
  have h := hA x y
  simp only [congrFun he,sub_self,show (0:ℝ)^2=0 by norm_num,Finset.sum_const_zero] at h
  have hz := (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ ha.ne')
  have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j-y j))).mp hz
  funext j
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hp j (Finset.mem_univ _)))

def geometricValue (k n : ℕ) : ℝ := sSup {a | GeometricSide k n a}

theorem geometricValue_eq_sqrt {k : ℕ} (hk : 0<k) (n : ℕ) :
    geometricValue k n=Real.sqrt (value k n) := by
  have hz : GeometricSide k n 0 := by
    rw [geometricSide_iff_feasibleValue]
    exact ⟨le_rfl,by simpa using zero_feasible k n⟩
  have hu {a : ℝ} (ha : GeometricSide k n a) : a≤Real.sqrt (value k n) :=
    Real.le_sqrt_of_sq_le (feasible_le_value hk (geometricSide_iff_feasibleValue.mp ha).2)
  have hb : BddAbove {a | GeometricSide k n a} := ⟨_,fun _ ha => hu ha⟩
  apply le_antisymm
  · exact csSup_le ⟨0,hz⟩ (fun _ ha => hu ha)
  · apply le_csSup hb
    change GeometricSide k n (Real.sqrt (value k n))
    rw [geometricSide_iff_feasibleValue,Real.sq_sqrt (value_nonneg hk n)]
    exact ⟨Real.sqrt_nonneg _,value_attained hk n⟩

theorem geometricValue_sq {k : ℕ} (hk : 0<k) (n : ℕ) :
    (geometricValue k n)^2=value k n := by
  rw [geometricValue_eq_sqrt hk,Real.sq_sqrt (value_nonneg hk n)]

end
end F3.General
