import F3.ExceptionalRoots

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

lemma exceptional_one_linear_identities (y : ℝ) :
    exceptionalX 1 y * exceptionalCOne y + y * exceptionalSOne y =
      Real.sqrt 2 - exceptionalX 1 y ∧
    exceptionalX 1 y * exceptionalSOne y + y * exceptionalCOne y = 1 := by
  have hx : (exceptionalX 1 y)^2-y^2 = 1 := by
    nlinarith [exceptionalX_sq (y:=y) (show (0:ℝ)≤1 by norm_num)]
  dsimp [exceptionalCOne,exceptionalSOne]
  constructor
  · calc
      _ = ((exceptionalX 1 y)^2-y^2)*(Real.sqrt 2-exceptionalX 1 y) := by ring
      _ = _ := by rw [hx]; ring
  · nlinarith

lemma exceptional_two_linear_identities (y : ℝ) :
    exceptionalX 2 y * exceptionalCTwo y + y * exceptionalSTwo y =
      Real.sqrt 2 - y ∧
    exceptionalX 2 y * exceptionalSTwo y + y * exceptionalCTwo y = 1 := by
  have hx : (exceptionalX 2 y)^2-y^2 = 2 := by
    nlinarith [exceptionalX_sq (y:=y) (show (0:ℝ)≤2 by norm_num)]
  dsimp [exceptionalCTwo,exceptionalSTwo]
  constructor
  · calc
      _ = ((exceptionalX 2 y)^2-y^2)*(Real.sqrt 2-y)/2 := by ring
      _ = _ := by rw [hx]; ring
  · nlinarith

def exceptionalCore4 (x y C S : ℝ) : Fin 4 → Fin 3 → ℝ :=
  ![ ![x*C/Real.sqrt 2, x/Real.sqrt 2, y*S/Real.sqrt 2],
     ![x*C/Real.sqrt 2, -(x/Real.sqrt 2), y*S/Real.sqrt 2],
     ![x*S, 0, -(y*C)],
     ![0, 0, 1] ]

def exceptionalCore7 (x y C S : ℝ) : Fin 7 → Fin 3 → ℝ :=
  ![ ![x*C/Real.sqrt 2, y/Real.sqrt 2, y*S/Real.sqrt 2],
     ![x*C/Real.sqrt 2, -(y/Real.sqrt 2), y*S/Real.sqrt 2],
     ![x*S, 0, -(y*C)],
     ![0,1,0], ![0,1,0], ![0,0,1], ![0,0,1] ]

lemma exceptionalCore4_feasible {x y C S : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hC : 0≤C) (hS : 0≤S)
    (hxy : x^2=1+y^2) (hcs : C^2+S^2=1)
    (hrow : x*C+y*S=Real.sqrt 2-x) (hrow' : x*S+y*C=1) :
    Feasible (1+y^2) (exceptionalCore4 x y C S) := by
  have hr := Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)
  have hrne := ne_of_gt hr
  have hrs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hxc : 0≤x*C/Real.sqrt 2 := by positivity
  have hxd : 0≤x/Real.sqrt 2 := by positivity
  have hys : 0≤y*S/Real.sqrt 2 := by positivity
  have hxs : 0≤x*S := by positivity
  have hyc : 0≤y*C := by positivity
  have hrb : x*C/Real.sqrt 2 + x/Real.sqrt 2 + y*S/Real.sqrt 2 = 1 := by
    rw [← add_div, ← add_div]
    apply (div_eq_one_iff_eq hrne).mpr
    linarith
  have hcolx : x^2*C^2+x^2*S^2 = x^2 := by
    calc
      _ = x^2*(C^2+S^2) := by ring
      _ = _ := by rw [hcs]; ring
  have hcoly : y^2*C^2+y^2*S^2 = y^2 := by
    calc
      _ = y^2*(C^2+S^2) := by ring
      _ = _ := by rw [hcs]; ring
  constructor
  · intro i
    fin_cases i <;>
      norm_num [RowBound,exceptionalCore4,abs_of_nonneg hxc,
        abs_of_nonneg hxd,abs_of_nonneg hys,abs_of_nonneg hxs,
        abs_of_nonneg hyc,abs_neg,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    all_goals linarith
  · intro j k
    fin_cases j <;> fin_cases k <;>
      norm_num [exceptionalCore4,Fin.sum_univ_succ] <;>
      field_simp <;> ring_nf <;> linarith only [hcolx,hcoly,hxy]

lemma exceptionalCore7_feasible {x y C S : ℝ}
    (hx : 0≤x) (hy : 0≤y) (hC : 0≤C) (hS : 0≤S)
    (hxy : x^2=2+y^2) (hcs : C^2+S^2=1)
    (hrow : x*C+y*S=Real.sqrt 2-y) (hrow' : x*S+y*C=1) :
    Feasible (2+y^2) (exceptionalCore7 x y C S) := by
  have hr := Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)
  have hrne := ne_of_gt hr
  have hrs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hxc : 0≤x*C/Real.sqrt 2 := by positivity
  have hxd : 0≤y/Real.sqrt 2 := by positivity
  have hys : 0≤y*S/Real.sqrt 2 := by positivity
  have hxs : 0≤x*S := by positivity
  have hyc : 0≤y*C := by positivity
  have hrb : x*C/Real.sqrt 2 + y/Real.sqrt 2 + y*S/Real.sqrt 2 = 1 := by
    rw [← add_div, ← add_div]
    apply (div_eq_one_iff_eq hrne).mpr
    linarith
  have hcolx : x^2*C^2+x^2*S^2 = x^2 := by
    calc
      _ = x^2*(C^2+S^2) := by ring
      _ = _ := by rw [hcs]; ring
  have hcoly : y^2*C^2+y^2*S^2 = y^2 := by
    calc
      _ = y^2*(C^2+S^2) := by ring
      _ = _ := by rw [hcs]; ring
  constructor
  · intro i
    fin_cases i <;>
      norm_num [RowBound,exceptionalCore7,abs_of_nonneg hxc,
        abs_of_nonneg hxd,abs_of_nonneg hys,abs_of_nonneg hxs,
        abs_of_nonneg hyc,abs_neg,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    all_goals linarith
  · intro j k
    fin_cases j <;> fin_cases k <;>
      norm_num [exceptionalCore7,Fin.sum_univ_succ] <;>
      field_simp <;> ring_nf <;> linarith only [hcolx,hcoly,hxy]


/-- The manuscript's exceptional witnesses, with no optimum assumption. -/
theorem exceptional_frames_of_roots {y₁ y₂ : ℝ} (h : ExceptionalRoots y₁ y₂) :
    FeasibleValue 4 (1+y₁^2) ∧ FeasibleValue 7 (2+y₂^2) := by
  have h₁ : y₁ ∈ Set.Icc (0:ℝ) (27/100) := ⟨h.1.le, by linarith [h.2.1]⟩
  have h₂ : y₂ ∈ Set.Icc (0:ℝ) (27/100) := ⟨by linarith [h.2.2.1], by linarith [h.2.2.2.1]⟩
  rcases exceptional_components_positive h₁ with ⟨hc₁,hs₁,_,_⟩
  rcases exceptional_components_positive h₂ with ⟨_,_,hc₂,hs₂⟩
  constructor
  · refine ⟨exceptionalCore4 (exceptionalX 1 y₁) y₁ (exceptionalCOne y₁)
        (exceptionalSOne y₁), ?_⟩
    exact exceptionalCore4_feasible (Real.sqrt_nonneg _) h.1.le hc₁.le hs₁.le
      (exceptionalX_sq (by norm_num)) h.2.2.2.2.1
      (exceptional_one_linear_identities y₁).1 (exceptional_one_linear_identities y₁).2
  · refine ⟨exceptionalCore7 (exceptionalX 2 y₂) y₂ (exceptionalCTwo y₂)
        (exceptionalSTwo y₂), ?_⟩
    exact exceptionalCore7_feasible (Real.sqrt_nonneg _) h₂.1 hc₂.le hs₂.le
      (exceptionalX_sq (by norm_num)) h.2.2.2.2.2
      (exceptional_two_linear_identities y₂).1 (exceptional_two_linear_identities y₂).2

/-- The two roots are defined using the proved unique-root theorems. -/
def firstExceptionalRoot : ℝ := Classical.choose rootOneEquation_unique.exists
def secondExceptionalRoot : ℝ := Classical.choose rootTwoEquation_unique.exists

lemma firstExceptionalRoot_spec :
    firstExceptionalRoot ∈ Set.Icc (0:ℝ) (27/100) ∧
    rootOneEquation firstExceptionalRoot = 1 :=
  Classical.choose_spec rootOneEquation_unique.exists

lemma secondExceptionalRoot_spec :
    secondExceptionalRoot ∈ Set.Icc (0:ℝ) (27/100) ∧
    rootTwoEquation secondExceptionalRoot = 1 :=
  Classical.choose_spec rootTwoEquation_unique.exists

theorem canonical_exceptional_roots :
    ExceptionalRoots firstExceptionalRoot secondExceptionalRoot := by
  obtain ⟨y₁,y₂,h⟩ := exceptional_roots_exist
  have h₁ : y₁ ∈ Set.Icc (0:ℝ) (27/100) := ⟨h.1.le, by linarith [h.2.1]⟩
  have h₂ : y₂ ∈ Set.Icc (0:ℝ) (27/100) := ⟨by linarith [h.2.2.1], by linarith [h.2.2.2.1]⟩
  have he₁ : y₁ = firstExceptionalRoot :=
    rootOneEquation_strictAntiOn.injOn h₁ firstExceptionalRoot_spec.1
      (h.2.2.2.2.1.trans firstExceptionalRoot_spec.2.symm)
  have he₂ : y₂ = secondExceptionalRoot :=
    rootTwoEquation_strictAntiOn.injOn h₂ secondExceptionalRoot_spec.1
      (h.2.2.2.2.2.trans secondExceptionalRoot_spec.2.symm)
  simpa [he₁,he₂] using h

theorem canonical_exceptional_frames :
    FeasibleValue 4 (1+firstExceptionalRoot^2) ∧
    FeasibleValue 7 (2+secondExceptionalRoot^2) :=
  exceptional_frames_of_roots canonical_exceptional_roots

theorem canonical_exceptional_lower_bounds :
    1+firstExceptionalRoot^2 ≤ frameValue 4 ∧
    2+secondExceptionalRoot^2 ≤ frameValue 7 :=
  ⟨feasible_le_frameValue canonical_exceptional_frames.1,
   feasible_le_frameValue canonical_exceptional_frames.2⟩

theorem canonical_exceptional_correction_order :
    0 < firstExceptionalRoot^2 ∧ firstExceptionalRoot^2 < (3:ℝ)/100 ∧
    (3:ℝ)/100 < secondExceptionalRoot^2 ∧ secondExceptionalRoot^2 < (49:ℝ)/1600 ∧
    (49:ℝ)/1600 < 15-4*Real.sqrt 14 := by
  have h := canonical_exceptional_roots
  refine ⟨sq_pos_of_pos h.1, ?_, ?_, ?_, stable_correction_gt_49_div_1600⟩
  · nlinarith [h.1,h.2.1]
  · nlinarith [h.2.2.1]
  · nlinarith [h.2.2.1,h.2.2.2.1]

end
end F3
