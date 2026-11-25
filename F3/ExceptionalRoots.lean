import F3.Recurrence
import Mathlib.Topology.Order.IntermediateValue

/-!
# Exceptional roots and frames

Direct formalization of the algebraic exceptional parameters in Sections 1 and 4.
No statement here assumes the sharp-value optimization theorem.
-/
namespace F3
noncomputable section
open scoped BigOperators

set_option maxHeartbeats 1000000

def exceptionalX (q y : ℝ) : ℝ := Real.sqrt (q + y^2)
def exceptionalCOne (y : ℝ) : ℝ :=
  exceptionalX 1 y * (Real.sqrt 2 - exceptionalX 1 y) - y
def exceptionalSOne (y : ℝ) : ℝ :=
  exceptionalX 1 y - y * (Real.sqrt 2 - exceptionalX 1 y)
def exceptionalCTwo (y : ℝ) : ℝ :=
  (exceptionalX 2 y * (Real.sqrt 2 - y) - y) / 2
def exceptionalSTwo (y : ℝ) : ℝ :=
  (exceptionalX 2 y - y * (Real.sqrt 2 - y)) / 2

lemma sqrt_two_bounds : (7:ℝ)/5 < Real.sqrt 2 ∧ Real.sqrt 2 < 3/2 := by
  constructor
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)

lemma exceptionalX_sq {q y : ℝ} (hq : 0 ≤ q) :
    (exceptionalX q y)^2 = q+y^2 :=
  Real.sq_sqrt (by positivity)

lemma exceptionalX_one_bounds {y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) (27/100)) :
    1 ≤ exceptionalX 1 y ∧ exceptionalX 1 y < 26/25 := by
  constructor
  · have h := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+y^2 by nlinarith [sq_nonneg y])
    simpa [exceptionalX] using h
  · apply (Real.sqrt_lt (by positivity) (by norm_num)).2
    rcases hy with ⟨hlo,hhi⟩
    nlinarith

lemma exceptionalX_two_bounds {y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) (27/100)) :
    (7:ℝ)/5 < exceptionalX 2 y ∧ exceptionalX 2 y < 29/20 := by
  constructor
  · apply (Real.lt_sqrt (by norm_num)).2
    nlinarith [sq_nonneg y]
  · apply (Real.sqrt_lt (by positivity) (by norm_num)).2
    rcases hy with ⟨hlo,hhi⟩
    nlinarith

/-- A Lipschitz estimate for the radicals on the common isolation interval. -/
lemma exceptionalX_difference {q u v : ℝ} (hq : 1 ≤ q)
    (hu : u ∈ Set.Icc (0:ℝ) (27/100))
    (hv : v ∈ Set.Icc (0:ℝ) (27/100)) (huv : u < v) :
    0 ≤ exceptionalX q v - exceptionalX q u ∧
    exceptionalX q v - exceptionalX q u ≤ (27/100)*(v-u) := by
  have hu0 := hu.1
  have hv0 := hv.1
  have hu1 := hu.2
  have hv1 := hv.2
  have hxu : 1 ≤ exceptionalX q u := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ) ≤ q+u^2 by nlinarith [sq_nonneg u])
    simpa [exceptionalX] using h
  have hxv : 1 ≤ exceptionalX q v := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ) ≤ q+v^2 by nlinarith [sq_nonneg v])
    simpa [exceptionalX] using h
  have hxuv : exceptionalX q u ≤ exceptionalX q v :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hxus := exceptionalX_sq (y:=u) (show 0≤q by linarith)
  have hxvs := exceptionalX_sq (y:=v) (show 0≤q by linarith)
  constructor
  · linarith
  · have hm := mul_nonneg (show 0 ≤ exceptionalX q v-exceptionalX q u by linarith)
        (show 0 ≤ exceptionalX q v+exceptionalX q u-2 by linarith)
    have hp := mul_nonneg (show 0 ≤ v-u by linarith)
        (show 0 ≤ (54:ℝ)/100-(v+u) by linarith)
    nlinarith

lemma exceptional_components_positive {y : ℝ}
    (hy : y ∈ Set.Icc (0:ℝ) (27/100)) :
    0 < exceptionalCOne y ∧ 0 < exceptionalSOne y ∧
    0 < exceptionalCTwo y ∧ 0 < exceptionalSTwo y := by
  have hy0 := hy.1
  have hy1 := hy.2
  rcases sqrt_two_bounds with ⟨hr0,hr1⟩
  rcases exceptionalX_one_bounds hy with ⟨hx10,hx11⟩
  rcases exceptionalX_two_bounds hy with ⟨hx20,hx21⟩
  have hp1 : (9:ℝ)/25 < Real.sqrt 2-exceptionalX 1 y := by linarith
  have hcp := mul_nonneg (show 0≤exceptionalX 1 y-1 by linarith)
      (show 0≤Real.sqrt 2-exceptionalX 1 y by linarith)
  have hsp := mul_nonneg hy0 (show 0≤(1:ℝ)/2-(Real.sqrt 2-exceptionalX 1 y) by linarith)
  have hcp2 := mul_nonneg (show 0≤exceptionalX 2 y-(7:ℝ)/5 by linarith)
      (show 0≤Real.sqrt 2-y by linarith)
  have hsp2 := mul_nonneg hy0 (show 0≤(3:ℝ)/2-(Real.sqrt 2-y) by linarith)
  dsimp [exceptionalCOne, exceptionalSOne, exceptionalCTwo, exceptionalSTwo]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

lemma exceptional_components_decreasing {u v : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) (27/100))
    (hv : v ∈ Set.Icc (0:ℝ) (27/100)) (huv : u<v) :
    exceptionalCOne v < exceptionalCOne u ∧
    exceptionalSOne v < exceptionalSOne u ∧
    exceptionalCTwo v < exceptionalCTwo u ∧
    exceptionalSTwo v < exceptionalSTwo u := by
  have hu0 := hu.1
  have hv0 := hv.1
  have hu1 := hu.2
  have hv1 := hv.2
  rcases sqrt_two_bounds with ⟨hr0,hr1⟩
  rcases exceptionalX_one_bounds hu with ⟨hxu10,hxu11⟩
  rcases exceptionalX_one_bounds hv with ⟨hxv10,hxv11⟩
  rcases exceptionalX_two_bounds hu with ⟨hxu20,hxu21⟩
  rcases exceptionalX_two_bounds hv with ⟨hxv20,hxv21⟩
  rcases exceptionalX_difference (q:=1) (by norm_num) hu hv huv with ⟨hd10,hd11⟩
  rcases exceptionalX_difference (q:=2) (by norm_num) hu hv huv with ⟨hd20,hd21⟩
  have h1 := mul_nonneg hd10
    (show 0≤exceptionalX 1 v+exceptionalX 1 u-Real.sqrt 2 by linarith)
  have h2 := mul_nonneg
    (show 0≤(27:ℝ)/100*(v-u)-(exceptionalX 1 v-exceptionalX 1 u) by linarith)
    (show 0≤1+v by linarith)
  have h3 := mul_nonneg (show 0≤v-u by linarith)
    (show 0≤(26:ℝ)/25-exceptionalX 1 u by linarith)
  have h4 := mul_nonneg (show 0≤v-u by linarith)
    (show 0≤(27:ℝ)/100-v by linarith)
  have h5 := mul_nonneg (show 0≤v-u by linarith)
    (show 0≤Real.sqrt 2-(7:ℝ)/5 by linarith)
  have h6 := mul_nonneg hd20 (show 0≤(3:ℝ)/2-(Real.sqrt 2-v) by linarith)
  have h7 := mul_nonneg (show 0≤v-u by linarith)
    (show 0≤exceptionalX 2 u-(7:ℝ)/5 by linarith)
  have h8 := mul_nonneg (show 0≤v-u by linarith)
    (show 0≤(54:ℝ)/100-(v+u) by linarith)
  dsimp [exceptionalCOne, exceptionalSOne, exceptionalCTwo, exceptionalSTwo]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

lemma rootOneEquation_strictAntiOn :
    StrictAntiOn rootOneEquation (Set.Icc (0:ℝ) (27/100)) := by
  intro u hu v hv huv
  rcases exceptional_components_positive hu with ⟨hcu,hsu,_,_⟩
  rcases exceptional_components_positive hv with ⟨hcv,hsv,_,_⟩
  rcases exceptional_components_decreasing hu hv huv with ⟨hc,hs,_,_⟩
  change (exceptionalCOne v)^2+(exceptionalSOne v)^2 <
    (exceptionalCOne u)^2+(exceptionalSOne u)^2
  nlinarith

lemma rootTwoEquation_strictAntiOn :
    StrictAntiOn rootTwoEquation (Set.Icc (0:ℝ) (27/100)) := by
  intro u hu v hv huv
  rcases exceptional_components_positive hu with ⟨_,_,hcu,hsu⟩
  rcases exceptional_components_positive hv with ⟨_,_,hcv,hsv⟩
  rcases exceptional_components_decreasing hu hv huv with ⟨_,_,hc,hs⟩
  change (exceptionalCTwo v)^2+(exceptionalSTwo v)^2 <
    (exceptionalCTwo u)^2+(exceptionalSTwo u)^2
  nlinarith

lemma sqrt_two_tight_bounds :
    (141421:ℝ)/100000 < Real.sqrt 2 ∧ Real.sqrt 2 < 141422/100000 := by
  constructor
  · exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)

lemma rootOneEquation_zero_gt : 1 < rootOneEquation 0 := by
  have hr := sqrt_two_bounds.1
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  norm_num [rootOneEquation]
  nlinarith

lemma rootTwoEquation_zero : rootTwoEquation 0 = 3/2 := by
  norm_num [rootTwoEquation, div_pow, Real.mul_self_sqrt (show (0:ℝ)≤2 by norm_num), Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]

lemma rootOneEquation_upper_test : rootOneEquation (17/100) < 1 := by
  let y : ℝ := 17/100
  let x := exceptionalX 1 y
  have hxlo : (10143:ℝ)/10000 < x := by
    apply (Real.lt_sqrt (by norm_num)).2
    norm_num [y]
  have hxhi : x < (10144:ℝ)/10000 := by
    apply (Real.sqrt_lt (by positivity) (by norm_num)).2
    norm_num [y]
  have hxs : x^2 = 1+y^2 := exceptionalX_sq (by norm_num)
  rcases sqrt_two_tight_bounds with ⟨hrlo,hrhi⟩
  have hm := mul_nonneg (show 0≤(10144:ℝ)/10000-x by linarith)
    (Real.sqrt_nonneg 2)
  have hc : exceptionalCOne y < (236:ℝ)/1000 := by
    change x*(Real.sqrt 2-x)-y < _
    dsimp [y] at *
    nlinarith
  have hs : exceptionalSOne y < (947:ℝ)/1000 := by
    change x-y*(Real.sqrt 2-x) < _
    dsimp [y] at *
    nlinarith
  have hy : y ∈ Set.Icc (0:ℝ) (27/100) := by norm_num [y]
  rcases exceptional_components_positive hy with ⟨hc0,hs0,_,_⟩
  change (exceptionalCOne y)^2+(exceptionalSOne y)^2 < 1
  nlinarith only [hc,hs,hc0,hs0]

lemma rootTwoEquation_lower_test : 1 < rootTwoEquation (347/2000) := by
  let y : ℝ := 347/2000
  let x := exceptionalX 2 y
  have hxlo : (142481:ℝ)/100000 < x := by
    apply (Real.lt_sqrt (by norm_num)).2
    norm_num [y]
  have hxhi : x < (142482:ℝ)/100000 := by
    apply (Real.sqrt_lt (by positivity) (by norm_num)).2
    norm_num [y]
  rcases sqrt_two_tight_bounds with ⟨hrlo,hrhi⟩
  have hm := mul_nonneg (show 0≤x-(142481:ℝ)/100000 by linarith)
    (show 0≤Real.sqrt 2-y by dsimp [y]; linarith)
  have hc : (7971:ℝ)/10000 < exceptionalCTwo y := by
    change _ < (x*(Real.sqrt 2-y)-y)/2
    dsimp [y] at *
    nlinarith
  have hs : (6047:ℝ)/10000 < exceptionalSTwo y := by
    change _ < (x-y*(Real.sqrt 2-y))/2
    dsimp [y] at *
    nlinarith
  change 1 < (exceptionalCTwo y)^2+(exceptionalSTwo y)^2
  nlinarith only [hc,hs]

lemma rootTwoEquation_upper_test : rootTwoEquation (7/40) < 1 := by
  let y : ℝ := 7/40
  have hx : exceptionalX 2 y = 57/40 := by
    have hx0 : 0 ≤ exceptionalX 2 y := Real.sqrt_nonneg _
    have hxs := exceptionalX_sq (y:=y) (show (0:ℝ)≤2 by norm_num)
    norm_num [y] at hxs
    nlinarith
  rcases sqrt_two_tight_bounds with ⟨hrlo,hrhi⟩
  have hc : exceptionalCTwo y < (796:ℝ)/1000 := by
    dsimp [exceptionalCTwo]
    rw [hx]
    norm_num [y]
    nlinarith
  have hs : exceptionalSTwo y < (605:ℝ)/1000 := by
    dsimp [exceptionalSTwo]
    rw [hx]
    norm_num [y]
    nlinarith
  have hy : y ∈ Set.Icc (0:ℝ) (27/100) := by norm_num [y]
  rcases exceptional_components_positive hy with ⟨_,_,hc0,hs0⟩
  change (exceptionalCTwo y)^2+(exceptionalSTwo y)^2 < 1
  nlinarith only [hc,hs,hc0,hs0]

lemma rootOneEquation_continuous : Continuous rootOneEquation := by
  unfold rootOneEquation
  continuity

lemma rootTwoEquation_continuous : Continuous rootTwoEquation := by
  unfold rootTwoEquation
  continuity

theorem exceptional_roots_exist : ∃ y₁ y₂ : ℝ, ExceptionalRoots y₁ y₂ := by
  obtain ⟨y₁,hy₁,he₁⟩ := intermediate_value_Icc'
    (a:=(0:ℝ)) (b:=17/100) (f:=rootOneEquation) (by norm_num)
    rootOneEquation_continuous.continuousOn
    ⟨rootOneEquation_upper_test.le,rootOneEquation_zero_gt.le⟩
  obtain ⟨y₂,hy₂,he₂⟩ := intermediate_value_Icc'
    (a:=((347:ℝ)/2000)) (b:=7/40) (f:=rootTwoEquation) (by norm_num)
    rootTwoEquation_continuous.continuousOn
    ⟨rootTwoEquation_upper_test.le,rootTwoEquation_lower_test.le⟩
  have h₁lo : 0 < y₁ := by
    have hn : y₁ ≠ 0 := by
      intro heq
      subst y₁
      linarith [rootOneEquation_zero_gt]
    exact lt_of_le_of_ne hy₁.1 (Ne.symm hn)
  have h₁hi : y₁ < 17/100 := by
    have hn : y₁ ≠ 17/100 := by
      intro heq
      rw [heq] at he₁
      linarith [rootOneEquation_upper_test]
    exact lt_of_le_of_ne hy₁.2 hn
  have h₂lo : 347/2000 < y₂ := by
    have hn : y₂ ≠ 347/2000 := by
      intro heq
      rw [heq] at he₂
      linarith [rootTwoEquation_lower_test]
    exact lt_of_le_of_ne hy₂.1 (Ne.symm hn)
  have h₂hi : y₂ < 7/40 := by
    have hn : y₂ ≠ 7/40 := by
      intro heq
      rw [heq] at he₂
      linarith [rootTwoEquation_upper_test]
    exact lt_of_le_of_ne hy₂.2 hn
  exact ⟨y₁,y₂,h₁lo,h₁hi,h₂lo,h₂hi,he₁,he₂⟩

theorem rootOneEquation_unique :
    ∃! y : ℝ, y ∈ Set.Icc (0:ℝ) (27/100) ∧ rootOneEquation y = 1 := by
  obtain ⟨y₁,y₂,h⟩ := exceptional_roots_exist
  have hy₁ : y₁ ∈ Set.Icc (0:ℝ) (27/100) := by
    constructor
    · exact h.1.le
    · linarith [h.2.1]
  refine ⟨y₁, ⟨hy₁,h.2.2.2.2.1⟩, ?_⟩
  intro z hz
  exact rootOneEquation_strictAntiOn.injOn hz.1 hy₁ (hz.2.trans h.2.2.2.2.1.symm)

theorem rootTwoEquation_unique :
    ∃! y : ℝ, y ∈ Set.Icc (0:ℝ) (27/100) ∧ rootTwoEquation y = 1 := by
  obtain ⟨y₁,y₂,h⟩ := exceptional_roots_exist
  have hy₂ : y₂ ∈ Set.Icc (0:ℝ) (27/100) := by
    constructor
    · linarith [h.2.2.1]
    · linarith [h.2.2.2.1]
  refine ⟨y₂, ⟨hy₂,h.2.2.2.2.2⟩, ?_⟩
  intro z hz
  exact rootTwoEquation_strictAntiOn.injOn hz.1 hy₂ (hz.2.trans h.2.2.2.2.2.symm)

end
end F3
