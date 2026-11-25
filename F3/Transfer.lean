import F3.Frames
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Energy transfer for cancelling saturated pair rows

The hypotheses below describe the magnitudes in the positive and negative
column-product groups.  The two product sums are equal precisely because
those signed products cancel.  No optimizer or sharp-value hypothesis is used.
The weak endpoint conditions include the strict interior case in the paper.
-/

namespace F3
namespace Transfer
noncomputable section
open scoped BigOperators

/-- Sum of squared smaller-coordinate magnitudes. -/
def energy {ι : Type*} [Fintype ι] (b : ι → ℝ) : ℝ := ∑ i, (b i)^2

/-- Sum of absolute products in one sign group. -/
def productMass {ι : Type*} [Fintype ι] (b : ι → ℝ) : ℝ :=
  ∑ i, b i * (1 - b i)

/-- Sharp nonlinear lower bound on loss. -/
def phi (E : ℝ) : ℝ := 2 * Real.sqrt (2 * E) - 2 * E

/-- The inverse transfer function in the manuscript. -/
def B (D : ℝ) : ℝ := 2 * (1 - Real.sqrt (1 - D / 2))^2

lemma energy_nonneg {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    0 ≤ energy b := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma productMass_nonneg {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1 / 2) : 0 ≤ productMass b := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hb i).1 (by linarith [(hb i).2]))

lemma energy_le_productMass {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1 / 2) : energy b ≤ productMass b := by
  apply Finset.sum_le_sum
  intro i _
  nlinarith [mul_nonneg (hb i).1 (show 0 ≤ 1 - 2 * b i by linarith [(hb i).2])]

lemma product_le_productMass {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1 / 2) (i : ι) :
    b i * (1 - b i) ≤ productMass b := by
  unfold productMass
  exact Finset.single_le_sum (f := fun j => b j * (1 - b j))
    (s := Finset.univ)
    (fun j _ => mul_nonneg (hb j).1 (by linarith [(hb j).2]))
    (Finset.mem_univ i)

lemma magnitude_le_root {b q : ℝ}
    (_hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1 / 2)
    (hprod : b * (1 - b) ≤ q * (1 - q)) : b ≤ q := by
  by_contra h
  have hqb : q < b := lt_of_not_ge h
  have hp : 0 < (b - q) * (1 - b - q) := by
    apply mul_pos
    · linarith
    · linarith
  nlinarith

lemma energy_le_root_sq {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1 / 2)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hP : productMass b = q * (1 - q)) : energy b ≤ q^2 := by
  have hi (i : ι) : b i ≤ q :=
    magnitude_le_root (hb i).1 (hb i).2 hq0 hq1
      (by simpa [hP] using product_le_productMass b hb i)
  have hs : (1 - q) * energy b ≤ q * productMass b := by
    unfold energy productMass
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_nonneg (hb i).1 (sub_nonneg.mpr (hi i))]
  rw [hP] at hs
  have hfac : 0 < 1 - q := by linarith
  have hmul : (1 - q) * energy b ≤ (1 - q) * q^2 := by nlinarith [hs]
  exact (mul_le_mul_left hfac).mp hmul

lemma phi_le_one {E : ℝ} (hE : 0 ≤ E) : phi E ≤ 1 := by
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * E by positivity)
  unfold phi
  nlinarith [sq_nonneg (Real.sqrt (2 * E) - 1)]

lemma phi_mono_half {E F : ℝ} (hE : 0 ≤ E) (hEF : E ≤ F)
    (hF : F ≤ 1 / 2) : phi E ≤ phi F := by
  have hr := Real.sqrt_le_sqrt (show 2 * E ≤ 2 * F by linarith)
  have ht : Real.sqrt (2 * F) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hsE := Real.sq_sqrt (show 0 ≤ 2 * E by positivity)
  have hsF := Real.sq_sqrt (show 0 ≤ 2 * F by linarith)
  have hp := mul_nonneg (sub_nonneg.mpr hr)
    (show 0 ≤ 2 - Real.sqrt (2 * F) - Real.sqrt (2 * E) by linarith)
  unfold phi
  nlinarith

/-- The edge-transfer loss inequalities from the actual two sign groups. -/
theorem edge_loss {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → ℝ) (c : κ → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1 / 2)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1 / 2)
    (hcancel : productMass b = productMass c) :
    let E := energy b + energy c
    let L := 2 * (productMass b + productMass c)
    2 * E ≤ L ∧ phi E ≤ L ∧ 3 * E ≤ L + E := by
  dsimp
  have hEb := energy_nonneg b
  have hEc := energy_nonneg c
  have hPb := productMass_nonneg b hb
  have hEcP := energy_le_productMass c hc
  have hEbP := energy_le_productMass b hb
  have hbasic : 2 * (energy b + energy c) ≤
      2 * (productMass b + productMass c) := by linarith
  refine ⟨hbasic, ?_, by linarith⟩
  by_cases hsmall : productMass b ≤ 1 / 4
  · let q := (1 - Real.sqrt (1 - 4 * productMass b)) / 2
    have hs0 : 0 ≤ 1 - 4 * productMass b := by linarith
    have hsle : Real.sqrt (1 - 4 * productMass b) ≤ 1 :=
      Real.sqrt_le_one.mpr (by linarith)
    have hsnonneg := Real.sqrt_nonneg (1 - 4 * productMass b)
    have hsq := Real.sq_sqrt hs0
    have hq0 : 0 ≤ q := by dsimp [q]; linarith
    have hq1 : q ≤ 1 / 2 := by dsimp [q]; linarith
    have hqP : productMass b = q * (1 - q) := by dsimp [q]; nlinarith
    have hqb := energy_le_root_sq b hb hq0 hq1 hqP
    have hqc := energy_le_root_sq c hc hq0 hq1 (hcancel.symm.trans hqP)
    have hE : energy b + energy c ≤ 2 * q^2 := by linarith
    have hroot : Real.sqrt (2 * (energy b + energy c)) ≤ 2 * q := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by positivity, by nlinarith⟩
    have hEsq := Real.sq_sqrt (show 0 ≤ 2 * (energy b + energy c) by positivity)
    have hfac := mul_nonneg (sub_nonneg.mpr hroot)
      (show 0 ≤ 2 - 2 * q - Real.sqrt (2 * (energy b + energy c)) by linarith)
    unfold phi
    nlinarith [hqP]
  · have hphi := phi_le_one (show 0 ≤ energy b + energy c by positivity)
    linarith

/-- Inversion on the branch actually used in the paper. -/
theorem edge_inverse {E L : ℝ} (hE : 0 ≤ E)
    (hlinear : 2 * E ≤ L) (hsharp : phi E ≤ L)
    (hD : L + E < 3 / 2) : E ≤ B (L + E) := by
  have hD0 : 0 ≤ L + E := by linarith
  have hEhalf : E < 1 / 2 := by linarith
  have hEroot := Real.sqrt_nonneg (2 * E)
  have hEroot1 : Real.sqrt (2 * E) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hEsq := Real.sq_sqrt (show 0 ≤ 2 * E by positivity)
  have hbase : 0 ≤ 1 - (L + E) / 2 := by linarith
  have hroot := Real.sqrt_le_one.mpr (show 1 - (L + E) / 2 ≤ 1 by linarith)
  have hrootsq := Real.sq_sqrt hbase
  have hinv : Real.sqrt (1 - (L + E) / 2) ≤ 1 - Real.sqrt (2 * E) / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · unfold phi at hsharp
      nlinarith
  have hp := mul_nonneg
    (show 0 ≤ 2 * (1 - Real.sqrt (1 - (L + E) / 2)) - Real.sqrt (2 * E) by linarith)
    (show 0 ≤ 2 * (1 - Real.sqrt (1 - (L + E) / 2)) + Real.sqrt (2 * E) by linarith)
  unfold B
  nlinarith

/-- A lower bound valid even if the incoming energy exceeds one half. -/
theorem loss_of_energy_lower_bound {E L d : ℝ}
    (hd0 : 0 ≤ d) (hdE : d ≤ E)
    (hlinear : 2 * E ≤ L) (hsharp : phi E ≤ L) : phi d ≤ L := by
  by_cases hhalf : E ≤ 1 / 2
  · exact (phi_mono_half hd0 hdE hhalf).trans hsharp
  · exact (phi_le_one hd0).trans (by linarith)

/-- Monotonicity and the one-Lipschitz bound used in residue two. -/
theorem B_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b < 3 / 2) : 0 ≤ B b - B a ∧ B b - B a ≤ b - a := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hbasea : 0 ≤ 1 - a / 2 := by linarith
  have hbaseb : 0 ≤ 1 - b / 2 := by linarith
  have hsa := Real.sq_sqrt hbasea
  have hsb := Real.sq_sqrt hbaseb
  have hra := Real.sqrt_nonneg (1 - a / 2)
  have hrb := Real.sqrt_nonneg (1 - b / 2)
  have hmono : Real.sqrt (1 - b / 2) ≤ Real.sqrt (1 - a / 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have ha1 : Real.sqrt (1 - a / 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hb1 : Real.sqrt (1 - b / 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hbhalf : 1 / 2 < Real.sqrt (1 - b / 2) := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hmono)
    (show 0 ≤ 2 - Real.sqrt (1 - a / 2) - Real.sqrt (1 - b / 2) by linarith)
  have hq := mul_nonneg (sub_nonneg.mpr hmono)
    (show 0 ≤ Real.sqrt (1 - a / 2) + Real.sqrt (1 - b / 2) - 1 by linarith)
  unfold B
  constructor <;> nlinarith

theorem B_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b < 3 / 2) : B a ≤ B b := by
  have h := (B_increment ha hab hb).1
  linarith

/-- The stable first-residue scalar upper bound, with its preliminary range. -/
theorem residue_one_scalar {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hloss : 4 * Real.sqrt (2 * d) - 4 * d ≤ 1 - 3 * d) :
    d ≤ 15 - 4 * Real.sqrt 14 := by
  have hr := Real.sqrt_nonneg (2 * d)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * d by positivity)
  have hp := mul_nonneg
    (show 0 ≤ 1 + d - 4 * Real.sqrt (2 * d) by linarith)
    (show 0 ≤ 1 + d + 4 * Real.sqrt (2 * d) by positivity)
  have hpoly : 0 ≤ d^2 - 30 * d + 1 := by nlinarith
  have h14 := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
  have h14n := Real.sqrt_nonneg 14
  by_contra hn
  have hpos : 0 < d - (15 - 4 * Real.sqrt 14) := by linarith
  have hneg : 0 < 15 + 4 * Real.sqrt 14 - d := by linarith
  have hproduct := mul_pos hpos hneg
  nlinarith

/-- The alternative row-count pattern is incompatible with d > 1/5. -/
theorem residue_two_surplus_exclusion {d : ℝ}
    (hd0 : 1 / 5 < d) (hd1 : d ≤ 4 / 9)
    (hloss : 4 * Real.sqrt (2 * d) - 4 * d ≤ 2 - 3 * d) : False := by
  have hr := Real.sqrt_nonneg (2 * d)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * d by linarith)
  have hp := mul_nonneg
    (show 0 ≤ 2 + d - 4 * Real.sqrt (2 * d) by linarith)
    (show 0 ≤ 2 + d + 4 * Real.sqrt (2 * d) by positivity)
  have hpoly : 0 ≤ d^2 - 28 * d + 4 := by nlinarith
  have hprod := mul_nonneg (show 0 ≤ d by linarith) (show 0 ≤ 4 / 9 - d by linarith)
  nlinarith

/-- The final scalar inequality in the second-residue proof. -/
theorem residue_two_scalar {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hsharp : d ≤ 4 * (1 - Real.sqrt ((1 + d) / 2))^2) :
    d ≤ 10 - 4 * Real.sqrt 6 := by
  have hx := Real.sqrt_nonneg d
  have hx2 := Real.sq_sqrt hd0
  have hy := Real.sqrt_nonneg ((1 + d) / 2)
  have hy2 := Real.sq_sqrt (show 0 ≤ (1 + d) / 2 by positivity)
  have hy1 : Real.sqrt ((1 + d) / 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hxy : Real.sqrt d ≤ 2 * (1 - Real.sqrt ((1 + d) / 2)) := by
    nlinarith [sq_nonneg (Real.sqrt d - 2 * (1 - Real.sqrt ((1 + d) / 2)))]
  have hpos := mul_nonneg
    (show 0 ≤ 2 - Real.sqrt d - 2 * Real.sqrt ((1 + d) / 2) by linarith)
    (show 0 ≤ 2 - Real.sqrt d + 2 * Real.sqrt ((1 + d) / 2) by linarith)
  have hquad : d + 4 * Real.sqrt d - 2 ≤ 0 := by nlinarith
  have h6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have h6n := Real.sqrt_nonneg 6
  have h6p : 2 ≤ Real.sqrt 6 := by nlinarith
  have hxle : Real.sqrt d ≤ Real.sqrt 6 - 2 := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hxle)
    (show 0 ≤ Real.sqrt 6 - 2 + Real.sqrt d by linarith)
  nlinarith


open scoped BigOperators

/-- The geometric row loss of a saturated pair with magnitudes 1-b and b. -/
def rowLoss (b : ℝ) : ℝ := 1 - ((1 - b)^2 + b^2)

def loss {ι : Type*} [Fintype ι] (b : ι → ℝ) : ℝ := ∑ i, rowLoss (b i)

theorem rowLoss_eq (b : ℝ) : rowLoss b = 2 * b * (1 - b) := by
  unfold rowLoss
  ring

theorem loss_eq_two_productMass {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    loss b = 2 * productMass b := by
  unfold loss productMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowLoss_eq]
  ring

/-- Edge transfer with loss defined as one minus the row squared norm. -/
theorem edge_transfer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → ℝ) (c : κ → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1 / 2)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1 / 2)
    (hcancel : productMass b = productMass c) :
    let E := energy b + energy c
    let L := loss b + loss c
    2 * E ≤ L ∧ phi E ≤ L ∧ 3 * E ≤ L + E := by
  dsimp
  have h := edge_loss b c hb hc hcancel
  dsimp at h
  rw [loss_eq_two_productMass, loss_eq_two_productMass]
  constructor
  · linarith [h.1]
  constructor
  · linarith [h.2.1]
  · linarith [h.2.2]

theorem correction_two_bounds : (1 : ℝ) / 5 < 10 - 4 * Real.sqrt 6 ∧
    10 - 4 * Real.sqrt 6 < 1 := by
  have h6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have h6n := Real.sqrt_nonneg 6
  constructor <;> nlinarith

theorem B_at_correction_two :
    B (1 - (10 - 4 * Real.sqrt 6)) = (10 - 4 * Real.sqrt 6) / 2 := by
  have h6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have h6n := Real.sqrt_nonneg 6
  have h6b : Real.sqrt 6 ≤ 4 := by nlinarith
  have hbase : 1 - (1 - (10 - 4 * Real.sqrt 6)) / 2 =
      (2 - Real.sqrt 6 / 2)^2 := by nlinarith
  unfold B
  rw [hbase, Real.sqrt_sq (by linarith : 0 ≤ 2 - Real.sqrt 6 / 2)]
  nlinarith

theorem B_source_cap {d : ℝ} (hdlo : 10 - 4 * Real.sqrt 6 ≤ d)
    (hdhi : d ≤ 1) : B (1 - d) ≤ d / 2 := by
  have hb := correction_two_bounds
  have hm := B_mono (show 0 ≤ 1 - d by linarith)
    (show 1 - d ≤ 1 - (10 - 4 * Real.sqrt 6) by linarith)
    (show 1 - (10 - 4 * Real.sqrt 6) < 3 / 2 by linarith)
  rw [B_at_correction_two] at hm
  linarith

/-- The three-vertex flow estimate.  The hypotheses are the individual
edge-transfer inequalities and the source, middle, and sink energy balances.
It does not assert that every optimizer admits such a flow. -/
theorem three_vertex_flow {d E12 E13 E23 D23 : ℝ}
    (hdlo : 10 - 4 * Real.sqrt 6 ≤ d) (hdhi : d ≤ 4 / 9)
    (hE12 : 0 ≤ E12) (hE13 : 0 ≤ E13)
    (hsource : E12 + E13 ≤ B (1 - d))
    (hmiddle : D23 = 1 - d + E12)
    (hsink : d = E13 + E23)
    (hedge : E23 ≤ B D23) : d ≤ 10 - 4 * Real.sqrt 6 := by
  have hdpos : 0 < d := lt_of_lt_of_le (by linarith [correction_two_bounds.1]) hdlo
  have hcap := B_source_cap hdlo (show d ≤ 1 by linarith)
  have hD0 : 0 ≤ 1 - d := by linarith
  have hD23hi : D23 < 1 := by linarith
  have hinc := (B_increment hD0
    (show 1 - d ≤ D23 by linarith)
    (show D23 < 3 / 2 by linarith)).2
  have hfinal : d ≤ 2 * B (1 - d) := by linarith
  apply residue_two_scalar (le_of_lt hdpos) (by linarith)
  have heq : 2 * B (1 - d) = 4 * (1 - Real.sqrt ((1 + d) / 2))^2 := by
    unfold B
    rw [show 1 - (1 - d) / 2 = (1 + d) / 2 by ring]
    ring
  rwa [heq] at hfinal

/-- Pair stationarity orders the dominant coordinate by multiplier diagonal. -/
theorem pair_orientation {a b p q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (_hq : 0 < q)
    (hstationary : p * a = q * b) : (b < a ↔ p < q) := by
  constructor
  · intro h
    by_contra hn
    have hqp : q ≤ p := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_right hqp (le_of_lt ha)
    nlinarith
  · intro h
    by_contra hn
    have hab : a ≤ b := le_of_not_gt hn
    have hmul := mul_le_mul_of_nonneg_left hab (le_of_lt hp)
    nlinarith

theorem pair_balanced_iff {a b p q : ℝ}
    (ha : 0 < a) (hp : 0 < p)
    (hstationary : p * a = q * b) : (a = b ↔ p = q) := by
  constructor
  · intro h
    rw [h] at ha hstationary
    exact (mul_left_inj' (ne_of_gt ha)).mp hstationary
  · intro h
    rw [← h] at hstationary
    exact (mul_right_inj' (ne_of_gt hp)).mp hstationary

/-- A strict scalar potential excludes directed cycles. -/
theorem ascending_transitive {ι : Type*} {R : ι → ι → Prop}
    {v : ι → ℝ} (hR : ∀ a b, R a b → v a < v b)
    {a b : ι} (h : Relation.TransGen R a b) : v a < v b := by
  induction h with
  | single h => exact hR _ _ h
  | tail h hlast ih => exact lt_trans ih (hR _ _ hlast)

theorem ascending_acyclic {ι : Type*} {R : ι → ι → Prop}
    {v : ι → ℝ} (hR : ∀ a b, R a b → v a < v b) (a : ι) :
    ¬ Relation.TransGen R a a := by
  intro h
  exact (lt_irrefl (v a)) (ascending_transitive hR h)

end
end Transfer
end F3
