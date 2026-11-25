import F3.KernelEdgeBounds

/-! Scalar consequences of the exact source, middle, and sink energy balances
with one positive exceptional row satisfying the triangle inequalities. -/

namespace F3
noncomputable section

theorem triangle_source_counts {m q₀ q₁ q₂ : ℕ}
    {d r₀ r₁ r₂ D₀₁ D₀₂ : ℝ}
    (hd : 0<d) (hr₀ : 0≤r₀) (htri : r₀≤r₁+r₂)
    (hq₀ : m≤q₀) (hq₁ : m≤q₁) (hq₂ : m≤q₂)
    (hqsum : q₀+q₁+q₂=3*m+1)
    (hsource : (q₀ : ℝ)+r₀^2-D₀₁-D₀₂=(m : ℝ)+d)
    (hD₀₁ : 2*r₀*r₁≤D₀₁) (hD₀₂ : 2*r₀*r₂≤D₀₂) :
    q₀=m+1 ∧ q₁=m ∧ q₂=m := by
  have hqgt : m<q₀ := by
    by_contra h
    have hqle : (q₀ : ℝ)≤m := by exact_mod_cast (le_of_not_gt h)
    have hm := mul_nonneg hr₀ (sub_nonneg.mpr htri)
    nlinarith [sq_nonneg r₀]
  omega

theorem strict_triangle_flow_upper
    {d r₀ r₁ r₂ E₀₁ E₀₂ E₁₂ D₁₂ : ℝ}
    (hd : 0<d) (hr₀ : 0≤r₀) (hr₁ : 0<r₁) (hr₂ : 0≤r₂)
    (hrsum : r₀+r₁+r₂≤1) (htri₁ : r₁≤r₀+r₂)
    (hmiddle : d=r₁^2+E₀₁-D₁₂) (hsink : d=r₂^2+E₀₂+E₁₂)
    (hE₀₁ : E₀₁≤r₀*r₁) (hE₀₂ : E₀₂≤r₀*r₂)
    (hE₁₂ : E₁₂≤r₁*r₂) (hD₁₂ : 2*r₁*r₂≤D₁₂) : d≤1/5 := by
  have hhalf : r₁≤1/2 := by linarith
  have hmid : d≤r₁*(1-3*r₂) := by
    have hm := mul_nonneg hr₁.le (sub_nonneg.mpr hrsum)
    nlinarith
  have hsin : d≤r₂ := by
    have hm := mul_nonneg hr₂ (sub_nonneg.mpr hrsum)
    nlinarith
  have hfactor : 0≤1-3*r₂ := by
    by_contra hn
    have hm := mul_neg_of_pos_of_neg hr₁ (lt_of_not_ge hn)
    linarith
  have hbound := mul_nonneg (sub_nonneg.mpr hhalf) hfactor
  nlinarith

theorem degenerate_source_flow_impossible
    {d r₀ r₁ r₂ E₀₁ E₀₂ E₁₂ D₁₂ : ℝ}
    (hd : 1/5<d) (hr₁ : 0≤r₁) (hr₂ : 0≤r₂)
    (hdeg : r₀=r₁+r₂) (hhalf : r₀≤1/2)
    (hmiddle : d=r₁^2+E₀₁-D₁₂) (hsink : d=r₂^2+E₀₂+E₁₂)
    (hE₀₁ : E₀₁≤r₁^2) (hE₀₂ : E₀₂≤r₂^2)
    (hE₁₂ : E₁₂<1/35) (hD₁₂ : 0≤D₁₂) : False := by
  have hr₂large : 1/4<r₂ := by
    by_contra hn
    have hsq : r₂^2≤1/16 := by nlinarith [mul_nonneg hr₂ (sub_nonneg.mpr (le_of_not_gt hn))]
    linarith
  have hr₁small : r₁<1/4 := by linarith
  have hsq : r₁^2<1/16 := by nlinarith [mul_nonneg hr₁ (sub_nonneg.mpr hr₁small.le)]
  linarith

theorem degenerate_middle_flow_impossible
    {d r₀ r₁ r₂ E₀₁ E₀₂ E₁₂ D₁₂ : ℝ}
    (hd : 1/5<d) (hr₀ : 0≤r₀) (hr₂ : 0≤r₂)
    (hdeg : r₁=r₀+r₂) (hhalf : r₁≤1/2)
    (hmiddle : d=r₁^2+E₀₁-D₁₂) (hsink : d=r₂^2+E₀₂+E₁₂)
    (hE₀₁ : E₀₁≤r₀^2) (hE₀₂ : E₀₂<1/35)
    (hE₁₂ : E₁₂≤r₂^2) (hD₁₂ : 2*r₁*r₂≤D₁₂) : False := by
  have hr₂large : 1/4<r₂ := by
    by_contra hn
    have hsq : r₂^2≤1/16 := by nlinarith [mul_nonneg hr₂ (sub_nonneg.mpr (le_of_not_gt hn))]
    linarith
  have hr₀small : r₀<1/4 := by linarith
  have hsq : r₀^2<1/16 := by nlinarith [mul_nonneg hr₀ (sub_nonneg.mpr hr₀small.le)]
  have hother : r₀^2≤r₂^2 := by nlinarith
  nlinarith

theorem degenerate_sink_flow_impossible
    {d r₀ r₁ r₂ E₀₁ D₁₂ : ℝ}
    (hd : 1/5<d) (hr₀ : 0≤r₀) (hr₁ : 0≤r₁)
    (hdeg : r₂=r₀+r₁)
    (hmiddle : d=r₁^2+E₀₁-D₁₂)
    (hE₀₁ : E₀₁<1/35) (hD₁₂ : 2*r₁*r₂≤D₁₂) : False := by
  nlinarith [mul_nonneg hr₀ hr₁,sq_nonneg r₁]

end
end F3
