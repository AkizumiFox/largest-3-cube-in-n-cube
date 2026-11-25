import F3.SignChanges

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

lemma scalar_negative_pair_stationarity {a b g h d e t lam : ℝ}
    (hab : a*b<0) (hg : a*g=|a|) (hh : b*h=|b|)
    (hs1 : a*d+b*t=lam*g) (hs2 : a*t+b*e=lam*h) :
    (d+t)*|a|=(e+t)*|b| := by
  by_cases ha : 0<a
  · have hb : b<0 := by nlinarith
    have hg1 : g=1 := mul_left_cancel₀ (ne_of_gt ha) (by simpa [abs_of_pos ha] using hg)
    have hh1 : h = -1 := mul_left_cancel₀ (ne_of_lt hb) (by simpa [abs_of_neg hb] using hh)
    rw [hg1] at hs1
    rw [hh1] at hs2
    rw [abs_of_pos ha,abs_of_neg hb]
    nlinarith
  · have han : a<0 := by
      have hane : a≠0 := by intro hz; rw [hz,zero_mul] at hab; linarith
      exact lt_of_le_of_ne (le_of_not_gt ha) hane
    have hb : 0<b := by nlinarith
    have hg1 : g = -1 := mul_left_cancel₀ (ne_of_lt han) (by simpa [abs_of_neg han] using hg)
    have hh1 : h=1 := mul_left_cancel₀ (ne_of_gt hb) (by simpa [abs_of_pos hb] using hh)
    rw [hg1] at hs1
    rw [hh1] at hs2
    rw [abs_of_neg han,abs_of_pos hb]
    nlinarith

lemma scalar_positive_pair_stationarity {a b g h d e t lam : ℝ}
    (hab : 0<a*b) (hg : a*g=|a|) (hh : b*h=|b|)
    (hs1 : a*d+b*t=lam*g) (hs2 : a*t+b*e=lam*h) :
    (d-t)*|a|=(e-t)*|b| := by
  by_cases ha : 0<a
  · have hb : 0<b := by nlinarith
    have hg1 : g=1 := mul_left_cancel₀ (ne_of_gt ha) (by simpa [abs_of_pos ha] using hg)
    have hh1 : h=1 := mul_left_cancel₀ (ne_of_gt hb) (by simpa [abs_of_pos hb] using hh)
    rw [hg1] at hs1
    rw [hh1] at hs2
    rw [abs_of_pos ha,abs_of_pos hb]
    nlinarith
  · have han : a<0 := by
      have hane : a≠0 := by intro hz; rw [hz,zero_mul] at hab; linarith
      exact lt_of_le_of_ne (le_of_not_gt ha) hane
    have hb : b<0 := by nlinarith
    have hg1 : g = -1 := mul_left_cancel₀ (ne_of_lt han) (by simpa [abs_of_neg han] using hg)
    have hh1 : h = -1 := mul_left_cancel₀ (ne_of_lt hb) (by simpa [abs_of_neg hb] using hh)
    rw [hg1] at hs1
    rw [hh1] at hs2
    rw [abs_of_neg han,abs_of_neg hb]
    nlinarith

lemma multiplier_pair_equations {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A) (i : ι)
    {j k : Fin 3} (hjk : j≠k)
    (hz : ∀l,l≠j → l≠k → A i l=0) :
    A i j*M.matrix j j+A i k*M.matrix j k=M.weight i*M.gradient i j ∧
    A i j*M.matrix j k+A i k*M.matrix k k=M.weight i*M.gradient i k := by
  classical
  have hs (t : Fin 3) : (∑ l,A i l*M.matrix l t)=
      A i j*M.matrix j t+A i k*M.matrix k t := by
    calc
      _ = ∑ l ∈ ({j,k}:Finset (Fin 3)), A i l*M.matrix l t := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro l _ hl
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hl
        rw [hz l hl.1 hl.2,zero_mul]
      _ = _ := by simp [hjk]
  constructor
  · have h := M.stationarity i j
    rw [hs j,M.symmetric k j] at h
    exact h
  · have h := M.stationarity i k
    rw [hs k] at h
    exact h

theorem multiplier_negative_pair_stationarity {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A) (i : ι)
    {j k : Fin 3} (hjk : j≠k)
    (hz : ∀l,l≠j → l≠k → A i l=0) (hneg : A i j*A i k<0) :
    (M.matrix j j+M.matrix j k)*|A i j|=
      (M.matrix k k+M.matrix j k)*|A i k| := by
  obtain ⟨hs1,hs2⟩ := multiplier_pair_equations M i hjk hz
  exact scalar_negative_pair_stationarity hneg ((M.subgradient i).2 j) ((M.subgradient i).2 k) hs1 hs2

theorem multiplier_positive_pair_stationarity {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A) (i : ι)
    {j k : Fin 3} (hjk : j≠k)
    (hz : ∀l,l≠j → l≠k → A i l=0) (hpos : 0<A i j*A i k) :
    (M.matrix j j-M.matrix j k)*|A i j|=
      (M.matrix k k-M.matrix j k)*|A i k| := by
  obtain ⟨hs1,hs2⟩ := multiplier_pair_equations M i hjk hz
  exact scalar_positive_pair_stationarity hpos ((M.subgradient i).2 j) ((M.subgradient i).2 k) hs1 hs2


lemma quadraticThree_two_support (S : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ)
    {j k : Fin 3} (hjk : j≠k) (hz : ∀l,l≠j → l≠k → v l=0) :
    quadraticThree S v=v j*S j j*v j+v j*S j k*v k+
      v k*S k j*v j+v k*S k k*v k := by
  classical
  have hs (f : Fin 3 → ℝ) (hf : ∀l,l≠j → l≠k → f l=0) :
      (∑l,f l)=f j+f k := by
    calc
      _ = ∑ l ∈ ({j,k}:Finset (Fin 3)),f l := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro l _ hl
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hl
        exact hf l hl.1 hl.2
      _ = _ := by simp [hjk]
  have hin (l : Fin 3) : (∑t,v l*S l t*v t)=v l*S l j*v j+v l*S l k*v k :=
    hs _ (by intro t htj htk; rw [hz t htj htk,mul_zero])
  unfold quadraticThree
  rw [hs _ (by intro l hlj hlk; simp [hz l hlj hlk]),hin j,hin k]
  ring

lemma quadratic_pair_plus {S : Fin 3 → Fin 3 → ℝ}
    (hsym : ∀j k,S j k=S k j) {j k : Fin 3} (hjk : j≠k) :
    quadraticThree S (fun l => if l=j ∨ l=k then 1 else 0)=
      S j j+S k k+2*S j k := by
  rw [quadraticThree_two_support S _ hjk (by intro l hlj hlk; simp [hlj,hlk])]
  simp [hjk,hjk.symm,hsym k j]
  ring

lemma quadratic_pair_minus {S : Fin 3 → Fin 3 → ℝ}
    (hsym : ∀j k,S j k=S k j) {j k : Fin 3} (hjk : j≠k) :
    quadraticThree S (fun l => if l=j then 1 else if l=k then -1 else 0)=
      S j j+S k k-2*S j k := by
  rw [quadraticThree_two_support S _ hjk (by intro l hlj hlk; simp [hlj,hlk])]
  simp [hjk,hjk.symm,hsym k j]
  ring

lemma positive_pair_coefficients {p q a b : ℝ}
    (hp : 0≤p) (hq : 0≤q) (hs : 0<p+q)
    (ha : 0<a) (hb : 0<b) (he : p*a=q*b) : 0<p ∧ 0<q := by
  constructor
  · by_contra! h
    have hp0 : p=0 := by linarith
    have hq0 : 0<q := by linarith
    rw [hp0,zero_mul] at he
    have ht := mul_pos hq0 hb
    linarith
  · by_contra! h
    have hq0 : q=0 := by linarith
    have hp0 : 0<p := by linarith
    rw [hq0,zero_mul] at he
    have ht := mul_pos hp0 ha
    linarith

lemma positive_pair_orientation {p q a b : ℝ}
    (hp : 0<p) (hq : 0<q) (ha : 0<a) (hb : 0<b)
    (he : p*a=q*b) : (b<a ↔ p<q) := by
  constructor
  · intro h
    by_contra! hn
    have h1 := mul_pos hp (show 0<a-b by linarith)
    have h2 := mul_nonneg (show 0≤p-q by linarith) hb.le
    nlinarith only [h1,h2,he]
  · intro h
    by_contra! hn
    have h1 := mul_pos (show 0<q-p by linarith) hb
    have h2 := mul_nonneg hp.le (show 0≤b-a by linarith)
    nlinarith only [h1,h2,he]

lemma negative_pair_coefficients_pos {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A)
    (hpd : ∀v : Fin 3 → ℝ, v≠0 → 0<quadraticThree M.matrix v)
    (i : ι) {j k : Fin 3} (hjk : j≠k)
    (hz : ∀l,l≠j → l≠k → A i l=0) (hneg : A i j*A i k<0) :
    0<M.matrix j j+M.matrix j k ∧ 0<M.matrix k k+M.matrix j k := by
  have hbound1 := abs_le.mp (multiplier_entry_bound hA hs M j k)
  have hbound2 := multiplier_entry_bound hA hs M k j
  rw [M.symmetric k j] at hbound2
  have hbound2' := abs_le.mp hbound2
  have hne : (fun l : Fin 3 => if l=j ∨ l=k then (1:ℝ) else 0)≠0 := by
    intro h
    have he := congrFun h j
    simp at he
  have hsum := hpd _ hne
  rw [quadratic_pair_plus M.symmetric hjk] at hsum
  have hpa : 0< |A i j| := abs_pos.mpr (left_ne_zero_of_mul (ne_of_lt hneg))
  have hpb : 0< |A i k| := abs_pos.mpr (right_ne_zero_of_mul (ne_of_lt hneg))
  exact positive_pair_coefficients (by linarith) (by linarith) (by linarith) hpa hpb
    (multiplier_negative_pair_stationarity M i hjk hz hneg)

lemma positive_pair_coefficients_pos {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A)
    (hpd : ∀v : Fin 3 → ℝ, v≠0 → 0<quadraticThree M.matrix v)
    (i : ι) {j k : Fin 3} (hjk : j≠k)
    (hz : ∀l,l≠j → l≠k → A i l=0) (hpos : 0<A i j*A i k) :
    0<M.matrix j j-M.matrix j k ∧ 0<M.matrix k k-M.matrix j k := by
  have hbound1 := abs_le.mp (multiplier_entry_bound hA hs M j k)
  have hbound2 := multiplier_entry_bound hA hs M k j
  rw [M.symmetric k j] at hbound2
  have hbound2' := abs_le.mp hbound2
  have hne : (fun l : Fin 3 => if l=j then (1:ℝ) else if l=k then -1 else 0)≠0 := by
    intro h
    have he := congrFun h j
    simp at he
  have hsum := hpd _ hne
  rw [quadratic_pair_minus M.symmetric hjk] at hsum
  have hpa : 0< |A i j| := abs_pos.mpr (left_ne_zero_of_mul (ne_of_gt hpos))
  have hpb : 0< |A i k| := abs_pos.mpr (right_ne_zero_of_mul (ne_of_gt hpos))
  exact positive_pair_coefficients (by linarith) (by linarith) (by linarith) hpa hpb
    (multiplier_positive_pair_stationarity M i hjk hz hpos)

theorem negative_pair_orientation {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A)
    (hpd : ∀v : Fin 3 → ℝ, v≠0 → 0<quadraticThree M.matrix v)
    (i : ι) {j k : Fin 3} (hjk : j≠k)
    (hz : ∀l,l≠j → l≠k → A i l=0) (hneg : A i j*A i k<0) :
    (|A i k|< |A i j| ↔ M.matrix j j<M.matrix k k) := by
  obtain ⟨hp,hq⟩ := negative_pair_coefficients_pos hA hs M hpd i hjk hz hneg
  have ha := abs_pos.mpr (left_ne_zero_of_mul (ne_of_lt hneg))
  have hb := abs_pos.mpr (right_ne_zero_of_mul (ne_of_lt hneg))
  have he := multiplier_negative_pair_stationarity M i hjk hz hneg
  simpa only [add_lt_add_iff_right] using positive_pair_orientation hp hq ha hb he

lemma negative_pair_orientation_le {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A)
    (hpd : ∀v : Fin 3 → ℝ, v≠0 → 0<quadraticThree M.matrix v)
    (i : ι) {j k : Fin 3} (hjk : j≠k)
    (hz : ∀l,l≠j → l≠k → A i l=0) (hneg : A i j*A i k<0)
    (horder : M.matrix j j≤M.matrix k k) : |A i k|≤ |A i j| := by
  obtain ⟨hp,hq⟩ := negative_pair_coefficients_pos hA hs M hpd i hjk hz hneg
  have ha := abs_pos.mpr (left_ne_zero_of_mul (ne_of_lt hneg))
  have hb := abs_pos.mpr (right_ne_zero_of_mul (ne_of_lt hneg))
  have he := multiplier_negative_pair_stationarity M i hjk hz hneg
  by_contra! hn
  have ho := (positive_pair_orientation hq hp hb ha he.symm).mp hn
  linarith

theorem positive_pair_orientation_actual {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A)
    (hpd : ∀v : Fin 3 → ℝ, v≠0 → 0<quadraticThree M.matrix v)
    (i : ι) {j k : Fin 3} (hjk : j≠k)
    (hz : ∀l,l≠j → l≠k → A i l=0) (hpos : 0<A i j*A i k) :
    (|A i k|< |A i j| ↔ M.matrix j j<M.matrix k k) := by
  obtain ⟨hp,hq⟩ := positive_pair_coefficients_pos hA hs M hpd i hjk hz hpos
  have ha := abs_pos.mpr (left_ne_zero_of_mul (ne_of_gt hpos))
  have hb := abs_pos.mpr (right_ne_zero_of_mul (ne_of_gt hpos))
  have he := multiplier_positive_pair_stationarity M i hjk hz hpos
  simpa only [sub_lt_sub_iff_right] using positive_pair_orientation hp hq ha hb he

end
end F3
