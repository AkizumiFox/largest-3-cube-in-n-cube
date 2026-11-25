import F3.KernelRows
import F3.OrderedPairFrames

namespace F3
noncomputable section
open scoped BigOperators

theorem fin_three_sum_distinct (f : Fin 3 → ℝ) {j k l : Fin 3}
    (hjk : j≠k) (hlj : l≠j) (hlk : l≠k) :
    (∑ q, f q)=f j+f k+f l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [Fin.sum_univ_three,add_comm,add_left_comm,add_assoc] <;> ring

theorem fin_three_exhaustive {j k l : Fin 3} (hjk : j≠k) (hlj : l≠j) (hlk : l≠k)
    (q : Fin 3) : q=j ∨ q=k ∨ q=l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases q <;> simp_all

/-- A vanishing principal minor and a full kernel vector provide a second,
independent kernel vector. This uses only elementary elimination. -/
theorem zero_principal_minor_independent_kernel {S : Fin 3 → Fin 3 → ℝ}
    (hsym : ∀j k,S j k=S k j) {r : Fin 3 → ℝ}
    (hr : ∀q,r q≠0) (hker : ∀q,(∑t,r t*S t q)=0)
    {j k : Fin 3} (hjk : j≠k) (hjj : 0<S j j)
    (hdet : S j j*S k k-(S j k)^2=0) :
    ∃ v : Fin 3 → ℝ, RowPairIndependent v r ∧ ∀q,(∑t,v t*S t q)=0 := by
  classical
  have he : ∀j k : Fin 3,j≠k→∃l,l≠j∧l≠k := by decide
  obtain ⟨l,hlj,hlk⟩ := he j k hjk
  let v : Fin 3 → ℝ := fun t => if t=j then S j k else if t=k then -S j j else 0
  have hvj : v j=S j k := by simp [v]
  have hvk : v k= -S j j := by simp [v,Ne.symm hjk]
  have hvl : v l=0 := by simp [v,hlj,hlk]
  have hsum (q : Fin 3) : (∑t,v t*S t q)=S j k*S j q-S j j*S k q := by
    rw [fin_three_sum_distinct _ hjk hlj hlk,hvj,hvk,hvl]
    ring
  have hkj := hsym k j
  have hlj' := hsym l j
  have hlk' := hsym l k
  have hkerj := hker j
  have hkerk := hker k
  rw [fin_three_sum_distinct _ hjk hlj hlk,hkj,hlj'] at hkerj
  rw [fin_three_sum_distinct _ hjk hlj hlk,hlk'] at hkerk
  have hell : r l*(S j k*S j l-S j j*S k l)=0 := by
    linear_combination S j k*hkerj-S j j*hkerk+r k*hdet
  have hel : S j k*S j l-S j j*S k l=0 := (mul_eq_zero.mp hell).resolve_left (hr l)
  refine ⟨v,?_,?_⟩
  · intro a b hab
    have hl := hab l
    rw [hvl,mul_zero,zero_add] at hl
    have hb : b=0 := (mul_eq_zero.mp hl).resolve_right (hr l)
    have hk := hab k
    rw [hb,zero_mul,add_zero,hvk] at hk
    have ha : a=0 := (mul_eq_zero.mp hk).resolve_right (neg_ne_zero.mpr (ne_of_gt hjj))
    exact ⟨ha,hb⟩
  · intro q
    rw [hsum]
    rcases fin_three_exhaustive hjk hlj hlk q with hq|hq|hq
    · rw [hq,hkj]; ring
    · rw [hq]; nlinarith
    · rw [hq]; exact hel

theorem residue_two_full_kernel_minor_positive {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (r : Fin (3*m+2))
    (hr : M.weight r=0) (hrfull : ∀j,A r j≠0)
    {j k : Fin 3} (hjk : j≠k) :
    0<M.matrix j j*M.matrix k k-(M.matrix j k)^2 := by
  have hs : 0<(m : ℝ)+d := by positivity
  have hj := residue_two_diagonal_positive hA M hd j
  have hb1 := multiplier_entry_bound hA hs M j k
  have hb2 := multiplier_entry_bound hA hs M k j
  rw [M.symmetric k j] at hb2
  have hmul := mul_le_mul hb1 hb2 (abs_nonneg _) hj.le
  have hnonneg : 0≤M.matrix j j*M.matrix k k-(M.matrix j k)^2 := by nlinarith [sq_abs (M.matrix j k)]
  by_contra hn
  have hzero : M.matrix j j*M.matrix k k-(M.matrix j k)^2=0 := le_antisymm (le_of_not_gt hn) hnonneg
  have hker : ∀q,(∑t,A r t*M.matrix t q)=0 := by intro q; simpa [hr] using M.stationarity r q
  obtain ⟨v,hind,hv⟩ := zero_principal_minor_independent_kernel M.symmetric hrfull hker hjk hj hzero
  exact residue_two_independent_kernel_impossible hA M hd
    (residue_two_preliminary_upper (by linarith) hA) hind hv hker

theorem pair_coefficients_positive_of_minor {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (i : Fin n) {j k : Fin 3} (hjk : j≠k)
    (hj : A i j≠0) (hk : A i k≠0) (hz : ∀l,l≠j→l≠k→A i l=0)
    (hminor : 0<M.matrix j j*M.matrix k k-(M.matrix j k)^2) :
    (A i j*A i k<0 → 0<M.matrix j j+M.matrix j k ∧ 0<M.matrix k k+M.matrix j k) ∧
    (0<A i j*A i k → 0<M.matrix j j-M.matrix j k ∧ 0<M.matrix k k-M.matrix j k) := by
  have hb1 := abs_le.mp (multiplier_entry_bound hA hs M j k)
  have hb2 := multiplier_entry_bound hA hs M k j
  rw [M.symmetric k j] at hb2
  have hb2' := abs_le.mp hb2
  have ha := abs_pos.mpr hj
  have hb := abs_pos.mpr hk
  constructor
  · intro hneg
    have hsum : 0<(M.matrix j j+M.matrix j k)+(M.matrix k k+M.matrix j k) := by
      by_contra hn
      have he1 : M.matrix j j= -M.matrix j k := by linarith
      have he2 : M.matrix k k= -M.matrix j k := by linarith
      rw [he1,he2] at hminor
      nlinarith
    exact positive_pair_coefficients (by linarith) (by linarith) hsum ha hb
      (multiplier_negative_pair_stationarity M i hjk hz hneg)
  · intro hpos
    have hsum : 0<(M.matrix j j-M.matrix j k)+(M.matrix k k-M.matrix j k) := by
      by_contra hn
      have he1 : M.matrix j j=M.matrix j k := by linarith
      have he2 : M.matrix k k=M.matrix j k := by linarith
      rw [he1,he2] at hminor
      nlinarith
    exact positive_pair_coefficients (by linarith) (by linarith) hsum ha hb
      (multiplier_positive_pair_stationarity M i hjk hz hpos)

theorem pair_orientation_of_minor {n : ℕ} {s : ℝ}
    {A : Fin n → Fin 3 → ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (i : Fin n) {j k : Fin 3} (hjk : j≠k)
    (hj : A i j≠0) (hk : A i k≠0) (hz : ∀l,l≠j→l≠k→A i l=0)
    (hminor : 0<M.matrix j j*M.matrix k k-(M.matrix j k)^2) :
    (|A i k| < |A i j| ↔ M.matrix j j<M.matrix k k) := by
  have hcoef := pair_coefficients_positive_of_minor hA hs M i hjk hj hk hz hminor
  have ha := abs_pos.mpr hj
  have hb := abs_pos.mpr hk
  rcases lt_or_gt_of_ne (mul_ne_zero hj hk) with hneg|hpos
  · obtain ⟨hp,hq⟩ := hcoef.1 hneg
    simpa only [add_lt_add_iff_right] using positive_pair_orientation hp hq ha hb
      (multiplier_negative_pair_stationarity M i hjk hz hneg)
  · obtain ⟨hp,hq⟩ := hcoef.2 hpos
    simpa only [sub_lt_sub_iff_right] using positive_pair_orientation hp hq ha hb
      (multiplier_positive_pair_stationarity M i hjk hz hpos)

theorem full_positive_pair_product {a : Fin 3 → ℝ} (ha : RowBound a)
    (hp : ∀j,0<a j) {j k : Fin 3} (hjk : j≠k) : 0<a j*a k ∧ a j*a k<1/4 := by
  have he : ∀j k : Fin 3,j≠k→∃l,l≠j∧l≠k := by decide
  obtain ⟨l,hlj,hlk⟩ := he j k hjk
  have hsum : (∑q,a q)≤1 := by
    simpa only [RowBound,Fin.sum_univ_three,abs_of_pos (hp 0),abs_of_pos (hp 1),abs_of_pos (hp 2)] using ha
  rw [fin_three_sum_distinct _ hjk hlj hlk] at hsum
  have htwo : a j+a k<1 := by linarith [hp l]
  exact ⟨mul_pos (hp j) (hp k),by nlinarith [sq_nonneg (a j-a k),hp j,hp k]⟩

/-- A nonzero product strictly between zero and one quarter cannot be cancelled
by rows whose products are integral multiples of one quarter. -/
theorem quarter_product_cancellation_impossible {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (r : ι) (hr : 0<x r ∧ x r<1/4)
    (hother : ∀i,i≠r→x i=0 ∨ x i=1/4 ∨ x i= -1/4)
    (hsum : (∑i,x i)=0) : False := by
  classical
  let T : Finset ι := Finset.univ.erase r
  let P : ℕ := (T.filter (fun i=>0<x i)).card
  let N : ℕ := (T.filter (fun i=>x i<0)).card
  have hrow (i : ι) (hi : i∈T) : 4*x i=
      (if 0<x i then (1 : ℝ) else 0)-(if x i<0 then 1 else 0) := by
    rcases hother i (Finset.mem_erase.mp hi).1 with h|h|h <;> rw [h] <;> norm_num
  have he : 4*(∑i∈T,x i)=(P : ℝ)-(N : ℝ) := by
    rw [Finset.mul_sum]
    calc
      _ = ∑i∈T,((if 0<x i then (1 : ℝ) else 0)-(if x i<0 then 1 else 0)) :=
        Finset.sum_congr rfl (fun i hi=>hrow i hi)
      _ = _ := by rw [Finset.sum_sub_distrib]; simp [P,N,Finset.sum_ite]
  have hex := Finset.sum_erase_add Finset.univ x (Finset.mem_univ r)
  rw [hsum] at hex
  change (∑i∈T,x i)+x r=0 at hex
  have hpn : (P : ℝ)<N := by linarith
  have hnp : (N : ℝ)<(P+1 : ℕ) := by push_cast; linarith
  have hpn' : P<N := by exact_mod_cast hpn
  have hnp' : N<P+1 := by exact_mod_cast hnp
  omega

theorem residue_two_full_kernel_distinct_diagonal {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (hopt : OptimalValue (3*m+2) ((m : ℝ)+d))
    (M : MultiplierSystem A) (hd : 1/5<d) (r : Fin (3*m+2))
    (hr : M.weight r=0) (hrpos : ∀j,0<A r j)
    {j k : Fin 3} (hjk : j≠k) : M.matrix j j≠M.matrix k k := by
  intro hdiag
  have hs : 0<(m : ℝ)+d := by positivity
  have hrest := residue_two_unique_zero hA M hd r hr
  have hn := residue_two_full_kernel_other_not_full hA hopt M hd r hr hrpos
  have hminor := residue_two_full_kernel_minor_positive hA M hd r hr (fun j=>ne_of_gt (hrpos j)) hjk
  have hprod : ∀i,i≠r→A i j*A i k=0 ∨ A i j*A i k=1/4 ∨ A i j*A i k= -1/4 := by
    intro i hir
    by_cases hp0 : A i j*A i k=0
    · exact Or.inl hp0
    have hij := left_ne_zero_of_mul hp0
    have hik := right_ne_zero_of_mul hp0
    have hz := third_zero_of_not_full hjk hij hik (hn i hir)
    have hcoef := pair_coefficients_positive_of_minor hA hs M i hjk hij hik hz hminor
    have heabs : |A i j|=|A i k| := by
      rcases lt_or_gt_of_ne hp0 with hneg|hpos
      · have he := multiplier_negative_pair_stationarity M i hjk hz hneg
        rw [hdiag] at he
        exact mul_left_cancel₀ (ne_of_gt (hcoef.1 hneg).2) he
      · have he := multiplier_positive_pair_stationarity M i hjk hz hpos
        rw [hdiag] at he
        exact mul_left_cancel₀ (ne_of_gt (hcoef.2 hpos).2) he
    have hsum := two_support_sum hjk hz
    rw [Fin.sum_univ_three,M.complementary i (hrest i hir)] at hsum
    have hjhalf : |A i j|=1/2 := by linarith
    have hkhalf : |A i k|=1/2 := by linarith
    have habs : |A i j*A i k|=1/4 := by rw [abs_mul,hjhalf,hkhalf]; norm_num
    right
    rcases le_or_gt 0 (A i j*A i k) with hpos|hneg
    · left; simpa [abs_of_nonneg hpos] using habs
    · right; rw [abs_of_neg hneg] at habs; linarith
  have hg : (∑i,A i j*A i k)=0 := by simpa [hjk] using hA.2 j k
  exact quarter_product_cancellation_impossible (fun i=>A i j*A i k) r
    (full_positive_pair_product (hA.1 r) hrpos hjk) hprod hg

theorem saturated_nonfull_without_large {a : Fin 3 → ℝ}
    (hsat : |a 0|+|a 1|+|a 2|=1) (hn : ∃j,a j=0)
    (hl : ∀j,|a j|≤1/2) :
    ∃j k : Fin 3,j≠k ∧ |a j|=1/2 ∧ |a k|=1/2 ∧ ∀l,l≠j→l≠k→a l=0 := by
  obtain ⟨l,hlzero⟩ := hn
  fin_cases l
  · change a 0=0 at hlzero
    have h1 := hl 1
    have h2 := hl 2
    rw [hlzero,abs_zero,zero_add] at hsat
    refine ⟨1,2,by decide,by linarith,by linarith,?_⟩
    intro q hq1 hq2
    fin_cases q <;> simp_all
  · change a 1=0 at hlzero
    have h0 := hl 0
    have h2 := hl 2
    rw [hlzero,abs_zero,add_zero] at hsat
    refine ⟨0,2,by decide,by linarith,by linarith,?_⟩
    intro q hq0 hq2
    fin_cases q <;> simp_all
  · have h0 := hl 0
    have h1 := hl 1
    have hz : a 2=0 := hlzero
    rw [hz,abs_zero,add_zero] at hsat
    refine ⟨0,1,by decide,by linarith,by linarith,?_⟩
    intro q hq0 hq1
    fin_cases q <;> simp_all

theorem balanced_pair_diagonal_equal {n : ℕ} {A : Fin n → Fin 3 → ℝ}
    (M : MultiplierSystem A) (i : Fin n) {j k : Fin 3} (hjk : j≠k)
    (hj : |A i j|=1/2) (hk : |A i k|=1/2)
    (hz : ∀l,l≠j→l≠k→A i l=0) : M.matrix j j=M.matrix k k := by
  have hij : A i j≠0 := by intro he; simp [he] at hj
  have hik : A i k≠0 := by intro he; simp [he] at hk
  rcases lt_or_gt_of_ne (mul_ne_zero hij hik) with hneg|hpos
  · have he := multiplier_negative_pair_stationarity M i hjk hz hneg
    rw [hj,hk] at he
    linarith
  · have he := multiplier_positive_pair_stationarity M i hjk hz hpos
    rw [hj,hk] at he
    linarith

theorem residue_two_full_kernel_others_large {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (hopt : OptimalValue (3*m+2) ((m : ℝ)+d))
    (M : MultiplierSystem A) (hd : 1/5<d) (r : Fin (3*m+2))
    (hr : M.weight r=0) (hrpos : ∀j,0<A r j) :
    ∀i,i≠r→∃j,1/2 < |A i j| := by
  intro i hir
  by_contra hn
  have hnlarge : ∀j,|A i j|≤1/2 := by simpa using hn
  have hi := residue_two_unique_zero hA M hd r hr i hir
  obtain ⟨j,k,hjk,hj,hk,hz⟩ := saturated_nonfull_without_large (M.complementary i hi)
    (residue_two_full_kernel_other_not_full hA hopt M hd r hr hrpos i hir) hnlarge
  exact residue_two_full_kernel_distinct_diagonal hA hopt M hd r hr hrpos hjk
    (balanced_pair_diagonal_equal M i hjk hj hk hz)

/-- After ordering the multiplier diagonal, all rows other than the exceptional
full kernel row form an actual ordered pair frame. -/
theorem residue_two_full_kernel_ordered_rest {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (hopt : OptimalValue (3*m+2) ((m : ℝ)+d))
    (M : MultiplierSystem A) (hd : 1/5<d) (r : Fin (3*m+2))
    (hr : M.weight r=0) (hrpos : ∀j,0<A r j) :
    ∃ e : Equiv.Perm (Fin 3),
      OrderedPairFrame (fun i : {i : Fin (3*m+2) // i≠r} => permuteColumns A e i.1) := by
  obtain ⟨e,he01,he12⟩ := exists_sorted_columns (fun j=>M.matrix j j)
  let B := permuteColumns A e
  let N := M.permuteColumns e
  have hB : Feasible ((m : ℝ)+d) B := feasible_permuteColumns hA e
  have hNr : N.weight r=0 := hr
  have hBpos (j : Fin 3) : 0<B r j := hrpos (e j)
  have hs : 0<(m : ℝ)+d := by positivity
  have hw := residue_two_unique_zero hB N hd r hNr
  have hn := residue_two_full_kernel_other_not_full hB hopt N hd r hNr hBpos
  have hl := residue_two_full_kernel_others_large hB hopt N hd r hNr hBpos
  refine ⟨e,⟨?_,?_,?_,?_⟩⟩
  · intro i
    exact N.complementary i.1 (hw i.1 i.2)
  · intro i
    exact hl i.1 i.2
  · intro i
    exact hn i.1 i.2
  · intro i j k hjk hj hk
    have hjkne := ne_of_lt hjk
    have hz := third_zero_of_not_full hjkne hj hk (hn i.1 i.2)
    have hminor := residue_two_full_kernel_minor_positive hB N hd r hNr
      (fun q=>ne_of_gt (hBpos q)) hjkne
    have hle : N.matrix j j≤N.matrix k k := by
      fin_cases j <;> fin_cases k <;> norm_num at hjk ⊢
      · exact he01
      · exact he01.trans he12
      · exact he12
    have hne := residue_two_full_kernel_distinct_diagonal hB hopt N hd r hNr hBpos hjkne
    have hlt : N.matrix j j<N.matrix k k := lt_of_le_of_ne hle hne
    exact (pair_orientation_of_minor hB hs N i.1 hjkne hj hk hz hminor).mpr hlt

theorem residue_two_positive_zero_triangle {m : ℕ} {d : ℝ}
    {A : Fin (3*m+2) → Fin 3 → ℝ} (hA : Feasible ((m : ℝ)+d) A)
    (M : MultiplierSystem A) (hd : 1/5<d) (r : Fin (3*m+2))
    (hr : M.weight r=0) (hp : ∀j,0<A r j) :
    A r 0≤A r 1+A r 2 ∧ A r 1≤A r 0+A r 2 ∧ A r 2≤A r 0+A r 1 := by
  have hn := residue_two_zero_row_nondominant hA M hd r hr
  have hc (j : Fin 3) : 2*A r j≤A r 0+A r 1+A r 2 := by
    have hj : |A r j|≤Dominance.minorL1 (A r) j := le_of_not_gt (hn j)
    have he := Dominance.l1_decompose (A r) j
    have hl1 : Dominance.l1 (A r)=A r 0+A r 1+A r 2 := by
      simp only [Dominance.l1,Fin.sum_univ_three,abs_of_pos (hp 0),abs_of_pos (hp 1),abs_of_pos (hp 2)]
    rw [hl1,abs_of_pos (hp j)] at he
    rw [abs_of_pos (hp j)] at hj
    linarith
  exact ⟨by linarith [hc 0],by linarith [hc 1],by linarith [hc 2]⟩

end
end F3
