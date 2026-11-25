import F3.GeneralFrames

/-! Pure coordinate rows and the finite-core stabilization principle. -/
namespace F3.General
noncomputable section
open scoped BigOperators
open F3.Dominance
set_option maxHeartbeats 1000000

def CoordinateAt {k : ℕ} (a : Fin k → ℝ) (j : Fin k) : Prop :=
  |a j|=1 ∧ ∀ l,l≠j → a l=0

def SignedCoordinate {k : ℕ} (a : Fin k → ℝ) : Prop := ∃j,CoordinateAt a j

def coordinateRows {ι : Type*} [Fintype ι] {k : ℕ}
    (A : ι → Fin k → ℝ) (j : Fin k) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => CoordinateAt (A i) j)

def noncoordinateCount {ι : Type*} [Fintype ι] {k : ℕ}
    (A : ι → Fin k → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => ¬SignedCoordinate (A i))).card

theorem CoordinateAt.unique {k : ℕ} {a : Fin k → ℝ} {j l : Fin k}
    (hj : CoordinateAt a j) (hl : CoordinateAt a l) : j=l := by
  by_contra h
  have hz := hl.2 j h
  have he := hj.1
  rw [hz,abs_zero] at he
  norm_num at he

theorem CoordinateAt.product {k : ℕ} {a : Fin k → ℝ} {j : Fin k}
    (h : CoordinateAt a j) (p q : Fin k) :
    a p*a q=if p=j ∧ q=j then 1 else 0 := by
  by_cases hp : p=j
  · subst p
    by_cases hq : q=j
    · subst q
      simp only [and_self,ite_true]
      nlinarith [sq_abs (a j),h.1]
    · simp [hq,h.2 q hq]
  · simp [hp,h.2 p hp]

theorem coordinate_count_partition {ι : Type*} [Fintype ι] {k : ℕ}
    (A : ι → Fin k → ℝ) :
    (∑j,(coordinateRows A j).card)+noncoordinateCount A=Fintype.card ι := by
  classical
  have hrow (i : ι) : (∑j : Fin k,if CoordinateAt (A i) j then (1:ℕ) else 0)=
      if SignedCoordinate (A i) then 1 else 0 := by
    by_cases hs : SignedCoordinate (A i)
    · obtain ⟨j,hj⟩ := hs
      have he (l : Fin k) : CoordinateAt (A i) l ↔ l=j :=
        ⟨fun hl => hl.unique hj,fun h => by simpa [h] using hj⟩
      simp [he,SignedCoordinate]
    · have hn (j : Fin k) : ¬CoordinateAt (A i) j := fun h => hs ⟨j,h⟩
      simp [hn,hs]
  simp only [coordinateRows,noncoordinateCount,Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [hrow]
  rw [←Finset.sum_add_distrib]
  have he (i : ι) : (if SignedCoordinate (A i) then (1:ℕ) else 0)+
      (if ¬SignedCoordinate (A i) then 1 else 0)=1 := by
    by_cases h : SignedCoordinate (A i) <;> simp [h]
  simp only [he,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]

theorem coordinate_column_energy {ι : Type*} [Fintype ι] {k : ℕ}
    (A : ι → Fin k → ℝ) (j : Fin k) :
    (∑i∈coordinateRows A j,(A i j)^2)=((coordinateRows A j).card:ℝ) := by
  classical
  have he (i : ι) (hi : i∈coordinateRows A j) : (A i j)^2=1 := by
    have hp := (Finset.mem_filter.mp hi).2
    nlinarith [sq_abs (A i j),hp.1]
  rw [Finset.sum_congr rfl he]
  simp

theorem coordinate_count_le_level {n k : ℕ} {s : ℝ}
    {A : Fin n → Fin k → ℝ} (hA : FeasibleK n k s A) (j : Fin k) :
    ((coordinateRows A j).card:ℝ)≤s := by
  rw [←coordinate_column_energy A j]
  calc
    _ ≤ ∑i,(A i j)^2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
    _ = _ := by simpa [pow_two] using hA.2 j j

theorem coordinate_count_le_integer {n k m : ℕ} {c : ℝ}
    {A : Fin n → Fin k → ℝ} (hA : FeasibleK n k ((m:ℝ)+c) A)
    (hc : c<1) (j : Fin k) : (coordinateRows A j).card≤m := by
  have h : ((coordinateRows A j).card:ℝ)<(m:ℝ)+1 :=
    lt_of_le_of_lt (coordinate_count_le_level hA j) (by linarith)
  have hnat : (coordinateRows A j).card<m+1 := by exact_mod_cast h
  omega

theorem coordinate_count_lower {k m r C : ℕ} (hk : 0<k) {c : ℝ}
    {A : Fin (k*m+r) → Fin k → ℝ}
    (hA : FeasibleK (k*m+r) k ((m:ℝ)+c) A) (hc : c<1)
    (hcore : noncoordinateCount A≤C) (j : Fin k) :
    m-C≤(coordinateRows A j).card := by
  classical
  have hle (l : Fin k) := coordinate_count_le_integer hA hc l
  have hrest := Finset.sum_le_sum (s:=Finset.univ.erase j)
    (f:=fun l => (coordinateRows A l).card) (g:=fun _ => m) (fun l _ => hle l)
  have hcounte := Finset.sum_erase_add Finset.univ (fun l => (coordinateRows A l).card)
    (Finset.mem_univ j)
  have htotal := coordinate_count_partition A
  simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hrest
  simp only [Fintype.card_fin] at htotal
  change (∑l∈Finset.univ.erase j,(coordinateRows A l).card)≤(k-1)*m at hrest
  change (∑l∈Finset.univ.erase j,(coordinateRows A l).card)+(coordinateRows A j).card=
    ∑l,(coordinateRows A l).card at hcounte
  have hkm : k*m=(k-1)*m+m := by
    calc
      k*m=(k-1+1)*m := by congr 1; omega
      _ = _ := by ring
  omega

/-- Remove t disjoint signed coordinate rows in each column. -/
theorem strip_coordinate_blocks {n k t : ℕ} {s : ℝ}
    {A : Fin n → Fin k → ℝ} (hA : FeasibleK n k s A)
    (ht : ∀j,t≤(coordinateRows A j).card) :
    ∃ N : ℕ, ∃ B : Fin N → Fin k → ℝ,
      FeasibleK N k (s-t) B ∧ N+k*t=n := by
  classical
  have hchoose (j : Fin k) : ∃ Q : Finset (Fin n), Q⊆coordinateRows A j ∧ Q.card=t :=
    Finset.exists_subset_card_eq (ht j)
  choose Q hQsub hQcard using hchoose
  have hdis : (Finset.univ : Finset (Fin k)).toSet.PairwiseDisjoint Q := by
    intro j _ l _ hjl
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hp := (Finset.mem_filter.mp (hQsub j hi)).2
    have hq := (Finset.mem_filter.mp (hQsub l hj)).2
    exact hjl (hp.unique hq)
  let D := Finset.univ.biUnion Q
  let R := Finset.univ\D
  have hD : D.card=k*t := by
    dsimp [D]
    rw [Finset.card_biUnion hdis]
    simp [hQcard]
  have hR : R.card+k*t=n := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
    simpa only [Finset.card_univ,Fintype.card_fin,hD] using h
  have hremoved (j l : Fin k) :
      (∑i∈D,A i j*A i l)=if j=l then (t:ℝ) else 0 := by
    dsimp [D]
    rw [Finset.sum_biUnion hdis]
    have hinner (a : Fin k) : (∑i∈Q a,A i j*A i l)=
        if j=a ∧ l=a then (t:ℝ) else 0 := by
      calc
        _ = ∑i∈Q a,if j=a ∧ l=a then (1:ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact ((Finset.mem_filter.mp (hQsub a hi)).2).product j l
        _ = _ := by simp [hQcard]
    simp_rw [hinner]
    by_cases hjl : j=l
    · subst l; simp
    · have hn (a : Fin k) : ¬(j=a ∧ l=a) := by
        rintro ⟨rfl,rfl⟩; exact hjl rfl
      simp [hn,hjl]
  have hrest : F3.FiniteFeasible k (s-t) (fun i : R => A i) := by
    constructor
    · intro i; exact hA.1 i
    · intro j l
      have hsum : (∑i : R,A i j*A i l)+(∑i∈D,A i j*A i l)=
          ∑i,A i j*A i l := by
        rw [show (∑i : R,A i j*A i l)=∑i∈R,A i j*A i l from
          Finset.sum_attach R (fun i => A i j*A i l)]
        exact Finset.sum_sdiff (Finset.subset_univ D)
      rw [hremoved,hA.2] at hsum
      by_cases h : j=l <;> simp only [h,ite_true,ite_false] at hsum ⊢ <;> linarith
  obtain ⟨B,hB⟩ := F3.finiteFeasible_pad hrest
    (show Fintype.card R≤R.card by simp)
  exact ⟨R.card,B,hB,hR⟩

end
end F3.General
