import F3.GeneralCores

namespace F3.General
noncomputable section
open scoped BigOperators
open F3.Dominance
set_option maxHeartbeats 1000000

def BoundedOptimalCores (k : ℕ) : Prop :=
  ∃ C N : ℕ, ∀ n, N≤n → ∃ A : Fin n → Fin k → ℝ,
    FeasibleK n k (value k n) A ∧ noncoordinateCount A≤C

def ResidueStabilization (k : ℕ) : Prop :=
  ∀r : ℕ,r<k → ∃M : ℕ,∀m,M≤m → correction k r m=correction k r M

theorem correction_lt_one {k r m : ℕ} (hk : 0<k) (hr : r<k) :
    correction k r m<1 := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hrr : (r:ℝ)<k := by exact_mod_cast hr
  exact lt_of_le_of_lt (correction_upper hk r m) ((div_lt_one hkr).mpr hrr)

/-- Bounded residual cores force exact stabilization.  Removing a common
number of pure coordinate blocks avoids enumerating continuous core types. -/
theorem boundedCores_implies_stabilization {k : ℕ} (hk : 0<k)
    (hcore : BoundedOptimalCores k) : ResidueStabilization k := by
  obtain ⟨C,N,hcore⟩ := hcore
  intro r hr
  let M := max C N
  refine ⟨M,?_⟩
  intro m hm
  have hCM : C≤M := le_max_left _ _
  have hNM : N≤M := le_max_right _ _
  have hmN : N≤k*m+r := by
    have hkm : m≤k*m := Nat.le_mul_of_pos_left m hk
    omega
  obtain ⟨A,hA,hcA⟩ := hcore (k*m+r) hmN
  let c := correction k r m
  have hc : c<1 := correction_lt_one hk hr
  have hAval : FeasibleK (k*m+r) k ((m:ℝ)+c) A := by
    simpa only [c,correction,add_sub_cancel] using hA
  have hcounts (j : Fin k) : m-M≤(coordinateRows A j).card :=
    (Nat.sub_le_sub_left hCM m).trans (coordinate_count_lower hk hAval hc hcA j)
  obtain ⟨N',B,hB,hN'⟩ := strip_coordinate_blocks hA hcounts
  have hdim : N'=k*M+r := by
    have hsplit : m=(m-M)+M := (Nat.sub_add_cancel hm).symm
    have hkm : k*m=k*(m-M)+k*M := by
      calc
        k*m=k*((m-M)+M) := congrArg (fun t => k*t) hsplit
        _ = _ := by ring
    omega
  have hlevel : value k (k*m+r)-(m-M:ℕ)=(M:ℝ)+c := by
    rw [Nat.cast_sub hm]
    dsimp [c,correction]
    ring
  have hfeas : FeasibleValue k (k*M+r) ((M:ℝ)+c) := by
    subst N'
    exact ⟨B,by rwa [hlevel] at hB⟩
  have hu := feasible_le_value hk hfeas
  have hle : correction k r m≤correction k r M := by
    dsimp [c,correction] at hu ⊢
    linarith
  exact le_antisymm hle (correction_monotone hk r hm)

theorem coordinateRow_signed {k : ℕ} (i : Fin k) : SignedCoordinate (coordinateRow i) := by
  classical
  refine ⟨i,?_,?_⟩
  · simp [coordinateRow]
  · intro j hj
    simp [coordinateRow,hj.symm]

theorem noncoordinateCount_le {n k : ℕ} (A : Fin n → Fin k → ℝ) :
    noncoordinateCount A≤n := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem appendRows_noncoordinateCount {n k : ℕ} (A : Fin n → Fin k → ℝ) :
    noncoordinateCount (appendRows A)=noncoordinateCount A := by
  classical
  simp only [noncoordinateCount,Finset.card_filter]
  rw [show (∑i : Fin (n+k),if ¬SignedCoordinate (appendRows A i) then (1:ℕ) else 0)=
      ∑i : Fin n ⊕ Fin k,if ¬SignedCoordinate (Sum.elim A coordinateRow i) then (1:ℕ) else 0
    from Equiv.sum_comp finSumFinEquiv.symm
      (fun i : Fin n ⊕ Fin k => if ¬SignedCoordinate (Sum.elim A coordinateRow i) then 1 else 0)]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,coordinateRow_signed,not_true_eq_false,
    ite_false,Finset.sum_const_zero,add_zero]

def FeasibleWithCore (k n : ℕ) (s : ℝ) (C : ℕ) : Prop :=
  ∃ A : Fin n → Fin k → ℝ,FeasibleK n k s A ∧ noncoordinateCount A≤C

theorem stack_with_core {n k C : ℕ} {s : ℝ} (h : FeasibleWithCore k n s C) :
    FeasibleWithCore k (n+k) (s+1) C := by
  obtain ⟨A,hA,hc⟩ := h
  exact ⟨appendRows A,appendRows_feasible hA,by rwa [appendRows_noncoordinateCount]⟩

theorem iterate_stack_with_core {n k C : ℕ} {s : ℝ}
    (h : FeasibleWithCore k n s C) (t : ℕ) :
    FeasibleWithCore k (n+k*t) (s+t) C := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.cast_add,Nat.cast_one,add_assoc] using stack_with_core ih

theorem stabilization_implies_boundedCores {k : ℕ} (hk : 0<k)
    (hstab : ResidueStabilization k) : BoundedOptimalCores k := by
  classical
  have hex (r : Fin k) : ∃ M : ℕ,∀m,M≤m → correction k r m=correction k r M :=
    hstab r r.isLt
  choose base hbase using hex
  let M : ℕ := ∑r,base r
  have hbaseM (r : Fin k) : base r≤M :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  refine ⟨k*M+k,k*M,?_⟩
  intro n hn
  let m := n/k
  let r : Fin k := ⟨n%k,Nat.mod_lt n hk⟩
  have hMm : M≤m := (Nat.le_div_iff_mul_le hk).mpr (by simpa [mul_comm] using hn)
  have hbm : base r≤m := (hbaseM r).trans hMm
  obtain ⟨A,hA⟩ := value_attained hk (k*base r+r)
  have hcA : noncoordinateCount A≤k*M+k := by
    apply (noncoordinateCount_le A).trans
    have hb := Nat.mul_le_mul_left k (hbaseM r)
    omega
  have hstart : FeasibleWithCore k (k*base r+r) (value k (k*base r+r)) (k*M+k) :=
    ⟨A,hA,hcA⟩
  have h := iterate_stack_with_core hstart (m-base r)
  have hdim : k*base r+r+k*(m-base r)=n := by
    have hsplit : base r+(m-base r)=m := Nat.add_sub_of_le hbm
    have hmul := congrArg (fun t => k*t) hsplit
    have hn' : k*m+r=n := by
      simpa [m,r,mul_comm,add_comm] using Nat.mod_add_div n k
    nlinarith
  have hvalue : value k (k*base r+r)+(m-base r:ℕ)=value k n := by
    have hs := hbase r m hbm
    have hn' : k*m+r=n := by
      simpa [m,r,mul_comm,add_comm] using Nat.mod_add_div n k
    dsimp [correction] at hs
    rw [hn'] at hs
    rw [Nat.cast_sub hbm]
    linarith
  rw [hdim,hvalue] at h
  exact h

theorem finite_core_iff_stabilization {k : ℕ} (hk : 2≤k) :
    BoundedOptimalCores k ↔ ResidueStabilization k :=
  ⟨boundedCores_implies_stabilization (by omega),
   stabilization_implies_boundedCores (by omega)⟩

end
end F3.General
