import F3.FiniteRowPadding
import F3.Attainment
import Mathlib.Topology.Order.MonotoneConvergence

/-! The genuine finite-frame supremum in arbitrary positive inner dimension. -/
namespace F3.General
noncomputable section
open scoped BigOperators Topology
open F3.Dominance Filter

def FeasibleValue (k n : ℕ) (s : ℝ) : Prop :=
  ∃ A : Fin n → Fin k → ℝ, FeasibleK n k s A

def value (k n : ℕ) : ℝ := sSup {s | FeasibleValue k n s}

theorem zero_feasible (k n : ℕ) : FeasibleValue k n 0 :=
  ⟨fun _ _ => 0,by simp [FeasibleK]⟩

theorem row_energy_bound {k : ℕ} {a : Fin k → ℝ}
    (ha : (∑j,|a j|)≤1) : (∑j,(a j)^2)≤1 := by
  have he := Finset.sum_sq_le_sq_sum_of_nonneg
    (s:=Finset.univ) (f:=fun j => |a j|) (fun j _ => abs_nonneg _)
  simp only [sq_abs] at he
  have hn : 0≤∑j,|a j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  nlinarith

theorem trace_bound {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) : (k:ℝ)*s≤n := by
  have h := Finset.sum_le_sum (s:=Finset.univ)
    (f:=fun i => en (A i)) (g:=fun _ => (1:ℝ))
    (fun i _ => row_energy_bound (hA.1 i))
  rw [Dominance.trace_identity hA] at h
  simpa using h

theorem feasible_nonneg {n k : ℕ} (hk : 0<k) {s : ℝ}
    {A : Fin n → Fin k → ℝ} (hA : FeasibleK n k s A) : 0≤s := by
  let j : Fin k := ⟨0,hk⟩
  have h := hA.2 j j
  simp only [ite_true] at h
  rw [←h]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

theorem values_bdd {k : ℕ} (hk : 0<k) (n : ℕ) :
    BddAbove {s | FeasibleValue k n s} := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  refine ⟨(n:ℝ)/k,?_⟩
  rintro s ⟨A,hA⟩
  exact (le_div_iff₀ hkr).mpr (by simpa only [mul_comm] using trace_bound hA)

theorem feasible_le_value {k n : ℕ} (hk : 0<k) {s : ℝ}
    (hs : FeasibleValue k n s) : s≤value k n := le_csSup (values_bdd hk n) hs

theorem value_nonneg {k : ℕ} (hk : 0<k) (n : ℕ) : 0≤value k n :=
  feasible_le_value hk (zero_feasible k n)

theorem value_trace_bound {k : ℕ} (hk : 0<k) (n : ℕ) :
    value k n≤(n:ℝ)/k := by
  apply csSup_le ⟨0,zero_feasible k n⟩
  rintro s ⟨A,hA⟩
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  exact (le_div_iff₀ hkr).mpr (by simpa only [mul_comm] using trace_bound hA)

def gram {n k : ℕ} (A : Fin n → Fin k → ℝ) (j l : Fin k) :=
  ∑i,A i j*A i l

def level {n k : ℕ} (hk : 0<k) (A : Fin n → Fin k → ℝ) :=
  gram A ⟨0,hk⟩ ⟨0,hk⟩

theorem continuous_gram (n k : ℕ) (j l : Fin k) :
    Continuous (fun A : Fin n → Fin k → ℝ => gram A j l) := by
  apply continuous_finset_sum
  intro i _
  exact ((continuous_apply j).comp (continuous_apply i)).mul
    ((continuous_apply l).comp (continuous_apply i))

theorem compact_feasible (n : ℕ) {k : ℕ} (hk : 0<k) :
    IsCompact {A : Fin n → Fin k → ℝ | FeasibleK n k (level hk A) A} := by
  have hclosed : IsClosed {A : Fin n → Fin k → ℝ | FeasibleK n k (level hk A) A} := by
    change IsClosed ({A : Fin n → Fin k → ℝ | ∀i,(∑j,|A i j|)≤1} ∩
      {A : Fin n → Fin k → ℝ | ∀j l,gram A j l=if j=l then level hk A else 0})
    apply IsClosed.inter
    · rw [Set.setOf_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_le _ continuous_const
      apply continuous_finset_sum
      intro j _
      exact ((continuous_apply j).comp (continuous_apply i)).abs
    · rw [Set.setOf_forall]
      apply isClosed_iInter
      intro j
      rw [Set.setOf_forall]
      apply isClosed_iInter
      intro l
      apply isClosed_eq (continuous_gram n k j l)
      by_cases h : j=l
      · simpa [h,level] using continuous_gram n k ⟨0,hk⟩ ⟨0,hk⟩
      · simp only [h,if_false]; exact continuous_const
  have hbox : IsCompact (Set.univ.pi (fun _ : Fin n =>
      Set.univ.pi (fun _ : Fin k => Set.Icc (-1:ℝ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  apply hbox.of_isClosed_subset hclosed
  intro A hA
  simp only [Set.mem_univ_pi]
  intro i j
  have he : |A i j|≤1 := (Finset.single_le_sum
    (fun j _ => abs_nonneg (A i j)) (Finset.mem_univ j)).trans (hA.1 i)
  exact abs_le.mp he

theorem value_attained {k : ℕ} (hk : 0<k) (n : ℕ) :
    FeasibleValue k n (value k n) := by
  have hne : ({A : Fin n → Fin k → ℝ | FeasibleK n k (level hk A) A}).Nonempty := by
    exact ⟨fun _ _ => 0,by simp [FeasibleK,level,gram]⟩
  obtain ⟨A,hA,hmax⟩ := (compact_feasible n hk).exists_isMaxOn hne
    (continuous_gram n k ⟨0,hk⟩ ⟨0,hk⟩).continuousOn
  have he : value k n=level hk A := by
    apply le_antisymm
    · apply csSup_le ⟨0,zero_feasible k n⟩
      rintro s ⟨B,hB⟩
      have hlevel : level hk B=s := by
        simpa [level,gram] using hB.2 ⟨0,hk⟩ ⟨0,hk⟩
      have hmem : FeasibleK n k (level hk B) B := by rwa [hlevel]
      have hh := hmax hmem
      change level hk B≤level hk A at hh
      rwa [hlevel] at hh
    · exact feasible_le_value hk ⟨A,hA⟩
  exact ⟨A,by rwa [he]⟩

def coordinateRow {k : ℕ} (i j : Fin k) : ℝ := if i=j then 1 else 0

theorem coordinateRow_budget {k : ℕ} (i : Fin k) :
    (∑j,|coordinateRow i j|)≤1 := by
  classical
  simp [coordinateRow,abs_ite]

theorem coordinateRow_gram {k : ℕ} (j l : Fin k) :
    (∑i,coordinateRow i j*coordinateRow i l)=if j=l then (1:ℝ) else 0 := by
  classical
  simp [coordinateRow,eq_comm]

def appendRows {n k : ℕ} (A : Fin n → Fin k → ℝ) : Fin (n+k) → Fin k → ℝ :=
  fun i => Sum.elim A coordinateRow (finSumFinEquiv.symm i)

theorem appendRows_feasible {n k : ℕ} {s : ℝ} {A : Fin n → Fin k → ℝ}
    (hA : FeasibleK n k s A) : FeasibleK (n+k) k (s+1) (appendRows A) := by
  constructor
  · intro i
    cases hi : finSumFinEquiv.symm i with
    | inl a => simpa [appendRows,hi] using hA.1 a
    | inr b => simpa [appendRows,hi] using coordinateRow_budget b
  · intro j l
    rw [show (∑i,appendRows A i j*appendRows A i l)=
        ∑i : Fin n ⊕ Fin k, (Sum.elim A coordinateRow i j)*(Sum.elim A coordinateRow i l)
      from Equiv.sum_comp finSumFinEquiv.symm
        (fun i : Fin n ⊕ Fin k => Sum.elim A coordinateRow i j*Sum.elim A coordinateRow i l)]
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl,Sum.elim_inr,hA.2,coordinateRow_gram]
    by_cases h : j=l <;> simp [h]

theorem stacking_feasible {k n : ℕ} {s : ℝ} (h : FeasibleValue k n s) :
    FeasibleValue k (n+k) (s+1) := by
  obtain ⟨A,hA⟩ := h
  exact ⟨appendRows A,appendRows_feasible hA⟩

theorem value_stacking {k : ℕ} (hk : 0<k) (n : ℕ) :
    value k n+1≤value k (n+k) :=
  feasible_le_value hk (stacking_feasible (value_attained hk n))

theorem value_mono {k : ℕ} (hk : 0<k) {n N : ℕ} (hn : n≤N) :
    value k n≤value k N := by
  obtain ⟨A,hA⟩ := value_attained hk n
  obtain ⟨B,hB⟩ := F3.finiteFeasible_pad (show F3.FiniteFeasible k (value k n) A from hA)
    (by simpa using hn)
  exact feasible_le_value hk ⟨B,hB⟩

theorem divisible_feasible (k m : ℕ) : FeasibleValue k (k*m) m := by
  induction m with
  | zero => simpa using zero_feasible k 0
  | succ m ih =>
    have h := stacking_feasible ih
    simpa [Nat.mul_succ,Nat.cast_add,Nat.cast_one] using h

theorem value_divisible {k : ℕ} (hk : 0<k) (m : ℕ) : value k (k*m)=m := by
  apply le_antisymm
  · have h := value_trace_bound hk (k*m)
    have hkr : (k:ℝ)≠0 := by exact_mod_cast (ne_of_gt hk)
    simpa [Nat.cast_mul,mul_div_cancel_left₀ _ hkr] using h
  · exact feasible_le_value hk (divisible_feasible k m)

def correction (k r m : ℕ) : ℝ := value k (k*m+r)-m

theorem correction_nonneg {k : ℕ} (hk : 0<k) (r m : ℕ) :
    0≤correction k r m := by
  have h := value_mono hk (show k*m≤k*m+r by omega)
  rw [value_divisible hk] at h
  exact sub_nonneg.mpr h

theorem correction_upper {k : ℕ} (hk : 0<k) (r m : ℕ) :
    correction k r m≤(r:ℝ)/k := by
  have h := value_trace_bound hk (k*m+r)
  have hkr : (k:ℝ)≠0 := by exact_mod_cast (ne_of_gt hk)
  have he : ((k*m+r:ℕ):ℝ)/k=(m:ℝ)+(r:ℝ)/k := by
    push_cast
    field_simp
    ring
  rw [he] at h
  dsimp [correction]
  linarith

theorem correction_monotone {k : ℕ} (hk : 0<k) (r : ℕ) :
    Monotone (correction k r) := by
  apply monotone_nat_of_le_succ
  intro m
  have h := value_stacking hk (k*m+r)
  have he : k*(m+1)+r=k*m+r+k := by ring
  dsimp [correction]
  rw [he]
  push_cast
  linarith

theorem correction_converges {k : ℕ} (hk : 0<k) (r : ℕ) :
    Tendsto (correction k r) atTop (𝓝 (⨆m,correction k r m)) := by
  apply tendsto_atTop_ciSup (correction_monotone hk r)
  exact ⟨(r:ℝ)/k,by rintro _ ⟨m,rfl⟩; exact correction_upper hk r m⟩

theorem value_three_eq_frameValue (n : ℕ) : value 3 n=F3.frameValue n := by
  apply congrArg sSup
  ext s
  exact exists_congr (fun A => feasibleK_three_iff)

end
end F3.General
