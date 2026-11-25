import F3.MatrixCurves
import Mathlib.Topology.Order.Compact

/-! Compactness of the actual normalized multiplier triples, including the
subgradients attached to zero row weights. -/

namespace F3
noncomputable section
open scoped BigOperators

abbrev MultiplierTuple (ι : Type*) :=
  (ι → ℝ) × (ι → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ)

def IsMultiplierTuple {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) (p : MultiplierTuple ι) : Prop :=
  (∀ i, 0 ≤ p.1 i) ∧
  (∑ i, p.1 i) = 1 ∧
  (∀ i j, |p.2.1 i j| ≤ 1) ∧
  (∀ i j, A i j * p.2.1 i j = |A i j|) ∧
  (∀ j k, p.2.2 j k = p.2.2 k j) ∧
  (∀ i j, (∑ k, A i k * p.2.2 k j) = p.1 i * p.2.1 i j) ∧
  ∀ i, p.1 i * (|A i 0| + |A i 1| + |A i 2| - 1) = 0

def multiplierTuple {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ}
    (M : MultiplierSystem A) : MultiplierTuple ι :=
  (M.weight,M.gradient,M.matrix)

theorem multiplierTuple_spec {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A) :
    IsMultiplierTuple A (multiplierTuple M) := by
  refine ⟨M.weight_nonneg,M.weight_sum,fun i => (M.subgradient i).1,
    fun i => (M.subgradient i).2,M.symmetric,M.stationarity,?_⟩
  intro i
  by_cases hi : M.weight i=0
  · simp [multiplierTuple,hi]
  · have hp : 0<M.weight i := lt_of_le_of_ne (M.weight_nonneg i) (Ne.symm hi)
    simp only [multiplierTuple,M.complementary i hp,sub_self,mul_zero]

def systemOfMultiplierTuple {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {p : MultiplierTuple ι} (hp : IsMultiplierTuple A p) :
    MultiplierSystem A where
  weight := p.1
  gradient := p.2.1
  matrix := p.2.2
  weight_nonneg := hp.1
  weight_sum := hp.2.1
  subgradient := fun i => ⟨hp.2.2.1 i,hp.2.2.2.1 i⟩
  symmetric := hp.2.2.2.2.1
  stationarity := hp.2.2.2.2.2.1
  complementary := by
    intro i hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp (hp.2.2.2.2.2.2 i)).resolve_left hi.ne')

theorem isMultiplierTuple_iff_exists_system {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {p : MultiplierTuple ι} :
    IsMultiplierTuple A p ↔ ∃ M : MultiplierSystem A, multiplierTuple M=p := by
  constructor
  · intro hp
    exact ⟨systemOfMultiplierTuple hp,rfl⟩
  · rintro ⟨M,rfl⟩
    exact multiplierTuple_spec M

theorem isClosed_multiplierTuples {ι : Type*} [Fintype ι]
    (A : ι → Fin 3 → ℝ) : IsClosed {p : MultiplierTuple ι | IsMultiplierTuple A p} := by
  have cw (i : ι) : Continuous (fun p : MultiplierTuple ι => p.1 i) :=
    (continuous_apply i).comp continuous_fst
  have cg (i : ι) (j : Fin 3) : Continuous (fun p : MultiplierTuple ι => p.2.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp continuous_snd))
  have cs (j k : Fin 3) : Continuous (fun p : MultiplierTuple ι => p.2.2 j k) :=
    (continuous_apply k).comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd))
  simp only [IsMultiplierTuple,Set.setOf_and,Set.setOf_forall]
  refine (isClosed_iInter (fun i => isClosed_le continuous_const (cw i))).inter ?_
  refine (isClosed_eq (continuous_finset_sum _ (fun i _ => cw i)) continuous_const).inter ?_
  refine (isClosed_iInter (fun i => isClosed_iInter (fun j =>
    isClosed_le (cg i j).abs continuous_const))).inter ?_
  refine (isClosed_iInter (fun i => isClosed_iInter (fun j =>
    isClosed_eq (continuous_const.mul (cg i j)) continuous_const))).inter ?_
  refine (isClosed_iInter (fun j => isClosed_iInter (fun k =>
    isClosed_eq (cs j k) (cs k j)))).inter ?_
  refine (isClosed_iInter (fun i => isClosed_iInter (fun j =>
    isClosed_eq (continuous_finset_sum _ (fun k _ => continuous_const.mul (cs k j)))
      ((cw i).mul (cg i j))))).inter ?_
  exact isClosed_iInter (fun i => isClosed_eq ((cw i).mul continuous_const) continuous_const)

theorem multiplier_weight_le_one {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} (M : MultiplierSystem A) (i : ι) : M.weight i≤1 := by
  classical
  calc
    M.weight i ≤ ∑ k, M.weight k :=
      Finset.single_le_sum (fun k _ => M.weight_nonneg k) (Finset.mem_univ i)
    _ = 1 := M.weight_sum

theorem multiplier_entry_abs_le_inv_level {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s)
    (M : MultiplierSystem A) (j k : Fin 3) : |M.matrix j k| ≤ 1/s := by
  classical
  have htrace : (∑ l, M.matrix l l)=1/s := by
    apply (eq_div_iff hs.ne').2
    simpa only [Fin.sum_univ_three,mul_comm] using multiplier_trace_identity hA M
  calc
    |M.matrix j k| ≤ M.matrix j j := multiplier_entry_bound hA hs M j k
    _ ≤ ∑ l, M.matrix l l :=
      Finset.single_le_sum (fun l _ => multiplier_diagonal_nonneg hA hs M l)
        (Finset.mem_univ j)
    _ = 1/s := htrace

theorem isCompact_multiplierTuples {ι : Type*} [Fintype ι]
    {A : ι → Fin 3 → ℝ} {s : ℝ} (hA : Feasible s A) (hs : 0<s) :
    IsCompact {p : MultiplierTuple ι | IsMultiplierTuple A p} := by
  let weights : Set (ι → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)
  let gradients : Set (ι → Fin 3 → ℝ) :=
    Set.univ.pi (fun _ => Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1))
  let matrices : Set (Fin 3 → Fin 3 → ℝ) :=
    Set.univ.pi (fun _ => Set.univ.pi (fun _ => Set.Icc (-(1/s)) (1/s)))
  have hw : IsCompact weights := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hg : IsCompact gradients :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hm : IsCompact matrices :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  apply (hw.prod (hg.prod hm)).of_isClosed_subset (isClosed_multiplierTuples A)
  intro p hp
  let M := systemOfMultiplierTuple hp
  change p.1 ∈ weights ∧ p.2.1 ∈ gradients ∧ p.2.2 ∈ matrices
  simp only [weights,gradients,matrices,Set.mem_univ_pi,Set.mem_Icc]
  refine ⟨fun i => ⟨hp.1 i,multiplier_weight_le_one M i⟩,
    fun i j => abs_le.mp ((M.subgradient i).1 j),?_⟩
  intro j k
  exact abs_le.mp (multiplier_entry_abs_le_inv_level hA hs M j k)

theorem multiplierTuples_nonempty_at_optimum {n : ℕ}
    {A : Fin n → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (hopt : OptimalValue n s) :
    ({p : MultiplierTuple (Fin n) | IsMultiplierTuple A p}).Nonempty := by
  obtain ⟨M⟩ := exists_multiplier_at_optimum hA hs hopt
  exact ⟨multiplierTuple M,multiplierTuple_spec M⟩

end
end F3
