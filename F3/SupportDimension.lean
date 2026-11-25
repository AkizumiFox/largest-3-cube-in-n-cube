import F3.FullRowClassification
import F3.OptimizationBridge
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Dimension counting for directions confined to the current row faces. -/
namespace F3
noncomputable section
open scoped BigOperators
open Module
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι]

def SupportSlot (A : ι → Fin 3 → ℝ) := Σ i, {j : Fin 3 // A i j ≠ 0}

noncomputable instance (A : ι → Fin 3 → ℝ) : Fintype (SupportSlot A) := by
  classical
  unfold SupportSlot
  infer_instance

def supportLift (A : ι → Fin 3 → ℝ) :
    (SupportSlot A → ℝ) →ₗ[ℝ] (ι → Fin 3 → ℝ) := by
  classical
  exact {
    toFun := fun x i j => if h : A i j≠0 then x ⟨i,⟨j,h⟩⟩ else 0
    map_add' := by
      intros
      ext i j
      dsimp
      split_ifs <;> simp
    map_smul' := by
      intros
      ext i j
      dsimp
      split_ifs <;> simp }

theorem supportLift_zero_entry (A : ι → Fin 3 → ℝ) (x : SupportSlot A → ℝ)
    (i : ι) (j : Fin 3) (h : A i j=0) : supportLift A x i j=0 := by
  simp [supportLift,h]

theorem supportLift_injective (A : ι → Fin 3 → ℝ) :
    Function.Injective (supportLift A) := by
  intro x y h
  funext p
  obtain ⟨i,j,hj⟩ := p
  have hh := congrFun (congrFun h i) j
  simpa [supportLift,hj] using hh

def rowFaceMap (A : ι → Fin 3 → ℝ) :
    (SupportSlot A → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x i := facetValue (supportLift A x i) (canonicalFacet (A i))
  map_add' x y := by
    ext i
    simp [facetValue,map_add,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' r x := by
    ext i
    simp [facetValue,map_smul,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]

theorem rowFaceMap_surjective (A : ι → Fin 3 → ℝ)
    (hsat : ∀ i, |A i 0|+|A i 1|+|A i 2|=1) :
    Function.Surjective (rowFaceMap A) := by
  intro y
  let x : SupportSlot A → ℝ := fun p => y p.1*A p.1 p.2.1
  refine ⟨x,?_⟩
  ext i
  have hl : supportLift A x i = fun j => y i*A i j := by
    ext j
    by_cases hj : A i j=0 <;> simp [supportLift,x,hj]
  change facetValue (supportLift A x i) (canonicalFacet (A i))=y i
  rw [hl]
  calc
    _ = y i*facetValue (A i) (canonicalFacet (A i)) := by
      simp [facetValue,Finset.mul_sum,mul_assoc]
    _ = y i := by rw [facetValue_canonical,hsat,mul_one]

theorem supportSlot_card (A : ι → Fin 3 → ℝ) :
    Fintype.card (SupportSlot A) = ∑ i, (rowSupport A i).card := by
  classical
  unfold SupportSlot
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp [rowSupport,Fintype.card_subtype]

theorem faceDirections_finrank (A : ι → Fin 3 → ℝ)
    (hsat : ∀ i, |A i 0|+|A i 1|+|A i 2|=1) :
    Module.finrank ℝ (LinearMap.ker (rowFaceMap A)) =
      (pairRows A).card+2*(fullRows A).card := by
  have he := (rowFaceMap A).finrank_range_add_finrank_ker
  have hr := LinearMap.range_eq_top.mpr (rowFaceMap_surjective A hsat)
  rw [hr,finrank_top,Module.finrank_pi,Module.finrank_pi,supportSlot_card,
    support_total_count A hsat] at he
  have hc := pure_pair_full_count A hsat
  omega

theorem active_facet_eq_canonical_on_support {A : ι → Fin 3 → ℝ}
    (hA : ∀ i, RowBound (A i)) (x : SupportSlot A → ℝ)
    (i : ι) (σ : Fin 3 → Bool) (hσ : facetValue (A i) σ=1) :
    facetValue (supportLift A x i) σ =
      facetValue (supportLift A x i) (canonicalFacet (A i)) := by
  have hg := active_facet_subgradient (hA i) hσ
  have hc := canonicalSubgradient_spec (A i)
  unfold facetValue
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : A i j=0
  · simp [supportLift_zero_entry A x i j hj]
  · have he : facetSign σ j=canonicalSubgradient (A i) j := by
      apply mul_left_cancel₀ hj
      exact (hg.2 j).trans (hc.2 j).symm
    have hcan : facetSign (canonicalFacet (A i)) j=canonicalSubgradient (A i) j := by
      simp [facetSign,canonicalFacet,canonicalSubgradient]
    rw [he,hcan]

theorem faceDirections_annihilate_active {A : ι → Fin 3 → ℝ}
    (hA : ∀ i, RowBound (A i)) (x : LinearMap.ker (rowFaceMap A)) :
    ∀ i σ, facetValue (A i) σ=1 → facetValue (supportLift A x i) σ=0 := by
  intro i σ hσ
  rw [active_facet_eq_canonical_on_support hA x i σ hσ]
  have hh := congrFun x.property i
  exact hh

def gramSix (A : ι → Fin 3 → ℝ) :
    (ι → Fin 3 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun H := ![crossGram A H 0 0+crossGram A H 0 0,
    crossGram A H 1 1+crossGram A H 1 1,
    crossGram A H 2 2+crossGram A H 2 2,
    crossGram A H 0 1+crossGram A H 1 0,
    crossGram A H 0 2+crossGram A H 2 0,
    crossGram A H 1 2+crossGram A H 2 1]
  map_add' H K := by
    ext k
    fin_cases k <;>
      simp [crossGram,Pi.add_apply,mul_add,Finset.sum_add_distrib] <;> ring
  map_smul' r H := by
    ext k
    fin_cases k <;>
      simp [crossGram,Pi.smul_apply,smul_eq_mul,mul_left_comm,
        ← Finset.mul_sum,mul_add]

theorem gramSix_zero_tangent (A H : ι → Fin 3 → ℝ) (h : gramSix A H=0) :
    FrameTangent A H := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp [gramSix] at h0 h1 h2 h3 h4 h5
  intro j k
  fin_cases j <;> fin_cases k <;> simp_all [add_comm] <;> linarith

def sixPairing (S : Fin 3 → Fin 3 → ℝ) : (Fin 6 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := S 0 0*x 0+S 1 1*x 1+S 2 2*x 2+
    2*S 0 1*x 3+2*S 0 2*x 4+2*S 1 2*x 5
  map_add' x y := by simp [Pi.add_apply]; ring
  map_smul' r x := by simp [Pi.smul_apply,smul_eq_mul]; ring

theorem sixPairing_gramSix {A H : ι → Fin 3 → ℝ}
    {S : Fin 3 → Fin 3 → ℝ} (hS : ∀j k,S j k=S k j) :
    sixPairing S (gramSix A H)=2*framePairing (rightMul A S) H := by
  change S 0 0*(crossGram A H 0 0+crossGram A H 0 0)+
    S 1 1*(crossGram A H 1 1+crossGram A H 1 1)+
    S 2 2*(crossGram A H 2 2+crossGram A H 2 2)+
    2*S 0 1*(crossGram A H 0 1+crossGram A H 1 0)+
    2*S 0 2*(crossGram A H 0 2+crossGram A H 2 0)+
    2*S 1 2*(crossGram A H 1 2+crossGram A H 2 1)=_
  rw [framePairing_rightMul]
  simp only [Fin.sum_univ_three]
  rw [hS 1 0,hS 2 0,hS 2 1]
  ring

theorem sixPairing_multiplier_ne_zero {A : ι → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (M : MultiplierSystem A) :
    sixPairing M.matrix ≠ 0 := by
  intro he
  have hz := congrArg (fun f : (Fin 6 → ℝ) →ₗ[ℝ] ℝ => f ![1,1,1,0,0,0]) he
  have ht := multiplier_trace_identity hA M
  change M.matrix 0 0*1+M.matrix 1 1*1+M.matrix 2 2*1+
    2*M.matrix 0 1*0+2*M.matrix 0 2*0+2*M.matrix 1 2*0=0 at hz
  simp only [mul_one,mul_zero,add_zero] at hz
  rw [hz] at ht
  norm_num at ht

theorem supported_subgradient_pairing {A : ι → Fin 3 → ℝ}
    (x : SupportSlot A → ℝ) (i : ι) {g : Fin 3 → ℝ}
    (hg : RowSubgradient (A i) g) :
    (∑ j, g j*supportLift A x i j)=
      facetValue (supportLift A x i) (canonicalFacet (A i)) := by
  unfold facetValue
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : A i j=0
  · simp [supportLift_zero_entry A x i j hj]
  · have hc := canonicalSubgradient_spec (A i)
    have he : g j=canonicalSubgradient (A i) j :=
      mul_left_cancel₀ hj ((hg.2 j).trans (hc.2 j).symm)
    have hcan : facetSign (canonicalFacet (A i)) j=canonicalSubgradient (A i) j := by
      simp [facetSign,canonicalFacet,canonicalSubgradient]
    rw [he,hcan,mul_comm]

theorem multiplier_annihilates_faceDirections {A : ι → Fin 3 → ℝ}
    (M : MultiplierSystem A) (x : LinearMap.ker (rowFaceMap A)) :
    framePairing (rightMul A M.matrix) (supportLift A x)=0 := by
  unfold framePairing
  apply Finset.sum_eq_zero
  intro i _
  have hstat (j : Fin 3) : rightMul A M.matrix i j=M.weight i*M.gradient i j :=
    M.stationarity i j
  simp_rw [hstat,mul_assoc]
  rw [← Finset.mul_sum,supported_subgradient_pairing x i (M.subgradient i)]
  have hz := congrFun x.property i
  change facetValue (supportLift A x i) (canonicalFacet (A i))=0 at hz
  rw [hz,mul_zero]

def faceGram (A : ι → Fin 3 → ℝ) :
    LinearMap.ker (rowFaceMap A) →ₗ[ℝ] (Fin 6 → ℝ) :=
  (gramSix A).comp ((supportLift A).comp (LinearMap.ker (rowFaceMap A)).subtype)

theorem faceGram_injective {A : ι → Fin 3 → ℝ}
    (hA : ∀ i, RowBound (A i))
    (hno : ∀ H, FrameTangent A H →
      (∀ i σ, facetValue (A i) σ=1 → facetValue (H i) σ=0) → H=0) :
    Function.Injective (faceGram A) := by
  intro x y hxy
  have he : faceGram A (x-y)=0 := by rw [map_sub,hxy,sub_self]
  have ht := gramSix_zero_tangent A (supportLift A (x-y)) he
  have hz := hno _ ht (faceDirections_annihilate_active hA (x-y))
  have hz' : supportLift A ((x-y : LinearMap.ker (rowFaceMap A)) : SupportSlot A → ℝ)=
      supportLift A 0 := by simpa only [map_zero] using hz
  have hx := supportLift_injective A hz'
  have hsub : x-y=0 := Subtype.ext hx
  exact sub_eq_zero.mp hsub

/-- The support dimension bound follows from the absence of a nonzero
face-preserving tangent direction and one actual normalized multiplier. -/
theorem support_bound_of_no_face_tangent {A : ι → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (hs : 0<s) (M : MultiplierSystem A)
    (hsat : ∀ i, |A i 0|+|A i 1|+|A i 2|=1)
    (hno : ∀ H, FrameTangent A H →
      (∀ i σ, facetValue (A i) σ=1 → facetValue (H i) σ=0) → H=0) :
    (pairRows A).card+2*(fullRows A).card≤5 := by
  let f : LinearMap.ker (rowFaceMap A) →ₗ[ℝ] LinearMap.ker (sixPairing M.matrix) :=
    (faceGram A).codRestrict (LinearMap.ker (sixPairing M.matrix)) (by
      intro x
      change sixPairing M.matrix (gramSix A (supportLift A x))=0
      rw [sixPairing_gramSix M.symmetric,multiplier_annihilates_faceDirections M x,
        mul_zero])
  have hf : Function.Injective f := by
    intro x y h
    exact faceGram_injective hA.1 hno (congrArg Subtype.val h)
  have hb := LinearMap.finrank_le_finrank_of_injective hf
  rw [faceDirections_finrank A hsat] at hb
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero
    (sixPairing_multiplier_ne_zero hA hs M)
  rw [Module.finrank_pi] at hk
  norm_num at hk
  omega

end
end F3
