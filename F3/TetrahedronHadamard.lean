import F3.SharpValues

namespace F3
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

def tetraSign : Fin 3 → Fin 4 → ℝ :=
  ![![1,1,-1,-1],![1,-1,1,-1],![1,-1,-1,1]]

def tetraVertices {ι : Type*} (A : ι → Fin 3 → ℝ) : ι → Fin 4 → ℝ :=
  fun i p => (∑j,A i j*tetraSign j p)/2

def tetraFrame {ι : Type*} (V : ι → Fin 4 → ℝ) : ι → Fin 3 → ℝ :=
  fun i j => (∑p,V i p*tetraSign j p)/2

lemma tetraSign_abs (j : Fin 3) (p : Fin 4) : |tetraSign j p|=1 := by
  fin_cases j <;> fin_cases p <;> norm_num [tetraSign]

lemma tetraSign_row_sum (j : Fin 3) : (∑p,tetraSign j p)=0 := by
  fin_cases j <;> norm_num [tetraSign,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.sum_univ_three,Fin.sum_univ_four]

lemma tetraSign_row_gram (j k : Fin 3) :
    (∑p,tetraSign j p*tetraSign k p)=if j=k then 4 else 0 := by
  fin_cases j <;> fin_cases k <;> norm_num [tetraSign,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.sum_univ_three,Fin.sum_univ_four]

lemma tetraSign_column_gram (p q : Fin 4) :
    (∑j,tetraSign j p*tetraSign j q)=4*(if p=q then 1 else 0)-1 := by
  fin_cases p <;> fin_cases q <;> norm_num [tetraSign,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.sum_univ_three,Fin.sum_univ_four]

lemma tetraVertices_centered {ι : Type*} (A : ι → Fin 3 → ℝ) (i : ι) :
    (∑p,tetraVertices A i p)=0 := by
  simp only [tetraVertices,←Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [←Finset.mul_sum,tetraSign_row_sum,mul_zero,Finset.sum_const_zero,zero_div]

lemma tetraFrame_reconstruct {ι : Type*} (V : ι → Fin 4 → ℝ)
    (hc : ∀i,(∑p,V i p)=0) (i : ι) (p : Fin 4) :
    tetraVertices (tetraFrame V) i p=V i p := by
  have hs := hc i
  simp only [Fin.sum_univ_three,Fin.sum_univ_four,Fin.sum_univ_zero,add_zero] at hs
  fin_cases p <;> norm_num [tetraVertices,tetraFrame,tetraSign,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.sum_univ_three,Fin.sum_univ_four]
  · linarith
  · linarith
  · change _=V i 2
    linarith
  · change _=V i 3
    linarith

lemma gram_transform {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (T : κ → ν → ℝ) (p q : ν) :
    (∑i,(∑j,A i j*T j p)*(∑k,A i k*T k q))=
      ∑j,∑k,(∑i,A i j*A i k)*T j p*T k q := by
  calc
    _ = ∑i,∑j,∑k,(A i j*T j p)*(A i k*T k q) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑j,∑k,∑i,(A i j*T j p)*(A i k*T k q) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma tetraVertices_gram {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) (p q : Fin 4) :
    (∑i,tetraVertices A i p*tetraVertices A i q)=
      s*((if p=q then 1 else 0)-1/4) := by
  classical
  have ht := gram_transform A tetraSign p q
  have hscaled : (∑i,tetraVertices A i p*tetraVertices A i q)=
      (∑i,(∑j,A i j*tetraSign j p)*(∑k,A i k*tetraSign k q))/4 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [tetraVertices]
    ring
  rw [hscaled,ht]
  simp only [hA.2,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have he : (∑j,s*tetraSign j p*tetraSign j q)=s*(∑j,tetraSign j p*tetraSign j q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,tetraSign_column_gram]
  ring

lemma squared_distance_gram {ι κ : Type*} [Fintype ι]
    (V : ι → κ → ℝ) (p q : κ) :
    (∑i,(V i p-V i q)^2)=
      (∑i,V i p*V i p)+(∑i,V i q*V i q)-2*(∑i,V i p*V i q) := by
  rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma tetraVertices_edge {ι : Type*} [Fintype ι] {A : ι → Fin 3 → ℝ} {s : ℝ}
    (hA : Feasible s A) {p q : Fin 4} (hpq : p≠q) :
    (∑i,(tetraVertices A i p-tetraVertices A i q)^2)=2*s := by
  rw [squared_distance_gram,tetraVertices_gram hA,tetraVertices_gram hA,tetraVertices_gram hA]
  simp only [ite_true,if_neg hpq]
  ring

lemma four_sign_bound {a b c : ℝ}
    (h0 : |a+b+c|≤1) (h1 : |a-b-c|≤1)
    (h2 : |-a+b-c|≤1) (h3 : |-a-b+c|≤1) : |a|+|b|+|c|≤1 := by
  obtain ⟨h0l,h0u⟩ := abs_le.mp h0
  obtain ⟨h1l,h1u⟩ := abs_le.mp h1
  obtain ⟨h2l,h2u⟩ := abs_le.mp h2
  obtain ⟨h3l,h3u⟩ := abs_le.mp h3
  rcases le_total 0 a with ha | ha <;>
    rcases le_total 0 b with hb | hb <;>
    rcases le_total 0 c with hc | hc <;>
    simp_all only [abs_of_nonneg,abs_of_nonpos] <;> linarith

lemma tetra_row_bound_iff (a : Fin 3 → ℝ) :
    (∀p : Fin 4, |(∑j,a j*tetraSign j p)/2|≤1/2) ↔ RowBound a := by
  constructor
  · intro h
    have hp (p : Fin 4) : |∑j,a j*tetraSign j p|≤1 := by
      have ht := h p
      rw [abs_div,show |(2:ℝ)|=2 by norm_num] at ht
      linarith
    have h0 := hp 0
    have h1 := hp 1
    have h2 := hp 2
    have h3 := hp 3
    norm_num [tetraSign,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.sum_univ_three,Fin.sum_univ_four] at h0 h1 h2 h3
    unfold RowBound
    apply four_sign_bound (by simpa [add_assoc] using h0)
    · convert h1 using 1
    · convert h2 using 1
    · convert h3 using 1
  · intro ha p
    have ht := Finset.abs_sum_le_sum_abs (f:=fun j => a j*tetraSign j p) (s:=Finset.univ)
    simp only [abs_mul,tetraSign_abs,mul_one,Fin.sum_univ_three] at ht
    unfold RowBound at ha
    rw [abs_div,show |(2:ℝ)|=2 by norm_num]
    simp only [Fin.sum_univ_three]
    linarith

lemma tetraVertices_contained {ι : Type*} (A : ι → Fin 3 → ℝ)
    (hA : ∀i,RowBound (A i)) : ∀i p,|tetraVertices A i p|≤1/2 := by
  intro i p
  exact (tetra_row_bound_iff (A i)).mpr (hA i) p

lemma tetraFrame_row_bound {ι : Type*} (V : ι → Fin 4 → ℝ)
    (hc : ∀i,(∑p,V i p)=0) (hV : ∀i p,|V i p|≤1/2) :
    ∀i,RowBound (tetraFrame V i) := by
  intro i
  apply (tetra_row_bound_iff (tetraFrame V i)).mp
  intro p
  change |tetraVertices (tetraFrame V) i p|≤1/2
  rw [tetraFrame_reconstruct V hc]
  exact hV i p

end
end F3
