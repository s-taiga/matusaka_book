import Mathlib.Data.Set.Lattice

open Set

namespace chapter_1

variable {S} (A B C D : Set S)

section part_A

/-
本では普通の部分集合を⊆ではなく⊂で記載している
-/

theorem exp_2_1 : A ∪ B = {x | x ∈ A ∨ x ∈ B} := by rfl

theorem exp_2_2_1 : A ⊆ A ∪ B := by
  intro x
  exact mem_union_left B

theorem exp_2_2_2 : B ⊆ A ∪ B := by
  intro x
  exact mem_union_right A

theorem exp_2_3 (h₁ : A ⊆ C) (h₂ : B ⊆ C) : A ∪ B ⊆ C := by
  rintro x (ha | hb)
  . exact h₁ ha
  . exact h₂ hb

theorem exp_2_4 : A ∪ A = A := union_self A
theorem exp_2_5 : A ∪ B = B ∪ A := union_comm A B
theorem exp_2_6 : (A ∪ B) ∪ C = A ∪ (B ∪ C) := union_assoc A B C

example : ((A ∪ B) ∪ C) ∪ D = (A ∪ (B ∪ C)) ∪ D :=
  calc
    ((A ∪ B) ∪ C) ∪ D
    _ = (A ∪ B) ∪ (C ∪ D) := exp_2_6 (A ∪ B) C D
    _ = A ∪ (B ∪ (C ∪ D)) := exp_2_6 A B (C ∪ D)
    _ = A ∪ ((B ∪ C) ∪ D) := by rw [← exp_2_6 B C D]
    _ = (A ∪ (B ∪ C)) ∪ D := by rw [← exp_2_6 A (B ∪ C) D]

theorem exp_2_7 : A ⊆ B ↔ A ∪ B = B := by
  constructor
  . intro h
    have h₁ : A ∪ B ⊆ B := exp_2_3 A B B h Subset.rfl
    have h₁' : B ⊆ A ∪ B := exp_2_2_2 A B
    exact Subset.antisymm h₁ h₁'
  . intro h
    rw [← h]
    exact exp_2_2_1 A B

theorem exp_2_8 (h : A ⊆ B) : A ∪ C ⊆ B ∪ C := by
  calc
    A ∪ C
    _ ⊆ B ∪ (A ∪ C) := exp_2_2_2 B (A ∪ C)
    _ = (B ∪ A) ∪ C := by rw [← exp_2_6]
    _ = (A ∪ B) ∪ C := by rw [exp_2_5 B A]
    _ = B ∪ C := by rw [(exp_2_7 A B).mp h]

theorem exp_2_9 : ∅ ∪ A = A := (exp_2_7 ∅ A).mp (empty_subset A)

end part_A

section part_B

theorem exp_2_2_1' : A ∩ B ⊆ A := by
  intro x h
  exact mem_of_mem_inter_left h

theorem exp_2_2_2' : A ∩ B ⊆ B := by
  intro x h
  exact mem_of_mem_inter_right h

theorem exp_2_3' (h₁ : C ⊆ A) (h₂ : C ⊆ B) : C ⊆ A ∩ B := by
  intro x hc
  exact ⟨h₁ hc, h₂ hc⟩

theorem exp_2_4' : A ∩ A = A := inter_self A
theorem exp_2_5' : A ∩ B = B ∩ A := inter_comm A B
theorem exp_2_6' : (A ∩ B) ∩ C = A ∩ (B ∩ C) := inter_assoc A B C

theorem exp_2_7' : A ⊆ B ↔ A ∩ B = A := by
  constructor
  . intro h
    have h₁ : A ∩ B ⊆ A := exp_2_2_1' A B
    have h₂ : A ⊆ A ∩ B := exp_2_3' A B A Subset.rfl h
    exact Subset.antisymm h₁ h₂
  . intro h
    rw [← h]
    exact exp_2_2_2' A B

theorem exp_2_8' (h : A ⊆ B) : A ∩ C ⊆ B ∩ C := by
  calc
    A ∩ C
    _ = (A ∩ B) ∩ C := by rw [(exp_2_7' A B).mp h]
    _ = A ∩ (B ∩ C) := exp_2_6' A B C
    _ ⊆ B ∩ C := exp_2_2_2' A (B ∩ C)

theorem exp_2_9' : ∅ ∩ A = ∅ := (exp_2_7' ∅ A).mp (empty_subset A)

theorem exp_2_10 : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
  ext x
  simp
  tauto

theorem exp_2_10' : (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) := by
  ext x
  simp
  tauto

theorem exp_2_11 : (A ∪ B) ∩ A = A := by
  ext x
  simp
  tauto

theorem exp_2_11' : (A ∩ B) ∪ A = A := by
  ext x
  simp
  tauto

end part_B

section part_C
-- nothing
end part_C

section part_D

theorem exp_2_12_1 : A ∪ Aᶜ = univ := union_compl_self A
theorem exp_2_12_2 : A ∩ Aᶜ = ∅ := inter_compl_self A
theorem exp_2_13 : Aᶜᶜ = A := by
  ext x
  constructor
  . intro hcc
    apply not_mem_compl_iff.mp
    exact not_mem_of_mem_compl hcc
  . intro h
    apply not_mem_compl_iff.mpr
    exact h

theorem exp_2_14_1 : (∅ : Set S)ᶜ = univ := compl_empty
theorem exp_2_14_2 : (univ : Set S)ᶜ = ∅ := compl_univ
theorem exp_2_15 : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  simp [compl_subset_compl]

theorem exp_2_16 : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  calc
    x ∈ (A ∪ B)ᶜ
    _ ↔ x ∉ A ∪ B := by rw [mem_compl_iff]
    _ ↔ x ∉ A ∧ x ∉ B := sorry
    _ ↔ x ∈ Aᶜ ∧ x ∈ Bᶜ := by rw [mem_compl_iff, mem_compl_iff]
    _ ↔ x ∈ Aᶜ ∩ Bᶜ := by simp

theorem exp_2_16' : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  calc
    x ∈ (A ∩ B)ᶜ
    _ ↔ x ∉ A ∩ B := by rw [mem_compl_iff]
    _ ↔ x ∉ A ∨ x ∉ B := sorry
    _ ↔ x ∈ Aᶜ ∨ x ∈ Bᶜ := by rw [mem_compl_iff, mem_compl_iff]
    _ ↔ x ∈ Aᶜ ∪ Bᶜ := by simp

end part_D

section part_E
-- nothing
end part_E

section part_F

variable {I} (A : I → Set S)

theorem exp_2_17 : ∀ i : I, A i ⊆ ⋃ j, A j := by sorry
theorem exp_2_18 : ∀ i : I, A i ⊆ C → ⋃ j, A j ⊆ C := by sorry
theorem exp_2_17' : ∀ i : I, ⋂ j, A j ⊆ A i := by sorry
theorem exp_2_18' : ∀ i : I, C ⊆ A i → C ⊆ ⋂ j, A j := by sorry

end part_F

namespace exercise_1_2

theorem ex_lemma_1 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := inter_distrib_left A B C
theorem ex_lemma_2 : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := union_distrib_left A B C

theorem ex_1_a : (A ∪ B) ∩ (A ∪ Bᶜ) = A :=
  calc
    (A ∪ B) ∩ (A ∪ Bᶜ)
    _ = (B ∪ A) ∩ (Bᶜ ∪ A) := by rw [exp_2_5 A B, exp_2_5 A Bᶜ]
    _ = (B ∩ Bᶜ) ∪ A := by rw [← exp_2_10']
    _ = ∅ ∪ A := by rw [exp_2_12_2]
    _ = A := exp_2_9 A

theorem ex_1_b : (A ∪ B) ∩ (Aᶜ ∪ B) ∩ (A ∪ Bᶜ) = A ∩ B :=
  calc
    (A ∪ B) ∩ (Aᶜ ∪ B) ∩ (A ∪ Bᶜ)
    _ = (A ∪ B) ∩ (A ∪ Bᶜ) ∩ (Aᶜ ∪ B) := by rw [exp_2_6', exp_2_5' (Aᶜ ∪ B), ← exp_2_6']
    _ = (Aᶜ ∪ B) ∩ A := by rw [ex_1_a, exp_2_5']
    _ = (Aᶜ ∩ A) ∪ (B ∩ A) := by rw [exp_2_10]
    _ = ∅ ∪ (A ∩ B) := by rw [exp_2_5', exp_2_12_2, exp_2_5']
    _ = A ∩ B := exp_2_9 (A ∩ B)

theorem ex_2_1 : A ∩ B = ∅ ↔ B ⊆ Aᶜ := by
  constructor
  . intro h
    have : B ∩ Aᶜ = B :=
      calc
        B ∩ Aᶜ
        _ = (B ∩ Aᶜ) ∪ ∅ := by rw [exp_2_5, exp_2_9]
        _ = (Aᶜ ∩ B) ∪ (A ∩ B) := by rw [← h, exp_2_5']
        _ = (Aᶜ ∪ A) ∩ B := by rw [← exp_2_10]
        _ = univ ∩ B := by rw [exp_2_5, exp_2_12_1]
        _ = B := univ_inter B
    rw [← this]
    apply exp_2_2_2' B Aᶜ
  . intro h
    have h₁ : ∅ ⊆ A ∩ B := empty_subset (A ∩ B)
    have h₂ : A ∩ B ⊆ ∅ :=
      calc
        A ∩ B
        _ ⊆ A ∩ Aᶜ := by rw [exp_2_5', exp_2_5' A]; exact exp_2_8' B Aᶜ A h
        _ = ∅ := exp_2_12_2 A
    exact Subset.antisymm h₂ h₁

theorem ex_2_2 : B ⊆ Aᶜ ↔ A ⊆ Bᶜ :=
  calc
    B ⊆ Aᶜ
    _ ↔ Aᶜᶜ ⊆ Bᶜ := by rw [exp_2_15]
    _ ↔ A ⊆ Bᶜ := by rw [exp_2_13]

theorem ex_3_a_1 : A \ B = (A ∪ B) \ B := by rw [← union_diff_right]
theorem ex_3_a_2 : A \ B = A \ (A ∩ B) := by rw [exp_2_5', diff_inter_self_eq_diff]
theorem ex_3_a_3 : A \ B = A ∩ Bᶜ := diff_eq A B

theorem ex_lemma_3 : A ∩ B = A ↔ A ⊆ B := by
  constructor
  . intro h
    rw [← h]
    exact exp_2_2_2' A B
  . intro h
    have h₁ : A ∩ B ⊆ A := exp_2_2_1' A B
    have h₂ : A ⊆ A ∩ B :=
      calc
        A
        _ = A ∩ A := (exp_2_4' A).symm
        _ ⊆ B ∩ A := exp_2_8' A B A h
        _ = A ∩ B := exp_2_5' B A
    exact Subset.antisymm h₁ h₂

theorem ex_3_b : A \ B = A ↔ A ∩ B = ∅ :=
  calc
    A \ B = A
    _ ↔ A ∩ Bᶜ = A := by rw [ex_3_a_3]
    _ ↔ A ⊆ Bᶜ := ex_lemma_3 A Bᶜ
    _ ↔ B ⊆ Aᶜ := ex_2_2 B A
    _ ↔ A ∩ B = ∅ := by rw [ex_2_1]

theorem ex_3_c : A \ B = ∅ ↔ A ⊆ B :=
  calc
    A \ B = ∅
    _ ↔ A ∩ Bᶜ = ∅ := by rw [ex_3_a_3]
    _ ↔ Bᶜ ⊆ Aᶜ := ex_2_1 A Bᶜ
    _ ↔ A ⊆ B := (exp_2_15 A B).symm

theorem ex_4_a : A \ (B ∪ C) = (A \ B) ∩ (A \ C) :=
  calc
    A \ (B ∪ C)
    _ = A ∩ (B ∪ C)ᶜ := ex_3_a_3 A (B ∪ C)
    _ = (A ∩ A) ∩ (Bᶜ ∩ Cᶜ) := by nth_rewrite 1 [← exp_2_4' A]; rw [exp_2_16]
    _ = (A ∩ Bᶜ) ∩ (A ∩ Cᶜ) := by rw [exp_2_6', ← exp_2_6' A Bᶜ]; nth_rewrite 1 [exp_2_5' A Bᶜ]; rw [exp_2_6', ← exp_2_6' A]
    _ = (A \ B) ∩ (A \ C) := by rw [ex_3_a_3 A B, ex_3_a_3]

theorem ex_4_b : A \ (B ∩ C) = (A \ B) ∪ (A \ C) :=
  calc
    A \ (B ∩ C)
    _ = A ∩ (B ∩ C)ᶜ := ex_3_a_3 A (B ∩ C)
    _ = A ∩ (Bᶜ ∪ Cᶜ) := by rw [exp_2_16']
    _ = (A ∩ Bᶜ) ∪ (A ∩ Cᶜ) := by rw [ex_lemma_1]
    _ = (A \ B) ∪ (A \ C) := by rw [ex_3_a_3 A B, ex_3_a_3]

theorem ex_4_c : (A ∪ B) \ C = (A \ C) ∪ (B \ C) :=
  calc
    (A ∪ B) \ C
    _ = (A ∪ B) ∩ Cᶜ := ex_3_a_3 (A ∪ B) C
    _ = (A ∩ Cᶜ) ∪ (B ∩ Cᶜ) := exp_2_10 A B Cᶜ
    _ = (A \ C) ∪ (B \ C) := by rw [ex_3_a_3 A C, ex_3_a_3]

theorem ex_4_d : (A ∩ B) \ C = (A \ C) ∩ (B \ C) :=
  calc
    (A ∩ B) \ C
    _ = (A ∩ B) ∩ Cᶜ := ex_3_a_3 (A ∩ B) C
    _ = (A ∩ B) ∩ (Cᶜ ∩ Cᶜ) := by rw [exp_2_4' Cᶜ]
    _ = (A ∩ Cᶜ) ∩ (B ∩ Cᶜ) := by rw [exp_2_6', ← exp_2_6' B Cᶜ]; nth_rewrite 1 [exp_2_5' B]; rw [exp_2_6', ← exp_2_6']
    _ = (A \ C) ∩ (B \ C) := by rw [ex_3_a_3 A C, ex_3_a_3]

theorem ex_4_e : A ∩ (B \ C) = (A ∩ B) \ (A ∩ C) :=
  calc
    A ∩ (B \ C)
    _ = A ∩ (B ∩ Cᶜ) := by rw [ex_3_a_3]
    _ = ∅ ∪ (A ∩ (B ∩ Cᶜ)) := by rw [exp_2_9]
    _ = (∅ ∩ B) ∪ (A ∩ (B ∩ Cᶜ)) := by rw [exp_2_9']
    _ = (A ∩ Aᶜ ∩ B) ∪ (A ∩ (B ∩ Cᶜ)) := by rw [exp_2_12_2]
    _ = (Aᶜ ∩ (A ∩ B)) ∪ (Cᶜ ∩ (A ∩ B)) := by rw [exp_2_5' A, exp_2_6', exp_2_5' A (B ∩ Cᶜ), exp_2_5' B Cᶜ, exp_2_6', exp_2_5' B A]
    _ = (Aᶜ ∪ Cᶜ) ∩ (A ∩ B) := by rw [exp_2_10]
    _ = (A ∩ B) ∩ (Aᶜ ∪ Cᶜ) := by rw [exp_2_5']
    _ = (A ∩ B) ∩ (A ∩ C)ᶜ := by rw [exp_2_16']
    _ = (A ∩ B) \ (A ∩ C) := by rw [ex_3_a_3]

theorem ex_5_a : (A \ B) \ C = A \ (B ∪ C) :=
  calc
    (A \ B) \ C
    _ = (A ∩ Bᶜ) ∩ Cᶜ := by rw [ex_3_a_3, ex_3_a_3]
    _ = A ∩ (Bᶜ ∩ Cᶜ) := by rw [exp_2_6']
    _ = A ∩ (B ∪ C)ᶜ := by rw [exp_2_16]
    _ = A \ (B ∪ C) := by rw [ex_3_a_3]

theorem ex_5_b : A \ (B \ C) = (A \ B) ∪ (A ∩ C) :=
  calc
    A \ (B \ C)
    _ = A ∩ (B ∩ Cᶜ)ᶜ := by rw [ex_3_a_3, ex_3_a_3]
    _ = A ∩ (Bᶜ ∪ Cᶜᶜ) := by rw [exp_2_16']
    _ = A ∩ (Bᶜ ∪ C) := by rw [exp_2_13]
    _ = (A ∩ Bᶜ) ∪ (A ∩ C) := by rw [ex_lemma_1]
    _ = (A \ B) ∪ (A ∩ C) := by rw [ex_3_a_3]

theorem ex_6 : A ⊆ C → ∀ B, A ∪ (B ∩ C) = (A ∪ B) ∩ C := by
  intro h B
  have : A ∪ C = C := by
    have h₁ : C ⊆ A ∪ C := exp_2_2_2 A C
    have h₂ : A ∪ C ⊆ C := by
      nth_rewrite 2 [← exp_2_4 C]
      exact exp_2_8 A C C h
    exact Subset.antisymm h₂ h₁
  calc
    A ∪ (B ∩ C)
    _ = (A ∪ B) ∩ (A ∪ C) := ex_lemma_2 A B C
    _ = (A ∪ B) ∩ C := by rw [this]

theorem ex_lemma_4 : A ∆ B = (A \ B) ∪ (B \ A) := symmDiff_def A B
theorem ex_lemma_5 : A ∆ B = (A ∩ Bᶜ) ∪ (Aᶜ ∩ B) := by
  rw [ex_lemma_4, ex_3_a_3, ex_3_a_3, exp_2_5' B]

theorem ex_7_a : A ∆ B = B ∆ A :=
  calc
    A ∆ B
    _ = (A \ B) ∪ (B \ A) := ex_lemma_4 A B
    _ = (B \ A) ∪ (A \ B) := exp_2_5 (A \ B) (B \ A)
    _ = B ∆ A := ex_lemma_4 B A

theorem ex_7_b : A ∆ B = (A ∪ B) \ (A ∩ B) :=
  calc
    A ∆ B
    _ = (A ∩ Bᶜ) ∪ (Aᶜ ∩ B) := ex_lemma_5 A B
    _ = (A ∪ (Aᶜ ∩ B)) ∩ (Bᶜ ∪ (Aᶜ ∩ B)) := by rw [exp_2_10']
    _ = ((A ∪ Aᶜ) ∩ (A ∪ B)) ∩ ((Bᶜ ∪ Aᶜ) ∩ (Bᶜ ∪ B)) := by rw [ex_lemma_2, ex_lemma_2]
    _ = (univ ∩ (A ∪ B)) ∩ ((Bᶜ ∪ Aᶜ) ∩ univ) := by rw [exp_2_12_1, exp_2_5 Bᶜ B, exp_2_12_1]
    _ = (A ∪ B) ∩ (Bᶜ ∪ Aᶜ) := by rw [univ_inter, inter_univ]
    _ = (A ∪ B) ∩ (A ∩ B)ᶜ := by rw [exp_2_16', exp_2_5 Bᶜ]
    _ = (A ∪ B) \ (A ∩ B) := by rw [ex_3_a_3]

theorem ex_lemma_6 : (A ∆ B)ᶜ = (Aᶜ ∩ Bᶜ) ∪ (A ∩ B) :=
  calc
    (A ∆ B)ᶜ
    _ = ((A ∪ B) ∩ (A ∩ B)ᶜ)ᶜ := by rw [ex_7_b, ex_3_a_3]
    _ = (A ∪ B)ᶜ ∪ (A ∩ B)ᶜᶜ := by rw [exp_2_16']
    _ = (A ∪ B)ᶜ ∪ (A ∩ B) := by rw [exp_2_13]
    _ = (Aᶜ ∩ Bᶜ) ∪ (A ∩ B) := by rw [exp_2_16]

theorem ex_7_c : (A ∆ B) ∆ C = A ∆ (B ∆ C) :=
  calc
    (A ∆ B) ∆ C
    _ = (A ∆ B) ∩ Cᶜ ∪ (A ∆ B)ᶜ ∩ C := by rw [ex_lemma_5]
    _ = (A ∩ Bᶜ ∪ Aᶜ ∩ B) ∩ Cᶜ ∪ ((Aᶜ ∩ Bᶜ) ∪ (A ∩ B)) ∩ C := by rw [ex_lemma_6, ex_lemma_5]
    _ = (A ∩ Bᶜ ∩ Cᶜ) ∪ (Aᶜ ∩ B ∩ Cᶜ) ∪ ((Aᶜ ∩ Bᶜ ∩ C) ∪ (A ∩ B ∩ C)) := by rw [exp_2_10, exp_2_10]
    _ = (A ∩ Bᶜ ∩ Cᶜ) ∪ (A ∩ B ∩ C) ∪ ((Aᶜ ∩ B ∩ Cᶜ) ∪ (Aᶜ ∩ Bᶜ ∩ C)) := by rw [exp_2_6, ← exp_2_6 (Aᶜ ∩ B ∩ Cᶜ), exp_2_5 _ (A ∩ B ∩ C), ← exp_2_6]
    _ = A ∩ (Bᶜ ∩ Cᶜ ∪ B ∩ C) ∪ Aᶜ ∩ ((B ∩ Cᶜ) ∪ (Bᶜ ∩ C)) := by rw [exp_2_6' A, exp_2_6' A, exp_2_6' Aᶜ, exp_2_6' Aᶜ, ex_lemma_1 A, ex_lemma_1 Aᶜ]
    _ = A ∩ (B ∆ C)ᶜ ∪ Aᶜ ∩ (B ∆ C) := by rw [ex_lemma_6, ex_lemma_5]
    _ = A ∆ (B ∆ C) := by rw [← ex_lemma_5]

theorem ex_7_d : A ∩ (B ∆ C) = (A ∩ B) ∆ (A ∩ C) :=
  calc
    A ∩ (B ∆ C)
    _ = A ∩ ((B ∪ C) \ (B ∩ C)) := by rw [ex_7_b]
    _ = (A ∩ (B ∪ C)) \ (A ∩ (B ∩ C)) := by rw [ex_4_e]
    _ = (A ∩ B ∪ A ∩ C) \ ((A ∩ A) ∩ (B ∩ C)) := by rw [ex_lemma_1, exp_2_4']
    _ = (A ∩ B ∪ A ∩ C) \ ((A ∩ B) ∩ (A ∩ C)) := by rw [exp_2_6', ← exp_2_6' A B, exp_2_5' (A ∩ B), ← exp_2_6', exp_2_5' (A ∩ C)]
    _ = (A ∩ B) ∆ (A ∩ C) := by rw [ex_7_b]

theorem ex_8_a : A ∆ ∅ = A :=
  calc
    A ∆ ∅
    _ = (A ∩ ∅ᶜ) ∪ (Aᶜ ∩ ∅) := by rw [ex_lemma_5]
    _ = (A ∩ univ) ∪ ∅ := by rw [exp_2_14_1, exp_2_5' Aᶜ, exp_2_9']
    _ = A := by rw [inter_univ, exp_2_5, exp_2_9]

theorem ex_8_b : A ∆ univ = Aᶜ :=
  calc
    A ∆ univ
    _ = (A ∩ univᶜ) ∪ (Aᶜ ∩ univ) := by rw [ex_lemma_5]
    _ = (A ∩ ∅) ∪ Aᶜ := by rw [exp_2_14_2, inter_univ]
    _ = Aᶜ := by rw [exp_2_5', exp_2_9', exp_2_9]

theorem ex_8_c : A ∆ A = ∅ :=
  calc
    A ∆ A
    _ = (A ∪ A) \ (A ∩ A) := by rw [ex_7_b]
    _ = A \ A := by rw [exp_2_4, exp_2_4']
    _ = ∅ := by rw [diff_self]

theorem ex_8_d : A ∆ Aᶜ = univ :=
  calc
    A ∆ Aᶜ
    _ = (A ∪ Aᶜ) \ (A ∩ Aᶜ) := by rw [ex_7_b]
    _ = univ \ ∅ := by rw [exp_2_12_1, exp_2_12_2]
    _ = univ := by rw [diff_empty]

theorem ex_9 (A₁ A₂ B₁ B₂ : Set S) : A₁ ∆ A₂ = B₁ ∆ B₂ → A₁ ∆ B₁ = A₂ ∆ B₂ := by
  intro h
  have : (A₁ ∆ A₂) ∆ B₂ = B₁ :=
    calc
      (A₁ ∆ A₂) ∆ B₂
      _ = (B₁ ∆ B₂) ∆ B₂ := by rw [h]
      _ = B₁ ∆ (B₂ ∆ B₂) := by rw [ex_7_c]
      _ = B₁ ∆ ∅ := by rw [ex_8_c]
      _ = B₁ := by rw [ex_8_a]
  calc
    A₁ ∆ B₁
    _ = A₁ ∆ ((A₁ ∆ A₂) ∆ B₂) := by rw [this]
    _ = A₁ ∆ A₁ ∆ (A₂ ∆ B₂) := by rw [ex_7_c, ← ex_7_c]
    _ = A₂ ∆ B₂ := by rw [ex_8_c, ex_7_a, ex_8_a]

end exercise_1_2

end chapter_1
