import Main.book_1.chapter_1.section_5
import Mathlib.Data.Int.Basic

open Set Function Bool Int

namespace chapter_1

section part_A

variable {A : Type*}

class R' (A : Type*) where
  rel : A → A → Prop

infix:70 " R` " => R'.rel

def G_R' (A : Type*) [R' A] : Set (A × A) := {⟨a, b⟩ | a R` b}

end part_A

section part_B

variable {A : Type*}

class Req (A : Type*) extends R' A where
  req_refl : ∀ a : A, a R` a
  req_symm : ∀ a b : A, a R` b → b R` a
  req_trans : ∀ a b c : A, a R` b → b R` c → a R` c

instance example_1 : Req A where
  rel := (· = ·)
  req_refl := by
    intro a
    dsimp
  req_symm := by
    intro a b hab
    dsimp at *
    exact hab.symm
  req_trans := by
    intro a b c hab hbc
    dsimp at *
    exact hab.trans hbc

instance example_2 (n : ℕ) : Req ℤ where
  rel := λ a b ↦ (a - b) % n = 0
  req_refl := by
    intro a
    dsimp
    simp only [sub_self, zero_emod]
  req_symm := by
    intro a b arb
    dsimp at *
    calc
      (b - a) % n
      _ = - (a - b) % n := by simp only [neg_sub]
      _ = 0 := by rw [← zero_sub, sub_emod, arb, zero_emod, sub_zero, zero_emod]
  req_trans := by
    intro a b c arb brc
    dsimp at *
    calc
      (a - c) % n
      _ = ((a - b) + (b - c)) % n := by rw [← neg_add_cancel_right (a - c) b]; simp
      _ = 0 := by rw [add_emod, arb, brc]; simp

section example_3

variable {A B : Type*} {f : A → B}

instance example_3 : Req A where
  rel := λ x y ↦ f x = f y
  req_refl := by
    intro x
    dsimp
  req_symm := by
    intro x y hxy
    dsimp at *
    rw [hxy]
  req_trans := by
    intro x y z hxy hyz
    dsimp at *
    rw [hxy, hyz]

end example_3

section example_4

variable {A : Type*} {M : Set (Set A)}

class UnionDiv {A : Type*} (M : Set (Set A)) where
  i : ⋃₀ M = univ
  ii : ∀ C ∈ M, C ≠ C' → C ∩ C' = ∅

theorem part_6_B_1 : ∀ a : A, ∃ C ∈ M, a ∈ C := by
  intro a
  sorry

variable [UnionDiv M]

-- UnionDivとReqの順番？が定まらない的なエラーがでる
-- instance example_4 : Req A where
--   rel := λ a b ↦ ∃ C ∈ M, a ∈ C ∧ b ∈ C
--   req_refl := by
--     intro a
--     dsimp
--     have ⟨C, hcm, hac⟩ := part_6_B_1 a (M := M)
--     use C
--   req_symm := by
--     intro a b
--     dsimp
--     rintro ⟨C, hcm, hac, hbc⟩
--     use C
--   req_trans := by
--     intro a b c
--     dsimp
--     rintro ⟨C, hcm, hac, hbc⟩ ⟨C', hcm', hbc', hcc'⟩
--     have : C = C' := by
--       apply Not.imp_symm (UnionDiv.ii C hcm (M := M) (C' := C'))
--       intro hcccup
--       have hnc := eq_empty_iff_forall_not_mem.mp hcccup b
--       have heq : b ∈ C ∩ C' := ⟨hbc, hbc'⟩
--       exact hnc heq
--     rw [← this] at hcc'
--     use C

end example_4

end part_B

section part_C

variable {A : Type*} [Req A]

def C_Req (a : A) : Set A := {x | a R` x}

theorem exp_6_1 (a : A) : a ∈ C_Req a := by
  rw [C_Req, mem_setOf]
  apply Req.req_refl a

theorem exp_6_2 (a b : A) : a R` b ↔ C_Req a = C_Req b := by
  constructor
  . intro harb
    have h₁ : C_Req a ⊆ C_Req b := by
      intro x hxa
      rw [C_Req, mem_setOf] at *
      apply Req.req_trans
      apply Req.req_symm a b harb
      exact hxa
    have h₂ : C_Req b ⊆ C_Req a := by
      intro x hxb
      rw [C_Req, mem_setOf] at *
      apply Req.req_trans
      apply harb
      exact hxb
    exact Subset.antisymm h₁ h₂
  . intro h
    have : b ∈ C_Req a := by
      rw [h]
      exact exp_6_1 b
    rw [C_Req, mem_setOf] at this
    exact this

theorem exp_6_3 (a b : A) : C_Req a ≠ C_Req b → C_Req a ∩ C_Req b = ∅ := by
  intro hn
  have := not_imp_not.mpr (exp_6_2 a b).mp hn
  by_contra hncap
  have ⟨c, hc⟩ := nonempty_def.mp (nonempty_iff_ne_empty.mpr hncap)
  have ⟨hac, hbc⟩ := hc
  rw [C_Req, mem_setOf] at *
  have hcont := Req.req_trans a c b hac (Req.req_symm _ _ hbc)
  exact this hcont

def M : Set (Set A) := {C | ∀ (a : A), C = C_Req a}

-- 上の例4と同じようにうまくいかない
-- theorem theorem_8 : UnionDiv M := by
--   sorry

end part_C

end chapter_1
