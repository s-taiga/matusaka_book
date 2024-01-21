import Main.book_1.chapter_1.section_5
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rel

open Set Function Bool Int

namespace chapter_1

section part_A

-- 教科書ではx R yのように中置記法だが、Mathlibでは普通にr x yと前置するスタイル
variable {A : Type*} {r : Rel A A}

-- Mathlibのgraphは関数から関係を作る関数として定義されているため、そもそも関係を集合そのものと捉えているっぽい？
def G' (r : Rel A A) : Set (A × A) := {⟨a, b⟩ | r a b}

end part_A

section part_B

variable {A : Type*} [Setoid A]

theorem part_6_B_1 : ∀ a : A, a ≈ a := Setoid.refl
theorem part_6_B_2 : ∀ a b : A, a ≈ b → b ≈ a := @Setoid.symm A _
theorem part_6_B_3 : ∀ a b c : A, a ≈ b → b ≈ c → a ≈ c := @Setoid.trans A _

local instance example_1 : Setoid A where
  r := (· = ·)
  iseqv := {
    refl := refl
    symm := symm
    trans := _root_.trans
  }

local instance example_2 (n : ℕ): Setoid ℤ where
  r := λ a b ↦ (a - b) % n = 0
  iseqv := {
    refl := by
      intro a
      simp only [sub_self, zero_emod]
    symm := by
      intro a b arb
      calc
        (b - a) % n
        _ = - (a - b) % n := by simp only [neg_sub]
        _ = 0 := by rw [← zero_sub, sub_emod, arb, zero_emod, sub_zero, zero_emod]
    trans := by
      intro a b c arb brc
      calc
        (a - c) % n
        _ = ((a - b) + (b - c)) % n := by rw [← neg_add_cancel_right (a - c) b]; simp
        _ = 0 := by rw [add_emod, arb, brc]; simp
  }

section example_3

variable {A B : Type*} {f : A → B}

scoped instance example_3 : Setoid A where
  r := λ x y ↦ f x = f y
  iseqv := {
    refl := by
      intro x
      dsimp
    symm := by
      intro x y hxy
      rw [hxy]
    trans := by
      intro x y z hxy hyz
      rw [hxy, hyz]
  }

end example_3

section example_4

variable {A : Type*} (M : Set (Set A))

class UnionDiv where
  i : ⋃₀ M = univ
  ii : ∀ C ∈ M, C ≠ C' → C ∩ C' = ∅

theorem part_6_B_4 : ∀ a : A, ∃ C ∈ M, a ∈ C := by
  intro a
  sorry

-- Mをパラメータに含めないとexample_4が定義できないため別でクラス作成
class MSetoid (A : Type*) (M : Set (Set A)) where
  r : A → A → Prop
  iseqv : Equivalence r

scoped instance example_4 [UnionDiv M] : MSetoid A M where
  r := λ a b ↦ ∃ C ∈ M, a ∈ C ∧ b ∈ C
  iseqv := {
    refl := by
      intro a
      have ⟨C, hcm, hac⟩ := part_6_B_4 M a
      use C
    symm := by
      intro a b
      rintro ⟨C, hcm, hac, hbc⟩
      use C
    trans := by
      intro a b c
      rintro ⟨C, hcm, hac, hbc⟩ ⟨C', _, hbc', hcc'⟩
      have : C = C' := by
        apply Not.imp_symm (@UnionDiv.ii A M _ C' C hcm)
        intro hcccup
        have hnc := eq_empty_iff_forall_not_mem.mp hcccup b
        have heq : b ∈ C ∩ C' := ⟨hbc, hbc'⟩
        exact hnc heq
      rw [← this] at hcc'
      use C
  }

end example_4

end part_B

section part_C

variable {A : Type*} [s : Setoid A]

def C_Req (a : A) : Set A := {x | a ≈ x}
-- MathlibではQuotientを使う（型はSetではない）

theorem exp_6_1 (a : A) : a ∈ C_Req a := by
  rw [C_Req, mem_setOf]

theorem exp_6_2 (a b : A) : a ≈ b ↔ C_Req a = C_Req b := by
  constructor
  . intro harb
    have h₁ : C_Req a ⊆ C_Req b := by
      intro x hxa
      rw [C_Req, mem_setOf] at *
      apply Setoid.trans
      apply Setoid.symm harb
      exact hxa
    have h₂ : C_Req b ⊆ C_Req a := by
      intro x hxb
      rw [C_Req, mem_setOf] at *
      apply Setoid.trans
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
  have hcont := Setoid.trans hac (Setoid.symm hbc)
  exact this hcont

def M : Set (Set A) := {C | ∀ (a : A), C = C_Req a}

def phi (a : A) : Quotient s := ⟦a⟧

theorem part_6_C_1 : ∀ ca : Quotient s, ∃ a, ca = phi a := by
  intro ca
  have ⟨a, ha⟩ := Quotient.exists_rep ca
  use a
  rw [phi, ha]

end part_C

section part_D

variable {A B : Type*} {f : A → B}

def φ (a : A) : @Quotient A (@example_3 _ B f) := ⟦a⟧

variable (a a' : A)

theorem part_6_D_1 : @φ _ _ f a = φ a' ↔ (@example_3 _ _ f).r a a' := by
  constructor
  . intro h
    simp [φ] at h
    have := Quotient.exact h
    apply this
  . intro h
    apply Quotient.sound
    apply h

theorem part_6_D_2 : (@example_3 _ _ f).r a a' ↔ f a = f a' := by
  simp [example_3]

noncomputable
def g' (p : @Quotient A (@example_3 _ B f)) : B := f (@Quotient.out _ (@example_3 _ _ f) p)

theorem part_6_D_3 : @Injective (@Quotient A (@example_3 _ B f)) _ g' := by
  intro phia phia' hg
  simp [g'] at hg
  have := (@part_6_D_2 _ _ f (@Quotient.out _ (@example_3 _ _ f) phia) (@Quotient.out _ (@example_3 _ _ f) phia')).mpr hg
  have := (@part_6_D_1 _ _ f (@Quotient.out _ (@example_3 _ _ f) phia) (@Quotient.out _ (@example_3 _ _ f) phia')).mpr this
  simp [φ] at this
  rw [@Quotient.out_eq _ (@example_3 _ _ f) phia, @Quotient.out_eq _ (@example_3 _ _ f) phia'] at this
  exact this

theorem part_6_D_4 : ∀ x : @Quotient A (@example_3 _ B f), g' x ∈ f '' univ := by
  sorry

noncomputable
def g := codRestrict g' (f '' univ) part_6_D_4

def j (b : f '' univ) : B := b

theorem exp_6_4 : f = j ∘ (@g _ _ f) ∘ φ := by
  ext a
  calc
    f a
    _ = j (g (φ a)) := sorry
    _ = (j ∘ g ∘ φ) a := by dsimp

end part_D

end chapter_1
