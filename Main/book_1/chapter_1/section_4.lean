import Main.book_1.chapter_1.section_2
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.BoolIndicator

open Set Function Bool

namespace chapter_1

section part_A

variable {A B} (f : A → B)

-- Mathlibでは像f(P)は f '' Pと書く
example (f : A → B) (P : Set A) : f '' P = {b | ∃ a ∈ P, f a = b} := rfl

example (f : A → B) (P : Set A) : f '' P = {f a | a ∈ P} := rfl

theorem part_A_1 : ∀ (a : A), f '' {a} = {f a} := λ _ ↦ image_singleton

theorem part_A_2 : ∀ (P : Set A), f '' P = ∅ ↔ P = ∅ := λ _ ↦ image_eq_empty

-- Mathlibでは逆像f⁻¹(Q)は f ⁻¹' Qと書く
example (f : A → B) (Q : Set B) : f ⁻¹' Q = {a | f a ∈ Q} := rfl

theorem part_A_3 : ∀ b : B, f ⁻¹' {b} = {a | f a = b} := by
  intro b
  rw [preimage]
  simp only [mem_singleton_iff]

theorem part_A_4 : f ⁻¹' univ = univ := by
  rw [preimage]
  simp only [mem_univ, setOf_true]

section theorem_3

variable {P P₁ P₂ : Set A} {Q Q₁ Q₂ : Set B}

theorem exp_4_1 : P₁ ⊆ P₂ → f '' P₁ ⊆ f '' P₂ := by
  intro h
  simp [image]
  intro a hp₁
  have := h hp₁
  use a

theorem exp_4_2 : f '' (P₁ ∪ P₂) = f '' P₁ ∪ f '' P₂ := by
  have h₁ : f '' (P₁ ∪ P₂) ⊆ f '' P₁ ∪ f '' P₂ := by
    intro b h
    have ⟨a, ha, _⟩ : ∃ a ∈ P₁ ∪ P₂, f a = b := (mem_image f _ b).mp h
    rcases ha with (h₁ | h₂)
    . left
      rw [image]
      simp
      use a
    . right
      rw [image]
      simp
      use a
  have h₂ : f '' P₁ ∪ f '' P₂ ⊆ f '' (P₁ ∪ P₂) :=
    calc
      f '' P₁ ∪ f '' P₂
      _ ⊆ f '' (P₁ ∪ P₂) ∪ f '' P₂ := by apply exp_2_8; apply exp_4_1; apply exp_2_2_1
      _ ⊆ f '' (P₁ ∪ P₂) ∪ f '' (P₁ ∪ P₂) := by rw [exp_2_5]; apply exp_2_8; apply exp_4_1; apply exp_2_2_2
      _ ⊆ f '' (P₁ ∪ P₂) := by rw [exp_2_4]
  exact Subset.antisymm h₁ h₂

theorem exp_4_3 : f '' (P₁ ∩ P₂) ⊆ f '' P₁ ∩ f '' P₂ :=
  calc
    f '' (P₁ ∩ P₂)
    _ ⊆ f '' (P₁ ∩ P₂) ∩ f '' (P₁ ∩ P₂) := by rw [exp_2_4']
    _ ⊆ f '' P₁ ∩ f '' (P₁ ∩ P₂) := by apply exp_2_8'; apply exp_4_1; apply exp_2_2_1'
    _ ⊆ f '' P₁ ∩ f '' P₂ := by rw [exp_2_5', exp_2_5' (f '' P₁)]; apply exp_2_8'; apply exp_4_1; apply exp_2_2_2'

theorem exp_4_4 : f '' univ \ f '' P ⊆ f '' (univ \ P) := by
  rw [diff_subset_iff, ← exp_4_2]
  apply exp_4_1
  rw [union_diff_self, union_univ]

theorem exp_4_1' : Q₁ ⊆ Q₂ → f ⁻¹' Q₁ ⊆ f ⁻¹' Q₂ := by
  simp [preimage]
  intro h a hq₁
  exact h hq₁

theorem exp_4_2' : f ⁻¹' (Q₁ ∪ Q₂) = f ⁻¹' Q₁ ∪ f ⁻¹' Q₂ := by
  apply Subset.antisymm
  . intro a h
    rw [preimage, mem_setOf] at h
    rcases h with (h₁ | h₂)
    . left
      simp only [mem_preimage]
      exact h₁
    . right
      simp only [mem_preimage]
      exact h₂
  . calc
      f ⁻¹' Q₁ ∪ f ⁻¹' Q₂
      _ ⊆ f ⁻¹' (Q₁ ∪ Q₂) ∪ f ⁻¹' Q₂ := by apply exp_2_8; apply exp_4_1'; apply exp_2_2_1
      _ ⊆ f ⁻¹' (Q₁ ∪ Q₂) ∪ f ⁻¹' (Q₁ ∪ Q₂) := by rw [exp_2_5]; apply exp_2_8; apply exp_4_1'; apply exp_2_2_2
      _ ⊆ f ⁻¹' (Q₁ ∪ Q₂) := by rw [exp_2_4]

theorem exp_4_3' : f ⁻¹' (Q₁ ∩ Q₂) = f ⁻¹' Q₁ ∩ f ⁻¹' Q₂ := by
  apply Subset.antisymm
  . calc
      f ⁻¹' (Q₁ ∩ Q₂)
      _ ⊆ f ⁻¹' (Q₁ ∩ Q₂) ∩ f ⁻¹' (Q₁ ∩ Q₂) := by rw [exp_2_4']
      _ ⊆ f ⁻¹' Q₁ ∩ f ⁻¹' (Q₁ ∩ Q₂) := by apply exp_2_8'; apply exp_4_1'; apply exp_2_2_1'
      _ ⊆ f ⁻¹' Q₁ ∩ f ⁻¹' Q₂ := by rw [exp_2_5', exp_2_5' (f ⁻¹' Q₁)]; apply exp_2_8'; apply exp_4_1'; apply exp_2_2_2'
  . rintro a ⟨hq₁, hq₂⟩
    simp only [mem_preimage] at *
    exact ⟨hq₁, hq₂⟩

theorem exp_4_4' : f ⁻¹' (univ \ Q) = univ \ f ⁻¹' Q := by
  apply Subset.antisymm
  . intro a h
    simp only [mem_preimage] at h
    rw [exercise_1_2.ex_3_a_3] at *
    have ⟨hu, hnq⟩ := h
    rw [mem_compl_iff] at hnq
    exact ⟨hu, hnq⟩
  . rw [diff_subset_iff, ← part_A_4 f, ← exp_4_2']
    apply exp_4_1'
    rw [union_diff_self, union_univ]

theorem exp_4_5 : P ⊆ f ⁻¹' (f '' P) := by
  intro a h
  -- rw [image, mem_preimage, mem_setOf]
  use a

theorem exp_4_5' : f '' (f ⁻¹' Q) ⊆ Q := by
  intro b h
  have ⟨a, hinv, heq⟩ : ∃ a ∈ f ⁻¹' Q, f a = b := (mem_image f _ b).mp h
  rw [mem_preimage] at hinv
  rw [← heq]
  exact hinv

end theorem_3

end part_A

section part_B

variable {A B} (f : A → B)

theorem part_B_1 : Surjective f ↔ f '' univ = univ := by
  simp
  exact range_iff_surjective.symm

theorem part_B_2 : Surjective f ↔ ∀ b : B, f ⁻¹' {b} ≠ ∅ := by
  rw [Surjective]
  sorry

theorem part_B_3 : Surjective f ↔ ∀ b : B, ∃ a : A, f a = b := by
  rw [Surjective]

theorem part_B_4 : Injective f ↔ ∀ a a' : A, a ≠ a' → f a ≠ f a' := by
  rw [Injective]
  simp
  constructor
  . intro h a a' hneq hfneq
    have := h hfneq
    contradiction
  . intro h x₁ x₂
    have := h x₁ x₂
    contrapose
    exact this

def f₁ (x : ℝ) : ℝ := x + 1

example : Bijective f₁ := by
  rw [Bijective]
  constructor
  . rw [Injective]
    intro x₁ x₂ hf₁
    simp [f₁] at hf₁
    exact hf₁
  . rw [Surjective]
    simp [f₁]
    intro x
    use x - 1
    ring

-- 逆対応からの証明は難しそうなので以下の形式にする
theorem theorem_4 : ∀ finv: B → A, LeftInverse finv f ∧ RightInverse finv f ↔ Bijective f := by
  intro finv
  simp only [Function.RightInverse, LeftInverse, Bijective, Injective, Surjective]
  constructor
  . rintro ⟨hlf, hrf⟩
    constructor
    . intro a₁ a₂ hf
      calc
        a₁
        _ = finv (f a₁) := (hlf a₁).symm
        _ = finv (f a₂) := by rw [hf]
        _ = a₂ := hlf a₂
    . intro b
      use finv b
      exact hrf b
  . rintro ⟨hin, hsur⟩
    constructor
    . intro a
      sorry
    . sorry

end part_B

section part_C

variable {A B C D} (f : A → B) (g : B → C) (h : C → D)

example : g ∘ f = λ a ↦ g (f a) := by
  rfl

theorem theorem_5_1 : Surjective f ∧ Surjective g → Surjective (g ∘ f) := by
  rintro ⟨hf, hg⟩
  simp_all [Surjective]
  intro c
  have ⟨b, hg⟩ := hg c
  have ⟨a, hf⟩ := hf b
  use a
  rw [hf, hg]

theorem theorem_5_2 : Injective f ∧ Injective g → Injective (g ∘ f) := by
  rintro ⟨hf, hg⟩
  simp_all [Injective]
  intro a₁ a₂ hgf
  have := hg hgf
  have := hf this
  exact this

theorem theroem_5_3 : Bijective f ∧ Bijective g → Bijective (g ∘ f) := by
  rintro ⟨⟨hinf, hsurf⟩, ⟨hing, hsurg⟩⟩
  exact ⟨theorem_5_2 f g ⟨hinf, hing⟩, theorem_5_1 f g ⟨hsurf, hsurg⟩⟩

theorem theorem_6_1 : (h ∘ g) ∘ f = h ∘ (g ∘ f) := by
  ext a
  calc
    ((h ∘ g) ∘ f) a
    _ = (h ∘ g) (f a) := by dsimp
    _ = h (g (f a)) := by dsimp
    _ = h ((g ∘ f) a) := by dsimp
    _ = (h ∘ (g ∘ f)) a := by dsimp

#check comp.right_id

theorem theorem_6_2_1 : f ∘ id = f := by
  ext a
  calc
    (f ∘ id) a
    _ = f (id a) := by dsimp
    _ = f a := by dsimp

theorem theorem_6_2_2 : id ∘ f = f := by
  rw [comp.left_id]

theorem theorem_6_3_1 : ∀ finv : B → A, LeftInverse finv f ∧ RightInverse finv f → finv ∘ f = id := by
  rintro finv ⟨hlf, _⟩
  simp only [LeftInverse] at hlf
  ext x
  exact hlf x

theorem theorem_6_3_2 : ∀ finv : B → A, LeftInverse finv f ∧ RightInverse finv f → f ∘ finv = id := by
  rintro finv ⟨_, hrf⟩
  simp only [Function.RightInverse] at hrf
  ext x
  exact hrf x

end part_C

-- part_D, Eでは特に式・定理なし

section part_F

#check boolIndicator

end part_F

namespace exercise_1_4

variable {A B C} (f f': A → B) (g g': B → C)
variable {P P₁ P₂ : Set A} {Q Q₁ Q₂ : Set B} {R : Set C}

-- 1, 2は上記で実施済み

theorem ex_3_1 : Injective f → P = f ⁻¹' (f '' P) := by
  intro hinjf
  apply Subset.antisymm
  . exact exp_4_5 f
  . intro x h
    rw [image, preimage, mem_setOf, mem_setOf] at h
    have ⟨a, ha, hab⟩ := h
    have := hinjf hab
    rw [← this]
    exact ha

theorem ex_3_2 : Surjective f → f '' (f ⁻¹' Q) = Q := by
  intro hsurf
  apply Subset.antisymm
  . exact exp_4_5' f
  . intro x h
    rw [Surjective] at hsurf
    rw [image, preimage, mem_setOf]
    have ⟨a, hx⟩ := hsurf x
    use a
    constructor
    . rw [mem_setOf, hx]
      exact h
    . exact hx

theorem ex_4 : Injective f → f '' (P₁ ∩ P₂) = f '' P₁ ∩ f '' P₂ := by
  intro hinjf
  apply Subset.antisymm
  . exact exp_4_3 f
  . rintro x ⟨hp₁, hp₂⟩
    rw [image, mem_setOf] at *
    have ⟨a₁, hp₁, ha₁⟩ := hp₁
    have ⟨a₂, hp₂, ha₂⟩ := hp₂
    have := ha₁.trans ha₂.symm
    have eq₁₂ := hinjf this
    rw [← eq₁₂] at hp₂
    use a₁
    constructor
    . exact ⟨hp₁, hp₂⟩
    . exact ha₁

theorem ex_5_c : Injective f → f '' univ \ f '' P = f '' (univ \ P) := by
  intro hinjf
  apply Subset.antisymm
  . exact exp_4_4 f
  . intro x h
    rw [exercise_1_2.ex_3_a_3] at *
    rw [image, image, mem_setOf] at *
    have ⟨a, ⟨hun, hpc⟩, h⟩ := h
    constructor
    . rw [mem_setOf]
      use a
    . rw [mem_compl_iff, mem_setOf]
      rintro ⟨a₁, ha₁, hh⟩
      have := h.trans hh.symm
      have heq := hinjf this
      rw [heq] at hpc
      contradiction

-- 6, 7は実施済み
-- 8は構成が思いつかなかったのでいったん飛ばす

theorem ex_9_a : (g ∘ f) '' P = g '' (f '' P) := by
  simp only [image]
  simp only [comp_apply]
  simp only [mem_setOf]
  simp only [exists_exists_and_eq_and]

theorem ex_10_a : Surjective (g ∘ f) → Surjective g := by
  intro hsurjgf b
  have ⟨a, h⟩ := hsurjgf b
  use (f a)
  exact h

theorem ex_10_b : Injective (g ∘ f) → Injective f := by
  intro hinjgf a₁ a₂ hf
  have := congr_arg g hf
  exact hinjgf this

theorem ex_11 : Surjective f → g ∘ f = g' ∘ f → g = g' := by
  intro hsurf hgf
  ext b
  have ⟨a, ha⟩ := hsurf b
  calc
    g b
    _ = g (f a) := by rw [← ha]
    _ = (g ∘ f) a := by dsimp
    _ = (g' ∘ f) a := by rw [hgf]
    _ = g' (f a) := by dsimp
    _ = g' b := by rw [ha]

theorem ex_12 : Injective g → g ∘ f = g ∘ f' → f = f' := by
  intro hinjg hgf
  ext a
  have : g (f a) = g (f' a) := by
    calc
      g (f a)
      _ = (g ∘ f) a := by dsimp
      _ = (g ∘ f') a := by rw [hgf]
      _ = g (f' a) := by dsimp
  exact hinjg this

theorem ex_13_a : Surjective (g ∘ f) → Injective g → Surjective f := by
  intro hsurgf hinjg b
  have ⟨a, ha⟩ := hsurgf (g b)
  use a
  exact hinjg ha

theorem ex_13_b : Injective (g ∘ f) → Surjective f → Injective g := by
  intro hinjgf hsurf b₁ b₂ hg
  have ⟨a₁, ha₁⟩ := hsurf b₁
  have ⟨a₂, ha₂⟩ := hsurf b₂
  rw [← ha₁, ← ha₂] at hg
  have := hinjgf hg
  rw [← ha₁, this, ha₂]

theorem ex_14 : ∀ g g' : B → A, g ∘ f = id ∧ f ∘ g' = id → Bijective f ∧ g = g' := by
  rintro g g' ⟨hr, hl⟩
  have hr := funext_iff.mp hr
  have hl := funext_iff.mp hl
  dsimp at *
  constructor
  . constructor
    . show Injective f
      intro a₁ a₂ hf
      rw [←hr a₁, hf, hr a₂]
    . show Surjective f
      intro b
      use g' b
      exact hl b
  . ext b
    calc
      g b
      _ = g (f (g' b)) := by rw [hl]
      _ = g' b := by rw [hr]

theorem ex_15 : ∀ A' B' : Set A, (∀ x : A, A'.boolIndicator x ≤ B'.boolIndicator x) ↔ A' ⊆ B' := by
  intro A' B'
  constructor
  . intro h x ha
    have := h x
    simp [boolIndicator, ha] at this
    -- have := ite_eq_left_iff.mp (Bool.eq_true_of_true_le this)  -- Decidable (x ∈ B')が示せない
    -- simp [*] at this
    -- exact this
    sorry
  . intro h x
    simp [boolIndicator]
    rw [subset_def] at h
    have := h x
    apply le_iff_imp.mpr
    intro ha
    -- apply ite_eq_left_iff.mp
    sorry

theorem ex_15_a : ∀ (A' B' : Set A) (x : A), (A' ∩ B').boolIndicator x ↔ (A'.boolIndicator x) && (B'.boolIndicator x) := by
  intro A' B' x
  apply (mem_iff_boolIndicator (A' ∩ B') x).symm.trans
  simp
  constructor
  . rintro ⟨ha, hb⟩
    constructor
    . apply (mem_iff_boolIndicator A' x).mp
      exact ha
    . apply (mem_iff_boolIndicator B' x).mp
      exact hb
  . rintro ⟨ha, hb⟩
    constructor
    . apply (mem_iff_boolIndicator A' x).mpr
      exact ha
    . apply (mem_iff_boolIndicator B' x).mpr
      exact hb

-- 16 ~ の有限集合関連は難しそうなのでスキップ

end exercise_1_4

end chapter_1
