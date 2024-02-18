import Main.book_1.chapter_1.section_6
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Real.Sqrt

open Set Function Bool Int Classical Cardinal

namespace chapter_2

section part_A

variable {X Y Z} (A : Set X) (B : Set Y) (C : Set Z) [Nonempty X] [Nonempty Y]

def EquipotentSet := ∃ f : X → Y, BijOn f A B

notation A "~" B => EquipotentSet A B

theorem theorem_1_1 : A ~ A := by
  use id
  apply bijOn_id

theorem theorem_1_2 : (A ~ B) → B ~ A := by
  rintro ⟨f, hbif⟩
  have ⟨f_inv, ⟨hleft, hright⟩, hmf, hmfinv⟩ := (chapter_1.theorem_4' f A B).mpr hbif
  use f_inv
  apply (chapter_1.theorem_4' f_inv B A).mp ⟨f, ⟨hright, hleft⟩, hmfinv, hmf⟩

theorem theorem_1_3 : (A ~ B) → (B ~ C) → A ~ C := by
  rintro ⟨f, ⟨hmapsf, hinjf, hsurf⟩⟩ ⟨g, ⟨hmapg, hinjg, hsurg⟩⟩
  use g ∘ f
  constructor
  . intro a ha
    exact hmapg (hmapsf ha)
  constructor
  . apply chapter_1.theorem_5_2'
    exact ⟨hinjf, hinjg, hmapsf⟩
  . apply chapter_1.theorem_5_1'
    exact ⟨hsurf, hsurg⟩

section examples

variable {a b c d : ℝ} (h₁ : a < b) (h₂ : c < d)

theorem part_1_A_1 : ∀ x : ℝ, -1 < x ∧ x < 1 → x ^ 2 < 1 := by
  intro x ⟨hxl, hxu⟩
  have : (1 : ℝ) = 1 ^ 2 := by
    ring
  have : ∀ x' : ℝ, 0 < x' ∧ x' < 1 → x' ^ 2 < 1 := by
    intro x' ⟨hxl, hxu⟩
    rw [this, pow_two, pow_two]
    apply mul_lt_mul hxu (le_of_lt hxu) hxl (by norm_num)
  by_cases h: 0 < x
  . apply this x ⟨h, hxu⟩
  push_neg at h
  rcases le_iff_eq_or_lt.mp h with (heq | hle)
  . rw [heq]
    norm_num
  have : (- x) ^ 2 < 1 := by
    apply this (-x)
    constructor
    . norm_num
      exact hle
    . rw [← neg_involutive 1]
      apply (neg_lt_neg_iff (a := x) (b := -1)).mpr
      exact hxl
  ring_nf at this
  exact this

theorem example_5' : ({x | -1 < x ∧ x < 1} : Set ℝ) ~ (univ : Set ℝ) := by
  set f : ℝ → ℝ := λ x ↦ x / (1 - x ^ 2) with hf
  use f
  constructor
  . intro x hx
    apply mem_univ
  constructor
  . apply (chapter_1.part_B_4 f _).mpr
    intro x hx x' hx' hnx
    rw [mem_setOf] at *
    simp only [hf]
    have : ∀ x₁ x₂ : ℝ, x₁ < x₂ → -1 < x₁ ∧ x₁ < 1 → -1 < x₂ ∧ x₂ < 1 → x₁ / (1 - x₁ ^ 2) < x₂ / (1 - x₂ ^ 2) := by
      intro x₁ x₂ hx₁x₂ ⟨hx₁l, hx₁u⟩ ⟨hx₂l, hx₂u⟩
      have hx₁sq : 0 < 1 - x₁ ^ 2 := by
        sorry
      have hx₂sq : 0 < 1 - x₂ ^ 2 := by
        sorry
      by_cases h: x₁ * x₂ > 0
      . apply (div_lt_div_iff hx₁sq hx₂sq).mpr
        ring_nf
        rw [add_comm _ x₂]
        apply add_lt_add hx₁x₂
        norm_num
        rw [pow_two, pow_two, mul_comm x₁ (x₂ * x₂), mul_assoc, mul_assoc, mul_comm x₂ x₁]
        apply mul_lt_mul_of_pos_right hx₁x₂ h
      . push_neg at h
        have ⟨hnx₁, hpx₂⟩ : x₁ < 0 ∧ 0 < x₂ := by
          sorry
        apply (div_lt_div_iff hx₁sq hx₂sq).mpr
        calc
          x₁ * (1 - x₂ ^ 2)
          _ < 0 := by
            apply mul_neg_iff.mpr
            right
            exact ⟨hnx₁, hx₂sq⟩
          _ ≤ x₂ * (1 - x₁ ^ 2) := by
            apply mul_nonneg_iff.mpr
            left
            exact ⟨le_of_lt hpx₂, le_of_lt hx₁sq⟩
    rcases lt_or_lt_iff_ne.mpr hnx with (hxx' | hx'x)
    . apply lt_or_lt_iff_ne.mp
      left
      apply this x x' hxx' hx hx'
    . apply lt_or_lt_iff_ne.mp
      right
      apply this x' x hx'x hx' hx
  intro y _
  simp
  by_cases h : y = 0
  . use 0
    constructor
    . norm_num
    simp
    rw [h]
  push_neg at h
  rcases lt_or_lt_iff_ne.mpr h with (h | h)
  . use (-1 - Real.sqrt (4 * y ^ 2 + 1)) / (2 * y)
    constructor
    . sorry
    set s := -1 - Real.sqrt (4 * y ^ 2 + 1) with hs
    rw [div_div]

    sorry
  use (-1 + Real.sqrt (4 * y ^ 2 + 1)) / (2 * y)
  sorry

theorem example_5 : {x | a < x ∧ x < b} ~ (univ : Set ℝ) := by
  sorry

end examples

end part_A

noncomputable
section part_B

variable {A B : Type u} {f : A → B} {g : B → A} (X : Set A) (Y : Set B) [Nonempty Y]

mutual

def Bs :ℕ → Set B
  | 0 => univ \ f '' univ
  | n + 1 => f '' (As n)

def As : ℕ → Set A := λ n ↦ g '' (Bs n)

end

-- theorem theorem_2 : (∃ f : A → B, InjOn f X ∧ MapsTo f X Y) ∧ (∃ g : B → A, InjOn g Y ∧ MapsTo g Y X) → X ~ Y := by
--   rintro ⟨⟨f, ⟨hinjf, hmapf⟩⟩, ⟨g, ⟨hinjg, hmapg⟩⟩⟩
--   by_cases h : SurjOn f X Y
--   . exact ⟨f, ⟨hmapf, hinjf, h⟩⟩
--   . set As := @As _ _ f g with has
--     set Bs := @Bs _ _ f g with hbs
--     set Astar := ⋃ i, As i
--     set Ares := univ \ Astar with hAres
--     set Bstar := ⋃ i, Bs i
--     set Bres := univ \ Bstar with hBres

--     have Auniv : Ares ∪ Astar = univ := by simp
--     have Buniv : Bres ∪ Bstar = univ := by simp
--     have Ain :∀ a: A, a ∈ Astar →  a ∉ Ares := by
--       intro a hainstar
--       rw [hAres, ← compl_eq_univ_diff]
--       exact not_mem_compl_iff.mpr hainstar
--     have Adisjoint : Disjoint Ares Astar := by
--       rw [hAres]
--       exact disjoint_sdiff_left
--     have Bdisjoint : Disjoint Bres Bstar := by
--       rw [hBres]
--       exact disjoint_sdiff_left

--     have exp_1_4 : f '' Ares = Bres := by
--       apply (
--         calc
--           f '' Ares
--           _ = f '' univ \ f '' Astar := by rw [chapter_1.exercise_1_4.ex_5_c f hinjf]
--           _ = (univ \ Bs 0) \ f '' Astar := by rw [hbs, chapter_2.Bs, ← compl_eq_univ_diff, ← compl_eq_univ_diff, chapter_1.exp_2_13 (f '' univ)]
--           _ = univ \ (Bs 0 ∪ f '' Astar) := by rw [chapter_1.exercise_1_2.ex_5_a]).trans
--       have :=
--         calc
--           f '' Astar
--           _ = f '' (⋃ i, As i) := by dsimp
--           _ = ⋃ i, f '' As i := by rw [chapter_1.exp_5_3]
--           _ = ⋃ i, Bs (i + 1) := by
--             rw [iUnion_congr]
--             intro i
--             rw [has, ← chapter_2.Bs, ← hbs]
--       have :=
--         calc
--           Bs 0 ∪ f '' Astar
--           _ = ⋃ i, Bs i := by rw [this, union_iUnion_nat_succ]
--           _ = Bstar := by dsimp
--       rw [this]
--     have exp_1_5 : g '' Bstar = Astar :=
--       calc
--         g '' Bstar
--         _ = g '' ⋃ i, Bs i := by dsimp
--         _ = ⋃ i, g '' Bs i := by rw [chapter_1.exp_5_3]
--         _ = ⋃ i, As i := by
--           rw [iUnion_congr]
--           intro i
--           rw [hbs, ← chapter_2.As]
--         _ = Astar := by dsimp

--     have Fres : BijOn f Ares Bres := by
--       have ⟨hfa_in_b, hb_in_fa⟩ := Subset.antisymm_iff.mp exp_1_4
--       constructor
--       . exact mapsTo'.mpr hfa_in_b
--       . constructor
--         . intro a _ a' _ hf
--           exact hinjf hf
--         . exact hb_in_fa
--     have Gstar : BijOn g Bstar Astar := by
--       have ⟨hgb_in_a, ha_in_gb⟩ := Subset.antisymm_iff.mp exp_1_5
--       constructor
--       . exact mapsTo'.mpr hgb_in_a
--       . constructor
--         . intro b _ b' _ hg
--           exact hinjg hg
--         . exact ha_in_gb

--     set fstar := invFunOn g Bstar
--     have : InvOn fstar g Bstar Astar := BijOn.invOn_invFunOn Gstar
--     have Fstar : BijOn fstar Astar Bstar := (bijOn_comm this).mpr Gstar

--     -- Classicalをopenしないと宣言できない
--     set F : A → B := λ a ↦ if a ∈ Ares then f a else fstar a with hF
--     sorry

end part_B

end chapter_2
