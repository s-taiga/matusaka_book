import Main.book_1.chapter_1.section_6
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Basic

open Set Function Bool Int Classical Cardinal

namespace chapter_2

section part_A

variable {X Y Z} {A : Set X} {B : Set Y} {C : Set Z}

def Equipotent (A B : Type*) : Prop := ∃ (f : A → B), Bijective f

notation A "~" B => Equipotent A B

def EquipotentSet (A : Set X) (B : Set Y) := ∃ f : X → Y, BijOn f A B

notation A "~ₛ" B => EquipotentSet A B

theorem theorem_1_1' : A ~ₛ A := by
  use id
  apply bijOn_id

theorem theorem_1_1 : A ~ A := by
  use id
  apply bijective_id

theorem theorem_1_2 {A B} : (A ~ B) → B ~ A := by
  rintro ⟨f, hbif⟩
  have ⟨f_inv, ⟨hleftinv, hrightinv⟩⟩ := (chapter_1.theorem_4 f).mpr hbif
  use f_inv
  apply (chapter_1.theorem_4 f_inv).mp ⟨f, ⟨hrightinv, hleftinv⟩⟩

theorem theorem_1_3 {A B C} : (A ~ B) → (B ~ C) → A ~ C := by
  rintro ⟨f, ⟨hinjf, hsurf⟩⟩ ⟨g, ⟨hinjg, hsurg⟩⟩
  use g ∘ f
  constructor
  . apply chapter_1.theorem_5_2
    exact ⟨hinjf, hinjg⟩
  . apply chapter_1.theorem_5_1
    exact ⟨hsurf, hsurg⟩

theorem part_1_A_1 {A B : Type*}: (A ~ B) ↔ Nonempty (A ≃ B) := by
  constructor
  . rintro ⟨f, hbif⟩
    have ⟨f_inv, ⟨hleftinv, hrightinv⟩⟩ := (chapter_1.theorem_4 f).mpr hbif
    use f
  . intro h
    have := h.some
    use this
    exact Equiv.bijective this

section examples

theorem example_1 {n : ℕ} (hfa: Finite A) (h : Nat.card A = n) : (A ~ₛ B) ↔ (Finite B ∧ Nat.card B = n) := by
  constructor
  . rintro ⟨f, ⟨hmap, hinj, hsur⟩⟩
    constructor
    . apply finite_iff_exists_equiv_fin.mpr
      use n
      sorry
    . sorry
  . sorry

theorem example_2 : (univ : Set ℕ) ~ₛ {2 * x | x : ℕ} := by
  constructor
  case w => exact λ x ↦ 2 * x
  case h =>
    constructor
    . intro x _
      dsimp
      use x
    constructor
    . intro x _ x' _ hf
      dsimp at hf
      simp only [_root_.mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, _root_.or_false] at hf
      exact hf
    intro n hn
    simp only [mem_setOf_eq, image_univ, range_two_mul] at *
    apply even_iff_two_dvd.mpr
    have ⟨x, hx⟩ := hn
    use x, hx.symm

theorem example_3 : ((univ : Set ℕ) ×ˢ (univ : Set ℕ)) ~ₛ (univ : Set ℕ) := by
  constructor
  case w =>
    exact λ ⟨i, j⟩ ↦ 2 ^ i * (2 * j + 1)
  constructor
  . intro ⟨i, j⟩ _
    simp only [mem_univ]
  constructor
  . intro ⟨i, j⟩ _ ⟨i', j'⟩ _ hf
    simp at hf
    sorry
  sorry

variable {a b c d : ℝ} (h₁ : a < b) (h₂ : c < d)

theorem example_4_1 : {x | a ≤ x ∧ x ≤ b} ~ₛ {x | c ≤ x ∧ x ≤ d} := by
  constructor
  case w =>
    exact λ x ↦ (d - c) / (b - a) * (x - a) + c
  have hcoef_pos : (d - c) / (b - a) > 0 := by
    sorry
  constructor
  . intro x hx
    simp at *
    rcases hx with ⟨hax, hxb⟩
    constructor
    . sorry
    . sorry
  sorry

theorem example_5 : {x | a < x ∧ x < b} ~ (univ : Set ℝ) := by
  sorry

end examples

end part_A

noncomputable
section part_B

variable {A B : Type u} {f : A → B} {g : B → A} [Nonempty B]

mutual

def Bs :ℕ → Set B
  | 0 => univ \ f '' univ
  | n + 1 => f '' (As n)

def As : ℕ → Set A := λ n ↦ g '' (Bs n)

end

theorem theorem_2 : (∃ f : A → B, Injective f) ∧ (∃ g : B → A, Injective g) → (A ~ B) := by
  rintro ⟨⟨f, hinjf⟩, ⟨g, hinjg⟩⟩
  by_cases h : Surjective f
  . exact ⟨f, ⟨hinjf, h⟩⟩
  . set As := @As _ _ f g with has
    set Bs := @Bs _ _ f g with hbs
    set Astar := ⋃ i, As i
    set Ares := univ \ Astar with hAres
    set Bstar := ⋃ i, Bs i
    set Bres := univ \ Bstar with hBres

    have Auniv : Ares ∪ Astar = univ := by simp
    have Buniv : Bres ∪ Bstar = univ := by simp
    have Ain :∀ a: A, a ∈ Astar →  a ∉ Ares := by
      intro a hainstar
      rw [hAres, ← compl_eq_univ_diff]
      exact not_mem_compl_iff.mpr hainstar
    have Adisjoint : Disjoint Ares Astar := by
      rw [hAres]
      exact disjoint_sdiff_left
    have Bdisjoint : Disjoint Bres Bstar := by
      rw [hBres]
      exact disjoint_sdiff_left

    have exp_1_4 : f '' Ares = Bres := by
      apply (
        calc
          f '' Ares
          _ = f '' univ \ f '' Astar := by rw [chapter_1.exercise_1_4.ex_5_c f hinjf]
          _ = (univ \ Bs 0) \ f '' Astar := by rw [hbs, chapter_2.Bs, ← compl_eq_univ_diff, ← compl_eq_univ_diff, chapter_1.exp_2_13 (f '' univ)]
          _ = univ \ (Bs 0 ∪ f '' Astar) := by rw [chapter_1.exercise_1_2.ex_5_a]).trans
      have :=
        calc
          f '' Astar
          _ = f '' (⋃ i, As i) := by dsimp
          _ = ⋃ i, f '' As i := by rw [chapter_1.exp_5_3]
          _ = ⋃ i, Bs (i + 1) := by
            rw [iUnion_congr]
            intro i
            rw [has, ← chapter_2.Bs, ← hbs]
      have :=
        calc
          Bs 0 ∪ f '' Astar
          _ = ⋃ i, Bs i := by rw [this, union_iUnion_nat_succ]
          _ = Bstar := by dsimp
      rw [this]
    have exp_1_5 : g '' Bstar = Astar :=
      calc
        g '' Bstar
        _ = g '' ⋃ i, Bs i := by dsimp
        _ = ⋃ i, g '' Bs i := by rw [chapter_1.exp_5_3]
        _ = ⋃ i, As i := by
          rw [iUnion_congr]
          intro i
          rw [hbs, ← chapter_2.As]
        _ = Astar := by dsimp

    have Fres : BijOn f Ares Bres := by
      have ⟨hfa_in_b, hb_in_fa⟩ := Subset.antisymm_iff.mp exp_1_4
      constructor
      . exact mapsTo'.mpr hfa_in_b
      . constructor
        . intro a _ a' _ hf
          exact hinjf hf
        . exact hb_in_fa
    have Gstar : BijOn g Bstar Astar := by
      have ⟨hgb_in_a, ha_in_gb⟩ := Subset.antisymm_iff.mp exp_1_5
      constructor
      . exact mapsTo'.mpr hgb_in_a
      . constructor
        . intro b _ b' _ hg
          exact hinjg hg
        . exact ha_in_gb

    set fstar := invFunOn g Bstar
    have : InvOn fstar g Bstar Astar := BijOn.invOn_invFunOn Gstar
    have Fstar : BijOn fstar Astar Bstar := (bijOn_comm this).mpr Gstar

    -- Classicalをopenしないと宣言できない
    set F : A → B := λ a ↦ if a ∈ Ares then f a else fstar a with hF
    have : Bijective F := by
      apply bijective_iff_bijOn_univ.mpr
      rw [← Auniv, ← Buniv]
      have bijon_ares := by
        have : EqOn f F Ares := by
          intro a hainres
          rw [hF]
          simp only [hainres]
          rw [ite_true]
        exact (EqOn.bijOn_iff this).mp Fres
      have bijon_astar := by
        have : EqOn fstar F Astar := by
          intro a hainstar
          rw [hF]
          simp only [Ain a hainstar]
          rw [ite_false]
        exact (EqOn.bijOn_iff this).mp Fstar

      apply @BijOn.union _ _ Ares Astar Bres Bstar F
      . exact bijon_ares
      . exact bijon_astar
      . have ⟨mapsto_ares, injon_ares, _⟩ := bijon_ares
        have ⟨mapsto_astar, injon_astar, _⟩ := bijon_astar
        apply (injOn_union _).mpr
        constructor
        . exact injon_ares
        . constructor
          . exact injon_astar
          . intro a hres a' hstar
            apply disjoint_iff_forall_ne.mp Bdisjoint
            . rw [← chapter_1.exp_2_13 Astar, ← chapter_1.exp_2_13 Bstar, compl_eq_univ_diff Astar, compl_eq_univ_diff Bstar, ← hAres, ← hBres] at mapsto_astar
              exact (@MapsTo.mem_iff _ _ _ _ _ mapsto_ares mapsto_astar a).mpr hres
            . rw [hAres, hBres, ← compl_eq_univ_diff, ← compl_eq_univ_diff] at mapsto_ares
              exact (@MapsTo.mem_iff _ _ _ _ _ mapsto_astar mapsto_ares a').mpr hstar
        . exact Adisjoint
    use F

theorem thoerem_2' : (∃ f : A → B, Injective f) ∧ (∃ f' : A → B, Surjective f') → (A ~ B) := by
  rintro ⟨hf, hf'⟩
  have := chapter_1.part_E_1.mpr hf'
  exact theorem_2 ⟨hf, this⟩

theorem theorem_2'' : (∃ f : A → B, Surjective f) ∧ (∃ g : B → A, Surjective g) → (A ~ B) := by
  rintro ⟨hf, hg⟩
  have hg' := chapter_1.part_E_1.mpr hf
  have hf' := chapter_1.part_E_1.mpr hg
  exact theorem_2 ⟨hf', hg'⟩

theorem theorem_2''' : (∃ B₁ : Set B, A ~ B₁) ∧ (∃ A₁ : Set A, B ~ A₁) → (A ~ B) := by
  rintro ⟨⟨B₁, ⟨f', ⟨hab₁, _⟩⟩⟩, ⟨A₁, ⟨g', ⟨hba₁, _⟩⟩⟩⟩
  have ⟨emB₁, hemB₁⟩ := Embedding.subtype B₁
  have ⟨emA₁, hemA₁⟩ := Embedding.subtype A₁
  set f := emB₁ ∘ f'
  set g := emA₁ ∘ g'
  have hinjf : Injective f := chapter_1.theorem_5_2 f' emB₁ ⟨hab₁, hemB₁⟩
  have hinjg : Injective g := chapter_1.theorem_5_2 g' emA₁ ⟨hba₁, hemA₁⟩
  exact theorem_2 ⟨⟨f, hinjf⟩, ⟨g, hinjg⟩⟩

end part_B

section part_C

variable {A B : Type u}

theorem part_1_C_1: (A ~ B) ↔ #A = #B := part_1_A_1.trans Cardinal.eq.symm

theorem part_1_C_2 : #ℕ = ℵ₀ := mk_nat

def ℵ := #ℝ

end part_C

section part_D

theorem part_D_i {B} (B₁ : Set B) : #B₁ ≤ #B := mk_set_le B₁

theorem part_D_ii (B₁ : Set B) : (A ~ B₁) → #A ≤ #B := by
  intro h
  have : #A = #B₁ := part_1_C_1.mp h
  rw [this]
  apply part_D_i

section

variable {f : A → B} (hf : Injective f)

theorem part_D_ii' : #A ≤ #B := mk_le_of_injective hf

variable {𝔪 𝔫 : Cardinal} {h𝔪 : #A = 𝔪} {h𝔫 : #B = 𝔫}

theorem part_D_iii : 𝔪 ≤ 𝔫 := by
  rw [← h𝔪, ← h𝔫]
  apply part_D_ii' hf

theorem part_1_D_1 {A' B' : Type u} {h𝔪' : #A' = 𝔪} {h𝔫' : #B' = 𝔫} : ∃ f' : A' → B', Injective f' := by
  have : #A' = #A := h𝔪'.trans h𝔪.symm
  have ⟨φ, ⟨hinjφ, _⟩⟩ := part_1_C_1.mpr this
  have : #B = #B' := h𝔫.trans h𝔫'.symm
  have ⟨ψ, ⟨hinjψ, _⟩⟩ := part_1_C_1.mpr this
  use ψ ∘ f ∘ φ
  apply chapter_1.theorem_5_2
  constructor
  . apply chapter_1.theorem_5_2 φ f ⟨hinjφ, hf⟩
  . exact hinjψ

end

theorem part_1_D_2 {𝔪 𝔫 : Cardinal} {h𝔪 : #A = 𝔪} {h𝔫 : #B = 𝔫} : 𝔪 ≤ 𝔫 ↔ ∃ f : B → A, Surjective f := by
  symm
  apply chapter_1.part_E_1.symm.trans
  constructor
  . rintro ⟨f, hinjf⟩
    apply @part_D_iii _ _ _ hinjf _ _ h𝔪 h𝔫
  rintro h
  rw [← h𝔪, ← h𝔫] at h
  have ⟨f, hf⟩ := (Cardinal.le_def A B).mp h
  use f

theorem part_1_D_3 {m n : ℕ} : (m : Cardinal) ≤ n ↔ m ≤ n := natCast_le

section theorem_3

variable {A B C : Type u} {𝔪 𝔫 𝔭 : Cardinal} {h𝔪 : #A = 𝔪} {h𝔫 : #B = 𝔫} {h𝔭 : #C = 𝔭}
variable [Nonempty B]

theorem exp_1_6 : 𝔪 ≤ 𝔪 := by
  rw [← h𝔪]

theorem exp_1_7 : 𝔪 ≤ 𝔫 ∧ 𝔫 ≤ 𝔪 → 𝔪 = 𝔫 := by
  rintro ⟨hmn, hnm⟩
  rw [← h𝔪, ← h𝔫] at *
  have ⟨f, hf⟩ := (Cardinal.le_def A B).mp hmn
  have ⟨g, hg⟩ := (Cardinal.le_def B A).mp hnm
  have : A ~ B := theorem_2 ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  apply part_1_C_1.mp this

theorem exp_1_8 : 𝔪 ≤ 𝔫 ∧ 𝔫 ≤ 𝔭 → 𝔪 ≤ 𝔭 := by
  rintro ⟨hmn, hnp⟩
  rw [← h𝔪, ← h𝔫, ← h𝔭] at *
  have ⟨f, hf⟩ := (Cardinal.le_def A B).mp hmn
  have ⟨g, hg⟩ := (Cardinal.le_def B C).mp hnp
  apply (Cardinal.le_def A C).mpr
  use g ∘ f
  apply chapter_1.theorem_5_2 f g ⟨hf, hg⟩

end theorem_3

end part_D

namespace exercise_1_1

theorem ex_2 {A} {X Y Z : Set A} [Nonempty Y] [Nonempty Z] (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) (hXZeq : X ~ Z) : (X ~ Y) ∧ Y ~ Z := by
  have ⟨f, hf⟩ := embeddingOfSubset X Y hXY
  have ⟨g, hg⟩ := embeddingOfSubset Y Z hYZ
  have ⟨h, ⟨hinj, _⟩⟩ := theorem_1_2 hXZeq
  constructor
  . apply theorem_2 ⟨⟨f, hf⟩, _⟩
    use h ∘ g
    apply chapter_1.theorem_5_2 _ _ ⟨hg, hinj⟩
  . apply theorem_2 ⟨⟨g, hg⟩, _⟩
    use f ∘ h
    apply chapter_1.theorem_5_2 _ _ ⟨hinj, hf⟩

theorem ex_3 {a b : ℝ} (A : Set ℝ) [Nonempty A]: {x | a < x ∧ x < b} ⊆ A → A ~ (univ : Set ℝ) := by
  intro h
  have := ex_2 h (subset_univ A) example_5
  exact this.2

theorem ex_4 {A B : Type u} (hb: Nonempty B) : #(A × B) ≥ #A := by
  set f : A → A × B := λ (a : A) ↦ ⟨a, hb.some⟩ with hfdef
  apply @part_D_ii' _ _ f
  intro a a' hf
  simp only [hfdef] at hf
  rw [Prod.mk.injEq] at hf
  exact hf.1

theorem ex_5 {Λ X : Type u} {A : Λ → Set X}
    (hnonempty : ∀ i : Λ, Nonempty (A i)) (hnins : ∀ i' : Λ × Λ, i'.1 ≠ i'.2 → A i'.1 ∩ A i'.2 = ∅) :
    #(⋃ i, A i) ≥ #Λ := by
  -- set f : Λ → ⋃ i, A i := λ i ↦ mem_iUnion.mpr ⟨i, (hnonempty i).some.mem⟩
  sorry

theorem ex_6 {Λ X : Type u} {A : Λ → Set X} (hmore2 : ∀ i : Λ, #(A i) ≥ 2) :
    #(⋂ i, A i) ≥ #Λ :=
  sorry

theorem ex_7 {A B : Type u} : (∃ f : A → B, Surjective f) → ∃ R : Setoid A, B ~ Quotient R := by
  intro ⟨f, hsurf⟩
  set R : Setoid A := @chapter_1.example_3 _ _ f with hR
  set f_inv : Quotient R → B := λ a' ↦ f a'.out with hf_inv
  use R
  apply theorem_1_2
  use f_inv
  constructor
  . intro a'₁ a'₂ hf_inva
    simp [hf_inv] at hf_inva
    have := (chapter_1.part_6_D_2 a'₁.out a'₂.out).mpr hf_inva
    have := (chapter_1.part_6_D_1 a'₁.out a'₂.out).mpr this
    simp [chapter_1.φ] at this
    exact this
  intro b
  have ⟨a, hf⟩ := hsurf b
  use ⟦a⟧
  simp
  rw [Quotient.mk_out a]
  exact hf

end exercise_1_1

end chapter_2
