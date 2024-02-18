import Main.book_1.chapter_1.section_4

open Set Function Bool

namespace chapter_1

-- part_A, Bには特に何もなし

section part_C

section set

variable {X Λ} (A : Λ → Set X) (B : Set X)

-- λ はラムダ関数用の予約語のため使えないため代わりにiを用いている
theorem part_C_1 : ⋃ i, A i = {x | ∃ i : Λ, x ∈ A i} := by
  ext x
  rw [mem_setOf]
  apply mem_iUnion.trans
  simp

theorem part_C_2 : ⋂ i, A i = {x | ∀ i : Λ, x ∈ A i} := by
  ext x
  rw [mem_setOf]
  apply mem_iInter.trans
  simp

theorem exp_5_1 : (⋃ i, A i) ∩ B = ⋃ i, A i ∩ B := by
  ext x
  simp only [part_C_1, mem_setOf]
  constructor
  . rintro ⟨hai, hb⟩
    rw [mem_setOf] at hai
    have ⟨i, hai⟩ := hai
    use i
    exact ⟨hai, hb⟩
  . rintro ⟨i, ⟨hai, hb⟩⟩
    constructor
    . rw [mem_setOf]
      use i
    . exact hb

theorem exp_5_1' : (⋂ i, A i) ∪ B = ⋂ i, A i ∪ B := by
  ext x
  simp only [part_C_2, mem_setOf]
  constructor
  . rintro (hai | hb) i
    . left
      rw [mem_setOf] at hai
      exact hai i
    . right
      exact hb
  . intro hai
    by_cases hb : x ∈ B
    . right
      exact hb
    . left
      rw [mem_setOf]
      intro i
      rcases hai i with (hai | hnb)
      . exact hai
      . contradiction

theorem exp_5_2 : (⋃ i, A i)ᶜ = ⋂ i, (A i)ᶜ := by
  ext x
  simp only [part_C_1, part_C_2, mem_setOf]
  rw [mem_compl_iff, mem_setOf, not_exists]
  constructor
  . intro h i
    rw [mem_compl_iff]
    exact h i
  . intro h i
    rw [← mem_compl_iff]
    exact h i

theorem exp_5_2' : (⋂ i, A i)ᶜ = ⋃ i, (A i)ᶜ := by
  ext x
  simp only [part_C_1, part_C_2, mem_setOf]
  rw [mem_compl_iff, mem_setOf, not_forall]
  constructor
  . rintro ⟨i, hnai⟩
    use i
    rw [mem_compl_iff]
    exact hnai
  . rintro ⟨i, hnai⟩
    use i
    rw [← mem_compl_iff]
    exact hnai

end set

section function

variable {A B Λ M} (P : Λ → Set A) (Q : M → Set B) (f : A → B)

theorem exp_5_3 : f '' ⋃ i, P i = ⋃ i, f '' P i := by
  ext x
  simp only [image, part_C_1, mem_setOf]
  constructor
  . rintro ⟨a, ⟨i, hp⟩, h⟩
    use i
    use a
  . rintro ⟨i, a, ⟨hp, ha⟩⟩
    use a
    constructor
    . use i
    . exact ha

theorem exp_5_4 : f '' ⋂ i, P i ⊆ ⋂ i, f '' P i := by
  intro x
  simp only [image, part_C_2, mem_setOf]
  rintro ⟨a, hp, hf⟩ i
  use a
  exact ⟨hp i, hf⟩

theorem exp_5_3' : f ⁻¹' ⋃ μ, Q μ = ⋃ μ, f ⁻¹' Q μ := by
  ext x
  simp only [preimage, part_C_1, mem_setOf]

theorem exp_5_4' : f ⁻¹' ⋂ μ, Q μ = ⋂ μ, f ⁻¹' Q μ := by
  ext x
  simp only [preimage, part_C_2, mem_setOf]

end function

end part_C

section part_D

variable {X Λ : Type*} (A : Λ → Set X)


theorem axiom_of_choice : (∀ i : Λ, A i ≠ ∅) → univ.pi A ≠ ∅ := by
  contrapose
  simp only [not_forall, ne_eq, Classical.not_not]
  intro h
  exact univ_pi_eq_empty_iff.mp h

def pr (i : Λ) (a : ∀ j, A j) : A i := a i

end part_D

section part_E

variable {A B : Type*} (f : A → B)

def A' := λ b ↦ f ⁻¹' {b}
def f' := codRestrict f (range f) (by simp)

theorem theorem_7_a : Surjective f ↔ ∃ s : B → A, f ∘ s = id := by
  constructor
  . intro hsurf
    rw [part_B_2' f] at hsurf
    have ⟨s, hs⟩ : ∃ s : B → A, ∀ b : B, s b ∈ A' f b := by
      have : univ.pi (A' f) ≠ ∅ := by
        apply axiom_of_choice
        intro b
        have := hsurf b
        rw [A']
        exact this
      sorry
    use s
    ext b
    have := hs b
    rw [A', mem_preimage, mem_singleton_iff] at this
    calc
      (f ∘ s) b
      _ = f (s b) := by dsimp
      _ = b := this
      _ = id b := by dsimp
  . rintro ⟨s, hfs⟩ b
    use s b
    have := funext_iff.mp hfs b
    exact this

theorem theorem_7_b : Injective f ↔ ∃ r : B → A, r ∘ f = id := by
  constructor
  . intro hinjf
    have : Bijective (f' f) := by
      constructor
      . intro a₁ a₂ hf'
        apply hinjf
        calc
          f a₁
          _ = f' f a₁ := rfl
          _ = f' f a₂ := by rw [hf']
          _ = f a₂ := rfl
      . apply range_iff_surjective.mp
        rw [f']
        sorry
    have a₀ : A := by
      -- apply Classical.choose _
      sorry
    -- have r : B → A := λ b ↦ if b ∈ range f then f' f b else a₀
    sorry
  . rintro ⟨r, hr⟩ a₁ a₂ hf
    have := funext_iff.mp hr
    calc
      a₁
      _ = (r ∘ f) a₁ := by rw [this a₁]; dsimp
      _ = r (f a₁) := by dsimp
      _ = r (f a₂) := by rw [hf]
      _ = (r ∘ f) a₂ := by dsimp
      _ = a₂ := by rw [this a₂]; dsimp

theorem part_E_1 : (∃ ψ : A → B, Injective ψ) ↔ ∃ φ : B → A, Surjective φ := by
  constructor
  . rintro ⟨ψ, hinjpi⟩
    have ⟨φ, hphi⟩ := (theorem_7_b ψ).mp hinjpi
    use φ
    exact (theorem_7_a φ).mpr ⟨ψ, hphi⟩
  . rintro ⟨φ, hsurphi⟩
    have ⟨ψ, hpi⟩ := (theorem_7_a φ).mp hsurphi
    use ψ
    apply (theorem_7_b ψ).mpr ⟨φ, hpi⟩

end part_E

-- part_F には数式なし

namespace exercise_1_5

-- 1は実例系なので対象外、2~4は実施済み

section ex_5

variable {X Λ M} {A : Λ → Set X} {B : M → Set X}

-- 積の和集合はカリー化されている？
theorem ex_5_a : (⋃ i, A i) ∩ (⋃ μ, B μ) = ⋃ (i) (μ), A i ∩ B μ := by
  rw [exp_5_1]
  simp only [part_C_1]
  ext x
  simp only [mem_setOf]
  constructor
  . rintro ⟨i, ⟨hai, hbm⟩⟩
    rw [mem_setOf] at hbm
    have ⟨μ, hbm⟩ := hbm
    use i
    use μ
    exact ⟨hai, hbm⟩
  . rintro ⟨i, μ, ⟨hai, hbm⟩⟩
    use i
    constructor
    . exact hai
    . rw [mem_setOf]
      use μ

theorem ex_5_b : (⋂ i, A i) ∪ (⋂ μ, B μ) = ⋂ (i) (μ), A i ∪ B μ := by
  rw [exp_5_1']
  simp only [part_C_2]
  ext x
  simp only [mem_setOf]
  constructor
  . rintro h i μ
    by_cases hb : x ∈ A i
    . left
      exact hb
    . right
      rcases (h i) with (ha | hb)
      . contradiction
      . rw [mem_setOf] at hb
        exact hb μ
  . intro h i
    by_cases hb : x ∈ A i
    . left
      exact hb
    . right
      rw [mem_setOf]
      intro μ
      rcases (h i μ) with (ha | hb)
      . contradiction
      . exact hb

theorem ex_5_c : (⋃ i, A i) ×ˢ (⋃ μ, B μ) = ⋃ i : Λ × M, A i.1 ×ˢ B i.2 := by
  simp only [part_C_1]
  ext x
  simp only [mem_prod, mem_setOf_eq, Prod.exists, exists_and_left, exists_and_right]

theorem ex_lemma_1 {Λ α β} {A : Λ → Set α} {B : Set β} [Nonempty Λ]: (⋂ i, A i) ×ˢ B = ⋂ i, A i ×ˢ B := by
  ext
  simp only [mem_prod, mem_iInter]
  constructor
  . intro ⟨hai, hb⟩ i
    exact ⟨hai i, hb⟩
  . intro h
    constructor
    . intro i
      exact (h i).1
    . have i := Classical.arbitrary Λ
      have ⟨_, hb⟩ := h i
      exact hb

theorem ex_5_d {Λ M α β} {A : Λ → Set α} {B : M → Set β} [Nonempty Λ] [Nonempty M]: (⋂ i, A i) ×ˢ (⋂ μ, B μ) = ⋂ i : Λ × M, A i.1 ×ˢ B i.2 := by
  ext
  simp only [mem_prod, mem_iInter, Prod.forall]
  constructor
  . intro ⟨hai, hbm⟩ i μ
    exact ⟨hai i, hbm μ⟩
  . intro h
    constructor
    . intro i
      have μ := Classical.arbitrary M
      exact (h i μ).1
    . intro μ
      have i := Classical.arbitrary Λ
      exact (h i μ).2

end ex_5

#print axioms ex_5_d


-- 定義域の縮小がうまく噛み合わないためスキップ
-- theorem ex_6 {Λ X Y} {A : Λ → Set X} {B : Set Y} {h : ∀ i : Λ × Λ, i.1 ≠ i.2 → A i.1 ∩ A i.2 = ∅} {f : (i : Λ) → A i → B} :
--     ∀ g g' : (⋃ i, A i) → B,  (∀ (i : Λ), ∀ a ∈ f i ⁻¹' univ, f i a = g a ∧ f i a = g' a) → g = g' := by
--   sorry

theorem ex_7 {Λ X} {A : Λ → Set X} {h : ∀ i : Λ, A i ≠ ∅} {i : Λ} : ∀ a ∈ univ.pi A, Surjective (pr A i) := by
  intro a hinc ai
  -- hから各A iがNonemptyであることを示してClassical.arbitraryする
  sorry
section

variable {Λ X} {A B : Λ → Set X}

theorem ex_8 {h : ∀ i, A i ≠ ∅} : univ.pi A ⊆ univ.pi B ↔ ∀ i, A i ⊆ B i := by
  constructor
  . intro hpi i x ha
    simp [pi] at hpi
    have ai := λ (_ : Λ) ↦ x
    have := hpi ai
    sorry
  . intro hi x
    simp
    intro hai i
    have hxi := hai i
    have := hi i
    exact this hxi

theorem ex_9 : (univ.pi A) ∩ (univ.pi B) = univ.pi (λ i ↦ A i ∩ B i) := by
  simp [pi]
  apply Subset.antisymm
  . rintro a ⟨ha, hb⟩
    simp [mem_setOf] at *
    intro i
    exact ⟨ha i, hb i⟩
  . intro a h
    simp [mem_setOf] at *
    constructor
    . intro i
      exact (h i).1
    . intro i
      exact (h i).2

end

section

variable {Λ X Y} {A : Λ → Set X} {B : Λ → Set Y} {f : ∀ i, A i → B i}

def f_all (a : ∀ i, A i) : ∀ j, B j := λ i ↦ f i (a i)

-- f_allがカリー化されているためかSurjective, Injectiveがうまいこと効かない
-- theorem ex_10_1 : @Surjective (∀ i, A i) (∀ j, B j) f_all ↔ ∀ i, Surjective (f i) := by
--   sorry

-- theorem ex_10_2 : @Injective (∀ i, A i) (∀ j, B j) f_all ↔ ∀ i, Injective (f i) := by
--   sorry

end

theorem ex_11 {A B : Type*} {f : A → B} {hsurf : Surjective f} {s s' : B → A} {hris : RightInverse s f} {hris' : RightInverse s' f} :
    range s ⊆ range s' → s = s' := by
  intro h
  ext x
  rw [Function.RightInverse, LeftInverse] at *
  rw [Surjective] at hsurf
  have hris_ := hris x
  have hris'_ := hris' x
  have ⟨a, ha⟩ := hsurf x
  rw [subset_def] at h
  simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at h
  have ⟨x', hx'⟩ := h (f (s' x))
  have : Injective s' := by
    apply (theorem_7_b s').mpr
    use f
    exact funext_iff.mpr hris'
  rw [Injective] at this
  have : x = x' := by
    apply this
    rw [hx']
    sorry
  calc
    s x
    _ = s (f (s' x)) := by rw [hris'_]
    _ = s' x' := by rw [hx']
    _ = s' x := by rw [this]

section ex_12

variable {A B C : Type*} {f : A → B} {f' : B → C}

theorem ex_12_a {hf : Surjective f} {hf' : Surjective f'} {s : B → A} {hs : RightInverse s f} {s' : C → B} {hs' : RightInverse s' f'} :
    RightInverse (s ∘ s') (f' ∘ f) := by
  simp [Function.RightInverse, LeftInverse] at *
  intro c
  calc
    f' (f (s (s' c)))
    _ = f' (s' c) := by rw [hs]
    _ = c := hs' c

theorem ex_12_b {hf : Injective f} {hf' : Injective f'} {r : B → A} {hr : LeftInverse r f} {r' : C → B} {hr' : LeftInverse r' f'} :
    LeftInverse (r ∘ r') (f' ∘ f) := by
  intro a
  calc
    (r ∘ r') ((f' ∘ f) a)
    _ = r (r' (f' (f a))) := by dsimp
    _ = r (f a) := by rw [hr']
    _ = a := hr a

end ex_12

theorem ex_13 {A B C : Type*} {g : B → C} {h : A → C} : (∃ f : A → B, h = g ∘ f) ↔ range h ⊆ range g := by
  constructor
  . rintro ⟨f, hf⟩ c hx
    simp [mem_range] at *
    have ⟨a, ha⟩ := hx
    use (f a)
    have := funext_iff.mp hf a
    dsimp at this
    rw [← this, ha]
  . intro hr
    simp only [subset_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hr
    -- なぜか分解ができない
    -- have f : A → B := λ a ↦ (hr a).1
    sorry

theorem ex_14 {A B C : Type*} {f : A → B} {h : A → C} [Nonempty C] : (∃ g : B → C, h = g ∘ f) ↔ ∀ a a' : A, f a = f a' → h a = h a' := by
  constructor
  . rintro ⟨g, hg⟩ a a' hfa
    rw [hg]
    dsimp
    rw [hfa]
  . intro hfha
    -- 関数では分割ができない？
    -- have b : B → C := by
    --   intro b
    --   by_cases hb : b ∈ range f
    --   . rw [mem_range] at hb
    --     have ⟨a, ha⟩ := hb
    sorry

section

variable {A A' B B' : Type*} {u : A' → A} {v : B → B'}

def phi (f : A → B) : A' → B' := v ∘ f ∘ u

-- phiがカリー化されているためかうまく型が定義できない
-- theorem ex_15_a : Surjective u → Injective v → @Injective (A → B) (A' → B') phi := by
--   sorry

end

end exercise_1_5

end chapter_1
