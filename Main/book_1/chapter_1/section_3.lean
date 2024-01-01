import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Card

open Set

variable {S} (A B C D : Set S)

section part_A

#check Set (A × B)

end part_A

section part_B

def map_equiv (Γ Γ' : A → B) : Prop := ∀ a : A, Γ a = Γ' a

end part_B

section part_C

def G {A B} (Γ : A → Set B) : Set (A × B) :=
  {⟨a, b⟩ | ∀ a : A, b ∈ Γ a}

variable (Γ : A → Set B)

theorem exp_3_1 {A B} (Γ : A → Set B) : ∀ a : A, Γ a = {b | ⟨a, b⟩ ∈ G Γ} := by
  intro a'
  rw [G]
  simp
  sorry

theorem exp_3_1' (Γ Γ': A → Set B) : G Γ = G Γ' → Γ = Γ' := by
  intro h
  ext a
  rw [exp_3_1 Γ, exp_3_1 Γ']
  simp
  rw [h]

theorem theorem_1 : ∀ G' : Set (A × B), ∃ Γ : A → Set B, G' = G Γ := by
  intro G'
  have Γ' : A → Set B := fun a ↦ {b | ⟨a, b⟩ ∈ G'}
  use Γ'
  ext ⟨a, b⟩
  calc
    ⟨a, b⟩ ∈ G'
    _ ↔ b ∈ Γ' a := sorry
    _ ↔ ⟨a, b⟩ ∈ G Γ' := sorry

def D' {A B} (Γ : A → Set B) : Set A :=
  {a | ∃ b : B, ⟨a, b⟩ ∈ G Γ}

def V' {A B} (Γ : A → Set B) : Set B :=
  {b | ∃ a : A, ⟨a, b⟩ ∈ G Γ}

end part_C

section part_D

variable {A B : Set S}
variable {Γ : A → Set B}

def inv_map (Γ : A → Set B) := fun b ↦ {a | b ∈ Γ a}

notation Γ "⁻¹" => inv_map Γ

theorem exp_3_2' : ∀ {a : A} {b : B}, b ∈ Γ a ↔ a ∈ (Γ⁻¹) b := by
  intro a b
  rw [inv_map]
  simp

theorem exp_3_3_1' : D' (Γ⁻¹) = V' Γ := by
  rw [D', V', G, G]
  sorry

theorem exp_3_3_2' : V' (Γ⁻¹) = D' Γ := by
  rw [D', V', G, G]
  sorry

theorem exp_3_4 : (Γ⁻¹)⁻¹ = Γ := by
  sorry

theorem part_D_1 : ∀ (b : B), (Γ⁻¹) b = ∅ ↔ b ∈ V' Γ := by
  sorry

end part_D

section part_E

variable {A B : Set S}

/--
Aの任意の元aに対して，Γ(a)はBのただ1つの元から成る集合である
-/
def IsMap (Γ : A → Set B) : Prop := ∀ (a : A), Subsingleton (Γ a)

/--
定理 2
A × Bの部分集合Gがある写像f : A → Bのグラフと成るためには、Gが次の条件(∗∗)を満たすことが必要十分である．

(∗∗) Aの任意の元aに対して，(a, b) ∈ GとなるようなBの元bがただ1つ存在する．
-/
theorem theorem_2 (f : A → Set B) (h : IsMap f) :
  ∀ G' : Set (A × B), G' = G f ↔ ∀ a : A, Subsingleton {b | ⟨a, b⟩ ∈ G'} := by
  intro G'
  rw [IsMap] at h
  constructor
  . intro hp
    rw [hp, G]
    convert h
    simp
    sorry
  . intro hp
    sorry

end part_E

namespace exercise_1_1_3

theorem ex_1 (m n : ℕ) (A : Finset S) (B : Finset S) (ha : A.card = m) (hb : B.card = n) (Γs : Finset (A → Set B)):
    Γs.card = n ^ m := by
  sorry

-- ex_2はスキップ

theorem ex_3 (Γ : A → Set B) : IsMap Γ ↔ D' Γ = univ ∧ ∀ (b b' : B), b ≠ b' → (Γ⁻¹) b ∩ (Γ⁻¹) b' = ∅ := by
  constructor
  . intro h
    constructor
    . show D' Γ = univ
      rw [IsMap] at h
      rw [D', G]
      sorry
    . intro b b' hn
      rw [inv_map, inv_map]
      rw [inter_def]
      sorry
  sorry

end exercise_1_1_3
