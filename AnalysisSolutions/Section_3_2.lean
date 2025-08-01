import Mathlib.Tactic
import AnalysisSolutions.Section_3_1

/-!
# Analysis I, Section 3.2

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be
as faithful as possible to the original text of Analysis I, Section 3.2. All numbering refers to
the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification)
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox
--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- this proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  obtain ⟨Ω, hΩ⟩ := h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  replace this := (hΩ _).mpr this
  contradiction

/-- Axiom 3.9 (Regularity ) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  obtain ⟨ x, h, h' ⟩ := SetTheory.regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS
  specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'
  simp at h'
  obtain ⟨ y, h1, h2 ⟩ := h'
  exact ⟨ y, h2, h1 ⟩

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  let P (x:Object) := x ≠ x
  have h' : ∃(A : Set), ∀ x : Object, x ∈ A ↔ P x := by
    apply h P
  obtain ⟨em, hem⟩ := h'
  use em
  intro x h''
  rw [hem] at h''
  unfold P at h''
  simp at h''

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  let P (y:Object) := y = x
  have h' : ∃(A : Set), ∀x:Object, x ∈ A ↔ P x := by
    apply h P
  obtain ⟨s, hs⟩ := h'
  use s

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  let P (y:Object) := y = x₁ ∨ y = x₂
  have h' : ∃(A : Set), ∀x:Object, x ∈ A ↔ P x := by
    apply h P
  obtain ⟨s, hs⟩ := h'
  use s

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  let P (y:Object) := y ∈ A ∨ y ∈ B
  have h' := h P
  obtain ⟨s, hs⟩ := h'
  use s

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  let Q (y:Object) := ∃h : y ∈ A, P ⟨y, h⟩
  have h' := h Q
  obtain ⟨s, hs⟩ := h'
  use s

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (_: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  let Q (y:Object) := ∃a:A, P a y
  have h' := h Q
  obtain ⟨s, hs⟩ := h'
  use s

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by sorry

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by sorry

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U:Set), ∀ x, x ∈ U := by
  constructor
  · intro h
    let P (x:Object) := x = x
    have h' := h P
    obtain ⟨U,hU⟩ := h'
    use U
    intro x
    rw [hU]
  · sorry

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  by_contra! h
  rw [← univ_iff] at h
  apply Russells_paradox
  exact h

end Chapter3
