import Mathlib.Tactic

/-!
# Analysis I, Section 3.1

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be
as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to
the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

-/

namespace Chapter3

/- The ability to work in multiple universe is not relevant immediately, but
becomes relevant when constructing models of set theory in the Chapter 3 epilogue. -/
universe u v

/-- The axioms of Zermelo-Frankel theory with atoms  -/
class SetTheory where
  Set : Type u -- Axiom 3.1
  Object : Type v -- Axiom 3.1
  set_to_object : Set ↪ Object -- Axiom 3.1
  mem : Object → Set → Prop -- Axiom 3.1
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y -- Axiom 3.2
  emptyset: Set -- Axiom 3.3
  emptyset_mem x : ¬ mem x emptyset -- Axiom 3.3
  singleton : Object → Set -- Axiom 3.4
  singleton_axiom x y : mem x (singleton y) ↔ x = y -- Axiom 3.4
  union_pair : Set → Set → Set -- Axiom 3.5
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y) -- Axiom 3.5
  specify A (P: Subtype (mem . A) → Prop) : Set -- Axiom 3.6
  specification_axiom A (P: Subtype (mem . A) → Prop) :
    (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x -- Axiom 3.6
  replace A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : Set -- Axiom 3.7
  replacement_axiom A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y -- Axiom 3.7
  nat : Set -- Axiom 3.8
  nat_equiv : ℕ ≃ Subtype (mem . nat) -- Axiom 3.8
  regularity_axiom A (hA : ∃ x, mem x A) :
    ∃ x, mem x A ∧ ∀ S, x = set_to_object S → ¬ ∃ y, mem y A ∧ mem y S -- Axiom 3.9
  pow : Set → Set → Set -- Axiom 3.11
  function_to_object (X: Set) (Y: Set) :
    (Subtype (mem . X) → Subtype (mem . Y)) ↪ Object -- Axiom 3.11
  powerset_axiom (X: Set) (Y: Set) (F:Object) :
    mem F (pow X Y) ↔ ∃ f: Subtype (mem . Y) → Subtype (mem . X),
    function_to_object Y X f = F -- Axiom 3.11
  union : Set → Set -- Axiom 3.12
  union_axiom A x : mem x (union A) ↔ ∃ S, mem x S ∧ mem (set_to_object S) A -- Axiom 3.12

export SetTheory (Set Object)

-- This instance implicitly imposes the axioms of Zermelo-Frankel set theory with atoms.
variable [SetTheory] (y z : Object) (X Y A : Set)

/-!
Main constructions and results of this section:

- A type `Chapter3.SetTheory.Set` of sets
- A type `Chapter3.SetTheory.Object` of objects
- An axiom that every set is (or can be coerced into) an object
- The empty set `∅`, singletons `{y}`, and pairs `{y,z}` (and more general finite tuples), with
  their attendant axioms
- Pairwise union `X ∪ Y`, and their attendant axioms
- Coercion of a set `A` to its associated type `A.toSubtype`, which is a subtype of `Object`, and
  basic API.  (This is a technical construction needed to make the Zermelo-Frankel set theory
  compatible with the dependent type theory of Lean.)
- The specification `A.specify P` of a set `A` and a predicate `P: A.toSubtype → Prop` to the
  subset of elements of `A` obeying `P`, and the axiom of specification.
  TODO: somehow implement set builder elaboration for this.
- The replacement `A.replace hP` of a set `A` via a predicate
  `P: A.toSubtype → Object → Prop` obeying a uniqueness condition
  `∀ x y y', P x y ∧ P x y' → y = y'`, and the axiom of replacement.
- A bijective correspondence between the Mathlib natural numbers `ℕ` and a set
  `Chapter3.Nat : Chapter3.Set` (the axiom of infinity).
- Axioms of regularity, power set, and union (used in later sections of this chapter, but not
  required here)
- Connections with Mathlib's notion of a set

The other axioms of Zermelo-Frankel set theory are discussed in later sections.

Some technical notes:
- Mathlib of course has its own notion of a `Set`, which is not compatible with the notion
  `Chapter3.Set` defined here, though we will try to make the notations match as much as
  possible.  This causes some notational conflict: for instance, one may need to explicitly
  specify `(∅:Chapter3.Set)` instead of just `∅` to indicate that one is using the `Chapter3.Set`
  version of the empty set, rather than the Mathlib version of the empty set, and similarly for
  other notation defined here.
- In Analysis I, we chose to work with an "impure" set theory, in which there could be more
  `Object`s than just `Set`s.  In the type theory of Lean, this requires treating `Chapter3.Set`
  and `Chapter3.Object` as distinct types. Occasionally this means we have to use a coercion
  `(X: Chapter3.Object)` of a `Chapter3.Set` `X` to make into a `Chapter3.Object`: this is
  mostly needed when manipulating sets of sets.
- After this chapter is concluded, the notion of a `Chapter3.SetTheory.Set` will be deprecated in
  favor of the standard Mathlib notion of a `Set` (or more precisely of the type `Set X` of a set
  in a given type `X`).  However, due to various technical incompatibilities between set theory
  and type theory, we will not attempt to create a full equivalence between these two
  notions of sets. (As such, this makes this entire chapter optional from the point of view of
  the rest of the book, though we retain it for pedagogical purposes.)
-/


/-- Definition 3.1.1 (objects can be elements of sets) -/
instance objects_mem_sets : Membership Object Set where
  mem X x := SetTheory.mem x X

-- Now we can use the `∈` notation between our `Object` and `Set`.
example (X: Set) (x: Object) : Prop := x ∈ X

/-- Axiom 3.1 (Sets are objects)-/
instance sets_are_objects : Coe Set Object where
  coe X := SetTheory.set_to_object X

-- Now we can treat a `Set` as an `Object` when needed.
example (X Y: Set) : Prop := (X: Object) ∈ Y

/-- Axiom 3.1 (Sets are objects)-/
theorem SetTheory.Set.coe_eq {X Y:Set} (h: (X: Object) = (Y: Object)) : X = Y :=
  SetTheory.set_to_object.inj' h

/-- Axiom 3.1 (Sets are objects)-/
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y:Set) : (X: Object) = (Y: Object) ↔  X = Y := by
  constructor
  . exact coe_eq
  intro h; subst h; rfl

/-- Axiom 3.2 (Equality of sets)-/
abbrev SetTheory.Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := SetTheory.extensionality _ _ h

/-- Axiom 3.2 (Equality of sets)-/
theorem SetTheory.Set.ext_iff (X Y: Set) : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y := by
  constructor
  . intro h; subst h; simp
  . exact ext

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := SetTheory.emptyset

-- Now we can use the `∅` notation to refer to `SetTheory.emptyset`.
example : ∅ = SetTheory.emptyset := by rfl

-- Make everything we define in `SetTheory.Set.*` accessible directly.
open SetTheory.Set

/--
  Axiom 3.3 (empty set).
  Note: in some applications one may have to explicitly cast ∅ to Set due to
  Mathlib's existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅:Set) := SetTheory.emptyset_mem

/-- Empty set has no elements -/
-- ex
theorem SetTheory.Set.eq_empty_iff_forall_notMem {X:Set} : X = ∅ ↔ (∀ x, x ∉ X) := by
  constructor
  · intro h x
    rw [h]
    apply emptyset_mem x
  · intro h
    rw [SetTheory.Set.ext_iff]
    intros x
    constructor
    · intro h'
      apply h at h'
      contradiction
    · intros h'
      apply SetTheory.emptyset_mem at h'
      contradiction

/-- Empty set is unique -/
-- ex
theorem SetTheory.Set.empty_unique : ∃! (X:Set), ∀ x, x ∉ X := by
  apply existsUnique_of_exists_of_unique
  · use ∅
    apply SetTheory.Set.not_mem_empty
  · intros y₁ y₂ h₁ h₂
    rw [← SetTheory.Set.eq_empty_iff_forall_notMem] at h₁
    rw [← SetTheory.Set.eq_empty_iff_forall_notMem] at h₂
    rw [h₁, h₂]


/-- Lemma 3.1.5 (Single choice) -/
lemma SetTheory.Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have claim (x:Object) : x ∈ X ↔ x ∈ (∅:Set) := by
    simp [this, not_mem_empty]
  replace claim := ext claim
  contradiction

theorem SetTheory.Set.nonempty_of_inhabited {X:Set} {x:Object} (h:x ∈ X) : X ≠ ∅ := by
  contrapose! h
  rw [eq_empty_iff_forall_notMem] at h
  exact h x

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := SetTheory.singleton

-- Now we can use the `{x}` notation for a single element `Set`.
example (x: Object) : Set := {x}

/--
  Axiom 3.3(a) (singleton).
  Note: in some applications one may have to explicitly cast {a} to Set due to Mathlib's
  existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a := by
  exact SetTheory.singleton_axiom x a


instance SetTheory.Set.instUnion : Union Set where
  union := SetTheory.union_pair

-- Now we can use the `X ∪ Y` notation for a union of two `Set`s.
example (X Y: Set) : Set := X ∪ Y

/-- Axiom 3.4 (Pairwise union)-/
@[simp]
theorem SetTheory.Set.mem_union (x:Object) (X Y:Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
  SetTheory.union_pair_axiom X Y x

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
theorem SetTheory.Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b} := by rfl

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
@[simp]
theorem SetTheory.Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  simp [pair_eq, mem_union, mem_singleton]

@[simp]
theorem SetTheory.Set.mem_triple (x a b c:Object) : x ∈ ({a,b,c}:Set) ↔ (x = a ∨ x = b ∨ x = c) := by
  simp [Insert.insert, mem_union, mem_singleton]

/-- Remark 3.1.8 -/
-- ex
theorem SetTheory.Set.singleton_uniq (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by
  apply existsUnique_of_exists_of_unique
  · exists ({a}:Set)
    intros x
    apply SetTheory.Set.mem_singleton
  · intros y₁ y₂ h₁ h₂
    rw [SetTheory.Set.ext_iff]
    intros x
    rw [h₁, h₂]

/-- Remark 3.1.8 -/
-- ex
theorem SetTheory.Set.pair_uniq (a b:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by
  apply existsUnique_of_exists_of_unique
  · exists ({a,b}:Set)
    intros x
    rw [SetTheory.Set.mem_pair]
  · intros y₁ y₂ h₁ h₂
    rw [SetTheory.Set.ext_iff]
    intros x
    rw [h₁, h₂]

/-- Remark 3.1.8 -/
-- ex
theorem SetTheory.Set.pair_comm (a b:Object) : ({a,b}:Set) = {b,a} := by
  rw [SetTheory.Set.ext_iff]
  intros x
  repeat rw [SetTheory.Set.mem_pair]
  rw [or_comm]

/-- Remark 3.1.8 -/
-- ex
theorem SetTheory.Set.pair_self (a:Object) : ({a,a}:Set) = {a} := by
  rw [SetTheory.Set.ext_iff]
  intros x
  rw [SetTheory.Set.mem_pair]
  simp

/-- Exercise 3.1.1 -/
-- ex

lemma actually_singleton {a b c : Object} (h: ({a,b}:Set) = {c}) : a = b := by
  rw [ext_iff] at h
  have h₀ : a = c := by
    specialize h a
    rcases h with ⟨mp, mpr⟩
    · have ha : a ∈ ({a,b}:Set) := by
        rw [mem_pair]; left; rfl
      apply mp at ha
      rw [mem_singleton] at ha; exact ha
  have h₁ : b = c := by
    specialize h b
    rcases h with ⟨mp, mpr⟩
    · have hb : b ∈ ({a,b}:Set) := by
        rw [mem_pair]; right; rfl
      apply mp at hb
      rw [mem_singleton] at hb; exact hb
  rw [h₀, h₁]

theorem SetTheory.Set.pair_eq_pair {a b c d:Object} (h: ({a,b}:Set) = {c,d}) :
    a = c ∧ b = d ∨ a = d ∧ b = c := by
  have h₁ : a ∈ ({c,d}:Set) := by
    rw [ext_iff] at h
    specialize h a
    simp at h
    rw [mem_pair]
    rcases h with hc|hd
    · left; exact hc
    · right; exact hd
  have h₂ : b ∈ ({c,d}:Set) := by
    rw [ext_iff] at h
    specialize h b
    simp at h
    rw [mem_pair]
    rcases h with hc|hd
    · left; exact hc
    · right; exact hd
  rw [mem_pair] at h₁
  rw [mem_pair] at h₂
  rcases h₁,h₂ with ⟨(hc|hd),(ha|hb)⟩
  · rw [hc, ha] at h
    rw [pair_self] at h
    symm at h
    apply actually_singleton at h
    left
    constructor
    · exact hc
    · rw [← h]; exact ha
  · left
    constructor
    · exact hc
    · exact hb
  · right
    constructor
    · exact hd
    · exact ha
  · rw [hd, hb] at h
    rw [pair_self] at h
    symm at h
    apply actually_singleton at h
    right
    constructor
    · exact hd
    · rw [h]; exact hb

abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {(empty: Object)}
abbrev SetTheory.Set.pair_empty : Set := {(empty: Object), (singleton_empty: Object)}

/-- Exercise 3.1.2-/
-- ex
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  by_contra! h
  rw [ext_iff] at h
  simp at h

/-- Exercise 3.1.2-/
-- ex
theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by
  by_contra! h
  rw [ext_iff] at h
  simp at h
  push_neg at h
  specialize h empty
  have h₁ := h.left
  simp at h₁

/-- Exercise 3.1.2-/
-- ex
theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  by_contra! h
  rw [ext_iff] at h
  simp at h
  rw [ext_iff] at h
  simp at h

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
-- ex
theorem SetTheory.Set.union_congr_left (A A' B:Set) (h: A = A') : A ∪ B = A' ∪ B := by
  rw [h]

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
-- ex
theorem SetTheory.Set.union_congr_right (A B B':Set) (h: B = B') : A ∪ B = A ∪ B' := by
  rw [h]

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
-- ex
theorem SetTheory.Set.singleton_union_singleton (a b:Object) :
    ({a}:Set) ∪ ({b}:Set) = {a,b} := by
  rw [pair_eq]


/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
-- ex
theorem SetTheory.Set.union_comm (A B:Set) : A ∪ B = B ∪ A := by
  apply ext
  intro x
  constructor
  · intro h
    rw [mem_union] at h
    rw [mem_union]
    rcases h with h|h
    · right; exact h
    · left; exact h
  · intro h
    rw [mem_union] at h
    rw [mem_union]
    rcases h with h|h
    · right; exact h
    · left; exact h


/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
-- ex
theorem SetTheory.Set.union_assoc (A B C:Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  -- this proof is written to follow the structure of the original text.
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    . rw [mem_union] at case1
      rcases case1 with case1a | case1b
      . rw [mem_union]; tauto
      have : x ∈ B ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto
    have : x ∈ B ∪ C := by rw [mem_union]; tauto
    rw [mem_union]; tauto
  · intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    · rw [mem_union]
      left; rw [mem_union]
      left; exact case1
    · rw [mem_union] at case2
      rcases case2 with case2' | case2''
      · rw [mem_union]; left
        rw [mem_union]; right; exact case2'
      · rw [mem_union]; right
        exact case2''

/-- Proposition 3.1.27(c) -/
-- ex
theorem SetTheory.Set.union_self (A:Set) : A ∪ A = A := by
  apply ext
  intro x
  constructor
  · intro hx
    rw [mem_union] at hx
    rcases hx with h|h
    · exact h
    · exact h
  · intro hx
    rw [mem_union]
    left; exact hx

/-- Proposition 3.1.27(a) -/
-- ex
theorem SetTheory.Set.union_empty (A:Set) : A ∪ ∅ = A := by
  apply ext
  intro x
  constructor
  · intro hx
    rw [mem_union] at hx
    rcases hx with h|h
    · exact h
    · apply not_mem_empty at h; contradiction
  · intro hx
    rw [mem_union]
    left; exact hx

/-- Proposition 3.1.27(a) -/
-- ex
theorem SetTheory.Set.empty_union (A:Set) : ∅ ∪ A = A := by
  rw [union_comm]
  apply union_empty

theorem SetTheory.Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c} := by
  rfl

/-- Example 3.1.10 -/
theorem SetTheory.Set.pair_union_pair (a b c:Object) :
    ({a,b}:Set) ∪ {b,c} = {a,b,c} := by
  apply ext
  intro x
  simp only [mem_union, mem_pair, mem_triple]
  tauto

/-- Definition 3.1.14.   -/
instance SetTheory.Set.instSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

-- Now we can use `⊆` for a subset relationship between two `Set`s.
example (X Y: Set) : Prop := X ⊆ Y

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

-- Now we can use `⊂` for a strict subset relationship between two `Set`s.
example (X Y: Set) : Prop := X ⊂ Y

/-- Definition 3.1.14. -/
theorem SetTheory.Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
theorem SetTheory.Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl



/-- Remark 3.1.15 -/
-- ex
theorem SetTheory.Set.subset_congr_left {A A' B:Set} (hAA':A = A') (hAB: A ⊆ B) : A' ⊆ B := by
  rw [hAA'] at hAB
  exact hAB


/-- Examples 3.1.16 -/
-- ex
theorem SetTheory.Set.subset_self (A:Set) : A ⊆ A := by
  rw [subset_def]
  simp


/-- Examples 3.1.16 -/
-- ex
-- This is how I would argue it on paper. Maybe a slicker way?
theorem SetTheory.Set.empty_subset (A:Set) : ∅ ⊆ A := by
  by_contra! h
  rw [subset_def] at h
  push_neg at h
  obtain ⟨x, hx⟩ := h
  have impossible := hx.left
  apply emptyset_mem at impossible
  exact impossible



/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C := by
  -- this proof is written to follow the structure of the original text.
  rw [subset_def]
  intro x hx
  rw [subset_def] at hAB
  replace hx := hAB x hx
  replace hx := hBC x hx
  assumption

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
-- ex
theorem SetTheory.Set.subset_antisymm (A B:Set) (hAB:A ⊆ B) (hBA:B ⊆ A) : A = B := by
  rw [ext_iff]
  intro x
  constructor
  · rw [subset_def] at hAB; apply hAB
  · rw [subset_def] at hBA; apply hBA


/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
-- ex
theorem SetTheory.Set.ssubset_trans (A B C:Set) (hAB:A ⊂ B) (hBC:B ⊂ C) : A ⊂ C := by
  rw [ssubset_def] at *
  have hAB_subset := hAB.left
  have hAB_ne := hAB.right
  have hBC_subset := hBC.left
  have hBC_ne := hBC.right
  constructor
  · apply subset_trans hAB_subset hBC_subset
  · by_contra! h
    rw [←h] at hBC_subset
    have hAB_eq : A = B := by
      apply subset_antisymm
      · exact hAB_subset
      · exact hBC_subset
    contradiction


/--
  This defines the subtype `A.toSubtype` for any `A:Set`.
  Note that `A.toSubtype` gives you a type, similar to how `Object` or `Set` are types.
  A value `x'` of type `A.toSubtype` combines some `x: Object` with a proof that `hx: x ∈ A`.

  To produce an element `x'` of this subtype, use `⟨ x, hx ⟩`, where `x: Object` and `hx: x ∈ A`.
  The object `x` associated to a subtype element `x'` is recovered as `x'.val`, and
  the property `hx` that `x` belongs to `A` is recovered as `x'.property`.
-/
abbrev SetTheory.Set.toSubtype (A:Set) := Subtype (fun x ↦ x ∈ A)

example (A: Set) (x: Object) (hx: x ∈ A) : A.toSubtype := ⟨x, hx⟩
example (A: Set) (x': A.toSubtype) : Object := x'.val
example (A: Set) (x': A.toSubtype) : x'.val ∈ A := x'.property

-- In practice, a subtype lets us carry an object with a membership proof as a single value.
-- Compare these two proofs. They are equivalent, but the latter packs `x` and `hx` into `x'`.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

instance : CoeSort (Set) (Type v) where
  coe A := A.toSubtype

-- Now instead of writing `x': A.toSubtype`, we can just write `x': A`.
-- Compare these three proofs. They are equivalent, but the last one reads most concisely.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property
example (A B: Set) (x': A) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

/--
  Elements of a set (implicitly coerced to a subtype) are also elements of the set
  (with respect to the membership operation of the set theory).
-/
lemma SetTheory.Set.subtype_property (A:Set) (x:A) : x.val ∈ A := x.property

lemma SetTheory.Set.subtype_coe (A:Set) (x:A) : x.val = x := rfl

lemma SetTheory.Set.coe_inj (A:Set) (x y:A) : x.val = y.val ↔ x = y := Subtype.coe_inj

/--
  If one has a proof `hx` of `x ∈ A`, then `A.subtype_mk hx` will then make the element of `A`
  (viewed as a subtype) corresponding to `x`.
-/
def SetTheory.Set.subtype_mk (A:Set) {x:Object} (hx:x ∈ A) : A := ⟨ x, hx ⟩

lemma SetTheory.Set.subtype_mk_coe {A:Set} {x:Object} (hx:x ∈ A) : A.subtype_mk hx = x := by rfl


abbrev SetTheory.Set.specify (A:Set) (P: A → Prop) : Set := SetTheory.specify A P

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom {A:Set} {P: A → Prop} {x:Object} (h: x ∈ A.specify P) :
    x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom' {A:Set} (P: A → Prop) (x:A.toSubtype) :
    x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom'' {A:Set} (P: A → Prop) (x:Object) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩ := by
  constructor
  . intro h
    use specification_axiom h
    simp [←specification_axiom' P, h]
  intro h
  obtain ⟨ h, hP ⟩ := h
  simp [←specification_axiom' P] at hP
  assumption

-- ex
theorem SetTheory.Set.specify_subset {A:Set} (P: A → Prop) : A.specify P ⊆ A := by
  rw [subset_def]
  intro x h
  use specification_axiom h

/-- This exercise may require some understanding of how  subtypes are implemented in Lean. -/
-- ex
theorem SetTheory.Set.specify_congr {A A':Set} (hAA':A = A') {P: A → Prop} {P': A' → Prop}
  (hPP': (x:Object) → (h:x ∈ A) → (h':x ∈ A') → P ⟨ x, h⟩ ↔ P' ⟨ x, h'⟩ ) :
    A.specify P = A'.specify P' := by
    dsimp [specify]
    rw [ext_iff]
    intro x
    constructor
    · intro h
      rw [specification_axiom''] at h
      obtain ⟨h, hP⟩ := h
      have h' : x ∈ A' := by
        rw [hAA'] at h
        exact h
      have hP' : P' ⟨x, h'⟩ := by
       rw [hPP' x h h'] at hP; exact hP
      rw [specification_axiom'']
      use h'
    · intro h
      rw [specification_axiom''] at h
      obtain ⟨h', hP'⟩ := h
      have h : x ∈ A := by rw [←hAA'] at h'; exact h'
      have hP : P ⟨x, h⟩ := by
        rw [← hPP' x h h'] at hP'; exact hP'
      rw [specification_axiom'']
      use h

instance SetTheory.Set.instIntersection : Inter Set where
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

-- Now we can use the `X ∩ Y` notation for an intersection of two `Set`s.
example (X Y: Set) : Set := X ∩ Y

/-- Definition 3.1.22 (Intersections) -/
@[simp]
theorem SetTheory.Set.mem_inter (x:Object) (X Y:Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∈ Y) ⟨ x,hX⟩).mpr hY

instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

-- Now we can use the `X \ Y` notation for a difference of two `Set`s.
example (X Y: Set) : Set := X \ Y

/-- Definition 3.1.26 (Difference sets) -/
@[simp]
theorem SetTheory.Set.mem_sdiff (x:Object) (X Y:Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩ ).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∉ Y) ⟨ x, hX⟩ ).mpr hY

/-- Proposition 3.1.27(d) / Exercise 3.1.6 -/
-- ex
theorem SetTheory.Set.inter_comm (A B:Set) : A ∩ B = B ∩ A := by
  rw [ext_iff]
  intro x
  constructor
  · intro h
    rw [mem_inter]
    rw [mem_inter, and_comm] at h
    exact h
  · intro h
    rw [mem_inter]
    rw [mem_inter, and_comm] at h
    exact h

/-- Proposition 3.1.27(b) -/
-- ex
theorem SetTheory.Set.subset_union {A X: Set} (hAX: A ⊆ X) : A ∪ X = X := by
  rw [ext_iff]
  intro x
  constructor
  · intro h
    rw [mem_union] at h
    rcases h with ha|hx
    · apply hAX at ha; exact ha
    · exact hx
  · intro h
    rw [mem_union]
    right; exact h

/-- Proposition 3.1.27(b) -/
-- ex
theorem SetTheory.Set.union_subset {A X: Set} (hAX: A ⊆ X) : X ∪ A = X := by
  rw [union_comm]
  apply subset_union
  exact hAX


/-- Proposition 3.1.27(c) -/
-- ex
theorem SetTheory.Set.inter_self (A:Set) : A ∩ A = A := by
  rw [ext_iff]
  intro x
  constructor
  · intro h
    rw [mem_inter] at h
    exact h.left
  · intro h
    rw [mem_inter]
    constructor
    · exact h
    · exact h

/-- Proposition 3.1.27(e) -/
-- ex
theorem SetTheory.Set.inter_assoc (A B C:Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  rw [ext_iff]
  intro x
  rw [mem_inter, mem_inter, mem_inter, mem_inter]
  apply and_assoc



/-- Proposition 3.1.27(f) -/
-- ex
theorem  SetTheory.Set.inter_union_distrib_left (A B C:Set) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  rw [ext_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  constructor
  · intro h
    have h₀ := h.left
    have h₁ := h.right
    rcases h₁ with hl|hr
    · left; apply (And.intro h₀ hl)
    · right; apply (And.intro h₀ hr)
  · intro h
    rcases h with hl|hr
    · have hl₀ := hl.left
      have hl₁ := hl.right
      constructor
      · exact hl₀
      · left; exact hl₁
    · have hr₀ := hr.left
      have hr₁ := hr.right
      constructor
      · exact hr₀
      · right; exact hr₁

/-- Proposition 3.1.27(f) -/
-- ex
theorem  SetTheory.Set.union_inter_distrib_left (A B C:Set) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  rw [ext_iff]
  intro x
  rw [mem_union, mem_inter, mem_inter, mem_union, mem_union]
  constructor
  · intro h
    rcases h with hl|hr
    · constructor
      · left; exact hl
      · left; exact hl
    · constructor
      · right; exact hr.left
      · right; exact hr.right
  · intro h
    rcases h with ⟨(ha|hb), (ha|hc)⟩
    · left; exact ha
    · left; exact ha
    · left; exact ha
    · right; apply (And.intro hb hc)

/-- Proposition 3.1.27(f) -/
-- ex
theorem SetTheory.Set.union_compl {A X:Set} (hAX: A ⊆ X) : A ∪ (X \ A) = X := by
  rw [ext_iff]
  simp
  intro x
  constructor
  · intro h
    rcases h with h|h
    · apply hAX at h; exact h
    · exact h.left
  · intro h
    by_cases h' : x ∈ A
    · left; exact h'
    · right; exact (And.intro h h')

/-- Proposition 3.1.27(f) -/
-- ex
-- getting rid of the warnings.
--theorem SetTheory.Set.inter_compl {A X:Set} (hAX: A ⊆ X) : A ∩ (X \ A) = ∅ := by
theorem SetTheory.Set.inter_compl {A X:Set} (_: A ⊆ X) : A ∩ (X \ A) = ∅ := by
  rw [ext_iff]
  simp
  intro x h₁ h₂
  exact h₁

/-- Proposition 3.1.27(g) -/
-- ex
-- getting rid of the warnings.
--theorem SetTheory.Set.compl_union {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) :
theorem SetTheory.Set.compl_union {A B X:Set} (_: A ⊆ X) (_: B ⊆ X) :
    X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  rw [ext_iff]
  simp
  intro x
  constructor
  · intro h
    constructor
    · apply (And.intro h.left h.right.left)
    · apply (And.intro h.left h.right.right)
  · intro h
    constructor
    · apply h.right.left
    · apply (And.intro h.left.right h.right.right)

/-- Proposition 3.1.27(g) -/
-- ex
--theorem SetTheory.Set.compl_inter {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) :
theorem SetTheory.Set.compl_inter {A B X:Set} (_: A ⊆ X) (_: B ⊆ X) :
    X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  rw [ext_iff]
  intro x
  constructor
  · intro h
    simp
    have hxX : x ∈ X := by rw [mem_sdiff] at h; exact h.left
    have hxAB : x ∉ A ∩ B := by rw [mem_sdiff] at h; exact h.right
    simp at hxAB
    by_cases hxA : x ∈ A
    · right
      apply (And.intro hxX (hxAB hxA))
    · left
      exact (And.intro hxX hxA)
  · intro h
    simp at h
    rcases h with (ha|hb)
    · rw [inter_comm]
      simp
      apply (And.intro ha.left (λx => ha.right))
    · simp
      apply (And.intro hb.left (λx => hb.right))



/-- Not from textbook: sets form a distributive lattice. -/
-- ex
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := fun _ _ _ ↦ subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left := by
    intro a b
    simp [subset_def]
    intro x h; left; exact h
  le_sup_right := by
    intro a b
    simp [subset_def]
    intro x h; right; exact h
  sup_le := by
    intro a b c h₁ h₂
    simp [subset_def]
    intro x h₃
    rcases h₃ with (ha|hb)
    · apply h₁ at ha; exact ha
    · apply h₂ at hb; exact hb
  inf_le_left := by
    intro a b
    simp [subset_def]
    intro x h₁ h₂
    exact h₁
  inf_le_right := by
    intro a b
    simp [subset_def]
  le_inf := by
    intro a b c h₁ h₂
    simp [subset_def]
    intro x h₃
    have hb : x ∈ b := by apply h₁ at h₃; exact h₃
    have hc : x ∈ c := by apply h₂ at h₃; exact h₃
    apply (And.intro hb hc)
  le_sup_inf := by
    intro X Y Z
    change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [←union_inter_distrib_left]
    exact subset_self _

/-- Sets have a minimal element.  -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

-- Now we've defined `A ≤ B` to mean `A ⊆ B`, and set `⊥` to `∅`.
-- This makes the `Disjoint` definition from Mathlib work with our `Set`.
example (A B: Set) : (A ≤ B) ↔ (A ⊆ B) := by rfl
example : ⊥ = (∅: Set) := by rfl
example (A B: Set) : Prop := Disjoint A B

/-- Definition of disjointness (using the previous instances) -/
theorem SetTheory.Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

abbrev SetTheory.Set.replace (A:Set) {P: A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/-- Axiom 3.7 (Axiom of replacement) -/
theorem SetTheory.Set.replacement_axiom {A:Set} {P: A → Object → Prop}
  (hP: ∀ x y y', P x y ∧ P x y' → y = y') (y:Object) :
    y ∈ A.replace hP ↔ ∃ x, P x y := SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

-- Going forward, we'll use `Nat` as a type.
-- However, notice we've set `Nat` to `SetTheory.nat` which is a `Set` and not a type.
-- The only reason we can write `x: Nat` is because we've previously defined a `CoeSort`
-- coercion that lets us write `x: A` (when `A` is a `Set`) as a shortcut for `x: A.toSubtype`.
-- This is why, whenever you see `x: Nat`, you're really looking at `x: Nat.toSubtype`.
example (x: Nat) : Nat.toSubtype := x
example (x: Nat) : Object := x.val
example (x: Nat) : (x.val ∈ Nat) := x.property
example (o: Object) (ho: o ∈ Nat) : Nat := ⟨o, ho⟩

/-- Axiom 3.8 (Axiom of infinity) -/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

-- Below are some API for handling coercions. This may not be the optimal way to set things up.

instance SetTheory.Set.instOfNat {n:ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

-- Now we can define `Nat` with a natural literal.
example : Nat := 5
example : (5 : Nat).val ∈ Nat := (5 : Nat).property

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

-- Now we can turn `ℕ` into `Nat`.
example (n : ℕ) : Nat := n
example (n : ℕ) : (n : Nat).val ∈ Nat := (n : Nat).property

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

-- Now we can turn `Nat` into `ℕ`.
example (n : Nat) : ℕ := n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n:Nat).val

-- Now we can turn `ℕ` into an `Object`.
example (n: ℕ) : Object := n
example (n: ℕ) : Set := {(n: Object)}

instance SetTheory.Object.instOfNat {n:ℕ} : OfNat Object n where
  ofNat := ((n:Nat):Object)

-- Now we can define `Object` with a natural literal.
example : Object := 1
example : Set := {1, 2, 3}

@[simp]
lemma SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object) := rfl

lemma SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m  :=
  Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

example : (5:Nat) ≠ (3:Nat) := by
  simp

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

example : (5:Object) ≠ (3:Object) := by
  simp

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff {m n : ℕ} : (m:Object) = ofNat(n) ↔ m = n := by exact ofNat_inj' m n

example (n: ℕ) : (n: Object) = 2 ↔ n = 2 := by
  simp

@[simp]
theorem SetTheory.Object.natCast_inj (n m:ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
      simp [←ofnat_eq, Subtype.val_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe'' (n:ℕ) : ((ofNat(n):Nat):ℕ) = n :=
  nat_equiv_coe_of_coe n

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff' {m: Nat} {n : ℕ} : (m:Object) = (ofNat(n):Object) ↔ (m:ℕ) = ofNat(n) := by
  constructor <;> intro h <;> rw [show m = n by aesop]
  apply nat_equiv_coe_of_coe
  rfl


/-- Example 3.1.16 (simplified).  -/
example : ({3, 5}:Set) ⊆ {1, 3, 5} := by
  simp only [subset_def, mem_pair, mem_triple]
  intro x hx
  tauto


/-- Example 3.1.17 (simplified). -/
example : ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3) = ({5}:Set) := by
  apply ext
  intro x
  simp only [mem_singleton, specification_axiom'']
  constructor
  · rintro ⟨h1, h2⟩
    simp only [mem_pair] at h1
    tauto
  rintro ⟨rfl⟩
  norm_num

/-- Example 3.1.24 -/

example : ({1, 2, 4}:Set) ∩ {2,3,4} = {2, 4} := by
  apply ext
  -- Instead of unfolding repetitive branches by hand like earlier,
  -- you can use the `aesop` tactic which does this automatically.
  aesop

/-- Example 3.1.24 -/

example : ({1, 2}:Set) ∩ {3,4} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  aesop

example : ¬ Disjoint ({1, 2, 3}:Set) {2,3,4} := by
  rw [disjoint_iff]
  intro h
  change {1, 2, 3} ∩ {2, 3, 4} = ∅ at h
  rw [eq_empty_iff_forall_notMem] at h
  aesop

-- ex
example : Disjoint (∅:Set) ∅ := by
  rw [disjoint_iff]
  apply ext
  simp

/-- Definition 3.1.26 example -/

example : ({1, 2, 3, 4}:Set) \ {2,4,6} = {1, 3} := by
  apply ext
  simp only [mem_sdiff, instInsert]
  aesop

/-- Example 3.1.30 -/
-- ex
example : ({3,5,9}:Set).replace (P := fun x y ↦ ∃ (n:ℕ), x.val = n ∧ y = (n+1:ℕ)) (by aesop) = {4,6,10} := by
  apply ext
  intro x
  rw [replacement_axiom]
  constructor
  · intro h
    obtain ⟨x', hx'⟩ := h
    aesop
  · intro h
    aesop

/-- Example 3.1.31 -/

example : ({3,5,9}:Set).replace (P := fun _ y ↦ y=1) (by aesop) = {1} := by
  apply ext
  simp only [replacement_axiom]
  aesop

/-- Exercise 3.1.5.  One can use the `tfae_have` and `tfae_finish` tactics here. -/
-- ex
theorem SetTheory.Set.subset_tfae (A B:Set) : [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by
  tfae_have 3 → 1 := by
    rw [ext_iff, subset_def]
    intro h x hxA
    rw [← h] at hxA
    rw [mem_inter] at hxA
    exact hxA.right
  tfae_have 1 → 2 := by
    rw [subset_def]
    intro h
    apply ext
    simp
    exact h
  tfae_have 2 → 3 := by
    intro h
    apply ext
    simp
    rw [ext_iff] at h
    intro x hxA
    have hxU : x ∈ A ∪ B := by
      rw [mem_union]; left; exact hxA
    rw [h] at hxU; exact hxU
  tfae_finish

/-- Exercise 3.1.7 -/
-- ex
theorem SetTheory.Set.inter_subset_left (A B:Set) : A ∩ B ⊆ A := by
  rw [subset_def]
  intro x h₁
  rw [mem_inter] at h₁
  exact h₁.left



/-- Exercise 3.1.7 -/
-- ex
theorem SetTheory.Set.inter_subset_right (A B:Set) : A ∩ B ⊆ B := by
  rw [inter_comm]
  apply inter_subset_left


/-- Exercise 3.1.7 -/
-- ex
theorem SetTheory.Set.subset_inter_iff (A B C:Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  rw [subset_def, subset_def, subset_def]
  constructor
  · intro h
    constructor
    · intro x h₁
      apply h at h₁
      rw [mem_inter] at h₁
      exact h₁.left
    · intro x h₁
      apply h at h₁
      rw [mem_inter] at h₁
      exact h₁.right
  intro h x h₁
  rw [mem_inter]
  constructor
  · apply h.left at h₁; exact h₁
  · apply h.right at h₁; exact h₁

/-- Exercise 3.1.7 -/
-- ex
theorem SetTheory.Set.subset_union_left (A B:Set) : A ⊆ A ∪ B := by
  rw [subset_def]
  intro x h
  rw [mem_union]
  left; exact h


/-- Exercise 3.1.7 -/
-- ex
theorem SetTheory.Set.subset_union_right (A B:Set) : B ⊆ A ∪ B := by
  rw [union_comm]
  apply subset_union_left

/-- Exercise 3.1.7 -/
-- ex
theorem SetTheory.Set.union_subset_iff (A B C:Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  repeat rw [subset_def]
  constructor
  · intro h
    constructor
    · intro x hxA
      have hxAB : x ∈ A ∪ B := by rw [mem_union]; left; exact hxA
      apply h at hxAB; exact hxAB
    · intro x hxB
      have hxAB : x ∈ A ∪ B := by rw [mem_union]; right; exact hxB
      apply h at hxAB; exact hxAB
  · intro h x hxAB
    rw [mem_union] at hxAB
    rcases hxAB with ha|hb
    · apply h.left at ha; exact ha
    · apply h.right at hb; exact hb


/-- Exercise 3.1.8 -/
-- ex
theorem SetTheory.Set.inter_union_cancel (A B:Set) : A ∩ (A ∪ B) = A := by
  rw [ext_iff]
  intro x
  constructor
  · intro h
    rw [mem_inter] at h
    exact h.left
  · intro h
    rw [mem_inter]
    constructor
    · exact h
    · rw [mem_union]; left; exact h


/-- Exercise 3.1.8 -/
-- ex
theorem SetTheory.Set.union_inter_cancel (A B:Set) : A ∪ (A ∩ B) = A := by
  rw [ext_iff]
  intro x
  constructor
  · intro h
    rw [mem_union] at h
    rcases h with (hₗ|hᵣ)
    · exact hₗ
    · rw [mem_inter] at hᵣ
      exact hᵣ.left
  · intro h
    rw [mem_union]
    left; exact h


/-- Exercise 3.1.9 -/
-- ex
theorem SetTheory.Set.partition_left {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
    A = X \ B := by
  rw [ext_iff]
  intro x
  rw [mem_sdiff]
  constructor
  · intro h
    constructor
    · rw [ext_iff] at h_union
      have hxAB : x ∈ A ∪ B := by rw [mem_union]; left; exact h
      rw [h_union] at hxAB; exact hxAB
    · by_contra!
      rw [ext_iff] at h_inter
      have hxAB : x ∈ A ∩ B := by rw [mem_inter]; apply (And.intro h this)
      rw [h_inter] at hxAB
      apply not_mem_empty at hxAB;
      assumption
  · intro h
    rw [← h_union, mem_union] at h
    have h' := h.left
    rcases h' with ha|hb
    · exact ha
    · have hnb := h.right
      apply hnb at hb
      contradiction

/-- Exercise 3.1.9 -/
-- ex
theorem SetTheory.Set.partition_right {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
    B = X \ A := by
  rw [union_comm] at h_union
  rw [inter_comm] at h_inter
  apply partition_left
  exact h_union
  exact h_inter


/--
  Exercise 3.1.10.
  You may find `Function.onFun_apply` and the `fin_cases` tactic useful.
-/
-- ex
theorem SetTheory.Set.pairwise_disjoint (A B:Set) :
    Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A]) := by
  intro i j h
  rw [Function.onFun_apply, disjoint_iff]
  rw [ext_iff]
  fin_cases i
  · fin_cases j
    · aesop
    · aesop
    · aesop
  · fin_cases j
    · aesop
    · aesop
    · aesop
  · fin_cases j
    · aesop
    · aesop
    · aesop

/-- Exercise 3.1.10 -/
-- ex
theorem SetTheory.Set.union_eq_partition (A B:Set) : A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by
  rw [ext_iff]
  intro x
  simp
  constructor
  · intro h
    rcases h with ha|hb
    · left
      by_cases hb : x ∈ B
      · right; apply And.intro ha hb
      · left; apply And.intro ha hb
    · by_cases ha : x ∈ A
      · left; right; apply And.intro ha hb
      · right; apply And.intro hb ha
  · intro h
    rcases h with ((⟨ha,hb⟩|⟨ha,hb⟩)|⟨hb,ha⟩)
    · left; exact ha
    · left; exact ha
    · right; exact hb


/--
  Exercise 3.1.11.
  The challenge is to prove this without using `Set.specify`, `Set.specification_axiom`,
  `Set.specification_axiom'`, or anything built from them (like differences and intersections).
-/
-- ex
theorem SetTheory.Set.specification_from_replacement {A:Set} {P: A → Prop} :
    ∃ B, B ⊆ A ∧ ∀ x, x.val ∈ B ↔ P x := by sorry

/-- Exercise 3.1.12.-/
-- ex
theorem SetTheory.Set.subset_union_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
    A' ∪ B' ⊆ A ∪ B := by
  rw [subset_def]
  simp
  intro x h
  rcases h with ha|hb
  · apply hA'A at ha; left; exact ha
  · apply hB'B at hb; right; exact hb

/-- Exercise 3.1.12.-/
-- ex
theorem SetTheory.Set.subset_inter_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
    A' ∩ B' ⊆ A ∩ B := by
  rw [subset_def]
  simp
  intro x h₁ h₂
  apply hA'A at h₁
  apply hB'B at h₂
  apply And.intro h₁ h₂

/-- Exercise 3.1.12.-/
-- ex
theorem SetTheory.Set.subset_diff_subset_counter :
    ∃ (A B A' B':Set), (A' ⊆ A) ∧ (B' ⊆ B) ∧ ¬ (A' \ B') ⊆ (A \ B) := by sorry

/-
  Final part of Exercise 3.1.12: state and prove a reasonable substitute positive result for the
  above theorem that involves set differences.
-/

/-- Exercise 3.1.13 -/
-- ex
theorem SetTheory.Set.singleton_iff (A:Set) (hA: A ≠ ∅) : (¬∃ B ⊂ A, B ≠ ∅) ↔ ∃ x, A = {x} := by sorry


/-
  Now we introduce connections between this notion of a set, and Mathlib's notion.
  The exercise below will acquiant you with the API for Mathlib's sets.
-/

instance SetTheory.Set.inst_coe_set : Coe Set (_root_.Set Object) where
  coe X := { x | x ∈ X }

-- Now we can convert our `Set` into a Mathlib `_root_.Set`.
-- Notice that Mathlib sets are parameterized by the element type, in our case `Object`.
example (X: Set) : _root_.Set Object := X

/--
  Injectivity of the coercion. Note however that we do NOT assert that the coercion is surjective
  (and indeed Russell's paradox prevents this)
-/
@[simp]
theorem SetTheory.Set.coe_inj' (X Y:Set) :
    (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y := by
  constructor
  . intro h; apply ext; intro x
    apply_fun (fun S ↦ x ∈ S) at h
    simp at h; assumption
  intro h; subst h; rfl

/-- Compatibility of the membership operation ∈ -/
theorem SetTheory.Set.mem_coe (X:Set) (x:Object) : x ∈ (X : _root_.Set Object) ↔ x ∈ X := by
  simp [Coe.coe]

/-- Compatibility of the emptyset -/
-- ex
theorem SetTheory.Set.coe_empty : ((∅:Set) : _root_.Set Object) = ∅ := by
  simp [Coe.coe]

/-- Compatibility of subset -/
-- ex
theorem SetTheory.Set.coe_subset (X Y:Set) :
    (X : _root_.Set Object) ⊆ (Y : _root_.Set Object) ↔ X ⊆ Y := by
  simp [Coe.coe]
  constructor
  · intro h
    rw [subset_def]
    exact h
  · intro h
    rw [subset_def] at h
    exact h

-- ex
theorem SetTheory.Set.coe_ssubset (X Y:Set) :
    (X : _root_.Set Object) ⊂ (Y : _root_.Set Object) ↔ X ⊂ Y := by
  sorry


/-- Compatibility of singleton -/
-- ex
theorem SetTheory.Set.coe_singleton (x: Object) : ({x} : _root_.Set Object) = {x} := by
  simp only [Coe.coe]

/-- Compatibility of union -/
-- ex
theorem SetTheory.Set.coe_union (X Y: Set) :
    (X ∪ Y : _root_.Set Object) = (X : _root_.Set Object) ∪ (Y : _root_.Set Object) := by
    simp

/-- Compatibility of pair -/
-- ex
theorem SetTheory.Set.coe_pair (x y: Object) : ({x, y} : _root_.Set Object) = {x, y} := by simp

/-- Compatibility of subtype -/
-- ex
theorem SetTheory.Set.coe_subtype (X: Set) :  (X : _root_.Set Object) = X.toSubtype := by simp

/-- Compatibility of intersection -/
-- ex
theorem SetTheory.Set.coe_intersection (X Y: Set) :
    (X ∩ Y : _root_.Set Object) = (X : _root_.Set Object) ∩ (Y : _root_.Set Object) := by simp

/-- Compatibility of set difference-/
-- ex
theorem SetTheory.Set.coe_diff (X Y: Set) :
    (X \ Y : _root_.Set Object) = (X : _root_.Set Object) \ (Y : _root_.Set Object) := by simp

/-- Compatibility of disjointness -/
-- ex
theorem SetTheory.Set.coe_Disjoint (X Y: Set) :
    Disjoint (X : _root_.Set Object) (Y : _root_.Set Object) ↔ Disjoint X Y := by sorry

end Chapter3
