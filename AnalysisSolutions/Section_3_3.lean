import Mathlib.Tactic
import AnalysisSolutions.Section_3_1
import AnalysisSolutions.Tools.ExistsUnique

/-!
# Analysis I, Section 3.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.
-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory] (X Y : Set)


/-!

Main constructions and results of this section:

- A notion of function `Function X Y` between two sets `X`, `Y` in the set theory of Section 3.1
- Various relations with the Mathlib notion of a function `X → Y` between two types `X`, `Y`.
  (Note from Section 3.1 that every `Set` `X` can also be viewed as a subtype
  `{x : Object // x ∈ X }` of `Object`.)
- Basic function properties and operations, such as composition, one-to-one and onto functions,
  and inverses.

In the rest of the book we will deprecate the Chapter 3 version of a function, and work with the
Mathlib notion of a function instead.  Even within this section, we will switch to the Mathlib
formalism for some of the examples involving number systems such as `ℤ` or `ℝ` that have not been
implemented in the Chapter 3 framework.
-/


/-
We will work here with the version `nat` of the natural numbers internal to the Chapter 3 set
theory, though usually we will use coercions to then immediately translate to the Mathlib
natural numbers `ℕ`.
-/
/--
  Definition 3.3.1. `Function X Y` is the structure of functions from `X` to `Y`.
  Analogous to the Mathlib type `X → Y`.
-/
@[ext]
structure Function (X Y: Set) where
  P : X → Y → Prop
  unique : ∀ x: X, ∃! y: Y, P x y

#check Function.mk

/--
  Converting a Chapter 3 function `f: Function X Y` to a Mathlib function `f: X → Y`.
  The Chapter 3 definition of a function was nonconstructive, so we have to use the
  axiom of choice here.
-/
noncomputable def Function.to_fn {X Y: Set} (f: Function X Y) : X → Y :=
  fun x ↦ (f.unique x).choose

noncomputable instance Function.inst_coefn (X Y: Set) : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := Function.to_fn

theorem Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x := rfl

/-- Converting a Mathlib function to a Chapter 3 `Function` -/
abbrev Function.mk_fn {X Y: Set} (f: X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by simp)

/-- Definition 3.3.1 -/
theorem Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y := by
  convert ((f.unique x).choose_iff y).symm

@[simp]
theorem Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x := by
  symm; rw [eval]


/-- Example 3.3.3.   -/
abbrev P_3_3_3a : nat → nat → Prop := fun x y ↦ (y:ℕ) = (x:ℕ)+1

theorem SetTheory.Set.P_3_3_3a_existsUnique (x: nat) : ∃! y: nat, P_3_3_3a x y := by
  apply ExistsUnique.intro ((x+1:ℕ):nat)
  . simp [P_3_3_3a]
  intro y h
  simpa [P_3_3_3a, Equiv.symm_apply_eq] using h

abbrev SetTheory.Set.f_3_3_3a : Function nat nat := Function.mk P_3_3_3a P_3_3_3a_existsUnique

theorem SetTheory.Set.f_3_3_3a_eval (x y: nat) : y = f_3_3_3a x ↔ (y:ℕ) = (x+1:ℕ) :=
  Function.eval _ _ _


theorem SetTheory.Set.f_3_3_3a_eval' (n: ℕ) : f_3_3_3a (n:nat) = (n+1:ℕ) := by
  symm
  simp only [f_3_3_3a_eval, nat_equiv_coe_of_coe]

theorem SetTheory.Set.f_3_3_3a_eval'' : f_3_3_3a 4 = 5 :=  f_3_3_3a_eval' 4

theorem SetTheory.Set.f_3_3_3a_eval''' (n:ℕ) : f_3_3_3a (2*n+3: ℕ) = (2*n+4:ℕ) := by
  convert f_3_3_3a_eval' _

abbrev SetTheory.Set.P_3_3_3b : nat → nat → Prop := fun x y ↦ (y+1:ℕ) = (x:ℕ)

theorem SetTheory.Set.not_P_3_3_3b_existsUnique : ¬ ∀ x, ∃! y: nat, P_3_3_3b x y := by
  by_contra h
  obtain ⟨ n, hn, _ ⟩ := h (0:nat)
  have : ((0:nat):ℕ) = 0 := by simp [OfNat.ofNat]
  simp [P_3_3_3b, this] at hn

abbrev SetTheory.Set.P_3_3_3c : (nat \ {(0:Object)}: Set) → nat → Prop :=
  fun x y ↦ ((y+1:ℕ):Object) = x

theorem SetTheory.Set.P_3_3_3c_existsUnique (x: (nat \ {(0:Object)}: Set)) :
    ∃! y: nat, P_3_3_3c x y := by
  -- Some technical unpacking here due to the subtle distinctions between the `Object` type,
  -- sets converted to subtypes of `Object`, and subsets of those sets.
  obtain ⟨ x, hx ⟩ := x; simp at hx
  obtain ⟨ hx1, hx2 ⟩ := hx
  set n := ((⟨ x, hx1 ⟩:nat):ℕ)
  have : x = (n:nat) := by simp [n]
  simp [P_3_3_3c, this, SetTheory.Object.ofnat_eq'] at hx2 ⊢
  replace hx2 : n = (n-1) + 1 := by omega
  apply ExistsUnique.intro ((n-1:ℕ):nat)
  . simp [←hx2]
  intro y hy
  simp [←hy]

abbrev SetTheory.Set.f_3_3_3c : Function (nat \ {(0:Object)}: Set) nat :=
  Function.mk P_3_3_3c P_3_3_3c_existsUnique

theorem SetTheory.Set.f_3_3_3c_eval (x: (nat \ {(0:Object)}: Set)) (y: nat) :
    y = f_3_3_3c x ↔ ((y+1:ℕ):Object) = x := Function.eval _ _ _

/-- Create a version of a non-zero `n` inside `nat \ {0}` for any natural number n. -/
abbrev SetTheory.Set.coe_nonzero (n:ℕ) (h: n ≠ 0): (nat \ {(0:Object)}: Set) :=
  ⟨((n:ℕ):Object), by
    simp [SetTheory.Object.ofnat_eq',h]
    rw [←SetTheory.Object.ofnat_eq]
    exact Subtype.property _
  ⟩

theorem SetTheory.Set.f_3_3_3c_eval' (n: ℕ) : f_3_3_3c (coe_nonzero (n+1) (by positivity)) = n := by
  symm; rw [f_3_3_3c_eval]; simp

theorem SetTheory.Set.f_3_3_3c_eval'' : f_3_3_3c (coe_nonzero 4 (by positivity)) = 3 := by
  convert f_3_3_3c_eval' 3

theorem SetTheory.Set.f_3_3_3c_eval''' (n:ℕ) :
    f_3_3_3c (coe_nonzero (2*n+3) (by positivity)) = (2*n+2:ℕ) := by convert f_3_3_3c_eval' (2*n+2)

/--
  Example 3.3.4 is a little tricky to replicate with the current formalism as the real numbers
  have not been constructed yet.  Instead, I offer some Mathlib counterparts. Of course, writing
  proofs for these will require using some Mathlib API, for instance for the nonnegative real
  class `NNReal`, and how this class interacts with `ℝ`.
-/
example : ¬ ∃ f: ℝ → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; set y := f (-1)
  have h1 := (hf _ y).mp (by rfl)
  have h2 := sq_nonneg y
  linarith

example : ¬ ∃ f: NNReal → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; set y := f 4
  have hy := (hf _ y).mp (by rfl)
  have h1 : 2 = y := (hf 4 2).mpr (by norm_num)
  have h2 : -2 = y := (hf 4 (-2)).mpr (by rwa [←sq_abs, ←abs_neg, sq_abs, ←h1] at hy)
  linarith

example : ∃ f: NNReal → NNReal, ∀ x y, y = f x ↔ y^2 = x := by
  use NNReal.sqrt; intro x y
  constructor
  · intro h; rw [h, NNReal.sq_sqrt]
  · intro h; rw [←h, NNReal.sqrt_sq]

/-- Example 3.3.5. The unused variable `_x` is underscored to avoid triggering a linter. -/
abbrev SetTheory.Set.P_3_3_5 : nat → nat → Prop := fun _x y ↦ y = 7

theorem SetTheory.Set.P_3_3_5_existsUnique (x: nat) : ∃! y: nat, P_3_3_5 x y := by
  apply ExistsUnique.intro 7
  all_goals simp [P_3_3_5]

abbrev SetTheory.Set.f_3_3_5 : Function nat nat := Function.mk P_3_3_5 P_3_3_5_existsUnique

theorem SetTheory.Set.f_3_3_5_eval (x: nat) : f_3_3_5 x = 7 := by
  symm; rw [Function.eval]

/-- Definition 3.3.8 (Equality of functions) -/
theorem Function.eq_iff {X Y: Set} (f g: Function X Y) : f = g ↔ ∀ x: X, f x = g x := by
  constructor
  . intro h; simp [h]
  intro h; ext x y; constructor
  . intro hf; rwa [←Function.eval, ←h x, Function.eval]
  intro hg; rwa [←Function.eval, h x, Function.eval]

/--
  Example 3.3.10 (simplified).  The second part of the example is tricky to replicate in this
  formalism, so a Mathlib substitute is offered instead.
-/
abbrev SetTheory.Set.f_3_3_10a : Function nat nat := Function.mk_fn (fun x ↦ (x^2 + 2*x + 1:ℕ))

abbrev SetTheory.Set.f_3_3_10b : Function nat nat := Function.mk_fn (fun x ↦ ((x+1)^2:ℕ))

theorem SetTheory.Set.f_3_3_10_eq : f_3_3_10a = f_3_3_10b := by
  simp_rw [Function.eq_iff, Function.eval_of]
  intros; simp; ring

example : (fun x:NNReal ↦ (x:ℝ)) = (fun x:NNReal ↦ |(x:ℝ)|) := by
  simp_rw [NNReal.abs_eq]

example : (fun x:ℝ ↦ (x:ℝ)) ≠ (fun x:ℝ ↦ |(x:ℝ)|) := by
  intro h
  let a := (fun (x:ℝ) ↦ x) (-1)
  let b := (fun x:ℝ ↦ |(x:ℝ)|) (-1)
  have hab : a = b := by unfold a; rw [h]
  norm_num [a, b] at hab

/-- Example 3.3.11 -/
abbrev SetTheory.Set.f_3_3_11 (X:Set) : Function (∅:Set) X :=
  Function.mk (fun _ _ ↦ True) (by intro ⟨ x,hx ⟩; simp at hx)

-- ex
theorem SetTheory.Set.empty_function_unique {X: Set} (f g: Function (∅:Set) X) : f = g := by
  rw [Function.eq_iff]
  simp

/-- Definition 3.3.13 (Composition) -/
noncomputable abbrev Function.comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    Function X Z :=
  Function.mk_fn (fun x ↦ g (f x))

-- `∘` is already taken in Mathlib for the composition of Mathlib functions,
-- so we use `○` here instead to avoid ambiguity.
infix:90 "○" => Function.comp

theorem Function.comp_eval {X Y Z: Set} (g: Function Y Z) (f: Function X Y) (x: X) :
    (g ○ f) x = g (f x) := Function.eval_of _ _

/--
  Compatibility with Mathlib's composition operation.
-/
theorem Function.comp_eq_comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    (g ○ f).to_fn = g.to_fn ∘ f.to_fn := by
  ext x; simp only [Function.comp_eval, Function.comp_apply, to_fn_eval]

/-- Example 3.3.14 -/
abbrev SetTheory.Set.f_3_3_14 : Function nat nat := Function.mk_fn (fun x ↦ (2*x:ℕ))

abbrev SetTheory.Set.g_3_3_14 : Function nat nat := Function.mk_fn (fun x ↦ (x+3:ℕ))

theorem SetTheory.Set.g_circ_f_3_3_14 :
    g_3_3_14 ○ f_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+3:ℕ):nat)) := by
  simp_rw [Function.eq_iff, Function.comp_eval, Function.eval_of]
  simp

theorem SetTheory.Set.f_circ_g_3_3_14 :
    f_3_3_14 ○ g_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+6:ℕ):nat)) := by
  simp_rw [Function.eq_iff, Function.comp_eval, Function.eval_of]
  intros; simp; ring

/-- Lemma 3.3.15 (Composition is associative) -/
theorem SetTheory.Set.comp_assoc {W X Y Z: Set} (h: Function Y Z) (g: Function X Y)
  (f: Function W X) :
    h ○ (g ○ f) = (h ○ g) ○ f := by
  simp_rw [Function.eq_iff, Function.comp_eval]
  simp

abbrev Function.one_to_one {X Y: Set} (f: Function X Y) : Prop := ∀ x x': X, x ≠ x' → f x ≠ f x'

theorem Function.one_to_one_iff {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' := by
  apply forall_congr'; intro x
  apply forall_congr'; intro x'
  tauto

/--
  Compatibility with Mathlib's `Function.Injective`.  You may wish to use the `unfold` tactic to
  understand Mathlib concepts such as `Function.Injective`.
-/
theorem Function.one_to_one_iff' {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn := by
  rw [one_to_one_iff, Function.Injective]

/--
  Example 3.3.18.  One half of the example requires the integers, and so is expressed using
  Mathlib functions instead of Chapter 3 functions.
-/
theorem SetTheory.Set.f_3_3_18_one_to_one :
    (Function.mk_fn (fun (n:nat) ↦ ((n^2:ℕ):nat))).one_to_one := by
  rw [Function.one_to_one_iff]
  intro x1 x2 h
  simpa [Function.eval, Function.eval_of] using h

example : ¬ Function.Injective (fun (n:ℤ) ↦ n^2) := by
  intro h
  have h1 : (fun n ↦ n ^ 2) 1 = (1:ℤ) := by norm_num
  have h2 : (fun n ↦ n ^ 2) (-1) = (1:ℤ) := by norm_num
  nth_rewrite 2 [←h1] at h2
  specialize h h2
  contradiction

example : Function.Injective (fun (n:ℕ) ↦ n^2) := by
  intro a b h
  rwa [← pow_left_inj₀ (by norm_num) (by norm_num) (show 2 ≠ 0 by norm_num)]

/-- Remark 3.3.19 -/
theorem SetTheory.Set.two_to_one {X Y: Set} {f: Function X Y} (h: ¬ f.one_to_one) :
    ∃ x x': X, x ≠ x' ∧ f x = f x' := by
  rw [Function.one_to_one] at h
  aesop

/-- Definition 3.3.20 (Onto functions) -/
abbrev Function.onto {X Y: Set} (f: Function X Y) : Prop := ∀ y: Y, ∃ x: X, f x = y

/-- Compatibility with Mathlib's Function.Surjective-/
theorem Function.onto_iff {X Y: Set} (f: Function X Y) : f.onto ↔ Function.Surjective f.to_fn := by
  rfl

/-- Example 3.3.21 (using Mathlib) -/
example : ¬ Function.Surjective (fun (n:ℤ) ↦ n^2) := by
  unfold Function.Surjective; push_neg
  use (-1); intro a
  linarith [sq_nonneg a]

abbrev A_3_3_21 := { m:ℤ // ∃ n:ℤ, m = n^2 }

example : Function.Surjective (fun (n:ℤ) ↦ ⟨ n^2, by use n ⟩ : ℤ → A_3_3_21) := by
  unfold Function.Surjective
  rintro ⟨b, ⟨a, ha⟩⟩; use a
  simp only [ha]

/-- Definition 3.3.23 (Bijective functions) -/
abbrev Function.bijective {X Y: Set} (f: Function X Y) : Prop := f.one_to_one ∧ f.onto

/-- Compatibility with Mathlib's Function.Bijective-/
theorem Function.bijective_iff {X Y: Set} (f: Function X Y) :
    f.bijective ↔ Function.Bijective f.to_fn := by
  rw [Function.bijective, Function.Bijective, one_to_one_iff', onto_iff]

/-- Example 3.3.24 (using Mathlib) -/
abbrev f_3_3_24 : Fin 3 → ({3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩
| 2 => ⟨ 4, by norm_num ⟩

example : ¬ Function.Injective f_3_3_24 := by decide
example : ¬ Function.Bijective f_3_3_24 := by decide

abbrev g_3_3_24 : Fin 2 → ({2,3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 2, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩

example : ¬ Function.Surjective g_3_3_24 := by decide
example : ¬ Function.Bijective g_3_3_24 := by decide

abbrev h_3_3_24 : Fin 3 → ({3,4,5}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 4, by norm_num ⟩
| 2 => ⟨ 5, by norm_num ⟩

example : Function.Bijective h_3_3_24 := by decide

/--
  Example 3.3.25 is formulated using Mathlib rather than the set theory framework here to avoid
  some tedious technical issues (cf. Exercise 3.3.2)
-/
example : Function.Bijective (fun n ↦ ⟨ n+1, by omega⟩ : ℕ → { n:ℕ // n ≠ 0 }) := by
  unfold Function.Bijective
  constructor
  · unfold Function.Injective; intro x y
    simp only [Subtype.mk.injEq]; omega
  unfold Function.Surjective
  · rintro ⟨x, hx⟩; use x-1
    simp only [Subtype.mk.injEq]; omega

example : ¬ Function.Bijective (fun n ↦ n+1) := by
  suffices h : ¬ Function.Surjective (fun n ↦ n+1) by unfold Function.Bijective; tauto
  unfold Function.Surjective; push_neg
  use 0; intro a
  symm; apply Nat.zero_ne_add_one

/-- Remark 3.3.27 -/
theorem Function.bijective_incorrect_def :
    ∃ X Y: Set, ∃ f: Function X Y, (∀ x: X, ∃! y: Y, y = f x) ∧ ¬ f.bijective := by
  use nat, nat
  set f := mk_fn fun x ↦ (0: nat); use f
  constructor
  · intro x
    apply existsUnique_of_exists_of_unique
    · use 0; rw [Function.eval]
    intro y1 y2 h1 h2
    rw [Function.eval] at *
    rw [h1, h2]
  rw [Function.bijective]
  suffices h : ¬ f.one_to_one by tauto
  rw [Function.one_to_one_iff]
  push_neg; use 0, 1
  simp [f]

/--
  We cannot use the notation `f⁻¹` for the inverse because in Mathlib's `Inv` class, the inverse
  of `f` must be exactly of the same type of `f`, and `Function Y X` is a different type from
  `Function X Y`.
-/
abbrev Function.inverse {X Y: Set} (f: Function X Y) (h: f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intro y
    apply existsUnique_of_exists_of_unique
    . obtain ⟨ x, hx ⟩ := h.2 y; use x
    intro x x' hx hx'; simp at hx hx'
    rw [←hx'] at hx
    apply f.one_to_one_iff.mp h.1
    simp [hx]
  )

theorem Function.inverse_eval {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) (x: X) :
    x = (f.inverse h) y ↔ f x = y := Function.eval _ _ _

/-- Compatibility with Mathlib's notion of inverse -/
theorem Function.inverse_eq {X Y: Set} [Nonempty X] {f: Function X Y} (h: f.bijective) :
    (f.inverse h).to_fn = Function.invFun f.to_fn := by
  ext y
  congr; symm
  rw [inverse_eval]
  apply Function.rightInverse_invFun
  have ⟨_, hf⟩ := f.bijective_iff.mp h
  exact hf

/--
  Exercise 3.3.1.  Although a proof operating directly on functions would be shorter,
  the spirit of the exercise is to show these using the `Function.eq_iff` definition.
-/
theorem Function.refl {X Y:Set} (f: Function X Y) : f = f := by
  rewrite [eq_iff]
  simp

theorem Function.symm {X Y:Set} (f g: Function X Y) : f = g ↔ g = f := by
  constructor
  · intro h
    symm; exact h
  · intro h
    symm; exact h

theorem Function.trans {X Y:Set} {f g h: Function X Y} (hfg: f = g) (hgh: g = h) : f = h := by
  rw [eq_iff] at *
  intro x
  rw [hfg, hgh]

theorem Function.comp_congr {X Y Z:Set} {f f': Function X Y} (hff': f = f') {g g': Function Y Z}
  (hgg': g = g') : g ○ f = g' ○ f' := by sorry

/-- Exercise 3.3.2 -/
theorem Function.comp_of_inj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.one_to_one)
  (hg: g.one_to_one) : (g ○ f).one_to_one := by sorry

theorem Function.comp_of_surj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.onto)
  (hg: g.onto) : (g ○ f).onto := by sorry

/--
  Exercise 3.3.3 - fill in the sorrys in the statements in  a reasonable fashion.
-/
example (X: Set) : (SetTheory.Set.f_3_3_11 X).one_to_one ↔ sorry := by sorry

example (X: Set) : (SetTheory.Set.f_3_3_11 X).onto ↔ sorry := by sorry

example (X: Set) : (SetTheory.Set.f_3_3_11 X).bijective ↔ sorry := by sorry

/--
  Exercise 3.3.4.
-/
theorem Function.comp_cancel_left {X Y Z:Set} {f f': Function X Y} {g : Function Y Z}
  (heq : g ○ f = g ○ f') (hg: g.one_to_one) : f = f' := by sorry

theorem Function.comp_cancel_right {X Y Z:Set} {f: Function X Y} {g g': Function Y Z}
  (heq : g ○ f = g' ○ f) (hf: f.onto) : g = g' := by sorry

def Function.comp_cancel_left_without_hg : Decidable (∀ (X Y Z:Set) (f f': Function X Y) (g : Function Y Z) (heq : g ○ f = g ○ f'), f = f') := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Function.comp_cancel_right_without_hg : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g g': Function Y Z) (heq : g ○ f = g' ○ f), g = g') := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/--
  Exercise 3.3.5.
-/
theorem Function.comp_injective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hinj :
    (g ○ f).one_to_one) : f.one_to_one := by sorry

theorem Function.comp_surjective {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hinj : (g ○ f).onto) : g.onto := by sorry

def Function.comp_injective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hinj :
    (g ○ f).one_to_one), g.one_to_one) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Function.comp_surjective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hinj :
    (g ○ f).onto), f.onto) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 3.3.6 -/
theorem Function.inverse_comp_self {X Y: Set} {f: Function X Y} (h: f.bijective) (x: X) :
    (f.inverse h) (f x) = x := by sorry

theorem Function.self_comp_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) :
    f ((f.inverse h) y) = y := by sorry

theorem Function.inverse_bijective {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).bijective := by sorry

theorem Function.inverse_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).inverse (f.inverse_bijective h) = f := by sorry

theorem Function.comp_bijective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.bijective)
  (hg: g.bijective) : (g ○ f).bijective := by sorry

/-- Exercise 3.3.7 -/
theorem Function.inv_of_comp {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hf: f.bijective) (hg: g.bijective) :
    (g ○ f).inverse (Function.comp_bijective hf hg) = (f.inverse hf) ○ (g.inverse hg) := by sorry

/-- Exercise 3.3.8 -/
abbrev Function.inclusion {X Y:Set} (h: X ⊆ Y) :
    Function X Y := Function.mk_fn (fun x ↦ ⟨ x.val, h x.val x.property ⟩ )

abbrev Function.id (X:Set) : Function X X := Function.mk_fn (fun x ↦ x)

theorem Function.inclusion_id (X:Set) :
    Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by sorry

theorem Function.inclusion_comp (X Y Z:Set) (hXY: X ⊆ Y) (hYZ: Y ⊆ Z) :
    Function.inclusion hYZ ○ Function.inclusion hXY = Function.inclusion (SetTheory.Set.subset_trans hXY hYZ) := by sorry

theorem Function.comp_id {A B:Set} (f: Function A B) : f ○ Function.id A = f := by sorry

theorem Function.id_comp {A B:Set} (f: Function A B) : Function.id B ○ f = f := by sorry

theorem Function.comp_inv {A B:Set} (f: Function A B) (hf: f.bijective) :
    f ○ f.inverse hf = Function.id B := by sorry

theorem Function.inv_comp {A B:Set} (f: Function A B) (hf: f.bijective) :
    f.inverse hf ○ f = Function.id A := by sorry

open Classical in
theorem Function.glue {X Y Z:Set} (hXY: Disjoint X Y) (f: Function X Z) (g: Function Y Z) :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by sorry

open Classical in
theorem Function.glue' {X Y Z:Set} (f: Function X Z) (g: Function Y Z)
    (hfg : ∀ x : ((X ∩ Y): Set), f ⟨x.val, by aesop⟩ = g ⟨x.val, by aesop⟩)  :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by sorry

end Chapter3
