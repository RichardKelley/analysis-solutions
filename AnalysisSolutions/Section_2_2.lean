import Mathlib.Tactic
import AnalysisSolutions.Section_2_1

/-!
# Analysis I, Section 2.2

This file is a translation of Section 2.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`
- Establishment of basic properties of addition and order

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's `Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- This instance allows for the `+` notation to be used for natural number addition. -/
instance Nat.instAdd : Add Nat where
  add := add

/-- Compare with Mathlib's `Nat.zero_add`-/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Compare with Mathlib's `Nat.succ_add` -/
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Compare with Mathlib's `Nat.one_add` -/
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- sum of two natural numbers is again a natural number
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n). Compare with Mathlib's `Nat.add_zero` -/
@[simp]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). Compare with Mathlib's `Nat.add_succ` -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- n++ = n + 1 (Why?). Compare with Mathlib's `Nat.succ_eq_add_one` -/
-- ex
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  revert n
  apply induction
  · apply zero_succ
  · intro n ih
    rw [ih, ← succ_add, ih]

/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's `Nat.add_comm` -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's `Nat.add_assoc` -/
-- ex
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert c; apply induction
  · simp
  · intro c ih
    rw [add_succ, ih, ← add_succ, add_succ b c]

/-- Proposition 2.2.6 (Cancellation law)
    Compare with Mathlib's `Nat.add_left_cancel` -/
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.IsPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.IsPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's `Nat.add_pos_left` -/
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.IsPos) : (a + b).IsPos := by
  -- this proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

/-- Compare with Mathlib's `Nat.add_pos_right` -/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.IsPos) : (b + a).IsPos := by
  rw [add_comm]
  exact add_pos_left _ ha

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's `Nat.add_eq_zero` -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- this proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . rw [← isPos_iff] at ha
    have : (a + b).IsPos := add_pos_left _ ha
    contradiction
  rw [← isPos_iff] at hb
  have : (a + b).IsPos := add_pos_right _ hb
  contradiction

/-
The following API for ∃! may be useful for the next problem.  Also, the `obtain` tactic is useful
for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique
#check ExistsUnique.exists
#check ExistsUnique.unique

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
-- ex
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.IsPos) : ∃! b, b++ = a := by
  apply existsUnique_of_exists_of_unique
  · revert a; apply induction
    · intros h
      contradiction
    · intros n ih h
      exists n
  · intros y₁ y₂ h₁ h₂
    rw [← h₂] at h₁
    apply succ_cancel at h₁
    exact h₁

/-- Definition 2.2.11 (Ordering of the natural numbers)
    This defines the `≤` operation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers)
    This defines the `<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Compare with Mathlib's `ge_iff_le` -/
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's `gt_iff_lt` -/
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's `Nat.le_of_lt` -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's `Nat.le_iff_lt_or_eq` -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

/-- Compare with Mathlib's `Nat.lt_succ_self`-/
-- ex
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  simp
  rw [Nat.lt_iff]
  constructor
  · exists 1; rw [← one_add, add_comm]
  · simp; intro h
    rw [← one_add n, add_comm] at h
    rw (occs := .pos [1]) [← zero_add n, add_comm] at h
    apply add_left_cancel at h
    contradiction

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's `Nat.le_refl`-/
-- ex
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  simp
  rw [le_iff_lt_or_eq]
  right; rfl

/-- (b) (Order is transitive).  The `obtain` tactic will be useful here.
    Compare with Mathlib's `Nat.le_trans` -/
-- ex
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  simp at *
  rw [le_iff] at *
  obtain ⟨a₁, ha₁⟩ := hab
  obtain ⟨a₂, ha₂⟩ := hbc
  rw [ha₂] at ha₁
  exists (a₁ + a₂)
  rw [add_comm a₁ a₂, ← add_assoc]
  exact ha₁

/-- (c) (Order is anti-symmetric). Compare with Mathlib's `Nat.le_antisymm`  -/
-- ex
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  simp at *
  rw [le_iff] at *
  obtain ⟨a₁, ha₁⟩ := hab
  obtain ⟨a₂, ha₂⟩ := hba
  have h_add : a + b = a + b + (a₁ + a₂) := by
    calc a + b
      _ = a + a + a₂ := by rw [ha₂, add_assoc]
      _ = a + b + a₁ + a₂ := by rw (occs := .pos [2]) [ha₁]
                                rw [add_assoc a b a₁]
      _ = a + b + (a₁ + a₂) := by rw [add_assoc]
  rw (occs := .pos [1]) [← add_zero (a+b)] at h_add
  apply add_left_cancel (a+b) 0 (a₁+a₂) at h_add
  symm at h_add
  apply add_eq_zero at h_add
  rw [h_add.left] at ha₁
  simp at ha₁
  exact ha₁

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`  -/
-- ex
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  revert c; apply induction
  · simp
  intros c ih
  rw [ih]
  constructor
  · intros h
    simp at *
    rw [le_iff] at *
    obtain ⟨a₁, ha₁⟩ := h
    rw [add_succ, add_succ, succ_eq_add_one, succ_eq_add_one]
    exists a₁
    rw [ha₁, add_assoc, add_comm a₁, ← add_assoc]
  · intros h
    simp at *
    rw [le_iff] at *
    obtain ⟨a₁, ha₁⟩ := h
    rw [add_succ, add_succ, succ_eq_add_one, succ_eq_add_one] at ha₁
    exists a₁
    rw [add_comm, add_comm (b+c)] at ha₁
    apply add_left_cancel 1 (a+c) (b+c+a₁) at ha₁
    exact ha₁

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Compare with Mathlib's `Nat.succ_le_iff` -/
-- ex
lemma lt_trans {a b c : Nat} (h₁ : a < b) (h₂ : b < c) : a < c := by
  rw [Nat.lt_iff] at *
  obtain ⟨k₁, hk₁⟩ := h₁.left
  replace h₁ := h₁.right
  obtain ⟨k₂, hk₂⟩ := h₂.left
  replace h₂ := h₂.right
  constructor
  · exists k₁+k₂
    rw [hk₁, add_assoc] at hk₂
    exact hk₂
  by_contra hcon
  rw [hk₂, hk₁, add_assoc] at hcon
  rw (occs := .pos [1]) [← add_zero a] at hcon
  apply Nat.add_left_cancel a at hcon
  symm at hcon; apply Nat.add_eq_zero at hcon
  rw [hcon.left] at hk₁; simp at hk₁
  symm at hk₁; contradiction

lemma lt_of_succ_le {a b : Nat} (h : a++ ≤ b) : a < b := by
  have h₁ : a < a++ := by
    rw [Nat.succ_eq_add_one, Nat.lt_iff]
    constructor
    · exists 1
    by_contra h'
    --rw [add_comm] at h'
    rw (occs := .pos [1]) [← Nat.zero_add a, add_comm] at h'
    apply Nat.add_left_cancel at h'
    contradiction
  rw [Nat.le_iff_lt_or_eq] at h
  rcases h with hl | hr
  · apply lt_trans h₁ hl
  · rw [← hr]
    exact h₁

lemma le_of_succ_lt {a b : Nat} (h : a < b) : a++ ≤ b := by
  rw [Nat.le_iff]
  rw [Nat.lt_iff] at h
  obtain ⟨c, hc⟩ := h.left
  replace h := h.right
  by_cases hcz : c = 0
  · rw [hcz] at hc; simp at hc; symm at hc; contradiction
  · push_neg at hcz
    rw [← Nat.isPos_iff] at hcz
    have h_csucc : ∃! k, k++ = c := by apply Nat.uniq_succ_eq; exact hcz
    replace h_csucc : ∃ k, k++ = c := by
      apply ExistsUnique.exists
      exact h_csucc
    obtain ⟨k, hk⟩ := h_csucc
    rw [← hk] at hc
    exists k
    rw [Nat.succ_add]
    rw [Nat.add_succ] at hc
    exact hc

-- rck: This was way more of a slog than it probably should have been... :(
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b :=
  ⟨le_of_succ_lt, lt_of_succ_le ⟩

/-- (f) a < b if and only if b = a + d for positive d. -/
-- ex
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.IsPos ∧ b = a + d := by
  constructor
  · intros h
    rw [lt_iff_succ_le, le_iff] at h
    obtain ⟨c, hc⟩ := h
    rw [succ_add, ← add_succ] at hc
    exists (c+1)
    constructor
    · apply Nat.add_pos_right
      rw [isPos_iff]
      simp
    · rw [← succ_eq_add_one]; exact hc
  · intros h
    obtain ⟨d, hd⟩ := h
    rw [lt_iff]
    constructor
    · exists d
      apply hd.right
    · by_contra hcon
      rw [hcon] at hd
      have h := hd.right
      replace hd := hd.left
      have hdz : 0 = d := by
        rw (occs := .pos [1]) [← add_zero b] at h
        apply Nat.add_left_cancel b 0 d at h
        exact h
      rw [isPos_iff] at hd; symm at hdz; apply hd; exact hdz

/-- If a < b then a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (Nat.le_of_lt h.1) (Nat.le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction


/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's `trichotomous` -/
-- ex
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- this proof is written to follow the structure of the original text.
  revert a; apply induction
  . have why : 0 ≤ b := by
      by_cases h : b = 0
      · rw [h]; rw [le_iff]; exists 0
      · push_neg at h;-- rw [← isPos_iff] at h;
        rw [le_iff_lt_or_eq]
        left
        rw[lt_iff]
        constructor
        · exists b
        · symm; exact h
    replace why := (Nat.le_iff_lt_or_eq _ _).mp why
    tauto
  intro a ih
  rcases ih with case1 | case2 | case3
  . rw [lt_iff_succ_le] at case1
    rw [Nat.le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by rw[case2]; apply succ_gt_self
    tauto
  have why : a++ > b := by have h: a++ > a := by
                             apply succ_gt_self
                           simp at *
                           apply (lt_trans case3 h)
  tauto

/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the
  proof involving decidability has been provided; the remaining sorries involve claims about the
  natural numbers.  One could also have established this result by the `classical` tactic
  followed by `exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's `Nat.decLe`
-/
-- ex
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    by_cases h' : b = 0
    · rw [h']; rw [le_iff]; exists 0
    · push_neg at h';-- rw [← isPos_iff] at h;
      rw [le_iff_lt_or_eq]
      left
      rw[lt_iff]
      constructor
      · exists b
      · symm; exact h'
  | a++, b => by
    cases decLe a b with
    | isTrue h' =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        intro hneg
        apply lt_of_succ_le at hneg
        dsimp [Nat.instLT] at hneg
        have h₀ := hneg.right
        contradiction
      | isFalse h =>
        apply isTrue
        apply le_of_succ_lt
        dsimp [Nat.instLT]
        apply And.intro h' h
    | isFalse h =>
      apply isFalse
      intro hneg
      apply lt_of_succ_le at hneg
      dsimp [Nat.instLT] at hneg
      have hcon : a ≤ b := hneg.left
      contradiction

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe

--rck
lemma Nat.le_total : ∀ (a b : Nat), a ≤ b ∨ b ≤ a  := by
  intros a b
  have h: a < b ∨ a = b ∨ a > b := (Nat.trichotomous a b)
  cases h with
  | inl h =>
    left
    exact (Nat.le_of_lt h)
  | inr h =>
    right
    rw [Nat.le_iff_lt_or_eq b a]
    cases h with
    | inl h => right; symm; exact h
    | inr h => left; simp at *; exact h

--rck
lemma Nat.lt_iff_le_not_le : ∀ (a b : Nat), a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  intros a b
  constructor
  · intro h
    constructor
    · apply Nat.le_of_lt; exact h
    · intro hneg
      rw [Nat.le_iff_lt_or_eq] at hneg
      cases hneg with
      | inl h' => apply Nat.not_lt_of_gt a b
                  apply And.intro h h'
      | inr h' => symm at h'; revert h'; simp; push_neg; apply Nat.ne_of_lt; exact h
  · intros h
    have h₁ := h.left
    have h₂ := h.right
    dsimp [Nat.instLT]
    constructor
    · exact h₁
    · intro hneg
      rw [hneg] at h₂
      rw [hneg] at h₁
      contradiction

/-- (Not from textbook) Nat has the structure of a linear ordering. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_le := Nat.lt_iff_le_not_le
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := Nat.le_total
  toDecidableLE := decidableRel

/-- (Not from textbook) Nat has the structure of an ordered monoid. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by
    intro a b hab c
    exact (add_le_add_left a b c).mp hab

/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's `Nat.strong_induction_on`
-/
-- ex
lemma Nat.ge_zero : ∀ n : Nat, 0 ≤ n := by
  intros n
  cases n with
  | zero => rfl
  | succ k => rw [Nat.le_iff]
              exists k+1
              simp; apply Nat.succ_eq_add_one

-- rck : ex
lemma le_zero_is_zero : ∀ n : Nat, n ≤ 0 → n = 0 := by
  intros n
  intros n_le_0
  have n_ge_0 : 0 ≤ n := by apply Nat.ge_zero
  apply le_antisymm n_le_0 n_ge_0

-- rck (auxiliary definition)
def Q (m₀: Nat) (P : Nat → Prop) (n : Nat) : Prop := ∀ k, m₀ ≤ k ∧ k ≤ n → P k

-- rck
lemma Nat.lt_succ_le : ∀ (n m : Nat), n < m++ ↔ n ≤ m := by
  intros n m
  constructor
  · intro h
    rw [Nat.lt_iff_succ_le] at h
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one] at h
    rw [← Nat.add_le_add_right] at h; exact h
  · intro h
    rw [Nat.lt_iff_succ_le]
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
    rw [← Nat.add_le_add_right]; exact h

-- rck
lemma never_le_zero : ∀ (n : Nat), ¬(n < 0) := by
  intro n
  induction n with
  | zero => simp
            rw [Nat.le_iff]
            exists 0
  | succ k ih =>
    simp
    rw [Nat.le_iff]
    simp

theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
    suffices h : (∀ n, Q m₀ P n)
    · intro m hm
      have h₁ := h m
      unfold Q at h₁
      apply hind
      exact hm
      intros m' h'
      apply h₁
      constructor
      · apply h'.left
      · have hmpm := h'.right
        rw [Nat.le_iff_lt_or_eq]; left; exact hmpm
    intro n
    induction n
    · unfold Q
      intro k h
      have hr : k ≤ zero := h.right
      apply le_zero_is_zero at hr
      apply hind
      simp
      exact h.left
      intro m' h
      rw [hr] at h
      have hcon := h.right
      apply never_le_zero at hcon
      contradiction
    · rename_i n ih
      unfold Q at ih
      unfold Q
      intro k hk
      have hk₁ := hk.left
      have hk₂ := hk.right
      rw [Nat.le_iff_lt_or_eq] at hk₂
      cases hk₂ with
      | inl hl =>
        apply ih
        constructor
        · exact hk₁
        · rw [Nat.lt_succ_le] at hl; exact hl
      | inr hr =>
        rw [hr]
        apply hind; simp
        · rw [Nat.le_iff_lt_or_eq]
          have hk₂ := hk.right
          rw [hr] at hk₁
          rw [Nat.le_iff_lt_or_eq] at hk₁ ; exact hk₁
        · intro m'
          rw [Nat.lt_succ_le m' n]
          apply ih

/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's `Nat.decreasingInduction` -/
-- ex
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  intro m h
  induction n with
  | zero => apply le_zero_is_zero at h
            rw [h]
            exact hn
  | succ k ih =>
    rw [Nat.le_iff_lt_or_eq] at h
    cases h with
    | inl h => rw [Nat.lt_succ_le] at h
               apply ih
               apply hind at hn
               exact hn
               exact h
    | inr h => rw [← h] at hn; exact hn

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's `Nat.le_induction` -/
-- ex
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
    intros hpn m
    induction m
    · intros h
      have h_ge_0 : n ≥ zero := by
        apply Nat.ge_zero
      have h_eq_0 : n = zero := by
        simp at h
        simp at h_ge_0
        apply le_antisymm
        · exact h
        · exact h_ge_0
      rw [h_eq_0] at hpn; exact hpn
    · rename_i m' ih
      simp
      intro hnmp
      rw [Nat.le_iff_lt_or_eq] at hnmp
      cases hnmp with
      | inr h => rw [← h]; exact hpn
      | inl h => rw [Nat.lt_iff_succ_le] at h
                 rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, ← Nat.add_le_add_right] at h
                 apply ih at h
                 apply hind at h
                 exact h



end Chapter2
