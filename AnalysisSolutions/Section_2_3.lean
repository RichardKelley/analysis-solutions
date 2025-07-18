import Mathlib.Tactic
import AnalysisSolutions.Section_2_2

/-!
# Analysis I, Section 2.3

This file is a translation of Section 2.3 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  `Chapter2.Nat`

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.
-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2. -/
-- ex
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  revert n; apply induction
  · apply Nat.zero_mul
  · intros n h
    rw [Nat.succ_mul]
    rw [h]; simp

/-- This lemma will be useful to prove Lemma 2.3.2. -/
-- ex
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  revert n; apply induction
  · apply Nat.zero_mul
  · intros n ih
    rw [Nat.succ_mul, Nat.succ_mul]
    rw [ih, add_assoc, add_assoc]
    rw [Nat.add_succ, Nat.add_succ m]
    rw [Nat.add_comm n m]

/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1 -/
-- ex
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  revert n; apply induction
  · rw [Nat.mul_zero, Nat.zero_mul]
  · intro n ih
    rw [Nat.mul_succ, Nat.succ_mul]
    rw [ih]

theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3. -/
-- ex
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  revert n ; apply induction
  · intros h
    contradiction
  · intros n ih h
    rw [Nat.succ_mul]
    apply Nat.add_pos_right
    exact h₂

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2. Compare with Mathlib's Nat.mul_eq_zero.  -/
-- ex
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · cases n
    · intro h; left; rfl
    · rename_i a
      intro h
      simp
      rw [Nat.succ_mul] at h
      apply Nat.add_eq_zero at h
      exact h.right
  · intros h
    cases h with
    | inl h => rw [h, Nat.zero_mul]
    | inr h => rw [h, Nat.mul_zero]

/-- Proposition 2.3.4 (Distributive law)-/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)-/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3 -/
-- ex
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  revert c; apply induction
  · rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  · intros c ih
    rw [Nat.succ_eq_add_one, Nat.mul_add]
    rw [ih]
    rw [Nat.mul_add, Nat.mul_add]
    rw [Nat.mul_one, Nat.mul_one]

/-- (Not from textbook)  Nat is a commutative semiring. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  obtain ⟨ d, hdpos, hd ⟩ := h
  apply_fun (· * c) at hd
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc



/-- Corollary 2.3.7 (Cancellation law) -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  rcases this with hlt | heq | hgt
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    replace hlt := ne_of_lt _ _ hlt
    contradiction
  . assumption
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  replace hgt := ne_of_gt _ _ hgt
  contradiction

/-- (Not from textbook) Nat is an ordered semiring. -/
-- ex
lemma Nat.mul_le_mul_of_nonneg_left : ∀ (a b c : Nat), a ≤ b → 0 ≤ c → c * a ≤ c * b := by
  intros a b c h₁ h₂
  revert c; apply induction
  · intros
    simp
  · intros n ih h₂
    rw [Nat.le_iff_lt_or_eq] at h₁
    cases h₁ with
    | inl h' =>
      have hpos : Nat.IsPos (n++) := by
        rw [Nat.succ_eq_add_one]
        apply Nat.add_pos_right
        rw [isPos_iff]
        simp
      rw [Nat.le_iff_lt_or_eq]
      left
      apply Nat.mul_lt_mul_of_pos_left h' hpos
    | inr h' =>
      rw [h']

instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by
    rw [← Nat.zero_succ]
    rw [le_iff]
    exists 1
  mul_le_mul_of_nonneg_left :=
    Nat.mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right := by
    intros a b c h₁ h₂
    rw [mul_comm a c, mul_comm b c]
    apply Nat.mul_le_mul_of_nonneg_left a b c h₁ h₂

/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5 -/
-- ex
lemma always_ge_0 : ∀(b : Nat), 0 ≤ b := by
  intros b
  by_cases h : b = 0
  · rw [h]
  · push_neg at h;
    rw [le_iff_lt_or_eq]
    left
    rw[Nat.lt_iff]
    constructor
    · exists b
    · symm; exact h

theorem Nat.exists_div_mod (n :Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  revert n ; apply induction
  · repeat exists 0
    simp
    dsimp [Nat.instLT]
    constructor
    · apply always_ge_0
    · push_neg
      rw [isPos_iff] at hq
      symm; exact hq
  · intros n ih
    obtain ⟨m, hm⟩ := ih
    obtain ⟨r, hr⟩ := hm
    obtain ⟨h0r, hrq, hdiv⟩ := hr
    rw [Nat.succ_eq_add_one]
    by_cases hr : r+1 = q
    · exists (m+1)
      exists 0
      simp
      constructor
      · dsimp [Nat.instLT]
        constructor
        · apply always_ge_0
        · push_neg; rw [isPos_iff] at hq; symm; exact hq
      · rw [hdiv, add_assoc, hr, add_mul]
        simp
    · exists m
      exists r+1
      constructor
      · apply always_ge_0
      · constructor
        · rw [lt_iff_succ_le] at hrq
          rw [succ_eq_add_one] at hrq
          rw [le_iff_lt_or_eq] at hrq
          cases hrq with
          | inl h_inl => exact h_inl
          | inr h_inr => contradiction
        · rw [hdiv, add_assoc]

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Exercise 2.3.4-/
-- ex
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  rw (occs := .pos [1]) [← Nat.one_succ, Nat.pow_succ, ← Nat.zero_succ, Nat.pow_succ, Nat.pow_zero]
  simp
  have ha_sq : a * a = a ^ (2 : Nat) := by
    rw [← Nat.one_succ, Nat.pow_succ, ← Nat.zero_succ, Nat.pow_succ, Nat.pow_zero]
    simp
  have hb_sq : b * b = b ^ (2 : Nat) := by
    rw [← Nat.one_succ, Nat.pow_succ, ← Nat.zero_succ, Nat.pow_succ, Nat.pow_zero]
    simp
  have hab : 2 * a * b = a * b + a * b := by
    rw [← Nat.one_succ, Nat.succ_mul]
    simp
    rw [Nat.add_mul]
  calc (a + b) * (a + b)
    _ = a * (a + b) + b * (a + b) := by rw [Nat.add_mul]
    _ = a * a + a * b + b * a + b * b := by rw [Nat.mul_add, Nat.mul_add, ← add_assoc ]
    _ = a * a + a * b + a * b + b * b := by rw [Nat.mul_comm b a]
    _ = a * a + 2 * a * b + b * b := by rw [add_assoc (a*a), ← hab]
    _ = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by rw[ha_sq, hb_sq]

end Chapter2
