import Mathlib.Tactic
import AnalysisSolutions.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue

In this (technical) epilogue, we show that the "Chapter 2" natural numbers `Chapter2.Nat` are
isomorphic in various standard senses to the standard natural numbers `ℕ`.

From this point onwards, `Chapter2.Nat` will be deprecated, and we will use the standard natural
numbers `ℕ` instead.  In particular, one should use the full Mathlib API for `ℕ` for all
subsequent chapters, in lieu of the `Chapter2.Nat` API.

Filling the sorries here requires both the Chapter2.Nat API and the Mathlib API for the standard
natural numbers `ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially
axiomatic, because we used a specific construction `Chapter2.Nat` of the natural numbers that was
an inductive type, and used that inductive type to construct a recursor.  Here, we give some
exercises to show how one can accomplish the same tasks directly from the Peano axioms, without
knowing the specific implementation of the natural numbers.
-/

abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn
    . rfl
    simp [succ_toNat, hn]
    symm
    exact succ_eq_add_one _
  right_inv n := by
    induction' n with n hn
    . rfl
    simp [←succ_eq_add_one]
    exact hn

-- ex
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl]
    rw [zero_add, _root_.Nat.zero_add]
  rw [Chapter2.Nat.succ_toNat n]
  rw [Chapter2.Nat.succ_add, Chapter2.Nat.succ_toNat]
  rw [hn]
  ring -- to rearrange the terms once we get into ℕ

-- ex
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' m with m' ih
  · simp
    rw [mul_comm]
  · rw [Chapter2.Nat.succ_toNat]
    rw [Chapter2.Nat.mul_succ, Nat.map_add, ih]
    ring

-- ex
-- This helped: https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/.E2.9C.94.20How.20to.20prove.20map_le_map_iff.20between.20Nats.20in.20a.20simpler.20way.3F/near/526681114
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  constructor
  · intro h
    rw [le_iff_exists_add] at h
    obtain ⟨c, hc⟩ := h
    rw [Nat.le_iff]
    use c
    rw [← equivNat.injective.eq_iff, Equiv.coe_fn_mk, map_add, hc, add_left_cancel_iff]
    symm
    apply equivNat.right_inv
  intro h
  obtain ⟨a, ha⟩ := h
  rw [le_iff_exists_add]
  use a.toNat
  rw [ha]
  apply map_add

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

-- ex
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = n^m := by
  induction m with
  | zero => simp
            have hz : zero = 0 := by rfl
            rw [hz, Nat.pow_zero]
  | succ k ih => rw [Chapter2.Nat.pow_succ]
                 rw [_root_.pow_succ, ih]
                 congr
                 apply equivNat.left_inv

/-- The Peano axioms for an abstract type `Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with `unfold Function.Injective`, although it is not strictly necessary. -/
-- ex
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast  := by
  intros a₁ a₂ h
  induction' a₁ with k ih generalizing a₂
  · rw [natCast] at h
    cases' a₂ with l
    · rfl
    · rw [natCast] at h
      have h_nez : P.succ (P.natCast l) ≠ P.zero := by apply P.succ_ne
      symm at h
      apply h_nez at h
      contradiction
  · rw [natCast] at h
    cases' a₂ with l
    · rw [natCast] at h
      have h_con := P.succ_ne (P.natCast k)
      contradiction
    · simp
      apply ih
      rw [natCast] at h
      apply P.succ_cancel
      exact h

/-- One can start the proof here with `unfold Function.Surjective`, although it is not strictly necessary. -/
-- ex
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  unfold Function.Surjective
  apply P.induction
  · use 0
  · intros n h
    obtain ⟨k, hk⟩ := h
    use k+1
    rw [natCast, hk]

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol `≃` is an alias for Mathlib's `Equiv` class; for instance `P.Nat ≃ Q.Nat` is
    an alias for `_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the `Equiv` class.
    Some of this API can be invoked automatically via the `simp` tactic. -/
-- ex
abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by
    rw [← equiv.equiv_zero]
    simp
  equiv_succ n := by
    apply_fun equiv.equiv
    rw [equiv.equiv_succ]
    simp

/-- This exercise will require application of Mathlib's API for the `Equiv` class.
    Some of this API can be invoked automatically via the `simp` tactic. -/
-- ex
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    simp
    rw [equiv1.equiv_zero, equiv2.equiv_zero]
  equiv_succ n := by
    simp
    rw [equiv1.equiv_succ, equiv2.equiv_succ]

/-- Useful Mathlib tools for inverting bijections include `Function.surjInv` and `Function.invFun`. -/
-- ex
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := by
      apply Function.invFun P.natCast
    left_inv := by
      apply Function.leftInverse_invFun (natCast_injective P)
    right_inv := by
      apply Function.rightInverse_invFun (natCast_surjective P)
  }
  equiv_zero := by rfl
  equiv_succ n := by rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
-- ex
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q := by
  have h_pequiv : Equiv P Mathlib_Nat := by
    apply Equiv.symm
    apply Equiv.fromNat
  have h_qequiv : Equiv Mathlib_Nat Q := by apply Equiv.fromNat
  apply Equiv.trans h_pequiv h_qequiv

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
-- ex
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  revert n
  apply P.induction
  · rw[equiv_zero1, equiv_zero2]
  · intros n h
    rw [equiv_succ1, equiv_succ2, h]

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
-- ex
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  sorry

end PeanoAxioms
