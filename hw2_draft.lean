import Mathlib.Tactic

/-!
# Homework 2 draft

This homework practices the material from:

* Negation and Constructive Contradiction
* Classical Reasoning
* Equality and Rewriting

Replace every `sorry` with a term or proof of the required type.
Do not change whether an exercise is written with `by`.
Complete exercises without `by` directly after `:=`; complete exercises with
`by` using tactics. In tactic mode, build the proof step by step; do not give
`exact` a complete proof term for the whole exercise. Follow any additional
instructions above an exercise.

The point of the homework is to practice the methods covered in class and the
lecture notes so far. Use only those methods, not more advanced tactics or
library theorems that already prove the result. Prove each exercise
independently.

-/

namespace Homework2

/-! ## Negation and Constructive Contradiction -/

theorem exercise01 (P Q : Prop) : (P → Q) → P → ¬ ¬ Q :=
  fun hPQ hP hQF => hQF (hPQ hP)

theorem exercise02 (P Q : Prop) : P ∧ ¬ Q → ¬ (P → Q) :=
  fun hPnQ hPQ => hPnQ.2 (hPQ (hPnQ.1))

theorem exercise03 (P Q : Prop) : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q :=
  fun hPQ => ⟨fun hP => hPQ (Or.inl hP), fun hQ => hPQ (Or.inr hQ)⟩

-- Prove the statement constructively.

theorem exercise04 (P Q : Prop) : P ∨ Q → ¬ P → Q := by
  intro hPQ hnP
  rcases hPQ with hP | hQ
  · exact False.elim (hnP hP)
  · exact hQ

-- Now prove the same statement clasically, using `Classical.byContradiction`.

#check Classical.byContradiction
#check Or.elim

theorem exercise04_classical (P Q : Prop) : P ∨ Q → ¬ P → Q :=
  fun hPQ hnP => Classical.byContradiction (
    fun hnQ =>
      Or.elim hPQ
        (fun hP => hnP hP)
        (fun hQ => hnQ hQ)
  )

-- Prove this constructive De Morgan direction.

theorem exercise05 (P Q : Prop) : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
  intro hnPnQ hPQ
  rcases hnPnQ with hnP | hnQ
  · exact hnP hPQ.1
  · exact hnQ hPQ.2

/-! ## Constructive and Classical Proofs -/

-- Triple negation. Decide whether a constructive proof is possible. If it is,
-- prove the statement constructively; otherwise, prove it classically.

theorem exercise06 (P : Prop) : ¬ ¬ ¬ P → ¬ P := by
  sorry

-- Decide whether a constructive proof is possible. If it is, prove the
-- statement constructively; otherwise, prove it classically.

theorem exercise07 (P : Prop) : P ∨ ¬ P → (¬ ¬ P → P) := by
  sorry

-- Assume double-negation elimination for `P ∨ ¬ P` and prove excluded middle.
-- Exercises 07 and 08 together show that excluded middle and
-- double-negation elimination are equivalent.

theorem exercise08 (P : Prop)
    (dne : ¬ ¬ (P ∨ ¬ P) → P ∨ ¬ P) : P ∨ ¬ P := by
  sorry

-- You may find `Classical.byContradiction` helpful.

theorem exercise09 (P Q : Prop) : ¬ ¬ (P ∧ Q) → Q ∧ P :=
  sorry

theorem exercise10 (P Q : Prop) : (P → Q) → ¬ P ∨ Q :=
  sorry

theorem exercise11 (P Q : Prop) : ¬ ¬ (P ∨ Q) → ¬ P → Q := by
  sorry

theorem exercise12 (P Q R : Prop) (h : ¬ Q → ¬ P ∨ ¬ R) :
    P ∧ R → Q := by
  sorry

theorem exercise13 (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  sorry

-- Decide whether a constructive proof is possible. If it is, prove the
-- statement constructively; otherwise, prove it classically.

theorem exercise14 (P Q : Prop) : ¬ (P → Q) → P ∧ ¬ Q := by
  sorry

-- Peirce's law. You may find `by_contra` helpful.

theorem exercise15 (P Q : Prop) : ((P → Q) → P) → P := by
  sorry

/-! ## Equality and Rewriting -/

theorem exercise16 (A : Type) (R : A → Prop)
    (x y : A) (hxy : x = y) (hy : R y) : R x :=
  sorry

theorem exercise17 (A B C : Type) (f : A → B) (g : B → C)
    (x y : A) (hxy : x = y) : g (f x) = g (f y) :=
  sorry

theorem exercise18 (A : Type) (x y z w : A)
    (hxy : x = y) (hzy : z = y) (hzw : z = w) : x = w :=
  sorry

theorem exercise19 (A B : Type) (f : A → B) (x y z : A)
    (hxz : x = z) (hyz : y = z) : f y = f x := by
  sorry

theorem exercise20 (A : Type) (R : A → A → Prop) (x y z : A)
    (hxy : x = y) (hzy : z = y) (hR : R x y) : R y z := by
  sorry

theorem exercise21 (A B : Type) (f : A → B) (x y : A) (hxy : x = y) :
    (fun p : A × A ↦ f p.1) (x, y) = f y := by
  sorry

theorem exercise22 (A B : Type) (f : A → B) (x y : A) (hxy : x = y) :
    (let p := (x, f x); p.2) = f y := by
  sorry

theorem exercise23 (A B C : Type) (f : A → C) (g : B → C) (b : B) :
    Sum.elim f g (Sum.inr b) = g b := by
  sorry

-- You may find a case split on `x` helpful.

theorem exercise24 (A B : Type) (x : A ⊕ B) :
    Sum.elim Sum.inr Sum.inl
      (Sum.elim Sum.inr Sum.inl x : B ⊕ A) = x := by
  sorry

-- Use a `calc` block.

theorem exercise25 (A B C : Type) (f : A → B) (g : B → C)
    (x : A) (y : B) (z : C)
    (h : f x = y) (k : z = g y) : g (f x) = z := by
  sorry

-- Hint: The two sides are values of the functions appearing in `heq`, but at
-- different pairs. Use `change` to restate the target as an equality between
-- those function applications. Then use `rw`.
-- Adapted from Reintroduction to Proofs, Equality World, Level 11:
-- https://github.com/emilyriehl/ReintroductionToProofs/blob/main/Game/Levels/EqualityWorld/L11_BossLevel.lean

theorem exercise26 (A B C D : Type) (f g : A × B → C) (h k : C → D)
    (a a' : A) (b b' : B) (ha : a = a') (hb : b = b')
    (heq : (fun p : A × B ↦ h (f p)) = (fun p : A × B ↦ k (g p))) :
    h (f (a, b)) = k (g (a', b')) := by
  sorry

end Homework2
