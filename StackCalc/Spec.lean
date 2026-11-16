import StackCalc.Motivation
import StackCalc.Expr
/-!
## Specification of an `Expr`
For example, we want an index based on variable `x`, `y` such that
it is larger than or equal to two and is monotone in `x` and `y`.
-/

namespace StackCalc.SpecExample

def e1: Expr := "x" * "y" + 1
def e2: Expr := "x" * "x" + "y" * "y" + 3

def montone_in_xy (e: Expr): Prop :=
  ∀ m1 m2: Map,
    m1 "x" ≤ m2 "x" →
    m1 "y" ≤ m2 "y" →
    e.eval m1 ≤ e.eval m2

def larger_than_or_equal_to_two (e: Expr): Prop :=
  ∀ m: Map, e.eval m ≥ 2

theorem e1_monotone_in_xy: montone_in_xy e1 := by
  intro m1 m2 H1 H2
  unfold e1
  simp [Expr.eval]
  apply Nat.mul_le_mul
  . exact H1
  . exact H2

theorem e2_larger_than_or_equal_to_two: larger_than_or_equal_to_two e2 := by
  intro m
  unfold e2
  simp only [Expr.eval]
  lia

theorem e1_not_larger_than_or_equal_to_two: ¬ larger_than_or_equal_to_two e1 := by
  intro H
  let m: Map := ∅![ "x" ↦ 0, "y" ↦ 0]
  specialize H m
  unfold e1 at H
  simp only [Expr.eval] at H
  simp [m, Map.update, -ge_iff_le, -Nat.mul_zero, -Nat.zero_mul, -Nat.reduceMul] at H
  contradiction


open Motivation

theorem e1_eq_f1: ∀ m: Map, e1.eval m = f1 (m "x") (m "y") := by
  intro m
  unfold e1 f1
  simp [Expr.eval]

theorem e2_eq_f2: ∀ m: Map, e2.eval m = f2 (m "x") (m "y") := by
  intro m
  unfold e2 f2
  simp [Expr.eval]

theorem e1_monotone_in_xy': montone_in_xy e1 := by
  intro m1 m2 H1 H2
  rw [e1_eq_f1]
  apply f1_monotone_in_xy
  . exact H1
  . exact H2

theorem e2_larger_than_or_equal_to_two': larger_than_or_equal_to_two e2 := by
  intro m
  rw [e2_eq_f2]
  apply f2_larger_than_or_equal_to_two
