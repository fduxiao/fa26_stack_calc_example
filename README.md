# StackCalc

A naive stack calculator.

## Motivation
Given a Lean function, we can prove its properties:
```lean
def f1 (x y: Nat): Nat := x * y + 1
def f2 (x y: Nat): Nat := x * x + y * y + 3

theorem f1_monotone_in_xy:
  forall x1 x2 y1 y2: Nat,
    x1 ≤ x2 →
    y1 ≤ y2 →
    f1 x1 y1 ≤ f1 x2 y2
:= by
  intro x1 x2 y1 y2 h1 h2
  simp [f1]
  apply Nat.mul_le_mul
  . exact h1
  . exact h2
```
However, if we want to make use of this code, e.g., using the generated C code for some real-world algorithm,
the functional essence of Lean means it is less efficient than some real C code.

Thus, instead of using Lean code directly, I model the arithmetic expressions as an inductive type and compile 
them to a stack machine. I also shows some naive examples of optimizations.

## Package Structure
- [StackCalc.Motivation](./StackCalc/Motivation.lean): Motivating examples
- [StackCalc.Syntax](./StackCalc/Syntax.lean): Syntax of the target language
- [StackCalc.Expr](./StackCalc/Expr.lean): Semantics and equivalence
- [StackCalc.Spec](./StackCalc/Spec.lean): Specification about the target language
- [StackCalc.Optim](./StackCalc/Optim.lean): Optimization
- [StackCalc.Machine](./StackCalc/Machine.lean): Stack machine and compilation
