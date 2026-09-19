import StackCalc.Syntax

/-!
Recall the definition of `Expr`.
```lean
inductive Expr : Type where
  | const : UInt8 → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
```
-/
