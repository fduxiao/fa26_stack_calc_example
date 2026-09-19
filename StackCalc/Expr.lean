import StackCalc.Syntax
import StackCalc.Map

/-!
# We build the semantic of `Expr` in this file.
Recall the definition of `Expr`.
```lean
inductive Expr : Type where
  | const : UInt8 → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
```
It is evaluated under a `Map`, which is just a function from `String` to `UInt8`.
-/


def Expr.eval (e: Expr) (m: Map): UInt8 :=
  match e with
  | Expr.const n => n
  | Expr.var x => m x
  | Expr.add e1 e2 => e1.eval m + e2.eval m
  | Expr.sub e1 e2 => e1.eval m - e2.eval m
  | Expr.mul e1 e2 => e1.eval m * e2.eval m
  | Expr.div e1 e2 => e1.eval m / e2.eval m
