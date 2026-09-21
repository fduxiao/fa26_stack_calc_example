import Lean


inductive Expr : Type where
  | const : Nat → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  deriving Repr, DecidableEq, Inhabited


instance: Coe Nat Expr where
  coe n := Expr.const n


instance: Coe String Expr where
  coe := Expr.var


instance {n}: OfNat Expr n where
  ofNat := Expr.const n


instance : Add Expr where
  add := Expr.add


instance : Sub Expr where
  sub := Expr.sub


instance : Mul Expr where
  mul := Expr.mul


instance : Div Expr where
  div := Expr.div


/-!
## Pretty printing of the language
-/


section
open Lean Elab Command Term PrettyPrinter Delaborator

@[app_unexpander Expr.const]
def unexpandConst: Unexpander
  | `($_ $x:num ) => `($x:num)
  | `($_ $x) => `($x)
  | _ => throw ()


@[app_unexpander Expr.var]
def unexpandVar: Unexpander
  | `($_ $x:str ) => `($x:str)
  | `($_ $x) => `($x)
  | _ => throw ()


@[app_unexpander Expr.add]
def unexpandAdd: Unexpander
  | `($_ $x $y) => `($x + $y)
  | _ => throw ()


@[app_unexpander Expr.sub]
def unexpandSub: Unexpander
  | `($_ $x $y) => `($x - $y)
  | _ => throw ()


@[app_unexpander Expr.mul]
def unexpandMul: Unexpander
  | `($_ $x $y) => `($x * $y)
  | _ => throw ()


@[app_unexpander Expr.div]
def unexpandDiv: Unexpander
  | `($_ $x $y) => `($x / $y)
  | _ => throw ()


namespace ExprPrettyPrinter
scoped elab "expr_pp" stx:term:51: term => do
  let expr ← elabTerm stx none
  let pretty ← ppExpr expr
  let str := toString pretty
  pure <| toExpr str


def n: Nat := 3
def x: String := "x"

#guard expr_pp (1: _root_.Expr) = "1"
#guard expr_pp (Expr.const 3) = "3"
#guard expr_pp (n: _root_.Expr) = "n"
#guard expr_pp (Expr.var "x") = "\"x\""
#guard expr_pp (Expr.var x) = "x"
#guard expr_pp (x + 3 * "y": _root_.Expr) = "x + 3 * \"y\""
#guard expr_pp (x + (3 + 2) * "y": _root_.Expr) = "x + (3 + 2) * \"y\""
