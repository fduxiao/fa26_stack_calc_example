import Lean


inductive Expr : Type where
  | const : UInt8 → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  deriving Repr, DecidableEq, Inhabited


instance: Coe Nat Expr where
  coe n := Expr.const (UInt8.ofNat n)


instance: Coe UInt8 Expr where
  coe := Expr.const


instance: Coe String Expr where
  coe := Expr.var


instance {n}: OfNat Expr n where
  ofNat := Expr.const (UInt8.ofNat n)


instance : Add Expr where
  add := Expr.add


instance : Sub Expr where
  sub := Expr.sub


instance : Mul Expr where
  mul := Expr.mul


instance : Div Expr where
  div := Expr.div


/-!
Pretty print of Uint8
-/
declare_syntax_cat uint8 (behavior := symbol)
syntax term : uint8
syntax "[uint8| " uint8 " ]" : term
macro_rules
  | `([uint8| $n:num]) => `((($n): UInt8))

example:
  [uint8| 1] = (UInt8.ofNat 1)
:= by rfl


@[app_unexpander UInt8.ofNat]
def unexpandUint8: Lean.PrettyPrinter.Unexpander
  | `($_ $x ) => `([uint8| $x:term ])
  | _ => throw ()


/-!
## Pretty printing of the language
-/


section
open Lean Elab Command Term PrettyPrinter Delaborator

@[app_unexpander Expr.const]
def unexpandConst: Unexpander
  | `($_ $x:num ) => `($x:num)
  | `($_ [uint8| $t:num ]) => `($t:num)
  | `($_ [uint8| $t:term ]) => `($t:term)
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
