import StackCalc.Syntax
import StackCalc.Map

/-!
# We build the semantic of `Expr` in this file.
Recall the definition of `Expr`.
```lean
inductive Expr : Type where
  | const : Nat → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
```
It is evaluated under a `Map`, which is just a function from `String → Nat`.
-/

namespace ExprExamples

example: 3 = Expr.const 3 := rfl
example (n: Nat):
  (n + "x": Expr) = Expr.add (Expr.const n) (Expr.var "x")
:= rfl

example (x: String):
  ("x" + x * (5 + "y") + 3) =
  Expr.add
    (Expr.add (Expr.var "x")
      (Expr.mul
        (Expr.var x)
        (Expr.add (Expr.const 5) (Expr.var "y"))))
    (Expr.const 3)
:= rfl

end ExprExamples


@[simp]
def Expr.eval (e: Expr) (m: Map): Nat :=
  match e with
  | Expr.const n => n
  | Expr.var x => m x
  | Expr.add e1 e2 => e1.eval m + e2.eval m
  | Expr.sub e1 e2 => e1.eval m - e2.eval m
  | Expr.mul e1 e2 => e1.eval m * e2.eval m
  | Expr.div e1 e2 => e1.eval m / e2.eval m

example:
  let m: Map := ∅ !["x" ↦ 0, "y" ↦ 1]
  Expr.eval ("x" + 5 * ("y" + 3)  + 1) m = 21
:= by
  intro m
  simp
  rfl

/-!
## Necessary simplifications
-/
@[simp]
theorem Expr.eval_const {m} {n: Nat}: (Expr.const n).eval m = n := rfl

@[simp]
theorem Expr.eval_var {m} {x: String}: (Expr.var x).eval m = m x := rfl

@[simp]
theorem Expr.eval_add {m} {e1 e2: Expr}: (e1 + e2).eval m = e1.eval m + e2.eval m := rfl

@[simp]
theorem Expr.eval_sub {m} {e1 e2: Expr}: (e1 - e2).eval m = e1.eval m - e2.eval m := rfl

@[simp]
theorem Expr.eval_mul {m} {e1 e2: Expr}: (e1 * e2).eval m = e1.eval m * e2.eval m := rfl

@[simp]
theorem Expr.eval_div {m} {e1 e2: Expr}: (e1 / e2).eval m = e1.eval m / e2.eval m := rfl


def Expr.equiv (e1 e2: Expr): Prop :=
  ∀ m: Map, e1.eval m = e2.eval m


notation:51 e1: 51 " ≡ " e2: 52 => Expr.equiv e1 e2


@[refl]
theorem Expr.equiv.refl {e: Expr}: e ≡ e := by
  intro m
  rfl


@[symm]
theorem Expr.equiv.symm {e1 e2: Expr}: e1 ≡ e2 → e2 ≡ e1 := by
  intro h
  intro m
  specialize h m
  simp_all


theorem Expr.equiv.trans {e1 e2 e3: Expr}: e1 ≡ e2 → e2 ≡ e3 → e1 ≡ e3 := by
  intro h1 h2
  intro m
  specialize h1 m
  specialize h2 m
  simp_all


instance: Trans Expr.equiv Expr.equiv Expr.equiv where
  trans := Expr.equiv.trans


theorem Expr.equiv.add {e1 e1' e2 e2': Expr}:
  e1 ≡ e1' →
  e2 ≡ e2' →
  e1 + e2 ≡ e1' + e2'
:= by
  intro h1 h2
  intro m
  simp
  specialize h1 m
  specialize h2 m
  simp_all


theorem Expr.equiv.sub {e1 e1' e2 e2': Expr}:
  e1 ≡ e1' →
  e2 ≡ e2' →
  e1 - e2 ≡ e1' - e2'
:= by
  intro h1 h2
  intro m
  simp
  specialize h1 m
  specialize h2 m
  simp_all


theorem Expr.equiv.mul {e1 e1' e2 e2': Expr}:
  e1 ≡ e1' →
  e2 ≡ e2' →
  e1 * e2 ≡ e1' * e2'
:= by
  intro h1 h2
  intro m
  simp
  specialize h1 m
  specialize h2 m
  simp_all


theorem Expr.equiv.div {e1 e1' e2 e2': Expr}:
  e1 ≡ e1' →
  e2 ≡ e2' →
  e1 / e2 ≡ e1' / e2'
:= by
  intro h1 h2
  intro m
  simp
  specialize h1 m
  specialize h2 m
  simp_all



macro "equiv_congr": tactic => `(tactic|
  repeat(
    intros <;>
    (first
      | apply Expr.equiv.add | apply Expr.equiv.sub
      | apply Expr.equiv.mul | apply Expr.equiv.div) <;>
    (try simp_all) <;>
    first
      | rfl | symm | grind
  )
)

theorem Expr.equiv.add1 {e1 e1' e2: Expr}:
  e1 ≡ e1' →
  e1 + e2 ≡ e1' + e2
:= by
  equiv_congr


theorem Expr.equiv.add2 {e1 e2 e2': Expr}:
  e2 ≡ e2' →
  e1 + e2 ≡ e1 + e2'
:= by
  equiv_congr


/-!
## Arithmetic laws
-/

section
open Lean Elab Tactic Meta

elab "expr_equiv" : tactic => withMainContext do
    Tactic.evalTactic (← `(tactic| intros))
    let goal ← getMainTarget
    if ! goal.isAppOf `Expr.equiv then
      throwError "Goals must be of the form `e1 ≡ e2`"
    -- intro variable
    Tactic.evalTactic (← `(tactic| intro m))

    -- specialize hypothesis
    let ctx ← Lean.MonadLCtx.getLCtx
    for decl in ctx do
      let declName := decl.userName
      let ident := Lean.mkIdent declName
      Tactic.evalTactic (← `(tactic| try have _ := $ident m))

    -- grind
    Tactic.evalTactic (← `(tactic| (
      try (simp_all [Expr.eval]) <;>
      first | grind [Expr.eval, Expr.equiv, Expr.equiv.refl, Expr.equiv.symm] | trivial
    )))
end

theorem Expr.equiv_add_comm {e1 e2: Expr}:
  e1 + e2 ≡ e2 + e1
:= by
  expr_equiv


theorem Expr.equiv_add_assoc {e1 e2 e3: Expr}:
  e1 + (e2 + e3) ≡ (e1 + e2) + e3
:= by
  expr_equiv


theorem Expr.equiv_mul_comm {e1 e2: Expr}:
  e1 * e2 ≡ e2 * e1
:= by
  expr_equiv


theorem Expr.equiv_mul_assoc {e1 e2 e3: Expr}:
  e1 * (e2 * e3) ≡ (e1 * e2) * e3
:= by
  expr_equiv


theorem Expr.equiv_mul_add_distr {e1 e2 e3: Expr}:
  e1 * (e2 + e3) ≡ e1 * e2 + e1 * e3
:= by
  expr_equiv


theorem Expr.equiv.add1' {e1 e1' e2: Expr}:
  e1 ≡ e1' →
  e1 + e2 ≡ e1' + e2
:= by
  expr_equiv
