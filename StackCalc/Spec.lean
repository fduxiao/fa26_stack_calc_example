import StackCalc.Expr
/-!
## Specification of an `Expr`
For example, we want an index based on variable `x`, `y` such that
it is larger than or equal to two and is monotone in `x` and `y`.
-/

namespace StackCalc.SpecExample

def expr_spec (e: Expr): Prop :=
  (∀ m: Map, e.eval m ≥ 2)
  ∧
  (∀ m1 m2: Map, m1 "x" ≤ m2 "x" → m1 "y" ≤ m2 "y" → e.eval m1 ≤ e.eval m2)


def e: Expr := "x" * "y" + 2


theorem e_spec: expr_spec e := by
  unfold expr_spec
  and_intros <;> unfold e
  . intro m
    simp only [Expr.eval]
    omega
  . intro m1 m2 h1 h2
    simp_all
    apply Nat.mul_le_mul
    . exact h1
    . omega
