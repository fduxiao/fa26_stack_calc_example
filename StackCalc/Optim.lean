import StackCalc.Expr


class Optim (optim: Expr → Expr) where
  equiv: forall e: Expr, e ≡ optim e


def fold0: Expr → Expr
  | Expr.add e1 e2 =>
    match fold0 e1, fold0 e2 with
      | Expr.const 0, e2 => e2
      | e1, Expr.const 0 => e1
      | e1, e2 => Expr.add e1 e2
  | Expr.sub e1 e2 =>
    match fold0 e1, fold0 e2 with
      | e1, Expr.const 0 => e1
      | e1, e2 => Expr.sub e1 e2
  | Expr.mul e1 e2 =>
    match fold0 e1, fold0 e2 with
      | Expr.const 0, _ => Expr.const 0
      | _, Expr.const 0 => Expr.const 0
      | e1, e2 => Expr.mul e1 e2
  | Expr.div e1 e2 =>
    match fold0 e1, fold0 e2 with
      | Expr.const 0, _ => Expr.const 0
      | e1, e2 => Expr.div e1 e2
  | e => e


instance: Optim fold0 where
  equiv e := by
    induction e
    case const n =>
      simp [fold0]
      rfl
    case var s =>
      simp [fold0]
      rfl
    case add e1 e2 ih1 ih2 =>
      simp [fold0]
      split
      . intro m
        simp_all
        specialize ih1 m
        specialize ih2 m
        simp_all
      . expr_equiv
      . expr_equiv
    case sub e1 e2 ih1 ih2 =>
      simp [fold0]
      split <;> expr_equiv
    case mul e1 e2 ih1 ih2 =>
      simp [fold0]
      split <;> expr_equiv
    case div e1 e2 ih1 ih2 =>
      simp [fold0]
      split <;> expr_equiv


theorem fold0_idempotent: forall e: Expr, fold0 (fold0 e) = fold0 e := by
  intro e
  induction e
  case const n =>
    simp [fold0]
  case var s =>
    simp [fold0]
  case add e1 e2 ih1 ih2 =>
    simp [fold0]
    split
    . exact ih2
    . exact ih1
    . simp [fold0]
      split
      . simp_all
      . simp_all
      . simp_all
  case sub e1 e2 ih1 ih2 =>
    repeat
      simp [fold0] <;>
      split <;>
      simp_all
  case mul e1 e2 ih1 ih2 =>
    repeat
      simp [fold0] <;>
      split <;>
      simp_all
  case div e1 e2 ih1 ih2 =>
    repeat
      simp [fold0] <;>
      split <;>
      simp_all
