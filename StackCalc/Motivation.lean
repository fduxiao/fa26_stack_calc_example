namespace Motivation

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


theorem f2_larger_than_or_equal_to_two:
  forall x y: Nat,
    f2 x y ≥ 2
:= by
  intro x y
  simp only [f2]
  lia

theorem f1_not_larger_than_or_equal_to_two:
  ¬ forall x y: Nat,
    f1 x y ≥ 2
:= by
  intro H
  simp [f1] at H
  specialize H 0 0
  simp at H
