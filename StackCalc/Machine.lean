import StackCalc.Map
import StackCalc.Expr


inductive Instruction : Type where
  | push : Nat → Instruction
  | load : String → Instruction
  | add : Instruction
  | sub : Instruction
  | mul : Instruction
  | div : Instruction
  | lshift: Nat → Instruction
  | rshift: Nat → Instruction
  deriving Repr, DecidableEq, Inhabited


def execute (prog: List Instruction) (m: Map) (s: List Nat): (List Nat) :=
  match prog with
  | [] => s
  | p :: ps =>
    match p with
    | Instruction.push n => execute ps m (n :: s)
    | Instruction.load x => execute ps m (m x :: s)
    | Instruction.add =>
      match s with
      | n1 :: n2 :: s' => execute ps m ((n1 + n2) :: s')
      | [_] | [] => execute ps m []
    | Instruction.sub =>
      match s with
      | n1 :: n2 :: s' => execute ps m ((n1 - n2) :: s')
      | [_] | [] => execute ps m []
    | Instruction.mul =>
      match s with
      | n1 :: n2 :: s' => execute ps m ((n1 * n2) :: s')
      | [_] | [] => execute ps m []
    | Instruction.div =>
      match s with
      | n1 :: n2 :: s' => execute ps m ((n1 / n2) :: s')
      | [_] | [] => execute ps m []
    | Instruction.lshift k =>
      match s with
      | n1 :: s' => execute ps m ((n1 <<< k) :: s')
      | [] => execute ps m []
    | Instruction.rshift k =>
      match s with
      | n1 :: s' => execute ps m ((n1 >>> k) :: s')
      | [] => execute ps m []

/-!
Examples of executing instructions.
-/

example:
  execute [Instruction.push 1, Instruction.push 2, Instruction.add] ∅ []
  =
  [3]
:= by
  unfold execute; simp
  unfold execute; simp
  unfold execute; simp
  unfold execute;
  simp


example:
  execute [Instruction.load "x", Instruction.push 2, Instruction.add] (∅["x" ↦ 1]) []
  =
  [3]
:= by
  unfold execute; simp
  unfold execute; simp
  unfold execute; simp
  unfold execute
  simp


def compile (e: Expr): List Instruction :=
  match e with
  | Expr.const n => [Instruction.push n]
  | Expr.var x => [Instruction.load x]
  | Expr.add e1 e2 => compile e2 ++ compile e1 ++ [Instruction.add]
  | Expr.sub e1 e2 => compile e2 ++ compile e1 ++ [Instruction.sub]
  | Expr.mul e1 e2 => compile e2 ++ compile e1 ++ [Instruction.mul]
  | Expr.div e1 e2 => compile e2 ++ compile e1 ++ [Instruction.div]


example:
  compile (Expr.add (Expr.const 1) (Expr.const 2))
  =
  [Instruction.push 2, Instruction.push 1, Instruction.add]
:= by
  rfl


theorem execute_app {p1 p2 m stack}:
  execute (p1 ++ p2) m stack  = execute p2 m (execute p1 m stack )
:= by
  induction p1 generalizing stack
  case nil =>
    simp [execute]
  case cons p ps ih =>
    simp [execute]
    cases p
    case push n =>
      grind
    case load x =>
      grind
    case add =>
      simp
      split
      . apply ih
      . apply ih
      . apply ih
    all_goals
      simp
      split <;> grind


theorem compile_correct_aux {e m stack}:
  execute (compile e) m stack = e.eval m :: stack
:= by
  induction e generalizing stack
  case const n =>
    simp [compile, execute]
  case var x =>
    simp [compile, execute]
  case add e1 e2 ih1 ih2 =>
    simp [compile]
    rw [execute_app]
    rw [execute_app]
    rw [ih1, ih2]
    simp [execute]
  all_goals
    simp [compile]
    grind[execute_app, execute]


theorem compile_correct {e m}:
  execute (compile e) m [] = [e.eval m]
:= by
  apply compile_correct_aux
