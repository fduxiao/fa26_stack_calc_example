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


def execute (prog: List Instruction) (state: Map) (stack: List Nat): (List Nat) :=
  match prog with
  | [] => stack
  | p :: ps =>
    match p with
    | Instruction.push n => execute ps state (n :: stack)
    | Instruction.load x => execute ps state (state x :: stack)
    | Instruction.add =>
      match stack with
      | n1 :: n2 :: s => execute ps state ((n1 + n2) :: s)
      | [_] | [] => execute ps state []
    | Instruction.sub =>
      match stack with
      | n1 :: n2 :: s => execute ps state ((n1 - n2) :: s)
      | [_] | [] => execute ps state []
    | Instruction.mul =>
      match stack with
      | n1 :: n2 :: s => execute ps state ((n1 * n2) :: s)
      | [_] | [] => execute ps state []
    | Instruction.div =>
      match stack with
      | n1 :: n2 :: s => execute ps state ((n1 / n2) :: s)
      | [_] | [] => execute ps state []
    | Instruction.lshift k =>
      match stack with
      | n1 :: s => execute ps state ((n1 <<< k) :: s)
      | [] => execute ps state []
    | Instruction.rshift k =>
      match stack with
      | n1 :: s => execute ps state ((n1 >>> k) :: s)
      | [] => execute ps state []

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



theorem execute_app {p1 p2 state stack}:
  execute (p1 ++ p2) state stack  = execute p2 state (execute p1 state stack )
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


theorem compile_correct_aux {e state stack}:
  execute (compile e) state stack = e.eval state :: stack
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


theorem compile_correct {e state}:
  execute (compile e) state [] = [e.eval state]
:= by
  apply compile_correct_aux
