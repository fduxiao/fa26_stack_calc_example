import StackCalc.MyTactics
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
  execute [Instruction.load "x", Instruction.push 2, Instruction.add] (∅!["x" ↦ 1]) []
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

trial compile_correct {e state}:
  execute (compile e) state [] = [e.eval state]
:= by
  induction e
  case const n =>
    simp [compile]
    unfold execute; simp
    unfold execute;
    simp
  case var x =>
    simp [compile]
    unfold execute; simp
    unfold execute
    simp
  case add e1 e2 ih1 ih2 =>
    simp [compile]
    sorry
  all_goals sorry


theorem execute_app {p1 p2 state stack}:
  execute (p1 ++ p2) state stack  = execute p2 state (execute p1 state stack )
:= by
  induction p1 generalizing stack
  case nil =>
    simp [execute]
  case cons p ps ih =>
    -- simp [execute]
    cases p
    case push n =>
      simp [execute]
      apply ih
    case load x =>
      simp [execute]
      grind
    case add =>
      simp [execute]
      split
      . apply ih
      . grind
      . grind
    all_goals
      simp [execute]
      split <;> grind

trial compile_correct {e state}:
  execute (compile e) state [] = [e.eval state]
:= by
  induction e
  case add e1 e2 ih1 ih2 =>
    simp [compile]
    rw [execute_app]
    rw [ih2]
    rw [execute_app]
    sorry
  all_goals sorry

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
    rw [ih2]
    rw [execute_app]
    rw [ih1]
    unfold execute; simp
    unfold execute
    simp
  all_goals
    simp [compile]
    grind [execute_app, execute]


theorem compile_correct {e state}:
  execute (compile e) state [] = [e.eval state]
:= by
  apply compile_correct_aux


def compile_optim_mult_2: Expr -> List Instruction
  | .const n => [Instruction.push n]
  | .var x => [Instruction.load x]
  | .add e1 e2 => compile_optim_mult_2 e2 ++ compile_optim_mult_2 e1 ++ [Instruction.add]
  | .sub e1 e2 => compile_optim_mult_2 e2 ++ compile_optim_mult_2 e1 ++ [Instruction.sub]
  | .mul (Expr.const 2) e2 => compile_optim_mult_2 e2 ++ [Instruction.lshift 1]
  | .mul e1 e2 => compile_optim_mult_2 e2 ++ compile_optim_mult_2 e1 ++ [Instruction.mul]
  | .div e1 e2 => compile_optim_mult_2 e2 ++ compile_optim_mult_2 e1 ++ [Instruction.div]


theorem app_lshift {r state prog stack n}:
  execute prog state stack = r :: stack →
  execute (prog ++ [Instruction.lshift n]) state stack = (r * 2^n) :: stack
:= by
  intro h
  simp [execute_app]
  rw [h]
  simp [execute]
  apply Nat.shiftLeft_eq


theorem compile_optim_mult_2_correct {e m stack}:
  execute (compile_optim_mult_2 e) m stack = e.eval m :: stack
:= by
  induction e generalizing stack
  case const n =>
    simp [compile_optim_mult_2, execute]
  case var x =>
    simp [compile_optim_mult_2, execute]
  case mul e1 e2 ih1 ih2 =>
    unfold compile_optim_mult_2
    split <;> simp_all <;> try grind [execute_app, execute]
    rw [app_lshift ih2]
    grind
  all_goals
    simp [compile_optim_mult_2]
    grind[execute_app, execute]


def compile_optim_mult_4: Expr -> List Instruction
  | .const n => [Instruction.push n]
  | .var x => [Instruction.load x]
  | .add e1 e2 => compile_optim_mult_4 e2 ++ compile_optim_mult_4 e1 ++ [Instruction.add]
  | .sub e1 e2 => compile_optim_mult_4 e2 ++ compile_optim_mult_4 e1 ++ [Instruction.sub]
  | .mul (Expr.const 2) e2 => compile_optim_mult_4 e2 ++ [Instruction.lshift 1]
  | .mul (Expr.const 4) e2 => compile_optim_mult_4 e2 ++ [Instruction.lshift 2]
  | .mul e1 e2 => compile_optim_mult_4 e2 ++ compile_optim_mult_4 e1 ++ [Instruction.mul]
  | .div e1 e2 => compile_optim_mult_4 e2 ++ compile_optim_mult_4 e1 ++ [Instruction.div]


theorem compile_optim_mult_4_correct {e m stack}:
  execute (compile_optim_mult_4 e) m stack = e.eval m :: stack
:= by
  induction e generalizing stack
  case const n =>
    simp [compile_optim_mult_4, execute]
  case var x =>
    simp [compile_optim_mult_4, execute]
  case mul e1 e2 ih1 ih2 =>
    unfold compile_optim_mult_4
    split <;>
      simp_all <;>
      grind [execute_app, execute, app_lshift ih2]
  all_goals
    simp [compile_optim_mult_4]
    grind[execute_app, execute]



def const_mul (n: Nat) (prog: List Instruction): List Instruction :=
  if n == 0 then [.push 0]
  else if n % 2 == 0 then
    const_mul (n / 2) (prog ++ [Instruction.lshift 1])
  else
    -- `n = n - 1 + 1`, so `n * r = (n - 1) * r + r`
    (const_mul (n - 1) prog) ++ prog ++ [Instruction.add]
termination_by n
decreasing_by
  . grind
  . grind


example x: const_mul 12 [Instruction.push x] = [
  .push 0,
  Instruction.push x,
  Instruction.lshift 1,
  Instruction.lshift 1,
  Instruction.lshift 1,
  Instruction.add,
  Instruction.push x,
  Instruction.lshift 1,
  Instruction.lshift 1,
  Instruction.add
]
:= by
  unfold const_mul; simp
  unfold const_mul; simp
  unfold const_mul; simp
  unfold const_mul; simp
  unfold const_mul; simp
  unfold const_mul; simp


example x: execute (const_mul 12 [Instruction.push x]) ∅ [] = [x * 12] := by
  simp [const_mul]
  simp [execute]
  simp [Nat.shiftLeft_eq]
  lia


theorem const_mul_correct {n r state prog}:
  (∀ {stack}, execute prog state stack = r :: stack) →
  ∀ {stack}, execute (const_mul n prog) state stack = n * r :: stack
:= by
  intro h stack
  induction n using Nat.strongRecOn generalizing r prog stack
  case ind n ih =>
    unfold const_mul
    split
    . simp [execute]
      simp_all
    . split
      . simp_all
        specialize ih (n/2) (by grind)
          (prog := prog ++ [Instruction.lshift 1])
          (r := r * 2)
          (app_lshift h) (stack := stack)
        simp_all
        calc n / 2 * (r * 2)
          _ = n / 2 * (2 * r) := by grind
          _ = (n / 2 * 2) * r := by grind
        congr
        apply Nat.div_mul_cancel
        grind
      . have k := @ih (n - 1) (by grind) _ _ h
        simp [execute_app]
        simp [k, h]
        simp [execute]
        calc r + (n - 1) * r
          _ = 1 * r + (n - 1) * r := by grind
          _ = (n - 1 + 1) * r := by grind
        congr
        grind


def compile_optim_mult: Expr -> List Instruction
  | .const n => [Instruction.push n]
  | .var x => [Instruction.load x]
  | .add e1 e2 => compile_optim_mult e2 ++ compile_optim_mult e1 ++ [Instruction.add]
  | .sub e1 e2 => compile_optim_mult e2 ++ compile_optim_mult e1 ++ [Instruction.sub]
  | .mul (Expr.const n) e2 => const_mul n (compile_optim_mult e2)
  | .mul e1 (Expr.const n) => const_mul n (compile_optim_mult e1)
  | .mul e1 e2 => compile_optim_mult e2 ++ compile_optim_mult e1 ++ [Instruction.mul]
  | .div e1 e2 => compile_optim_mult e2 ++ compile_optim_mult e1 ++ [Instruction.div]


theorem compile_optim_mult_correct {e m stack}:
  execute (compile_optim_mult e) m stack = e.eval m :: stack
:= by
  induction e generalizing stack
  case const n =>
    simp [compile_optim_mult, execute]
  case var x =>
    simp [compile_optim_mult, execute]
  case mul e1 e2 ih1 ih2 =>
    unfold compile_optim_mult
    split <;> simp_all
    . rewrite [const_mul_correct ih2]
      rfl
    . rewrite [const_mul_correct ih1]
      simp
      apply Nat.mul_comm
    . grind [execute_app, execute, const_mul_correct]
  all_goals
    simp [compile_optim_mult]
    grind [execute_app, execute, const_mul_correct]
