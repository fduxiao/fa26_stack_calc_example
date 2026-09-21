def Map := String → Nat


def Map.empty : Map := fun _ => 0

def Map.update (m: Map) (x: String) (n: Nat): Map :=
  fun y => if x = y then n else m y


@[simp]
theorem Map.update_eq (m: Map) (x: String) (n: Nat):
  (m.update x n) x = n
:= by
  simp [Map.update]


theorem Map.update_neq (m: Map) (x y: String) (n: Nat):
  x ≠ y → (m.update x n) y = m y
:= by
  intro h
  simp [Map.update, h]



theorem Map.update_shadow (m: Map) (x: String) (n1 n2: Nat):
  (m.update x n1).update x n2 = m.update x n2
:= by
  funext y
  simp [Map.update]
  simp_all


theorem Map.update_perm (m: Map) (x y: String) (n1 n2: Nat):
  x ≠ y → (m.update x n1).update y n2 = (m.update y n2).update x n1
:= by
  intro h
  funext z
  simp_all [Map.update]
  split
  . simp_all
  . simp_all


instance: Inhabited Map where
  default := Map.empty


instance: EmptyCollection Map where
  emptyCollection := Map.empty


syntax term "[" (term " ↦ " term),+ "]" : term
macro_rules
  | `($m[$x ↦ $n]) => `(Map.update $m $x $n)
  | `($m[$x ↦ $n , $[ $xs ↦ $ns ],* ]) => `($m[$x ↦ $n][$[ $xs ↦ $ns ],* ])


@[app_unexpander Map.update]
def unexpandMapUpdate: Lean.PrettyPrinter.Unexpander
  | `($_ $m $x $n) =>
    match m with
    | `($m[ $[$xs ↦ $ns],* ]) => `($m[$[$xs ↦ $ns],*, $x ↦ $n])
    | _ => `($m[$x ↦ $n])
  | _ => throw ()
