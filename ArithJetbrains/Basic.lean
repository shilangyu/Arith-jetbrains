inductive Op where
  | add
  | sub
  | mul
  | div

inductive Term where
  | const : Nat -> Term
  | op : Op -> Term → Term → Term

inductive Result (α : Type) where
  | ok : α → Result α
  | divByZero : Result α

instance : Monad Result where
  pure := Result.ok
  bind
    | Result.ok n, f => f n
    | Result.divByZero, _ => Result.divByZero

def eval : Term → Result Nat
  | .const n => pure n
  | .op op t1 t2 =>
      eval t1 >>= fun r1 =>
      eval t2 >>= fun r2 =>
      match op with
      | .add => pure (r1 + r2)
      | .sub => pure (r1 - r2)
      | .mul => pure (r1 * r2)
      | .div => if r2 == 0 then Result.divByZero else pure (r1 / r2)

#eval eval (Term.op .add (Term.const 5) (Term.op .mul (Term.const 2) (Term.const 3))) -- 11
#eval eval (Term.op .div (Term.const 10) (Term.op .sub (Term.const 5) (Term.const 5))) -- divByZero
