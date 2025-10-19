inductive Term where
  | const : Nat -> Term
  | add : Term → Term → Term
  | sub : Term → Term → Term
  | mul : Term → Term → Term
  | div : Term → Term → Term

inductive Result (α : Type) where
  | ok : α → Result α
  | divByZero : Result α

instance : Monad Result where
  pure := Result.ok
  bind
    | Result.ok n, f => f n
    | Result.divByZero, _ => Result.divByZero

def eval : Term → Result Nat
  | Term.const n => pure n
  | Term.add t1 t2 => eval t1 >>= fun r1 =>
                      eval t2 >>= fun r2 =>
                      pure (r1 + r2)
  | Term.sub t1 t2 => eval t1 >>= fun r1 =>
                      eval t2 >>= fun r2 =>
                      pure (r1 - r2)
  | Term.mul t1 t2 => eval t1 >>= fun r1 =>
                      eval t2 >>= fun r2 =>
                      pure (r1 * r2)
  | Term.div t1 t2 => eval t1 >>= fun r1 =>
                      eval t2 >>= fun r2 =>
                      if r2 == 0 then Result.divByZero else Result.ok (r1 / r2)

#eval eval (Term.add (Term.const 5) (Term.mul (Term.const 2) (Term.const 3))) -- 11
#eval eval (Term.div (Term.const 10) (Term.sub (Term.const 5) (Term.const 5))) -- divByZero
