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

@[simp]
instance : Monad Result where
  pure := Result.ok
  bind
    | Result.ok n, f => f n
    | Result.divByZero, _ => Result.divByZero

@[simp]
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


inductive Step : Term -> Term -> Prop where
  | opCtx1 : ∀ op t1 t1' t2,
      Step t1 t1' →
      Step (Term.op op t1 t2) (Term.op op t1' t2)
  | opCtx2 : ∀ op n1 t2 t2',
      Step t2 t2' →
      Step (Term.op op (.const n1) t2) (Term.op op (.const n1) t2')
  | addConst : ∀ n1 n2,
      Step (Term.op .add (.const n1) (.const n2)) (.const (n1 + n2))
  | subConst : ∀ n1 n2,
      Step (Term.op .sub (.const n1) (.const n2)) (.const (n1 - n2))
  | mulConst : ∀ n1 n2,
      Step (Term.op .mul (.const n1) (.const n2)) (.const (n1 * n2))
  | divConst : ∀ n1 n2,
      n2 ≠ 0 →
      Step (Term.op .div (.const n1) (.const n2)) (.const (n1 / n2))

-- reflexive transitive closure of Step
inductive StepStar : Term -> Term -> Prop where
  | refl : ∀ t, StepStar t t
  | trans : ∀ t1 t2 t3, Step t1 t2 → StepStar t2 t3 → StepStar t1 t3

-- reducing a term does not affect its evaluation
theorem step_eval : ∀ t t',
    Step t t' →
    eval t = eval t' := by
    intro t t' h
    induction h <;> simp [*]

-- correctness of the small-step semantics
theorem step_correct : ∀ t t' n,
    StepStar t t' →
    t' = Term.const n →
    eval t = Result.ok n := by
  intro t t' n h ht'
  induction h with
  | refl => intros; subst ht'; rfl
  | trans t1 t2 t3 hstep hstar ih =>
      rw [step_eval _ _ hstep, ih ht']
