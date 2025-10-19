inductive Op where
  | add
  | sub
  | mul
  | div

inductive Comp where
  | eq
  | lt
  | le
  | gt
  | ge

inductive Term where
  | const : Nat -> Term
  | var : String -> Term
  | cond : Term -> Comp -> Term -> Term -> Term -> Term
  | op : Op -> Term → Term → Term

inductive Result (α : Type) where
  | ok : α → Result α
  | divByZero : Result α
  | unknownReference : String -> Result α

@[simp]
instance : Monad Result where
  pure := Result.ok
  bind
    | Result.ok n, f => f n
    | Result.divByZero, _ => Result.divByZero
    | Result.unknownReference s, _ => Result.unknownReference s

def Context := String → Option Nat

@[simp]
def compare (c : Comp) (n1 n2 : Nat) : Bool :=
  match c with
  | .eq => n1 == n2
  | .lt => n1 < n2
  | .le => n1 ≤ n2
  | .gt => n1 > n2
  | .ge => n1 ≥ n2

@[simp]
def eval (ctx : Context) : Term → Result Nat
  | .const n => pure n
  | .cond t1 cmp t2 tt te =>
      eval ctx t1 >>= fun r1 =>
      eval ctx t2 >>= fun r2 =>
      if compare cmp r1 r2 then
        eval ctx tt
      else
        eval ctx te
  | .var s =>
      match ctx s with
      | some n => pure n
      | none => Result.unknownReference s
  | .op op t1 t2 =>
      eval ctx t1 >>= fun r1 =>
      eval ctx t2 >>= fun r2 =>
      match op with
      | .add => pure (r1 + r2)
      | .sub => pure (r1 - r2)
      | .mul => pure (r1 * r2)
      | .div => if r2 == 0 then Result.divByZero else pure (r1 / r2)

#eval eval (fun _ => none) (Term.op .add (Term.const 5) (Term.op .mul (Term.const 2) (Term.const 3))) -- 11
#eval eval (fun _ => none) (Term.op .div (Term.const 10) (Term.op .sub (Term.const 5) (Term.const 5))) -- divByZero


inductive Step {ctx : Context} : Term -> Term -> Prop where
  | var : ∀ s n,
      ctx s = some n →
      Step (Term.var s) (Term.const n)
  | condCtx1 : ∀ t1 t1' cmp t2 tt te,
      Step t1 t1' →
      Step (Term.cond t1 cmp t2 tt te) (Term.cond t1' cmp t2 tt te)
  | condCtx2 : ∀ n1 t2 t2' cmp tt te,
      Step t2 t2' →
      Step (Term.cond (.const n1) cmp t2 tt te) (Term.cond (.const n1) cmp t2' tt te)
  | condTrue : ∀ n1 n2 tt te cmp,
      compare cmp n1 n2 = true →
      Step (Term.cond (.const n1) cmp (.const n2) tt te) tt
  | condFalse : ∀ n1 n2 tt te cmp,
      compare cmp n1 n2 = false →
      Step (Term.cond (.const n1) cmp (.const n2) tt te) te
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
inductive StepStar {ctx : Context} : Term -> Term -> Prop where
  | refl : ∀ t, StepStar t t
  | trans : ∀ t1 t2 t3, @Step ctx t1 t2 → StepStar t2 t3 → StepStar t1 t3

-- reducing a term does not affect its evaluation
theorem step_eval {ctx : Context} : ∀ t t',
    @Step ctx t t' →
    eval ctx t = eval ctx t' := by
    intro t t' h
    induction h <;> simp [*]
    case condTrue hcmp =>
      simp at hcmp
      rw [hcmp]
      intro; contradiction
    case condFalse hcmp =>
      simp at hcmp
      rw [hcmp]
      intro; contradiction

-- correctness of the small-step semantics
theorem step_correct {ctx : Context} : ∀ t t' n,
    @StepStar ctx t t' →
    t' = Term.const n →
    eval ctx t = Result.ok n := by
  intro t t' n h ht'
  induction h with
  | refl => intros; subst ht'; rfl
  | trans t1 t2 t3 hstep hstar ih =>
      rw [step_eval _ _ hstep, ih ht']
