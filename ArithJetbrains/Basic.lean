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
  | bind : String -> Term -> Term -> Term
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
def extend (ctx : Context) (s : String) (n : Nat) : Context :=
  fun key => if key == s then some n else ctx key

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
  | .bind s e b =>
      eval ctx e >>= fun n =>
      eval (extend ctx s n) b
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


inductive Step : Context → Term → Term → Prop where
  | bindCtx : ∀ ctx s e e' b,
      Step ctx e e' →
      Step ctx (.bind s e b) (.bind s e' b)
  | bindBody : ∀ s n b b',
      Step (extend ctx s n) b b' →
      Step ctx (.bind s (.const n) b) (.bind s (.const n) b')
  | bind : ∀ ctx s n b,
      Step ctx (.bind s (.const n) (.const b)) (.const b)
  | var : ∀ ctx s n,
      ctx s = some n →
      Step ctx (.var s) (.const n)
  | condCtx1 : ∀ ctx t1 t1' cmp t2 tt te,
      Step ctx t1 t1' →
      Step ctx (.cond t1 cmp t2 tt te) (.cond t1' cmp t2 tt te)
  | condCtx2 : ∀ ctx n1 t2 t2' cmp tt te,
      Step ctx t2 t2' →
      Step ctx (.cond (.const n1) cmp t2 tt te) (.cond (.const n1) cmp t2' tt te)
  | condTrue : ∀ ctx n1 n2 tt te cmp,
      compare cmp n1 n2 = true →
      Step ctx (.cond (.const n1) cmp (.const n2) tt te) tt
  | condFalse : ∀ ctx n1 n2 tt te cmp,
      compare cmp n1 n2 = false →
      Step ctx (.cond (.const n1) cmp (.const n2) tt te) te
  | opCtx1 : ∀ ctx op t1 t1' t2,
      Step ctx t1 t1' →
      Step ctx (.op op t1 t2) (.op op t1' t2)
  | opCtx2 : ∀ ctx op n1 t2 t2',
      Step ctx t2 t2' →
      Step ctx (.op op (.const n1) t2) (.op op (.const n1) t2')
  | addConst : ∀ ctx n1 n2,
      Step ctx (.op .add (.const n1) (.const n2)) (.const (n1 + n2))
  | subConst : ∀ ctx n1 n2,
      Step ctx (.op .sub (.const n1) (.const n2)) (.const (n1 - n2))
  | mulConst : ∀ ctx n1 n2,
      Step ctx (.op .mul (.const n1) (.const n2)) (.const (n1 * n2))
  | divConst : ∀ ctx n1 n2,
      n2 ≠ 0 →
      Step ctx (.op .div (.const n1) (.const n2)) (.const (n1 / n2))

-- reflexive transitive closure of Step
inductive StepStar : Context → Term → Term → Prop where
  | refl : ∀ ctx t, StepStar ctx t t
  | trans : ∀ ctx t1 t2 t3, Step ctx t1 t2 → StepStar ctx t2 t3 → StepStar ctx t1 t3

-- reducing a term does not affect its evaluation
theorem step_eval : ∀ ctx t t',
    Step ctx t t' →
    eval ctx t = eval ctx t' := by
    intro ctx t t' h
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
theorem step_correct : ∀ ctx t t' n,
    StepStar ctx t t' →
    t' = Term.const n →
    eval ctx t = Result.ok n := by
  intro ctx t t' n h ht'
  induction h with
  | refl => intros; subst ht'; rfl
  | trans t1 t2 t3 hstep hstar ih =>
      rw [step_eval _ _ _ hstep, ih ht']
