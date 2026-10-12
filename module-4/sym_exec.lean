abbrev Var := String
abbrev State := Var -> Int

-- Define a simple state. s[x]=3, s[y]=7, s[z]=0
-- for any other variable z.
def initialState : State :=
  fun x => if x == "x" then 3
            else if x == "y" then 7
            else 0

#eval initialState "x"
#eval initialState "y"

example : initialState "x" = 3 := by
 rfl
example : initialState "y" = 7 := by
 rfl

-- Update state s: s[x->n]
def update (s : State) (x : Var) (n : Int) : State :=
  fun y => if y == x then n else s y

def nextState : State :=
  update initialState "x" 10

#eval nextState "x"
#eval nextState "y"

example : nextState "x" = 10 := by
 rfl
example : nextState "y" = 7 := by
 rfl
example : nextState "z" = initialState "z" := by
 rfl


-- s[x->n][x] = n
theorem update_same (s : State) (x : Var) (n : Int) :
  update s x n x = n := by
 simp [update]

example : update initialState "y" 42 "y" = 42 := by
 exact update_same initialState "y" 42

example : update initialState "y" 42 "y" = 42 := by
 apply update_same

-- if x ≠ y then s[x->n][y] = s[y]
theorem update_other (s : State) (x y : Var) (n : Int)
  (h : x ≠ y) :
  update s x n y = s y := by
  simp [update]
  have hReverse : y ≠ x := Ne.symm h
  simp [hReverse]

inductive AExp where
  | num : Int -> AExp
  | var : Var -> AExp
  | add : AExp -> AExp -> AExp
  | sub : AExp -> AExp -> AExp
  | mul : AExp -> AExp -> AExp
  | le : AExp -> AExp -> AExp
  | eq : AExp -> AExp -> AExp
  | ne : AExp -> AExp -> AExp
  deriving Repr

def incrementX : AExp :=
  AExp.add (AExp.var "x") (AExp.num 1)

#eval incrementX

def subtractY : AExp :=
  AExp.sub (incrementX) (AExp.var "y")

#eval subtractY

-- Expression evaluation: [a]s
def eval (a : AExp) (s : State) : Int :=
  match a with
  | AExp.num n => n
  | AExp.var x => s x
  | AExp.add a1 a2 => eval a1 s + eval a2 s
  | AExp.sub a1 a2 => eval a1 s - eval a2 s
  | AExp.mul a1 a2 => eval a1 s * eval a2 s
  | AExp.le a1 a2 => if eval a1 s ≤ eval a2 s then 1 else 0
  | AExp.eq a1 a2 => if eval a1 s = eval a2 s then 1 else 0
  | AExp.ne a1 a2 => if eval a1 s ≠ eval a2 s then 1 else 0

example : eval incrementX initialState = 4 := by
 rfl
example : eval subtractY initialState = -3 := by
 rfl

theorem eval_incrementX (s : State) :
  eval incrementX s = s "x" + 1 := by rfl

theorem eval_subtractY (s : State) :
  eval subtractY s = (s "x" + 1) - s "y" := by rfl

-- if two states agree on all variables,
-- then they evaluate the same expression to the same value
theorem eval_agree (a: AExp) (s1 s2 : State)
  (h : ∀ x, s1 x = s2 x) :
  eval a s1 = eval a s2 := by
  induction a with
  | num n => rfl
  | var x => exact h x
  | add a1 a2 ih1 ih2 =>
    simp [eval]
    rw [ih1, ih2]
  | sub a1 a2 ih1 ih2 =>
    simp [eval]
    rw [ih1, ih2]
  | mul a1 a2 ih1 ih2 =>
    simp [eval]
    rw [ih1, ih2]
  | le a1 a2 ih1 ih2 =>
    simp only [eval]
    rw [ih1, ih2]
  | eq a1 a2 ih1 ih2 =>
    simp only [eval]
    rw [ih1, ih2]
  | ne a1 a2 ih1 ih2 =>
    simp only [eval]
    rw [ih1, ih2]

-- Remmber we are using variables as symbols
abbrev SymState := Var -> AExp
def symEval (a:AExp) (θ: SymState) : AExp :=
  match a with
  | AExp.num n => AExp.num n
  | AExp.var x => θ x
  | AExp.add a1 a2 => AExp.add (symEval a1 θ) (symEval a2 θ)
  | AExp.sub a1 a2 => AExp.sub (symEval a1 θ) (symEval a2 θ)
  | AExp.mul a1 a2 => AExp.mul (symEval a1 θ) (symEval a2 θ)
  | AExp.le a1 a2 => AExp.le (symEval a1 θ) (symEval a2 θ)
  | AExp.eq a1 a2 => AExp.eq (symEval a1 θ) (symEval a2 θ)
  | AExp.ne a1 a2 => AExp.ne (symEval a1 θ) (symEval a2 θ)

def replaceX (x : Var) : AExp :=
  if x == "x" then AExp.num 10 else AExp.var x

#eval symEval incrementX replaceX

#eval eval (symEval incrementX replaceX) initialState

abbrev Valuation := State

def concretize (σ:SymState) (ν :Valuation) : State :=
  fun x => eval (σ x) ν


-- Theorem: Evaluating a substituted expression in a state
--  is equivalent to evaluating the original expression
-- in a state where each variable is replaced by its
-- evaluation under the substitution.
-- [[a]θ] γ = [a]([θ]γ)
theorem eval_sym (a : AExp) (σ  : SymState) (ν  : Valuation) :
    eval (symEval a σ) ν  = eval a (concretize σ ν ) := by
    induction a with
    | num n => rfl
    | var x => rfl
    | add a1 a2 ih1 ih2 =>
      simp only [eval, symEval]
      rw [ih1, ih2]
    | sub a1 a2 ih1 ih2 =>
      simp only [eval, symEval]
      rw [ih1, ih2]
    | mul a1 a2 ih1 ih2 =>
      simp only [eval, symEval]
      rw [ih1, ih2]
    | le a1 a2 ih1 ih2 =>
      simp only [eval, symEval]
      rw [ih1, ih2]
    | eq a1 a2 ih1 ih2 =>
      simp only [eval, symEval]
      rw [ih1, ih2]
    | ne a1 a2 ih1 ih2 =>
      simp only [eval, symEval]
      rw [ih1, ih2]

-- [a]([θ]γ) = [[a]θ] γ
theorem eval_concretize (a:AExp) (σ:SymState) (ν :Valuation) :
  eval a (concretize σ ν) = eval (symEval a σ) ν  := by
  unfold concretize
  exact (eval_sym a σ ν).symm

-- update a symbolic state σ with a new value for variable x
-- σ[x->a]
def symUpdate (σ:SymState) (x:Var) (a:AExp) :=
  fun y => if y == x then a else σ y

-- Concretizing a symbolic state after an update is equivalent
-- to updating the concretized state with the evaluated expression.
-- Notice here the concretiation is used as state in eval
-- σ[x->a]ν = (σν)[x->eval a ν]
theorem concretize_update (σ:SymState) (ν:Valuation)
  (x:Var) (a:AExp) :
  concretize (symUpdate σ x a) ν =
    update (concretize σ ν) x (eval a ν)
  := by
  funext y
  by_cases h : y =x
  · simp [concretize, symUpdate, h, update]
  · simp [concretize, symUpdate, h, update]

-- σ[x->([a]σ)]ν = (σν)[x->eval a (σν)]
theorem concretize_assign (σ : SymState) (ν : Valuation)
    (x : Var) (a : AExp) :
    concretize (symUpdate σ x (symEval a σ)) ν =
      update (concretize σ ν) x (eval a (concretize σ ν))
  := by
    rw [concretize_update]
    have h : eval (symEval a σ) ν = eval a (concretize σ ν)
      := by rw [eval_concretize]
    simp [h]

-- [P]ν
def Holds (a : AExp) (s : State) : Prop :=
  eval a s ≠ 0

abbrev AExpAnd := AExp.mul
abbrev AExpNot := AExp.eq (AExp.num 0)

theorem holds_mul (a b : AExp) (s : State) :
    Holds (AExp.mul a b) s ↔ Holds a s ∧ Holds b s := by
  simp [Holds, eval, Int.mul_eq_zero, not_or]

theorem holds_eq_zero (a : AExp) (s : State) :
    Holds (AExp.eq (AExp.num 0) a) s ↔ ¬ Holds a s := by
  simp [Holds, eval, eq_comm]


--[P](σν) <=> ([P]σ)ν
theorem holds_subst (a : AExp) (σ : SymState) (ν : Valuation) :
    Holds a (concretize σ ν) ↔ Holds (symEval a σ) ν := by
  unfold Holds
  rw [eval_concretize]

-- Instructions
inductive Cmd where
    | skip : Cmd
    | assign : Var -> AExp -> Cmd
    | seq : Cmd -> Cmd -> Cmd
    | ite : AExp -> Cmd -> Cmd -> Cmd
    | while : AExp -> Cmd -> Cmd
    deriving Repr

def incrementThenCopy : Cmd :=
  Cmd.seq (Cmd.assign "x" (AExp.add (AExp.var "x") (AExp.num 1)))
          (Cmd.assign "y" (AExp.var "x"))

abbrev Conf := Cmd × State

-- BigStep (c, s) s' means that c terminates from s with final state s'.
inductive BigStep : Conf → State → Prop where
  | skip (s : State) :
      BigStep (Cmd.skip, s) s

  | assign (x : Var) (a : AExp) (s : State) :
      BigStep (Cmd.assign x a, s) (update s x (eval a s))

  | seq {c1 c2 : Cmd} {s s1 s2 : State}
      (h1 : BigStep (c1, s) s1)
      (h2 : BigStep (c2, s1) s2) :
      BigStep (Cmd.seq c1 c2, s) s2

  | ifTrue {a : AExp} {c1 c2 : Cmd} {s s' : State}
      (hGuard : Holds a s)
      (hBranch : BigStep (c1, s) s') :
      BigStep (Cmd.ite a c1 c2, s) s'

  | ifFalse {a : AExp} {c1 c2 : Cmd} {s s' : State}
      (hGuard : ¬ Holds a s)
      (hBranch : BigStep (c2, s) s') :
      BigStep (Cmd.ite a c1 c2, s) s'

  | whileFalse {a : AExp} {body : Cmd} {s : State}
      (hGuard : ¬ Holds a s) :
      BigStep (Cmd.while a body, s) s

  | whileTrue {a : AExp} {body : Cmd} {s s1 s2 : State}
      (hGuard : Holds a s)
      (hBody : BigStep (body, s) s1)
      (hLoop : BigStep (Cmd.while a body, s1) s2) :
      BigStep (Cmd.while a body, s) s2

-- Small step semantics
inductive Step : Conf → Conf → Prop where
  | assign (x : Var) (a : AExp) (s : State) :
      Step (Cmd.assign x a, s)
           (Cmd.skip, update s x (eval a s))

  | seqStep {c1 c1' c2 : Cmd} {s s' : State}
      (h : Step (c1, s) (c1', s')) :
      Step (Cmd.seq c1 c2, s) (Cmd.seq c1' c2, s')

  | seqSkip (c2 : Cmd) (s : State) :
      Step (Cmd.seq Cmd.skip c2, s) (c2, s)

  | ifTrue (a : AExp) (c1 c2 : Cmd) (s : State)
      (h : Holds a s) :
      Step (Cmd.ite a c1 c2, s) (c1, s)

  | ifFalse (a : AExp) (c1 c2 : Cmd) (s : State)
      (h : ¬ Holds a s) :
      Step (Cmd.ite a c1 c2, s) (c2, s)

  | whileUnfold (a : AExp) (body : Cmd) (s : State) :
      Step (Cmd.while a body, s)
           (Cmd.ite a (Cmd.seq body (Cmd.while a body)) Cmd.skip, s)

example (x : Var) (a : AExp) (s : State) :
    Step (Cmd.assign x a, s)
         (Cmd.skip, update s x (eval a s)) := by
    apply Step.assign x a s

theorem skip_no_step (s : State) (c : Conf) :
    ¬ Step (Cmd.skip, s) c := by
    intro h
    cases h

-- Small-step semantics is deterministic: if a configuration can step to two different configurations, they must be equal.
-- thas it is c->c1 and c->c2 then c1=c2
-- Generalizing c2 lets the induction hypothesis compare any competing successor.
theorem step_deterministic (c c1 c2:Conf)
  (h1 : Step c c1)
  (h2 : Step c c2) :
  c1 = c2 := by
  induction h1 generalizing c2 with
  | assign x a s =>
    cases h2
    rfl
  | seqStep hStep ih =>
    cases h2 with
    | seqStep hOther =>
      -- The induction hypothesis identifies the results of the inner steps.
      have heq := ih _ hOther
      cases heq
      rfl
    | seqSkip =>
      -- This would require hStep to be a transition from skip.
      cases hStep
  | seqSkip cNext s =>
    cases h2 with
    | seqStep hOther => cases hOther
    | seqSkip => rfl
  | ifTrue a cThen cElse s hGuard =>
    cases h2 with
    | ifTrue => rfl
    | ifFalse =>
      -- The guard cannot both hold and fail to hold.
      contradiction
  | ifFalse a cThen cElse s hGuard =>
    cases h2 with
    | ifTrue => contradiction
    | ifFalse => rfl
  | whileUnfold a body s =>
    cases h2
    rfl

abbrev PathCondition := AExp
abbrev SymConf := Cmd × SymState × PathCondition

-- Symbolic small step sematics
inductive SymStep : SymConf → SymConf → Prop where
  | assign :
      SymStep (Cmd.assign x a, σ, π)
              (Cmd.skip, symUpdate σ x (symEval a σ), π)
  | seqStep
      (h : SymStep (c1, σ, π) (c1', σ', π')) :
      SymStep (Cmd.seq c1 c2, σ, π) (Cmd.seq c1' c2, σ', π')
  | seqSkip :
      SymStep (Cmd.seq Cmd.skip c2, σ, π) (c2, σ, π)
  | ifTrue :
      SymStep (Cmd.ite a c1 c2, σ, π)
              (c1, σ, AExpAnd π (symEval a σ))
  | ifFalse :
      SymStep (Cmd.ite a c1 c2, σ, π)
              (c2, σ, AExpAnd π (AExpNot (symEval a σ)))
  | whileUnfold :
      SymStep (Cmd.while a body, σ, π)
              (Cmd.ite a (Cmd.seq body (Cmd.while a body)) Cmd.skip, σ, π)


-- Single step soundness
-- Whole configurations as indices allow induction on the transition derivation.
theorem sym_step_sound {q q' : SymConf} (h : SymStep q q') (ν : Valuation) :
    Holds q'.2.2 ν →
      Holds q.2.2 ν ∧
        Step (q.1, concretize q.2.1 ν) (q'.1, concretize q'.2.1 ν) := by
  induction h with
  | assign =>
      intro hPath
      constructor
      · exact hPath
      · rw [concretize_assign]
        exact Step.assign _ _ _
  | seqStep hStep ih =>
      intro hPath
      obtain ⟨hOldPath, hConcrete⟩ := ih hPath
      exact ⟨hOldPath, Step.seqStep hConcrete⟩
  | seqSkip =>
      intro hPath
      exact ⟨hPath, Step.seqSkip _ _⟩
  | @ifTrue a c1 c2 σ π =>
      intro hPath
      obtain ⟨hOldPath, hGuard⟩ := (holds_mul π (symEval a σ) ν).mp hPath
      constructor
      · exact hOldPath
      · apply Step.ifTrue
        exact (holds_subst a σ ν).mpr hGuard
  | @ifFalse a c1 c2 σ π =>
      intro hPath
      obtain ⟨hOldPath, hZero⟩ := (holds_mul _ _ ν).mp hPath
      have hGuard : ¬ Holds (symEval a σ) ν := (holds_eq_zero _ ν).mp hZero
      constructor
      · exact hOldPath
      · apply Step.ifFalse
        intro hConcrete
        exact hGuard ((holds_subst a σ ν).mp hConcrete)
  | whileUnfold =>
      intro hPath
      exact ⟨hPath, Step.whileUnfold _ _ _⟩

-- (c, σ, π) -> (c', σ', π') and [π']ν and s=σν then
--  [π]ν and (c, s) -> (c', [σ']ν)
theorem sym_soundness (c : Cmd) (σ : SymState) (π : PathCondition)
  (ν : Valuation) (s : State)
  (h1 : SymStep (c, σ, π) (c', σ', π'))
  (h2 : Holds π' ν)
  (h3 : s = concretize σ ν) :
  Holds π ν /\
  Step (c, s) (c', concretize σ' ν) := by
  subst s
  exact sym_step_sound h1 ν h2

-- Keep the symbolic store and path arbitrary for the recursive sequencing case.
-- single step coverage aux lemma
theorem sym_step_coverage {q q' : Conf} (h : Step q q') (ν : Valuation) :
    ∀ (σ : SymState) (π : PathCondition),
      Holds π ν → q.2 = concretize σ ν →
      ∃ σ' π', SymStep (q.1, σ, π) (q'.1, σ', π') ∧
        Holds π' ν ∧ q'.2 = concretize σ' ν := by
  induction h with
  | assign x a s =>
      intro σ π hPath hState
      change s = concretize σ ν at hState
      subst s
      refine ⟨symUpdate σ x (symEval a σ), π, SymStep.assign, hPath, ?_⟩
      exact (concretize_assign σ ν x a).symm
  | seqStep hStep ih =>
      intro σ π hPath hState
      obtain ⟨σ', π', hSym, hPath', hState'⟩ := ih σ π hPath hState
      exact ⟨σ', π', SymStep.seqStep hSym, hPath', hState'⟩
  | seqSkip c2 s =>
      intro σ π hPath hState
      exact ⟨σ, π, SymStep.seqSkip, hPath, hState⟩
  | ifTrue a c1 c2 s hGuard =>
      intro σ π hPath hState
      change s = concretize σ ν at hState
      subst s
      have hSymGuard := (holds_subst a σ ν).mp hGuard
      refine ⟨σ, AExpAnd π (symEval a σ), SymStep.ifTrue, ?_, rfl⟩
      exact (holds_mul _ _ ν).mpr ⟨hPath, hSymGuard⟩
  | ifFalse a c1 c2 s hGuard =>
      intro σ π hPath hState
      change s = concretize σ ν at hState
      subst s
      have hSymGuard : ¬ Holds (symEval a σ) ν := by
        intro hTrue
        exact hGuard ((holds_subst a σ ν).mpr hTrue)
      refine ⟨σ, AExpAnd π (AExpNot (symEval a σ)),
        SymStep.ifFalse, ?_, rfl⟩
      exact (holds_mul _ _ ν).mpr
        ⟨hPath, (holds_eq_zero _ ν).mpr hSymGuard⟩
  | whileUnfold a body s =>
      intro σ π hPath hState
      exact ⟨σ, π, SymStep.whileUnfold, hPath, hState⟩

-- Single step coverage
-- (c,s) -> (c',s') and [π]ν and s=σν then
-- there is (c',σ',π') such that
-- (c,σ,π) -> (c',σ',π') and [π']ν and s'=[σ']ν
theorem sym_coverage (c : Cmd) (σ : SymState) (π : PathCondition)
  (ν : Valuation) (s : State)
  (h1 : Holds π ν)
  (h2 : s = concretize σ ν)
  (h3 : Step (c, s) (c', s')) :
  ∃ σ' π',
    SymStep (c, σ, π) (c', σ', π') /\
    Holds π' ν /\
    s' = concretize σ' ν
  := by
  exact sym_step_coverage h3 ν σ π h1 h2

-- Steps n q q' is a concrete execution of exactly n small steps.
inductive Steps : Nat → Conf → Conf → Prop where
  | refl (q : Conf) : Steps 0 q q
  | cons {n : Nat} {q q1 q2 : Conf}
      (hStep : Step q q1) (hRest : Steps n q1 q2) :
      Steps (n + 1) q q2

-- Concatenate two finite executions.
-- q -n-> q1 and q1 -m-> q2 then q -n+m-> q2
theorem steps_trans {n m : Nat} {q q1 q2 : Conf}
    (h1 : Steps n q q1) (h2 : Steps m q1 q2) :
    Steps (n + m) q q2 := by
  induction h1 with
  | refl => simpa using h2
  | cons hStep hRest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.cons hStep (ih h2)

-- Lift each step through the left side of a sequence.
theorem steps_seq {n : Nat} {q q' : Conf} (h : Steps n q q') (c2 : Cmd) :
    Steps n (Cmd.seq q.1 c2, q.2) (Cmd.seq q'.1 c2, q'.2) := by
  induction h with
  | refl => exact Steps.refl _
  | cons hStep hRest ih =>
      exact Steps.cons (Step.seqStep hStep) ih

-- Slide 8: induction on the big-step derivation builds a finite execution.
-- if q ⇓ s' then there is n such that q -n-> (skip, s')
theorem bigStep_to_steps {q : Conf} {s' : State} (h : BigStep q s') :
    ∃ n, Steps n q (Cmd.skip, s') := by
  induction h with
  | skip s => exact ⟨0, Steps.refl _⟩
  | assign x a s =>
      exact ⟨1, Steps.cons (Step.assign x a s) (Steps.refl _)⟩
  | @seq c1 c2 s s1 s2 h1 h2 ih1 ih2 =>
      obtain ⟨n, hn⟩ := ih1
      obtain ⟨m, hm⟩ := ih2
      exact ⟨_, steps_trans (steps_seq hn c2)
        (Steps.cons (Step.seqSkip c2 s1) hm)⟩
  | @ifTrue a c1 c2 s s' hGuard hBranch ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨_, Steps.cons (Step.ifTrue a c1 c2 s hGuard) hn⟩
  | @ifFalse a c1 c2 s s' hGuard hBranch ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨_, Steps.cons (Step.ifFalse a c1 c2 s hGuard) hn⟩
  | @whileFalse a body s hGuard =>
      exact ⟨2, Steps.cons (Step.whileUnfold a body s)
        (Steps.cons (Step.ifFalse _ _ _ _ hGuard) (Steps.refl _))⟩
  | @whileTrue a body s s1 s2 hGuard hBody hLoop ihBody ihLoop =>
      obtain ⟨n, hn⟩ := ihBody
      obtain ⟨m, hm⟩ := ihLoop
      exact ⟨_, Steps.cons (Step.whileUnfold a body s)
        (Steps.cons (Step.ifTrue _ _ _ _ hGuard)
          (steps_trans (steps_seq hn (Cmd.while a body))
            (Steps.cons (Step.seqSkip _ _) hm)))⟩

-- Slide 9: a small step followed by a big-step execution can be expanded.
-- q -> q' and q' ⇓ s' then q ⇓ s'
theorem step_bigStep_expansion {q q' : Conf} {s' : State}
    (hStep : Step q q') (hBig : BigStep q' s') : BigStep q s' := by
  induction hStep generalizing s' with
  | assign x a s =>
      cases hBig
      exact BigStep.assign x a s
  | seqStep hStep ih =>
      cases hBig with
      | seq hFirst hSecond =>
          exact BigStep.seq (ih hFirst) hSecond
  | seqSkip c2 s =>
      exact BigStep.seq (BigStep.skip s) hBig
  | ifTrue a c1 c2 s hGuard =>
      exact BigStep.ifTrue hGuard hBig
  | ifFalse a c1 c2 s hGuard =>
      exact BigStep.ifFalse hGuard hBig
  | whileUnfold a body s =>
      cases hBig with
      | ifTrue hGuard hBranch =>
          cases hBranch with
          | seq hBody hLoop =>
              exact BigStep.whileTrue hGuard hBody hLoop
      | ifFalse hGuard hBranch =>
          cases hBranch
          exact BigStep.whileFalse hGuard

-- Repeated expansion lifts a big-step execution backwards along a finite path.
theorem steps_bigStep_expansion {n : Nat} {q q' : Conf} {s' : State}
    (hSteps : Steps n q q') (hBig : BigStep q' s') : BigStep q s' := by
  induction hSteps with
  | refl => exact hBig
  | cons hStep hRest ih =>
      exact step_bigStep_expansion hStep (ih hBig)

-- Other direction of the semantic equivalence
-- q -n-> (skip, s') then q ⇓ s'
theorem steps_to_bigStep {n : Nat} {q : Conf} {s' : State}
    (h : Steps n q (Cmd.skip, s')) : BigStep q s' := by
  exact steps_bigStep_expansion h (BigStep.skip s')

-- Slide 7: small-step termination and big-step evaluation agree.
-- q -n-> (skip, s') for some n iff q ⇓ s'
theorem smallStep_iff_bigStep (c : Cmd) (s s' : State) :
    (∃ n : Nat, Steps n (c, s) (Cmd.skip, s')) ↔ BigStep (c, s) s' := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    exact steps_to_bigStep hn
  · intro h
    exact bigStep_to_steps h

-- SymSteps n q q' is a symbolic path of exactly n transitions.
inductive SymSteps : Nat → SymConf → SymConf → Prop where
  | refl (q : SymConf) : SymSteps 0 q q
  | cons {n : Nat} {q q1 q2 : SymConf}
      (hStep : SymStep q q1) (hRest : SymSteps n q1 q2) :
      SymSteps (n + 1) q q2

-- Soundness preserves the valuation and the number of steps.
-- Propagate satisfaction backwards from the final path condition.
theorem sym_steps_sound {n : Nat} {q q' : SymConf}
    (h : SymSteps n q q') (ν : Valuation) :
    Holds q'.2.2 ν → Holds q.2.2 ν ∧
      Steps n (q.1, concretize q.2.1 ν) (q'.1, concretize q'.2.1 ν) := by
  induction h with
  | refl =>
      intro hPath
      exact ⟨hPath, Steps.refl _⟩
  | cons hStep hRest ih =>
      intro hPath
      obtain ⟨hMiddlePath, hConcreteRest⟩ := ih hPath
      obtain ⟨hOldPath, hConcreteStep⟩ := sym_step_sound hStep ν hMiddlePath
      exact ⟨hOldPath, Steps.cons hConcreteStep hConcreteRest⟩

-- Coverage follows the concrete path, keeping the same valuation throughout.
theorem sym_steps_coverage {n : Nat} {q q' : Conf}
    (h : Steps n q q') (ν : Valuation) :
    ∀ (σ : SymState) (π : PathCondition),
      Holds π ν → q.2 = concretize σ ν →
      ∃ σ' π', SymSteps n (q.1, σ, π) (q'.1, σ', π') ∧
        Holds π' ν ∧ q'.2 = concretize σ' ν := by
  induction h with
  | refl =>
      intro σ π hPath hState
      exact ⟨σ, π, SymSteps.refl _, hPath, hState⟩
  | cons hStep hRest ih =>
      intro σ π hPath hState
      -- Lift the first concrete step with one-step coverage.
      obtain ⟨σ1, π1, hSymStep, hMiddlePath, hMiddleState⟩ :=
        sym_step_coverage hStep ν σ π hPath hState
      -- Continue from its symbolic successor, then prepend the lifted step.
      obtain ⟨σ', π', hSymRest, hFinalPath, hFinalState⟩ :=
        ih σ1 π1 hMiddlePath hMiddleState
      exact ⟨σ', π', SymSteps.cons hSymStep hSymRest, hFinalPath, hFinalState⟩

-- Terminal-path soundness for any starting symbolic store and condition.
theorem sym_finite_soundness {c : Cmd} {σ σf : SymState}
    {π πf : PathCondition} {n : Nat} (ν : Valuation)
    (hPath : SymSteps n (c, σ, π) (Cmd.skip, σf, πf))
    (hSat : Holds πf ν) :
    Holds π ν ∧ BigStep (c, concretize σ ν) (concretize σf ν) := by
  obtain ⟨hInitial, hConcrete⟩ := sym_steps_sound hPath ν hSat
  exact ⟨hInitial, steps_to_bigStep hConcrete⟩

-- Every terminating concrete execution from a represented state has a path.
theorem sym_finite_coverage {c : Cmd} {s s' : State}
    (σ : SymState) (π : PathCondition) (ν : Valuation)
    (hSat : Holds π ν) (hState : s = concretize σ ν)
    (hRun : BigStep (c, s) s') :
    ∃ n σf πf, SymSteps n (c, σ, π) (Cmd.skip, σf, πf) ∧
      Holds πf ν ∧ s' = concretize σf ν := by
  obtain ⟨n, hSteps⟩ := bigStep_to_steps hRun
  obtain ⟨σf, πf, hPath, hFinal, hResult⟩ :=
    sym_steps_coverage hSteps ν σ π hSat hState
  exact ⟨n, σf, πf, hPath, hFinal, hResult⟩

-- Input symbols use the corresponding variable names in this representation.
def initialSymState : SymState := fun x => AExp.var x

theorem concretize_initial (ν : Valuation) :
    concretize initialSymState ν = ν := by
  funext x
  rfl

-- Slide 23: initialize with P[σ₀]. Preconditions use our nonzero AExp encoding.
theorem sym_initial_soundness {c : Cmd} (P : AExp) (ν : Valuation)
    {n : Nat} {σf : SymState} {πf : PathCondition}
    (hPath : SymSteps n (c, initialSymState, symEval P initialSymState)
      (Cmd.skip, σf, πf))
    (hSat : Holds πf ν) :
    Holds P ν ∧ BigStep (c, ν) (concretize σf ν) := by
  -- Repeated one-step soundness gives a concrete path of the same length.
  obtain ⟨hInitial, hSteps⟩ := sym_steps_sound hPath ν hSat
  constructor
  · have hPre := (holds_subst P initialSymState ν).mpr hInitial
    simpa only [concretize_initial] using hPre
  · -- Only now convert the terminating concrete path to big-step semantics.
    apply (smallStep_iff_bigStep c ν (concretize σf ν)).mp
    refine ⟨n, ?_⟩
    simpa only [concretize_initial] using hSteps

-- The initial valuation is the concrete starting state itself.
theorem sym_initial_coverage {c : Cmd} (P : AExp) {s s' : State}
    (hPre : Holds P s) (hRun : BigStep (c, s) s') :
    ∃ n σf πf,
      SymSteps n (c, initialSymState, symEval P initialSymState)
        (Cmd.skip, σf, πf) ∧
      Holds πf s ∧ s' = concretize σf s := by
  -- First use slide 7 to replace big-step execution by a finite small-step path.
  obtain ⟨n, hSteps⟩ := (smallStep_iff_bigStep c s s').mpr hRun
  have hInitial : Holds (symEval P initialSymState) s := by
    apply (holds_subst P initialSymState s).mp
    simpa only [concretize_initial] using hPre
  -- Induction on that path applies one-step coverage at each transition.
  obtain ⟨σf, πf, hPath, hFinal, hResult⟩ :=
    sym_steps_coverage hSteps s initialSymState (symEval P initialSymState)
      hInitial (concretize_initial s).symm
  exact ⟨n, σf, πf, hPath, hFinal, hResult⟩

namespace Slide12

-- The program incrementThenCopy is x := x + 1; y := x.
-- Names in initialSymState denote initial inputs (the slide's α_x and α_y).
def afterX : SymState :=
  symUpdate initialSymState "x" (symEval incrementX initialSymState)

def afterY : SymState :=
  symUpdate afterX "y" (symEval (AExp.var "x") afterX)

-- Assignment, removal of skip, assignment: three symbolic transitions.
theorem symbolic_execution (π : PathCondition) :
    SymSteps 3 (incrementThenCopy, initialSymState, π)
      (Cmd.skip, afterY, π) := by
  have hX : SymStep (incrementThenCopy, initialSymState, π)
      (Cmd.seq Cmd.skip (Cmd.assign "y" (AExp.var "x")), afterX, π) := by
    exact SymStep.seqStep SymStep.assign
  have hSeq : SymStep
      (Cmd.seq Cmd.skip (Cmd.assign "y" (AExp.var "x")), afterX, π)
      (Cmd.assign "y" (AExp.var "x"), afterX, π) := by
    exact SymStep.seqSkip
  have hY : SymStep (Cmd.assign "y" (AExp.var "x"), afterX, π)
      (Cmd.skip, afterY, π) := by
    exact SymStep.assign
  exact SymSteps.cons hX (SymSteps.cons hSeq (SymSteps.cons hY (SymSteps.refl _)))

-- Both variables now contain the expression for the initial x plus one.
theorem final_symbolic_values :
    afterY "x" = incrementX ∧ afterY "y" = incrementX := by
  constructor <;> rfl

theorem final_values (ν : Valuation) :
    concretize afterY ν "y" = concretize afterY ν "x" := by
  change eval (afterY "y") ν = eval (afterY "x") ν
  rw [final_symbolic_values.1, final_symbolic_values.2]

-- Instantiate the unchanged path condition with true (the integer 1).
-- Finite-path soundness turns our symbolic derivation into a concrete execution.
theorem execution_correct (ν : Valuation) :
    BigStep (incrementThenCopy, ν) (concretize afterY ν) ∧
      concretize afterY ν "y" = concretize afterY ν "x" := by
  have hTrue : Holds (AExp.num 1) ν := by
    simp [Holds, eval]
  have hRun := (sym_finite_soundness ν (symbolic_execution (AExp.num 1)) hTrue).2
  constructor
  · simpa only [concretize_initial] using hRun
  · exact final_values ν

-- The postcondition also holds for any given terminating execution.
theorem postcondition {s s' : State} (hRun : BigStep (incrementThenCopy, s) s') :
    s' "y" = s' "x" := by
  cases hRun with
  | seq hX hY =>
      cases hX
      cases hY
      exact (execution_correct s).2

end Slide12

namespace Slide15

-- Faulty absolute value: the positive branch subtracts one by mistake.
def guardExpr : AExp := AExp.le (AExp.var "x") (AExp.num 0)
def positiveBranch : Cmd :=
  Cmd.assign "y" (AExp.sub (AExp.var "x") (AExp.num 1))
def program : Cmd :=
  Cmd.ite guardExpr
    (Cmd.assign "y" (AExp.sub (AExp.num 0) (AExp.var "x")))
    positiveBranch

def postcondition (s : State) : Prop :=
  0 ≤ s "y" ∧ (s "y" = s "x" ∨ s "y" = -s "x")

def falsePath : PathCondition :=
  AExp.mul (AExp.num 1)
    (AExp.eq (AExp.num 0) (symEval guardExpr initialSymState))

def finalStore : SymState :=
  symUpdate initialSymState "y"
    (symEval (AExp.sub (AExp.var "x") (AExp.num 1)) initialSymState)

theorem symbolic_execution :
    SymSteps 2 (program, initialSymState, AExp.num 1)
      (Cmd.skip, finalStore, falsePath) := by
  have hBranch : SymStep (program, initialSymState, AExp.num 1)
      (positiveBranch, initialSymState, falsePath) := by
    exact SymStep.ifFalse
  have hAssign : SymStep (positiveBranch, initialSymState, falsePath)
      (Cmd.skip, finalStore, falsePath) := by
    exact SymStep.assign
  exact SymSteps.cons hBranch (SymSteps.cons hAssign (SymSteps.refl _))

-- x = 1 is a satisfying model of the false branch.
def witness : Valuation := fun x => if x == "x" then 1 else 0

theorem witness_feasible : Holds falsePath witness := by
  change (1 : Int) ≠ 0
  decide

theorem witness_final_values :
    concretize finalStore witness "x" = 1 ∧
    concretize finalStore witness "y" = 0 := by
  constructor <;> rfl

theorem symbolic_violation :
    Holds falsePath witness ∧
      ¬ postcondition (concretize finalStore witness) := by
  constructor
  · exact witness_feasible
  · unfold postcondition
    rw [witness_final_values.1, witness_final_values.2]
    decide

-- One-step/finite-path soundness turns the symbolic counterexample into a
-- genuine concrete execution.
theorem counterexample :
    ∃ s s', BigStep (program, s) s' ∧ ¬ postcondition s' := by
  have hRun :=
    (sym_finite_soundness witness symbolic_execution symbolic_violation.1).2
  refine ⟨witness, concretize finalStore witness, ?_, symbolic_violation.2⟩
  simpa only [concretize_initial] using hRun

theorem contract_false :
    ¬ (∀ s s', BigStep (program, s) s' → postcondition s') := by
  intro hContract
  obtain ⟨s, s', hRun, hViolation⟩ := counterexample
  exact hViolation (hContract s s' hRun)

end Slide15
