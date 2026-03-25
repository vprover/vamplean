import Mathlib.Logic.Basic
import Lean
import Duper
import Mathlib.Tactic.NthRewrite
import Qq
open Lean Elab Tactic Meta
universe u
set_option linter.style.longLine false
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option warningAsError false

variable {iota : Type u}
variable [Inhabited iota]
def inhabit_iota : iota := default

omit [Inhabited iota] in
theorem or_forall_prenex (A : Prop) (B : iota → Prop) : (A ∨ (∀ v0 : iota, B v0)) ↔ (∀ v0 : iota, (A ∨ B v0)) := by
  constructor
  · intro h v0
    cases h with
    | inl a => left; exact a
    | inr b => right; exact b v0
  · intro h
    by_cases ha : A
    · left; exact ha
    · right; intro v0; have hb := h v0; cases hb with
      | inl a' => contradiction
      | inr b' => exact b'

omit [Inhabited iota] in
theorem or_forall_prenex_left (A : Prop) (B : iota → Prop) : ((∀ v0 : iota, B v0) ∨ A) ↔ (∀ v0 : iota, (B v0 ∨ A)) := by
  grind



theorem and_forall_prenex (ι : Type u) [Inhabited ι] (A : Prop) (B : ι → Prop) : (A ∧ (∀ v0 : ι, B v0)) ↔ (∀ v0 : ι, (A ∧ B v0)) := by
  constructor
  · intro h v0
    have a := h.left
    have b := h.right v0
    exact And.intro a b
  · intro h
    constructor
    · have a := h default
      exact a.left
    · intro v0
      exact (h v0).right



theorem and_forall_prenex_left (ι : Type u) [Inhabited ι] (A : Prop) (B : ι → Prop) : ((∀ v0 : ι, B v0) ∧ A) ↔ (∀ v0 : ι, (B v0 ∧ A)) := by
  constructor
  · intro h v0
    have a := h.left v0
    have b := h.right
    exact And.intro a b
  · intro h
    constructor
    · intro v0
      exact (h v0).left
    · have a := h inhabit_iota
      exact a.right


theorem or_exists_prenex (ι : Type u) [Inhabited ι] (A : Prop) (B : ι → Prop) :
  (A ∨ (∃ v0 : ι, B v0)) ↔ (∃ v0 : ι, (A ∨ B v0)) := by
  constructor
  · intro h
    cases h with
    | inl a => apply Exists.intro default; left; exact a
    | inr b => rcases b with ⟨ v0 , hb ⟩ ; apply Exists.intro v0; right; exact hb
  · intro h
    rcases h with ⟨ v0 , h1 ⟩
    cases h1 with
    | inl a => left; exact a
    | inr b => right; apply Exists.intro v0; exact b

theorem or_exists_prenex_left (ι : Type u) [Inhabited ι] (A : Prop) (B : ι → Prop) :
  ((∃ v0 : ι, B v0) ∨ A) ↔ (∃ v0 : ι, (B v0 ∨ A)) := by
  grind

theorem and_exists_prenex_left (ι : Type u) [Inhabited ι] (A : Prop) (B : ι → Prop) :
   ((∃ v0 : ι, B v0) ∧ A) ↔ (∃ v0 : ι, (B v0 ∧ A)) := by
  grind

theorem and_exists_prenex (ι : Type u) [Inhabited ι] (A : Prop) (B : ι → Prop) :
   (A ∧ (∃ v0 : ι, B v0)) ↔ (∃ v0 : ι, (A ∧ B v0)) := by
  simp_all only [exists_and_left]


syntax "prenexify" (" at " ident)? : tactic

macro_rules
  | `(tactic| prenexify) => `(tactic| repeat (first | simp (config := {maxSteps := 10000000}) only [or_forall_prenex_left, and_forall_prenex_left] | simp (config := {maxSteps := 10000000}) only [and_forall_prenex, or_forall_prenex]))
  | `(tactic| prenexify at $a:ident) => `(tactic | repeat (first | simp (config := {maxSteps := 10000000}) only [or_forall_prenex_left, and_forall_prenex_left] at $a:ident | simp (config := {maxSteps := 10000000}) only [and_forall_prenex, or_forall_prenex] at $a:ident))

syntax "exists_prenex" (" at " ident)? : tactic

macro_rules
  | `(tactic| exists_prenex) => `(tactic| repeat (first | simp (config := {maxSteps := 10000000}) only [or_exists_prenex_left, and_exists_prenex_left, Classical.skolem] | simp (config := {maxSteps := 10000000}) only [or_exists_prenex, and_exists_prenex, Classical.skolem]))
  | `(tactic| exists_prenex at $a:ident) => `(tactic | repeat (first | simp (config := {maxSteps := 10000000}) only [or_exists_prenex_left, and_exists_prenex_left, Classical.skolem] at $a:ident | simp (config := {maxSteps := 10000000}) only [or_exists_prenex, and_exists_prenex, Classical.skolem] at $a:ident))


theorem not_iff_xor (a b : Prop) : ¬(a ↔ b) ↔ Xor' a b := by
  constructor
  · intro h
    grind
  · intro h
    grind

theorem not_xor_iff (a b : Prop) : ¬ Xor' a b ↔ (a ↔ b) := by
  constructor
  · intro h
    grind
  · intro h
    grind

theorem true_xor (a : Prop) : (Xor' True a) ↔ ¬a := by
  simp_all only [xor_true]

theorem false_xor (a : Prop) : (Xor' False a) ↔ a := by
  simp_all only [xor_false, id_eq]


theorem our_xor_to_nnf (a b : Prop) : Xor' a b ↔ (¬b ∨ ¬a) ∧ (b ∨ a) := by
  grind


theorem our_iff_to_nnf {a b : Prop} : (a ↔ b) ↔ (a ∨ ¬b) ∧ (b ∨ ¬a) :=
  by
  grind

theorem our_not_xor_to_nnf (a b : Prop) : ¬(Xor' a b) ↔ (a ∨ ¬b) ∧ (b ∨ ¬a) := by
  grind

theorem our_not_iff_to_nnf (a b : Prop) : ¬(a ↔ b) ↔ (¬b ∨ ¬a) ∧ (b ∨ a) := by
  grind

syntax "ennf_transformation" "at" ident : tactic
macro_rules
  | `(tactic| ennf_transformation at $a) =>
    `(tactic | try simp only [imp_iff_or_not, not_and_or, not_or,
      not_not, not_iff_xor, not_xor_iff, not_forall,
       not_exists, not_false_iff, not_true, xor_self] at $a:ident<;>try simp only [not_true, xor_self])

syntax "flattening" "at" ident : tactic
macro_rules
  | `(tactic| flattening at $a) => `(tactic | try simp only [and_assoc, or_assoc, not_not] at $a:ident)

syntax "remove_tauto" "at" ident : tactic
macro_rules
  | `(tactic| remove_tauto at $a) =>
     `(tactic | try simp only [true_and, false_and, true_or,
       false_or, not_true, not_false_iff, imp_true, false_imp,
       true_imp, true_iff, iff_true, false_iff, iff_false,
       true_xor, xor_true, false_xor, xor_false ,forall_true_iff,
       forall_false_iff, exists_true_iff_nonempty, exists_false] at $a:ident<;>try simp only [not_true])

syntax "nnf_transformation" "at" ident: tactic
macro_rules
| `(tactic| nnf_transformation at $a) =>
    `(tactic | try simp only [↓ not_and_or, ↓ not_or, imp_iff_or_not,
       ↓ not_not, ↓  not_forall, ↓ not_exists, ↓ not_false,
       ↓ not_true, ↓ our_iff_to_nnf, ↓ our_xor_to_nnf,
       ↓ our_not_iff_to_nnf, ↓ our_not_xor_to_nnf] at $a:ident<;>try simp only [not_true])


--  simp [or_forall_prenex]

syntax "and_constr" "⟨" term,* "⟩" : term

-- Use an elaboration rule to iteratively build nested `And.intro` applications
open Term

elab_rules : term
| `(and_constr ⟨ $[$ts:term],* ⟩) => do
  let terms := ts
  if terms.isEmpty then
    throwError "and_constr: requires at least one term"
  -- start with the last term and iteratively build `And.intro` applications
  let mut accExpr ← elabTerm terms[terms.size - 1]! none
  let mut i := terms.size
  while i > 1 do
    i := i - 1
    let tExpr ← elabTerm terms[i - 1]! none
    accExpr ← mkAppM ``And.intro #[tExpr, accExpr]
  return accExpr



partial def symmUnify (e1 e2 : Expr) : MetaM Expr := do
  if ← isDefEq e1 e2 then return ← mkEqRefl e1
  -- Leaf Case: (a = b) vs (b = a)
  if let some (_, l1, r1) := e1.eq? then
    if let some (_, l2, r2) := e2.eq? then
      if (← isDefEq l1 r2) && (← isDefEq r1 l2) then
        let commIff ← mkAppOptM ``Eq.comm #[none, some l1, some r1]
        return ← mkAppM ``propext #[commIff]
  if e1.isForall && e2.isForall then
    if !(← isDefEq e1.bindingDomain! e2.bindingDomain!) then
      throwError "Symmetry match failed: Quantifier domain mismatch."
    return ← withLocalDecl e1.bindingName! e1.bindingInfo! e1.bindingDomain! fun x => do
      -- Instantiate the binder bodies with the local variable x
      let b1 := e1.bindingBody!.instantiate1 x
      let b2 := e2.bindingBody!.instantiate1 x
      let eqBody ← symmUnify b1 b2
      -- mkForallCongr: (∀ x, P x = Q x) → (∀ x, P x) = (∀ x, Q x)
      mkForallCongr (← mkLambdaFVars #[x] eqBody)
  -- Structural Recursion
  if e1.isApp && e2.isApp then
    let f1 := e1.getAppFn
    let f2 := e2.getAppFn
    if ← isDefEq f1 f2 then
      let args1 := e1.getAppArgs
      let args2 := e2.getAppArgs
      if args1.size == args2.size then
        let mut pr ← mkEqRefl f1
        for i in [:args1.size] do
          let argPr ← symmUnify args1[i]! args2[i]!
          pr ← mkAppM ``congr #[pr, argPr]
        return pr
  throwError "Symmetry match failed between types:\n  {e1}\n  {e2}"

/--
  Usage:
  'symm_match'      (tries to find a matching hyp in context)
  'symm_match h'    (uses specific hypothesis h)
-/
syntax (name := symm_match_tactic) "symm_match" "using" (ident) : tactic

elab_rules : tactic
  | `(tactic| symm_match using $h) => do
    -- try simplifying the goal first
    try Lean.Elab.Tactic.evalTactic (← `(tactic| simp only at $h:ident)) catch _ => pure ()
    try Lean.Elab.Tactic.evalTactic (← `(tactic| simp only)) catch _ => pure ()
    -- also try simplifying the given hypothesis `h`
    let goal ← getMainGoal
    goal.withContext do
      let target ← goal.getType
      let fvarId ← getFVarId h
      let hypDecl ← fvarId.getDecl
      let eqPr ← symmUnify hypDecl.type target
      let finalPr ← mkAppM ``Eq.mp #[eqPr, hypDecl.toExpr]
      goal.assign finalPr
