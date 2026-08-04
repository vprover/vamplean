import Lean.Meta.WHNF
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic
import Std.Tactic.BVDecide

universe u
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option warningAsError false

set_option maxHeartbeats 1000000000

variable {iota : Type u}
variable [Inhabited iota]

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
theorem or_forall_prenex_left (ι : Type u) (A : Prop) (B : ι → Prop) : ((∀ v0 : ι, B v0) ∨ A) ↔ (∀ v0 : ι, (B v0 ∨ A)) := by
  constructor
  · intro h v0
    cases h with
    | inl a => left; exact a v0
    | inr b => right; exact b
  · intro h
    by_cases ha : A
    · right; exact ha
    · left; intro v0; have hb := h v0; cases hb with
      | inl b' => exact b'
      | inr a' => contradiction

theorem and_forall_prenex (ι : Type u) [hι : Nonempty ι] (A : Prop) (B : ι → Prop) : (A ∧ (∀ v0 : ι, B v0)) ↔ (∀ v0 : ι, (A ∧ B v0)) := by
  constructor
  · intro h v0
    have a := h.left
    have b := h.right v0
    exact And.intro a b
  · intro h
    constructor
    · have a := h (Classical.choice hι)
      exact a.left
    · intro v0
      exact (h v0).right

theorem and_forall_prenex_left (ι : Type u) [hι : Nonempty ι] (A : Prop) (B : ι → Prop) : ((∀ v0 : ι, B v0) ∧ A) ↔ (∀ v0 : ι, (B v0 ∧ A)) := by
  constructor
  · intro h v0
    have a := h.left v0
    have b := h.right
    exact And.intro a b
  · intro h
    constructor
    · intro v0
      exact (h v0).left
    · have a := h (Classical.choice hι)
      exact a.right

theorem or_exists_prenex (ι : Type u) [hι : Nonempty ι] (A : Prop) (B : ι → Prop) :
  (A ∨ (∃ v0 : ι, B v0)) ↔ (∃ v0 : ι, (A ∨ B v0)) := by
  constructor
  · intro h
    cases h with
    | inl a => apply Exists.intro (Classical.choice hι); left; exact a
    | inr b => rcases b with ⟨ v0 , hb ⟩ ; apply Exists.intro v0; right; exact hb
  · intro h
    rcases h with ⟨ v0 , h1 ⟩
    cases h1 with
    | inl a => left; exact a
    | inr b => right; apply Exists.intro v0; exact b


theorem or_exists_prenex_left (ι : Type u) [hι : Nonempty ι] (A : Prop) (B : ι → Prop) :
  ((∃ v0 : ι, B v0) ∨ A) ↔ (∃ v0 : ι, (B v0 ∨ A)) := by
  constructor
  · intro h
    cases h with
    | inl a => rcases a with ⟨ v0 , hb ⟩ ; apply Exists.intro v0; left; exact hb
    | inr b => apply Exists.intro (Classical.choice hι); right; exact b
  · intro h
    rcases h with ⟨ v0 , h1 ⟩
    cases h1 with
    | inl b => left; apply Exists.intro v0; exact b
    | inr a => right; exact a

theorem and_exists_prenex_left (ι : Type u) (A : Prop) (B : ι → Prop) :
   ((∃ v0 : ι, B v0) ∧ A) ↔ (∃ v0 : ι, (B v0 ∧ A)) := by
  constructor
  · intro h
    cases h with
    | intro a b => rcases a with ⟨ v0 , hb ⟩ ; apply Exists.intro v0; constructor; exact hb; exact b
  · intro h
    rcases h with ⟨ v0 , h1 ⟩
    constructor
    · apply Exists.intro v0; exact h1.left
    · exact h1.right

theorem and_exists_prenex (ι : Type u) (A : Prop) (B : ι → Prop) :
   (A ∧ (∃ v0 : ι, B v0)) ↔ (∃ v0 : ι, (A ∧ B v0)) := by
  simp_all only [exists_and_left]

export Classical (not_not)

syntax "prenexify" (" at " ident)? : tactic

macro_rules
  | `(tactic| prenexify) => `(tactic| repeat (first | simp (config := {maxSteps := 10000000, failIfUnchanged := true}) only [or_forall_prenex_left, and_forall_prenex_left] | simp (config := {maxSteps := 10000000, failIfUnchanged := true}) only [and_forall_prenex, or_forall_prenex]))
  | `(tactic| prenexify at $a:ident) => `(tactic | repeat (first | simp (config := {maxSteps := 10000000, failIfUnchanged := true}) only [or_forall_prenex_left, and_forall_prenex_left] at $a:ident | simp (config := {maxSteps := 10000000, failIfUnchanged := true}) only [and_forall_prenex, or_forall_prenex] at $a:ident))

syntax "exists_prenex" (" at " ident)? : tactic

macro_rules
  | `(tactic| exists_prenex) => `(tactic| repeat (first | simp (config := {maxSteps := 10000000, failIfUnchanged := true}) only [or_exists_prenex_left, and_exists_prenex_left, Classical.skolem] | simp (config := {maxSteps := 10000000, failIfUnchanged := true}) only [or_exists_prenex, and_exists_prenex, Classical.skolem]))
  | `(tactic| exists_prenex at $a:ident) => `(tactic | repeat (first | simp (config := {maxSteps := 10000000, failIfUnchanged := true}) only [or_exists_prenex_left, and_exists_prenex_left, Classical.skolem] at $a:ident | simp (config := {maxSteps := 10000000, failIfUnchanged := true}) only [or_exists_prenex, and_exists_prenex, Classical.skolem] at $a:ident))

def Xor' (a b : Prop) := (a ∧ ¬b) ∨ (b ∧ ¬a)

@[grind =] theorem xor_def {a b : Prop} : Xor' a b ↔ (a ∧ ¬b) ∨ (b ∧ ¬a) := Iff.rfl

@[simp] theorem xor_true : Xor' True = Not := by grind

@[simp] theorem xor_false : Xor' False = id := by grind


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

theorem by_contradiction {p : Prop} : (¬p → False) → p :=
  open scoped Classical in Decidable.byContradiction


theorem our_xor_to_nnf (a b : Prop) : Xor' a b ↔ (¬b ∨ ¬a) ∧ (b ∨ a) := by
  unfold Xor'
  constructor
  · intro h
    cases h with
    | inl x =>
      constructor
      · left; exact x.right
      · right; exact x.left
    | inr x =>
      constructor
      · right; exact x.right
      · left; exact x.left
  · intro h
    have h1 := h.left
    have h2 := h.right
    simp only [Classical.or_iff_not_imp_left,Classical.not_not] at h1 h2
    apply by_contradiction
    intro contra
    simp_all only [not_or, not_and, Classical.not_not, not_false_eq_true, not_true_eq_false, imp_false,
      or_true, or_false, and_self]

theorem our_iff_to_nnf {a b : Prop} : (a ↔ b) ↔ (a ∨ ¬b) ∧ (b ∨ ¬a) :=
  by
  constructor
  · intro h
    rw[h]
    simp only [and_self]
    exact Classical.em b
  · intro h
    classical
    simp only [Decidable.iff_iff_not_or_and_or_not]
    rw[And.comm]
    rewrite (occs := [2]) [Or.comm]
    trivial

theorem our_not_xor_to_nnf (a b : Prop) : ¬(Xor' a b) ↔ (a ∨ ¬b) ∧ (b ∨ ¬a) := by
  simp only [not_xor_iff]
  exact our_iff_to_nnf

theorem our_not_iff_to_nnf (a b : Prop) : ¬(a ↔ b) ↔ (¬b ∨ ¬a) ∧ (b ∨ a) := by
  simp only [not_iff_xor]
  exact our_xor_to_nnf a b

theorem forall_false_iff {α : Prop} [hα : Nonempty α] : (∀ x : α, False) ↔ (False) := by
  constructor
  · intro h
    exact h (Classical.choice hα)
  · intro h
    intro x
    exact h

theorem exists_true_iff {alpha : Prop} [hα : Nonempty α] : (∃ x : α, True) ↔ (True) := by
  constructor
  · intro h
    trivial
  · intro
    apply Exists.intro (Classical.choice hα)
    trivial

theorem imp_iff_not_or : a → b ↔ ¬a ∨ b := open scoped Classical in Decidable.imp_iff_not_or

theorem imp_iff_or_not {b a : Prop} : b → a ↔ a ∨ ¬b :=
  open scoped Classical in Decidable.imp_iff_or_not

theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := open scoped Classical in Decidable.not_and_iff_not_or_not

theorem forall_true_iff {α : Prop} [hα : Nonempty α] : (∀ x : α, True) ↔ (True) := by
  constructor
  · intro h
    trivial
  · intro
    intro x
    trivial

theorem not_imp_not : ¬a → ¬b ↔ b → a := by
  constructor
  · intro h hb
    apply Classical.byContradiction
    intro ha
    exact h ha hb
  · exact mt

@[simp] theorem xor_self (a : Prop) : Xor' a a = False := by grind

syntax "ennf_transformation" "at" ident : tactic
macro_rules
  | `(tactic| ennf_transformation at $a) =>
    `(tactic | simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [imp_iff_or_not, not_and_or, not_or,
      Classical.not_not, not_iff_xor, not_xor_iff, Classical.not_forall,
       not_exists, not_false_iff, not_true, xor_self, ne_eq,-eq_self] at $a:ident<;> simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [not_true, xor_self, -eq_self])

syntax "flattening" "at" ident : tactic
macro_rules
  | `(tactic| flattening at $a) => `(tactic | simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [and_assoc, or_assoc, Classical.not_not] at $a:ident<;> simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [])

syntax "remove_tauto" "at" ident : tactic
macro_rules
  | `(tactic| remove_tauto at $a) =>
     `(tactic | simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [true_and, and_true, false_and, and_false, or_true, true_or,
       false_or, or_false, not_true, not_false_iff, imp_true_iff, false_imp_iff,
       true_imp_iff, true_iff, iff_true, false_iff, iff_false,
       true_xor, xor_true, false_xor, xor_false ,forall_true_iff,
       forall_false_iff, exists_true_iff, exists_false] at $a:ident<;> simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [not_true])

syntax "nnf_transformation" "at" ident: tactic
macro_rules
| `(tactic| nnf_transformation at $a) =>
    `(tactic | simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [↓ not_and_or, ↓ not_or, imp_iff_or_not,
       ↓ Classical.not_not, ↓  Classical.not_forall, ↓ not_exists, ↓ not_false,
       ↓ not_true, ↓ our_iff_to_nnf, ↓ our_xor_to_nnf,
       ↓ our_not_iff_to_nnf, ↓ our_not_xor_to_nnf] at $a:ident<;>try simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [not_true])

theorem imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a → b) = (c → d) :=
  propext (imp_congr h₁.to_iff h₂.to_iff)

partial def symmUnify (e1 e2 : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let e1 ← Lean.Meta.whnf e1
  let e2 ← Lean.Meta.whnf e2
  if ← Lean.Meta.isDefEq e1 e2 then return ← Lean.Meta.mkEqRefl e1
  -- Leaf Case: (a = b) vs (b = a)
  if let some (_, l1, r1) := e1.eq? then
    if let some (_, l2, r2) := e2.eq? then
      if (← Lean.Meta.isDefEq l1 r2) && (← Lean.Meta.isDefEq r1 l2) then
        let commIff ← Lean.Meta.mkAppOptM ``Eq.comm #[none, some l1, some r1]
        return ← Lean.Meta.mkAppM ``propext #[commIff]
  if e1.isArrow && e2.isArrow then
    let dom1 := e1.bindingDomain!
    let dom2 := e2.bindingDomain!
    let body1 := e1.bindingBody!
    let body2 := e2.bindingBody!
    let domEq ← symmUnify dom1 dom2
    let bodyEq ← symmUnify body1 body2
    return ← Lean.Meta.mkAppM ``imp_congr_eq #[domEq, bodyEq]
  if e1.isForall && e2.isForall && !e1.isArrow && !e2.isArrow then
    if !(← Lean.Meta.isDefEq e1.bindingDomain! e2.bindingDomain!) then
      throwError "Symmetry match failed: Quantifier domain mismatch."
    return ← Lean.Meta.withLocalDecl e1.bindingName! e1.bindingInfo! e1.bindingDomain! fun x => do
      -- Instantiate the binder bodies with the local variable x
      let b1 := e1.bindingBody!.instantiate1 x
      let b2 := e2.bindingBody!.instantiate1 x
      --trace debug b1 b2
      let eqBody ← symmUnify b1 b2
      -- mkForallCongr: (∀ x, P x = Q x) → (∀ x, P x) = (∀ x, Q x)
      Lean.Meta.mkForallCongr (← Lean.Meta.mkLambdaFVars #[x] eqBody)
  if e1.isLambda && e2.isLambda then
    if !(← Lean.Meta.isDefEq e1.bindingDomain! e2.bindingDomain!) then
      throwError "Symmetry match failed: Lambda domain mismatch."
    return ← Lean.Meta.withLocalDecl e1.bindingName! e1.bindingInfo! e1.bindingDomain! fun x => do
      let b1 := e1.bindingBody!.instantiate1 x
      let b2 := e2.bindingBody!.instantiate1 x
      let eqBody ← symmUnify b1 b2
      -- Apply funext: (∀ x, f x = g x) → f = g
      let proofForall ← Lean.Meta.mkLambdaFVars #[x] eqBody
      Lean.Meta.mkAppM ``funext #[proofForall]
  -- Structural Recursion
  if e1.isApp && e2.isApp then
    let f1 := e1.getAppFn
    let f2 := e2.getAppFn
    if ← Lean.Meta.isDefEq f1 f2 then
      let args1 := e1.getAppArgs
      let args2 := e2.getAppArgs
      if args1.size == args2.size then
        let mut pr ← Lean.Meta.mkEqRefl f1
        for i in [:args1.size] do
          let arg1 := args1[i]!
          let arg2 := args2[i]!
          let argPr ← symmUnify arg1 arg2
          -- mkCongr: given (f = g) and (a = b), produces (f a = g b)
          pr ← Lean.Meta.mkCongr pr argPr
        return pr
  throwError "Symmetry match failed between types:\n  {e1} and \n  {e2}"

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
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let target ← goal.getType
      let fvarId ← Lean.Elab.Tactic.getFVarId h
      let hypDecl ← fvarId.getDecl
      let eqPr ← symmUnify hypDecl.type target
      let finalPr ← Lean.Meta.mkAppM ``Eq.mp #[eqPr, hypDecl.toExpr]
      goal.assign finalPr


theorem sat_or_norm1 {a b:Bool} : (¬(a = true) ∨ (b = true)) = (!a || b) := by
  simp only [Bool.not_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]

theorem sat_or_norm2 {a b: Bool} : ((a = true) ∨ ¬(b = true)) = (a || !b) := by
  simp only [Bool.not_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]

theorem sat_or_norm3 {a b:Bool} : (¬(a = true) ∨ ¬(b = true)) = (!a || !b) := by
  simp only [Bool.not_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]

theorem sat_or_norm4 {a b:Bool} : ((a = true) ∨ (b = true)) = (a || b) := by
  simp only [Bool.or_eq_true]

theorem sat_not_norm1 {a:Bool} : (¬a = true) = (!a) := by
  simp only [Bool.not_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]

syntax "rewrite_decide_eq" "[" (ident)+ "]" : tactic
elab "rewrite_decide_eq" "[" vars:(ident)+ "]" : tactic => do
  for v in vars do
    Lean.Elab.Tactic.evalTactic (← `(tactic| rewrite [← @decide_eq_true_eq $(v)]))

syntax "sat_norm" : tactic
macro_rules
  | `(tactic| sat_norm) => `(tactic | simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [sat_or_norm1, sat_or_norm2, sat_or_norm3, sat_or_norm4, ← Bool.or_assoc, sat_not_norm1])

theorem cnf1 {a b c : Prop} : a ∧ b ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by
  exact and_or_right

theorem cnf2 {a b c : Prop} : c ∨ a ∧ b ↔ (c ∨ a) ∧ (c ∨ b) := by
  exact or_and_left

theorem cnf_prenex1 {α : Sort u} [hα : Nonempty α] (a : α → Prop) (b : Prop) : (∀ x, a x ∧ b) ↔ (∀ x, a x) ∧ b := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).left
    · exact (h (Classical.choice hα)).right
  · intro h
    intro x
    constructor
    · exact h.left x
    · exact h.right

theorem cnf_prenex2 {α : Sort u} [hα : Nonempty α] (a : α → Prop) (b : Prop) : (∀ x, b ∧ a x) ↔ b ∧ (∀ x, a x) := by
  constructor
  · intro h
    constructor
    · exact (h (Classical.choice hα)).left
    · intro x
      exact (h x).right
  · intro h
    intro x
    constructor
    · exact h.left
    · exact h.right x

theorem cnf_prenex3 {α : Sort u} (a b : α → Prop) : (∀ x, a x ∧ b x) ↔ (∀ x, a x) ∧ (∀ x, b x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).left
    · intro x
      exact (h x).right
  · intro h
    intro x
    constructor
    · exact h.left x
    · exact h.right x

syntax "cnfify" "at" ident : tactic
macro_rules  | `(tactic| cnfify at $a) => `(tactic | (simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [cnf1, cnf2, and_assoc] at $a:ident; simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [cnf_prenex1, cnf_prenex2, cnf_prenex3] at $a:ident))

def exists' {α : Sort u} (p : α → Prop) := ∃ x, p x

theorem exists'_eq_exists {α : Sort u} (p : α → Prop) : exists' p ↔ ∃ x, p x := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem or_exists'_prenex (ι : Type u) [hι : Nonempty ι] (A : Prop) (B : ι → Prop) :
  (A ∨ (exists' B)) ↔ (exists' (fun v0 => A ∨ B v0)) := by
  simp_all only [exists'_eq_exists, or_exists_prenex]

theorem or_exists'_prenex_left (ι : Type u) [hι : Nonempty ι] (A : Prop) (B : ι → Prop) :
  ((exists' B) ∨ A) ↔ (exists' (fun v0 => B v0 ∨ A)) := by
  simp_all only [exists'_eq_exists, or_exists_prenex_left]

theorem and_exists'_prenex_left (ι : Type u) (A : Prop) (B : ι → Prop) :
   ((exists' B) ∧ A) ↔ (exists' (fun v0 => B v0 ∧ A)) := by
  simp_all only [exists'_eq_exists, exists_and_right]

theorem and_exists'_prenex (ι : Type u) (A : Prop) (B : ι → Prop) :
   (A ∧ (exists' B)) ↔ (exists' (fun v0 => A ∧ B v0)) := by
  simp_all only [exists'_eq_exists, exists_and_left]

theorem exists'_skolem.{v} {α : Sort u} {b : α → Sort v} {p : (x : α) → b x → Prop} :
  (∀ (x : α), exists' (fun y => p x y)) ↔ exists' (fun f : ((x : α) → b x) => ∀ (x : α), p x (f x)) := by
  simp_all [exists'_eq_exists, Classical.skolem]


theorem exists'_exists_prenex.{v} (α : Type u) (β: Type v) (A : α → β → Prop) : (∃ x: α, exists' (fun y : β => A x y)) ↔ (exists' (fun x: β => ∃ y: α, A y x)) := by
  simp_all only [exists'_eq_exists]
  rw[exists_comm]


#check Classical.skolem

syntax "existspr_prenex" (" at " ident)? : tactic

macro_rules
  | `(tactic| existspr_prenex) => `(tactic| simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [or_exists'_prenex_left, and_exists'_prenex_left, exists'_skolem, or_exists'_prenex, and_exists'_prenex, exists'_exists_prenex] )
  | `(tactic| existspr_prenex at $a:ident) => `(tactic | simp (config := {maxSteps := 10000000, failIfUnchanged := false}) only [or_exists'_prenex_left, and_exists'_prenex_left, exists'_skolem, or_exists'_prenex, and_exists'_prenex,exists'_exists_prenex] at $a:ident)

open Lean Meta Elab Tactic

/--
Removes all free variables from the local context except for those specified
in the `exceptions` array.
-/
def _root_.Lean.MVarId.clearAllExcept (mvarId : MVarId) (exceptions : Array FVarId) : MetaM MVarId :=
  mvarId.withContext do
    let lctx ← getLCtx
    -- Collect all fvars in the context that are NOT in the exceptions list
    let toClear := lctx.foldl (init := #[]) fun acc localDecl =>
      if exceptions.contains localDecl.fvarId then acc else acc.push localDecl.fvarId

    -- tryClearMany clears from bottom-to-top, handling basic dependency ordering
    mvarId.tryClearMany toClear

-- Syntax allowing one or more identifiers: e.g., `clear - asdf` or `clear - a b c`
syntax (name := clearExcept) "clearExcept" (ident+) : tactic

@[tactic clearExcept]
def evalClearExcept : Tactic := fun stx => do
  match stx with
  | `(tactic| clearExcept $ids*) => do
    let mvarId ← getMainGoal
    mvarId.withContext do
      -- Resolve the syntax identifiers to actual FVarIds in the current context
      let exceptFVarIds ← ids.mapM getFVarId
      -- Run the clearing function
      let newMVarId ← mvarId.clearAllExcept exceptFVarIds
      -- Update the proof state with the new goal
      replaceMainGoal [newMVarId]
  | _ => throwUnsupportedSyntax
