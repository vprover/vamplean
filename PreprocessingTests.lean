import VampLean

/-! Structural preprocessing must preserve equality literals for proof replay.
`guard_hyp` and `guard_target` check clause shape before finishing the proof.
Run with `lake env lean PreprocessingTests.lean`.
-/

example {α : Type} (t : α) (P : α → Prop)
    (h : ¬ (t = t) ∨ ∀ x, P x) : ∀ x, ¬ (t = t) ∨ P x := by
  prenexify at h
  guard_hyp h : ∀ x, ¬ (t = t) ∨ P x
  exact h

example {α : Type} (t : α) (P : α → Prop)
    (h : ∀ x, ¬ (t = t) ∨ P x) : ¬ (t = t) ∨ ∀ x, P x := by
  prenexify
  guard_target = ∀ x, ¬ (t = t) ∨ P x
  exact h

example {α : Type} (t : α) (P : α → Prop)
    (h : ¬ (t = t) ∨ ∃ x, P x) : ∃ x, ¬ (t = t) ∨ P x := by
  letI : Inhabited α := ⟨t⟩
  exists_prenex at h
  guard_hyp h : ∃ x, ¬ (t = t) ∨ P x
  exact h

example {α : Type} (t : α) (P : α → Prop)
    (h : ∃ x, ¬ (t = t) ∨ P x) : ¬ (t = t) ∨ ∃ x, P x := by
  letI : Inhabited α := ⟨t⟩
  exists_prenex
  guard_target = ∃ x, ¬ (t = t) ∨ P x
  exact h

example {α : Type} (t : α) (A B : Prop)
    (h : (¬ (t = t) ∨ A) ∨ B) : ¬ (t = t) ∨ (A ∨ B) := by
  flattening at h
  guard_hyp h : ¬ (t = t) ∨ (A ∨ B)
  exact h

example {α : Type} (t : α) (A : Prop)
    (h : ¬ (t = t ∧ A)) : ¬ (t = t) ∨ ¬ A := by
  ennf_transformation at h
  guard_hyp h : ¬ (t = t) ∨ ¬ A
  exact h

example {α : Type} (t : α) (A : Prop)
    (h : ¬ (t = t ∧ A)) : ¬ (t = t) ∨ ¬ A := by
  nnf_transformation at h
  guard_hyp h : ¬ (t = t) ∨ ¬ A
  exact h

example {α : Type} (t : α) (A B : Prop)
    (h : ¬ (t = t) ∨ (A ∧ B)) : (¬ (t = t) ∨ A) ∧ (¬ (t = t) ∨ B) := by
  cnfify at h
  guard_hyp h : (¬ (t = t) ∨ A) ∧ (¬ (t = t) ∨ B)
  exact h

-- Explicit tautology removal should still simplify reflexive equality.
example {α : Type} (t : α) (A : Prop) (h : ¬ (t = t) ∨ A) : A := by
  remove_tauto at h
  guard_hyp h : A
  exact h
