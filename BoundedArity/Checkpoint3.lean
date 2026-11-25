module

public import BoundedArity.FormalTable

/-!
# The formal-table checkpoint

This file collects T3 of the approved review packet and adds the named arity
coefficient (B10) and the maximum-share bound predicate (E32).

This is an UNCOMPILED DRAFT. The source must pass `lake build` and the axiom
audit before this checkpoint is described as formally verified.

No claim about local linear representations, entropy inequalities, or the
final bounded-arity barrier is made in this milestone.
-/

@[expose] public section

namespace BoundedArity

/-- B10: the coefficient in the bounded-arity barrier. Natural-number
subtraction is truncated and natural-number division is floor division. -/
def arityConstant (r : ℕ) : ℕ :=
  (r - 2).choose ((r - 2) / 2)

theorem arityConstant_pos (r : ℕ) : 0 < arityConstant r := by
  exact Nat.choose_pos (Nat.div_le_self (r - 2) 2)

theorem one_le_arityConstant (r : ℕ) : 1 ≤ arityConstant r :=
  arityConstant_pos r

@[simp] theorem arityConstant_six : arityConstant 6 = 6 := by
  decide

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- E32: a supplied upper bound on every physical singleton. Normalisation
at the secret is imposed separately by `HasNormalizedAccess`. -/
def MaxShareAtMost (F : Finset (Option P) → ℝ) (L : ℝ) : Prop :=
  ∀ p : P, F {some p} ≤ L

/-- The exact singleton formula implies the pointwise objective bound. -/
theorem formalTable_maxShareAtMost (Γ : AccessStructure P) (b : ℕ) :
    MaxShareAtMost (fun X => (formalTable Γ b X : ℝ))
      ((1 + b * (Fintype.card P - 1) : ℕ) : ℝ) := by
  intro p
  change (formalTable Γ b {some p} : ℝ) ≤
    ((1 + b * (Fintype.card P - 1) : ℕ) : ℝ)
  exact (Nat.cast_le (α := ℝ)).2 (formalTable_singleton Γ b p).le

/-- T3: the fixed formal table satisfies the whole-table Shannon and access
constraints and has the claimed exact singleton values. -/
theorem formalTable_checkpoint (Γ : AccessStructure P) (b : ℕ) (hb : 1 ≤ b) :
    IsPolymatroid (fun X => (formalTable Γ b X : ℝ)) ∧
      HasNormalizedAccess Γ (fun X => (formalTable Γ b X : ℝ)) ∧
      (∀ p : P, formalTable Γ b {some p} =
        1 + b * (Fintype.card P - 1)) ∧
      MaxShareAtMost (fun X => (formalTable Γ b X : ℝ))
        ((1 + b * (Fintype.card P - 1) : ℕ) : ℝ) := by
  exact ⟨formalTable_isPolymatroid Γ b hb,
    formalTable_hasNormalizedAccess Γ b,
    formalTable_singleton Γ b,
    formalTable_maxShareAtMost Γ b⟩

/-- The T3 checkpoint with the eventual arity-dependent coefficient.
This still asserts only Shannon/access feasibility, not E31 feasibility. -/
theorem formalTable_arity_checkpoint (Γ : AccessStructure P) (r : ℕ) :
    IsPolymatroid (fun X => (formalTable Γ (arityConstant r) X : ℝ)) ∧
      HasNormalizedAccess Γ
        (fun X => (formalTable Γ (arityConstant r) X : ℝ)) ∧
      MaxShareAtMost
        (fun X => (formalTable Γ (arityConstant r) X : ℝ))
        ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ) := by
  obtain ⟨hpoly, haccess, _hsingle, hbound⟩ :=
    formalTable_checkpoint Γ (arityConstant r) (one_le_arityConstant r)
  exact ⟨hpoly, haccess, hbound⟩

end BoundedArity
