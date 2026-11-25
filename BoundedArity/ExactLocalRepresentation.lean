module

public import BoundedArity.LocalRepresentation
public import BoundedArity.LocalContract
public import BoundedArity.TypeModelExact

/-!
# T6: exact local representability over every field

The pair-difference clause ingredient removes the field-size restriction from
T6. For every grouping, a single finite-dimensional model realizes all queried
physical ranks, all ranks with the secret adjoined, and all full-group ranks.
The secret has rank exactly one, and none of the target ranks are scaled.
-/

@[expose] public section

namespace BoundedArity

section ArbitraryGroups

variable {K P G : Type*} [Field K] [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- The simultaneous physical/secret equations hold over every prescribed field. -/
theorem physicalGroupRealizes_everyField (B : G → Finset P)
    (Γ : AccessStructure P) (b : ℕ) (hb : arityConstant (Fintype.card G) ≤ b) :
    PhysicalGroupRealizes K B Γ b := by
  apply physicalGroupRealizes_of_clauseModels B Γ b hb
  intro C _hC hcard
  exact oneClause_exact_checkpoint C hcard

/-- T6's stronger contract: one model realizes all three reviewed equations. -/
theorem localGroupRealizes_checkpoint
    (Γ : AccessStructure P) (b : ℕ) (_hr : 2 ≤ Fintype.card G)
    (hb : arityConstant (Fintype.card G) ≤ b) (A : G → Finset (Option P)) :
    LocalGroupRealizes K Γ b A :=
  physicalGroupRealizes_localGroupRealizes A Γ b
    (physicalGroupRealizes_everyField (fun j => physicalPart (A j)) Γ b hb)

/-- T6's exact every-field headline: every chosen grouping of the fixed table
has one unscaled linear representation, valid for every group coalition. -/
theorem localRepresentability_checkpoint
    (Γ : AccessStructure P) (b : ℕ) (hr : 2 ≤ Fintype.card G)
    (hb : arityConstant (Fintype.card G) ≤ b) (A : G → Finset (Option P)) :
    LinearRankRealizes K (groupProjection (formalTable Γ b) A) :=
  localGroupRealizes_linearRankRealizes A Γ b
    (localGroupRealizes_checkpoint Γ b hr hb A)

end ArbitraryGroups

section AritySpecialization

variable {K P : Type*} [Field K] [Fintype P] [DecidableEq P]

/-- The stronger local contract at the exact coefficient used by the barrier. -/
theorem localGroupRealizes_arity_checkpoint (Γ : AccessStructure P)
    (r : ℕ) (hr : 2 ≤ r) (A : Fin r → Finset (Option P)) :
    LocalGroupRealizes K Γ (arityConstant r) A := by
  exact localGroupRealizes_checkpoint Γ (arityConstant r)
    (by simpa only [Fintype.card_fin] using hr) (by simp only [Fintype.card_fin, le_refl]) A

/-- T6 specialized to `r` groups and the coefficient `arityConstant r`. -/
theorem localRepresentability_arity_checkpoint (Γ : AccessStructure P)
    (r : ℕ) (hr : 2 ≤ r) (A : Fin r → Finset (Option P)) :
    LinearRankRealizes K (groupProjection (formalTable Γ (arityConstant r)) A) :=
  localGroupRealizes_linearRankRealizes A Γ (arityConstant r)
    (localGroupRealizes_arity_checkpoint Γ r hr A)

end AritySpecialization

end BoundedArity
