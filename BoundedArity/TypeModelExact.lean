module

public import BoundedArity.TypeModel
public import BoundedArity.OneClauseExact

/-!
# Exact type models over every prescribed field

The pair-difference one-clause construction supplies the same T5 interface
without a field-size assumption. All subsequent type and physical rank
identities therefore remain exact and unscaled over an arbitrary field.
-/

@[expose] public section

namespace BoundedArity

variable {K P G : Type*} [Field K] [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- T6's type model over every prescribed field, including the two-element field. -/
theorem typeModel_everyField
    (B : G → Finset P) (Γ : AccessStructure P)
    (hfull : Γ.Authorized (physicalUnion B Finset.univ))
    (b : ℕ) (hb : arityConstant (Fintype.card G) ≤ b) :
    ClauseAssemblyRealizes K (typeClauses B Γ) b := by
  apply typeModel_checkpoint B Γ hfull b hb
  intro C _hC hcard
  exact oneClause_exact_checkpoint C hcard

end BoundedArity
