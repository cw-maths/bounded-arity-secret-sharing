module

public import BoundedArity.ClauseAssemblyCount
public import BoundedArity.FormalTable

/-!
# The access structure defined by a family of clauses

Nonempty clauses make the full participant set authorised. A nonempty
family makes the empty coalition unauthorised. Meeting every clause is
monotone, so these data give the proper access structure used in T5.
-/

@[expose] public section

namespace BoundedArity

variable {E : Type*} [DecidableEq E]

/-- The unit of rank gained by adjoining the secret to an unauthorised view. -/
noncomputable def clauseUnauthorizedBit (Cs : Finset (Finset E))
    (U : Finset E) : ℕ := by
  classical
  exact if HitsAll Cs U then 0 else 1

theorem clauseUnauthorizedBit_of_hits (Cs : Finset (Finset E))
    (U : Finset E) (hU : HitsAll Cs U) :
    clauseUnauthorizedBit Cs U = 0 := by
  classical
  simp [clauseUnauthorizedBit, hU]

theorem clauseUnauthorizedBit_of_not_hits (Cs : Finset (Finset E))
    (U : Finset E) (hU : ¬ HitsAll Cs U) :
    clauseUnauthorizedBit Cs U = 1 := by
  classical
  simp [clauseUnauthorizedBit, hU]

variable [Fintype E]

/-- A proper monotone access structure from a nonempty family of nonempty clauses. -/
def clauseAccessStructure (Cs : Finset (Finset E)) (hCs : Cs.Nonempty)
    (hClauses : ∀ C ∈ Cs, C.Nonempty) : AccessStructure E where
  Authorized := HitsAll Cs
  upward_closed := hitsAll_mono Cs
  empty_unauthorized := not_hitsAll_empty Cs hCs
  univ_authorized := hitsAll_univ Cs hClauses

@[simp] theorem authorized_clauseAccessStructure (Cs : Finset (Finset E))
    (hCs : Cs.Nonempty) (hClauses : ∀ C ∈ Cs, C.Nonempty) (U : Finset E) :
    (clauseAccessStructure Cs hCs hClauses).Authorized U ↔ HitsAll Cs U :=
  Iff.rfl

/-- The clause indicator agrees exactly with the fixed-table access indicator. -/
@[simp] theorem unauthorizedBit_clauseAccessStructure (Cs : Finset (Finset E))
    (hCs : Cs.Nonempty) (hClauses : ∀ C ∈ Cs, C.Nonempty) (U : Finset E) :
    unauthorizedBit (clauseAccessStructure Cs hCs hClauses) U =
      clauseUnauthorizedBit Cs U := by
  classical
  rfl

end BoundedArity
