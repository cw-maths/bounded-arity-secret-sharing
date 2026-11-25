module

public import BoundedArity.GroupModel

/-!
# One common local model for all three rank equations

The stronger T6 contract chooses one secret and one family of physical group
observations before quantifying over group coalitions. Adding that same secret
to exactly the groups which request it gives the full formal-table projection
in the same ambient space.
-/

@[expose] public section

namespace BoundedArity

variable {P G : Type*} [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- All physical, secret-adjoined, and full-group ranks in one common model. -/
def LocalGroupRealizes (K : Type*) [Field K] (Γ : AccessStructure P)
    (b : ℕ) (A : G → Finset (Option P)) : Prop :=
  ∃ n : ℕ, ∃ s : Fin n → K, ∃ X : G → Submodule K (Fin n → K),
    Module.finrank K (Submodule.span K {s}) = 1 ∧
      ∀ I : Finset G,
        Module.finrank K (jointSubspace X I) =
          physicalTable b (physicalUnion (fun j => physicalPart (A j)) I) ∧
        Module.finrank K
          (Submodule.span K {s} ⊔ jointSubspace X I : Submodule K (Fin n → K)) =
          physicalTable b (physicalUnion (fun j => physicalPart (A j)) I) +
            unauthorizedBit Γ (physicalUnion (fun j => physicalPart (A j)) I) ∧
        Module.finrank K (jointSubspace (fullGroupSpace A s X) I) =
          groupProjection (formalTable Γ b) A I

variable {K : Type*} [Field K]

omit [Fintype G] [DecidableEq G] in
/-- The full-group equation follows within the supplied physical/secret model. -/
theorem physicalGroupRealizes_localGroupRealizes
    (A : G → Finset (Option P)) (Γ : AccessStructure P) (b : ℕ)
    (h : PhysicalGroupRealizes K (fun j => physicalPart (A j)) Γ b) :
    LocalGroupRealizes K Γ b A := by
  classical
  obtain ⟨n, s, X, hs, hrank⟩ := h
  refine ⟨n, s, X, hs, ?_⟩
  intro I
  refine ⟨(hrank I).1, (hrank I).2, ?_⟩
  rw [jointSubspace_fullGroupSpace]
  change Module.finrank K
    ((if none ∈ I.biUnion A then Submodule.span K {s} else ⊥) ⊔
      jointSubspace X I : Submodule K (Fin n → K)) =
    formalTable Γ b (I.biUnion A)
  by_cases hsecret : none ∈ I.biUnion A
  · rw [ite_eq_left hsecret, (hrank I).2]
    simp [formalTable, hsecret, physicalPart_biUnion]
  · rw [ite_eq_right hsecret, bot_sup_eq, (hrank I).1]
    simp [formalTable, hsecret, physicalPart_biUnion]

omit [Fintype G] [DecidableEq G] in
/-- Forgetting the extra equations yields D18's representation of the projection. -/
theorem localGroupRealizes_linearRankRealizes
    (A : G → Finset (Option P)) (Γ : AccessStructure P) (b : ℕ)
    (h : LocalGroupRealizes K Γ b A) :
    LinearRankRealizes K (groupProjection (formalTable Γ b) A) := by
  obtain ⟨n, s, X, _hs, hrank⟩ := h
  refine ⟨n, fullGroupSpace A s X, ?_⟩
  intro I
  exact ((hrank I).2.2).symm

end BoundedArity
