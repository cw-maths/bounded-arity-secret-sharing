module

public import BoundedArity.TypeInterface
public import BoundedArity.PairCodegree
public import BoundedArity.Checkpoint3
public import BoundedArity.ClauseAssembly

/-!
# The clause model on occurring membership types

The interpolation clauses originally consist of finite sets of group-label
sets. Restricting them to `OccurringType B` changes their ambient type but
not their members. We transfer the proved interpolation and pair-codegree
bounds, then invoke T5 to obtain one common type model.
-/

@[expose] public section

namespace BoundedArity

open scoped Classical

variable {P G : Type*} [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- Regard a clause as a finite set of participants in the type model. -/
def liftTypeClause (B : G → Finset P) (D : Finset (Finset G)) :
    Finset (OccurringType B) :=
  D.subtype (fun t => t ∈ occurringTypes B)

@[simp] theorem mem_liftTypeClause (B : G → Finset P)
    (D : Finset (Finset G)) (t : OccurringType B) :
    t ∈ liftTypeClause B D ↔ t.val ∈ D := by
  simp [liftTypeClause]

/-- Distinct interpolation clauses, on the type model's ground set. -/
noncomputable def typeClauses (B : G → Finset P) (Γ : AccessStructure P) :
    Finset (Finset (OccurringType B)) :=
  (clauses B Γ).image (liftTypeClause B)

theorem mem_typeClauses (B : G → Finset P) (Γ : AccessStructure P)
    (C : Finset (OccurringType B)) :
    C ∈ typeClauses B Γ ↔ ∃ D ∈ clauses B Γ, liftTypeClause B D = C := by
  simp [typeClauses]

theorem typeClauses_nonempty (B : G → Finset P) (Γ : AccessStructure P) :
    (typeClauses B Γ).Nonempty := by
  obtain ⟨D, hD⟩ := clauses_nonempty B Γ
  exact ⟨liftTypeClause B D, Finset.mem_image.mpr ⟨D, hD, rfl⟩⟩

theorem typeClause_nonempty (B : G → Finset P) (Γ : AccessStructure P)
    (hfull : Γ.Authorized (physicalUnion B Finset.univ))
    (C : Finset (OccurringType B)) (hC : C ∈ typeClauses B Γ) : C.Nonempty := by
  obtain ⟨D, hD, rfl⟩ := (mem_typeClauses B Γ C).mp hC
  obtain ⟨I, hI, rfl⟩ := (mem_clauses B Γ).mp hD
  obtain ⟨t, ht⟩ := clause_nonempty B Γ hfull hI
  have htT : t ∈ occurringTypes B := (Finset.mem_sdiff.mp ht).1
  exact ⟨⟨t, htT⟩, (mem_liftTypeClause B (clause B I) ⟨t, htT⟩).mpr ht⟩

/-- The lifted access rule agrees with the original rule on all group unions. -/
theorem hitsAll_typeClauses_visible_iff (B : G → Finset P)
    (Γ : AccessStructure P) (I : Finset G) :
    HitsAll (typeClauses B Γ) (visibleTypeSet B I) ↔
      Γ.Authorized (physicalUnion B I) := by
  constructor
  · intro h
    apply (interpolation B Γ I).mp
    intro D hD
    have hC : liftTypeClause B D ∈ typeClauses B Γ :=
      Finset.mem_image.mpr ⟨D, hD, rfl⟩
    obtain ⟨t, ht⟩ := h (liftTypeClause B D) hC
    have ht' := Finset.mem_inter.mp ht
    exact ⟨t.val, Finset.mem_inter.mpr
      ⟨(mem_visibleTypeSet_iff_val B I t).mp ht'.1,
        (mem_liftTypeClause B D t).mp ht'.2⟩⟩
  · intro h C hC
    obtain ⟨D, hD, rfl⟩ := (mem_typeClauses B Γ C).mp hC
    obtain ⟨t, ht⟩ := (interpolation B Γ I).mpr h D hD
    have ht' := Finset.mem_inter.mp ht
    have htT := visibleTypes_subset B I ht'.1
    refine ⟨⟨t, htT⟩, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact (mem_visibleTypeSet_iff_val B I ⟨t, htT⟩).mpr ht'.1
    · exact (mem_liftTypeClause B D ⟨t, htT⟩).mpr ht'.2

/-- Reinterpreting clauses on the subtype cannot increase a pair codegree. -/
theorem type_clauses_pair_count_le (B : G → Finset P)
    (Γ : AccessStructure P) (t u : OccurringType B) (hne : t ≠ u) :
    clausePairCount (typeClauses B Γ) t u ≤ arityConstant (Fintype.card G) := by
  classical
  have hsub :
      ((typeClauses B Γ).filter (fun C => t ∈ C ∧ u ∈ C)) ⊆
        (clausesContainingPair B Γ t.val u.val).image (liftTypeClause B) := by
    intro C hC
    obtain ⟨hC, ht, hu⟩ := Finset.mem_filter.mp hC
    obtain ⟨D, hD, rfl⟩ := (mem_typeClauses B Γ C).mp hC
    apply Finset.mem_image.mpr
    refine ⟨D, Finset.mem_filter.mpr ⟨hD, ?_, ?_⟩, rfl⟩
    · exact (mem_liftTypeClause B D t).mp ht
    · exact (mem_liftTypeClause B D u).mp hu
  have hv : t.val ≠ u.val := fun h => hne (Subtype.ext h)
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (pair_codegree_le B Γ t.property u.property hv))

/-- The interpolation indicator becomes the original unauthorized indicator. -/
theorem clauseUnauthorizedBit_visibleTypeSet (B : G → Finset P)
    (Γ : AccessStructure P) (I : Finset G) :
    clauseUnauthorizedBit (typeClauses B Γ) (visibleTypeSet B I) =
      unauthorizedBit Γ (physicalUnion B I) := by
  unfold clauseUnauthorizedBit unauthorizedBit
  rw [hitsAll_typeClauses_visible_iff]

variable {K : Type*} [Field K]

/-- The type-model construction needs only the stated one-clause ingredient.
This interface also accepts a future exact every-field ingredient. -/
theorem typeModel_checkpoint
    (B : G → Finset P) (Γ : AccessStructure P)
    (hfull : Γ.Authorized (physicalUnion B Finset.univ))
    (b : ℕ) (hb : arityConstant (Fintype.card G) ≤ b)
    (hmodel : ∀ C ∈ typeClauses B Γ, 2 ≤ C.card → OneClauseRealizes K C) :
    ClauseAssemblyRealizes K (typeClauses B Γ) b := by
  apply clauseAssembly_checkpoint (typeClauses B Γ)
    (typeClauses_nonempty B Γ) (typeClause_nonempty B Γ hfull) b
    ((one_le_arityConstant (Fintype.card G)).trans hb)
  · intro t u hne
    exact (type_clauses_pair_count_le B Γ t u hne).trans hb
  · exact hmodel

/-- The sufficiently large finite-field type model used by T6. -/
theorem typeModel_finiteField [Fintype K]
    (B : G → Finset P) (Γ : AccessStructure P)
    (hfull : Γ.Authorized (physicalUnion B Finset.univ))
    (b : ℕ) (hb : arityConstant (Fintype.card G) ≤ b)
    (hK : 2 ^ Fintype.card G - 1 ≤ Fintype.card K) :
    ClauseAssemblyRealizes K (typeClauses B Γ) b := by
  apply typeModel_checkpoint B Γ hfull b hb
  intro C _hC hcard
  exact oneClause_finiteField_checkpoint C hcard
    ((Finset.card_le_univ C).trans ((occurringType_card_le B).trans hK))

/-- The same construction works over every infinite field. -/
theorem typeModel_infiniteField [Infinite K]
    (B : G → Finset P) (Γ : AccessStructure P)
    (hfull : Γ.Authorized (physicalUnion B Finset.univ))
    (b : ℕ) (hb : arityConstant (Fintype.card G) ≤ b) :
    ClauseAssemblyRealizes K (typeClauses B Γ) b := by
  apply typeModel_checkpoint B Γ hfull b hb
  intro C _hC hcard
  exact oneClause_infiniteField_checkpoint C hcard

end BoundedArity
