module

public import BoundedArity.TypeModel
public import BoundedArity.CoverageRestore
public import BoundedArity.GroupModel

/-!
# Local representations of the fixed formal table

T6 restores the physical coverage coordinates after type compression. If the
union of all selected physical groups is unauthorized, ordinary coverage and
a fresh independent secret handle every queried coalition. Both branches
give one common model, including the stronger physical/secret rank equations.
-/

@[expose] public section

namespace BoundedArity

variable {K P G : Type*} [Field K] [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- Restore the coordinates omitted by the type model, independently of its secret. -/
theorem physicalGroupRealizes_of_typeModel (B : G → Finset P)
    (Γ : AccessStructure P) (b : ℕ)
    (hmodel : ClauseAssemblyRealizes K (typeClauses B Γ) b) :
    PhysicalGroupRealizes K B Γ b := by
  classical
  obtain ⟨n, s, W, hs, hrank⟩ := hmodel
  have hs0 : s ≠ 0 := by
    intro hzero
    have hspan : Submodule.span K {s} = ⊥ := Submodule.span_singleton_eq_bot.mpr hzero
    rw [hspan, finrank_bot] at hs
    exact Nat.zero_ne_one hs
  let R := RetainedAmbient K (typeRepresentative B) b
  let Z := retainedShares K (typeRepresentative B) b
  have htype (I : Finset G) :
      jointSubspace (fun j => jointSubspace W (typeGroup B j)) I =
        jointSubspace W (visibleTypeSet B I) := by
    rw [jointSubspace_biUnion, ← visibleTypeSet_eq_biUnion]
  have hretained (I : Finset G) :
      jointSubspace (fun j => jointSubspace Z (B j)) I =
        jointSubspace Z (physicalUnion B I) := jointSubspace_biUnion Z B I
  apply physicalGroupRealizes_of_finiteDimensional B Γ b (s, (0 : R))
    (fun h => hs0 (congrArg Prod.fst h))
    (fun j => (jointSubspace W (typeGroup B j)).prod (jointSubspace Z (B j)))
  intro I
  constructor
  · rw [jointSubspace_prod, htype, hretained, finrank_prodSubmodule,
      (hrank (visibleTypeSet B I)).1, retainedShares_joint_finrank,
      type_coverage_restore]
  · rw [jointSubspace_prod, htype, hretained, finrank_secret_prod,
      (hrank (visibleTypeSet B I)).2, retainedShares_joint_finrank,
      clauseUnauthorizedBit_visibleTypeSet]
    have h := type_coverage_restore B b I
    omega

omit [DecidableEq G] in
/-- If all groups together are unauthorized, ordinary coverage and an independent
secret already have the correct ranks on every queried union. -/
theorem physicalGroupRealizes_of_unauthorized (B : G → Finset P)
    (Γ : AccessStructure P) (b : ℕ)
    (hfull : ¬ Γ.Authorized (physicalUnion B Finset.univ)) :
    PhysicalGroupRealizes K B Γ b := by
  classical
  let f : Empty → P := Empty.elim
  let R := RetainedAmbient K f b
  let Z := retainedShares K f b
  have hretained (I : Finset G) :
      jointSubspace (fun j => jointSubspace Z (B j)) I =
        jointSubspace Z (physicalUnion B I) := jointSubspace_biUnion Z B I
  have hunauthorized (I : Finset G) :
      ¬ Γ.Authorized (physicalUnion B I) := by
    intro hI
    apply hfull
    exact Γ.upward_closed (physicalUnion_mono B (Finset.subset_univ I)) hI
  have hzero : (1, (0 : R)) ≠ (0 : K × R) := by
    intro h
    exact one_ne_zero (congrArg Prod.fst h)
  apply physicalGroupRealizes_of_finiteDimensional B Γ b (1, (0 : R)) hzero
    (fun j => (⊥ : Submodule K K).prod (jointSubspace Z (B j)))
  intro I
  have hbot : jointSubspace (fun _ : G => (⊥ : Submodule K K)) I = ⊥ := by
    apply bot_unique
    exact iSup_le (fun _ => iSup_le (fun _ => bot_le))
  constructor
  · rw [jointSubspace_prod, hbot, hretained, finrank_prodSubmodule,
      finrank_bot, zero_add, retainedShares_joint_finrank, retainedCount_empty]
  · rw [jointSubspace_prod, hbot, hretained, finrank_secret_prod,
      sup_bot_eq, finrank_span_singleton (one_ne_zero : (1 : K) ≠ 0),
      retainedShares_joint_finrank, retainedCount_empty]
    simp [unauthorizedBit, hunauthorized I, Nat.add_comm]

/-- T6's assembly is independent of the choice of one-clause ingredient. -/
theorem physicalGroupRealizes_of_clauseModels (B : G → Finset P)
    (Γ : AccessStructure P) (b : ℕ) (hb : arityConstant (Fintype.card G) ≤ b)
    (hmodel : ∀ C ∈ typeClauses B Γ, 2 ≤ C.card → OneClauseRealizes K C) :
    PhysicalGroupRealizes K B Γ b := by
  classical
  by_cases hfull : Γ.Authorized (physicalUnion B Finset.univ)
  · exact physicalGroupRealizes_of_typeModel B Γ b
      (typeModel_checkpoint B Γ hfull b hb hmodel)
  · exact physicalGroupRealizes_of_unauthorized B Γ b hfull

/-- T6: the complete physical/secret model over a sufficiently large finite field. -/
theorem physicalGroupRealizes_finiteField [Fintype K] (B : G → Finset P)
    (Γ : AccessStructure P) (b : ℕ) (hb : arityConstant (Fintype.card G) ≤ b)
    (hK : 2 ^ Fintype.card G - 1 ≤ Fintype.card K) :
    PhysicalGroupRealizes K B Γ b := by
  apply physicalGroupRealizes_of_clauseModels B Γ b hb
  intro C _hC hcard
  exact oneClause_finiteField_checkpoint C hcard
    ((Finset.card_le_univ C).trans ((occurringType_card_le B).trans hK))

/-- T6: every infinite field supplies the same physical/secret contract. -/
theorem physicalGroupRealizes_infiniteField [Infinite K] (B : G → Finset P)
    (Γ : AccessStructure P) (b : ℕ) (hb : arityConstant (Fintype.card G) ≤ b) :
    PhysicalGroupRealizes K B Γ b := by
  apply physicalGroupRealizes_of_clauseModels B Γ b hb
  intro C _hC hcard
  exact oneClause_infiniteField_checkpoint C hcard

/-- The reviewed large-field local representation theorem, with arbitrary full groups. -/
theorem localRepresentability_finiteField_checkpoint [Fintype K]
    (Γ : AccessStructure P) (b : ℕ) (_hr : 2 ≤ Fintype.card G)
    (hb : arityConstant (Fintype.card G) ≤ b)
    (A : G → Finset (Option P)) (hK : 2 ^ Fintype.card G - 1 ≤ Fintype.card K) :
    LinearRankRealizes K (groupProjection (formalTable Γ b) A) :=
  physicalGroupRealizes_groupProjection A Γ b
    (physicalGroupRealizes_finiteField (fun j => physicalPart (A j)) Γ b hb hK)

theorem localRepresentability_infiniteField_checkpoint [Infinite K]
    (Γ : AccessStructure P) (b : ℕ) (_hr : 2 ≤ Fintype.card G)
    (hb : arityConstant (Fintype.card G) ≤ b) (A : G → Finset (Option P)) :
    LinearRankRealizes K (groupProjection (formalTable Γ b) A) :=
  physicalGroupRealizes_groupProjection A Γ b
    (physicalGroupRealizes_infiniteField (fun j => physicalPart (A j)) Γ b hb)

end BoundedArity
