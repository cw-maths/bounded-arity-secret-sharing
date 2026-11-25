module

public import BoundedArity.ClauseAccess
public import BoundedArity.CoverageBlocks
public import BoundedArity.SecretRank

/-!
# Assembling the clauses in one linear model

T5 uses independent blocks for nonsingleton clauses, one private coordinate
per participant, and one padding block per unordered pair. A singleton
clause uses its holder's existing private coordinate as its key. The secret
is the sum of all clause keys in these independent coordinate blocks.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators Classical

variable {K E : Type*} [Field K] [Fintype E] [DecidableEq E]

/-- Separate indices for clause blocks, private scalars, and pair padding. -/
abbrev ClauseAssemblyIndex (Cs : Finset (Finset E)) :=
  ↥(nonsingletonClauses Cs) ⊕ (E ⊕ ParticipantPair E)

def assemblyBlockDim (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) : ClauseAssemblyIndex Cs → ℕ
  | Sum.inl C => (models C).dim
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr e) => b - pairMultiplicity Cs e.val

abbrev AssemblyAmbient (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val) (b : ℕ) :=
  (d : ClauseAssemblyIndex Cs) → (Fin (assemblyBlockDim Cs models b d) → K)

/-- Each participant receives precisely its observations in each block. -/
noncomputable def assemblyBlockShare (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) (p : E) (d : ClauseAssemblyIndex Cs) :
    Submodule K (Fin (assemblyBlockDim Cs models b d) → K) :=
  match d with
  | Sum.inl C => (models C).shares p
  | Sum.inr (Sum.inl i) => heldSpace K {i} 1 p
  | Sum.inr (Sum.inr e) => heldSpace K e.val (b - pairMultiplicity Cs e.val) p

noncomputable def assemblyShares (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) (p : E) : Submodule K (AssemblyAmbient Cs models b) :=
  Submodule.pi Set.univ (assemblyBlockShare Cs models b p)

/-- Only clause keys contribute to the secret. A singleton key reuses
the one private scalar already present for its holder. Padding contributes zero. -/
noncomputable def assemblyBlockKey (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) (d : ClauseAssemblyIndex Cs) :
    Fin (assemblyBlockDim Cs models b d) → K :=
  match d with
  | Sum.inl C => (models C).key
  | Sum.inr (Sum.inl p) => if ({p} : Finset E) ∈ Cs then privateKeyVector K else 0
  | Sum.inr (Sum.inr _) => 0

/-- D22: the sum of the independently embedded clause keys. -/
noncomputable def assemblySecret (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) : AssemblyAmbient Cs models b :=
  combinedBlockSecret (assemblyBlockKey Cs models b)

@[simp] theorem assemblySecret_apply (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) (d : ClauseAssemblyIndex Cs) :
    assemblySecret Cs models b d = assemblyBlockKey Cs models b d := by
  simp [assemblySecret]

/-- A coalition obtains the sum-key exactly when it meets every clause.
The converse uses the independent block of a missed clause. -/
theorem assemblySecret_mem_joint_iff (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) (U : Finset E) (hClauses : ∀ C ∈ Cs, C.Nonempty) :
    assemblySecret Cs models b ∈ jointSubspace (assemblyShares Cs models b) U ↔
      HitsAll Cs U := by
  classical
  unfold assemblyShares
  rw [jointSubspace_pi]
  constructor
  · intro h
    apply (hitsAll_iff_nonsingletons_singletons_subtype Cs U hClauses).mpr
    constructor
    · intro C
      have hc := Submodule.mem_pi.mp h (Sum.inl C) (Set.mem_univ _)
      rw [assemblySecret_apply] at hc
      change (models C).key ∈ jointSubspace (models C).shares U at hc
      exact ((models C).key_mem_joint_iff U).mp hc
    · intro p hp
      have hp' := Submodule.mem_pi.mp h (Sum.inr (Sum.inl p)) (Set.mem_univ _)
      rw [assemblySecret_apply] at hp'
      change (if ({p} : Finset E) ∈ Cs then privateKeyVector K else 0) ∈
        jointSubspace (heldSpace K {p} 1) U at hp'
      rw [ite_eq_left hp] at hp'
      exact (privateKeyVector_mem_joint_iff K p U).mp hp'
  · intro h
    obtain ⟨hnon, hsingle⟩ :=
      (hitsAll_iff_nonsingletons_singletons_subtype Cs U hClauses).mp h
    apply Submodule.mem_pi.mpr
    intro d _
    rw [assemblySecret_apply]
    rcases d with C | d
    · change (models C).key ∈ jointSubspace (models C).shares U
      exact ((models C).key_mem_joint_iff U).mpr (hnon C)
    · rcases d with p | e
      · change (if ({p} : Finset E) ∈ Cs then privateKeyVector K else 0) ∈
          jointSubspace (heldSpace K {p} 1) U
        exact (optionalPrivateKey_mem_joint_iff K (({p} : Finset E) ∈ Cs) p U).mpr
          (hsingle p)
      · change (0 : Fin (b - pairMultiplicity Cs e.val) → K) ∈
          jointSubspace (heldSpace K e.val (b - pairMultiplicity Cs e.val)) U
        exact Submodule.zero_mem _

theorem assemblySecret_ne_zero (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) (hCs : Cs.Nonempty) (hClauses : ∀ C ∈ Cs, C.Nonempty) :
    assemblySecret Cs models b ≠ 0 := by
  intro hzero
  apply not_hitsAll_empty Cs hCs
  apply (assemblySecret_mem_joint_iff Cs models b ∅ hClauses).mp
  rw [hzero]
  exact Submodule.zero_mem _

/-- Private scalars, clause profiles, and pair padding give the exact physical table. -/
theorem assembly_physical_rank (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) (U : Finset E)
    (hpair : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b) :
    Module.finrank K (jointSubspace (assemblyShares Cs models b) U) =
      physicalTable b U := by
  classical
  unfold assemblyShares
  rw [jointSubspace_pi, finrank_piSubmodule]
  simp only [Fintype.sum_sum_type]
  change
    (∑ C : nonsingletonClauses Cs,
      Module.finrank K (jointSubspace (models C).shares U)) +
      ((∑ p : E, Module.finrank K (jointSubspace (heldSpace K {p} 1) U)) +
        ∑ e : ParticipantPair E,
          Module.finrank K
            (jointSubspace (heldSpace K e.val (b - pairMultiplicity Cs e.val)) U)) =
      physicalTable b U
  have hclause :
      (∑ C : nonsingletonClauses Cs,
        Module.finrank K (jointSubspace (models C).shares U)) =
      ∑ C : nonsingletonClauses Cs, clausePairCoverage C.val U := by
    apply Finset.sum_congr rfl
    intro C _
    exact (models C).joint_rank U
  have hpad :
      (∑ e : ParticipantPair E,
        Module.finrank K
          (jointSubspace (heldSpace K e.val (b - pairMultiplicity Cs e.val)) U)) =
      ∑ e : ParticipantPair E,
        if (U ∩ e.val).Nonempty then b - pairMultiplicity Cs e.val else 0 := by
    apply Finset.sum_congr rfl
    intro e _
    exact heldSpace_joint_finrank K e.val (b - pairMultiplicity Cs e.val) U
  rw [hclause, sum_private_joint_finrank K U, hpad]
  have hcount := clauseAssembly_pair_rank_sum Cs b U hpair
  unfold physicalTable
  omega

/-- Adding the secret contributes zero for authorised coalitions and one otherwise. -/
theorem assembly_secret_rank (Cs : Finset (Finset E))
    (models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val)
    (b : ℕ) (U : Finset E) (hClauses : ∀ C ∈ Cs, C.Nonempty)
    (hpair : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b) :
    Module.finrank K
      (Submodule.span K {assemblySecret Cs models b} ⊔
        jointSubspace (assemblyShares Cs models b) U :
        Submodule K (AssemblyAmbient Cs models b)) =
      physicalTable b U + clauseUnauthorizedBit Cs U := by
  rw [finrank_secret_sup, assembly_physical_rank Cs models b U hpair]
  unfold clauseUnauthorizedBit
  rw [assemblySecret_mem_joint_iff Cs models b U hClauses]

/-- T5's complete common-model contract. The two rank identities are
simultaneous for all coalitions; the secret has rank one. -/
def ClauseAssemblyRealizes (K : Type*) [Field K]
    (Cs : Finset (Finset E)) (b : ℕ) : Prop :=
  ∃ n : ℕ, ∃ s : Fin n → K, ∃ W : E → Submodule K (Fin n → K),
    Module.finrank K (Submodule.span K {s}) = 1 ∧
      ∀ U : Finset E,
        Module.finrank K (jointSubspace W U) = physicalTable b U ∧
        Module.finrank K
          (Submodule.span K {s} ⊔ jointSubspace W U : Submodule K (Fin n → K)) =
          physicalTable b U + clauseUnauthorizedBit Cs U

/-- T5: assemble the supplied nonsingleton models, reusing private
coordinates for singleton keys and respecting the pair-codegree budget. -/
theorem clauseAssembly_checkpoint (Cs : Finset (Finset E))
    (hCs : Cs.Nonempty) (hClauses : ∀ C ∈ Cs, C.Nonempty)
    (b : ℕ) (_hb : 1 ≤ b)
    (hpair : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b)
    (hmodel : ∀ C ∈ Cs, 2 ≤ C.card → OneClauseRealizes K C) :
    ClauseAssemblyRealizes K Cs b := by
  classical
  let models : ∀ C : nonsingletonClauses Cs, ClauseVectorModel K C.val :=
    fun C => Classical.choice (clauseVectorModel_of_oneClause
      (hmodel C.val ((mem_nonsingletonClauses Cs C.val).mp C.property).1
        ((mem_nonsingletonClauses Cs C.val).mp C.property).2))
  let V := AssemblyAmbient Cs models b
  let s : V := assemblySecret Cs models b
  let W : E → Submodule K V := assemblyShares Cs models b
  let e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    (Module.finBasis K V).equivFun
  have hs : s ≠ 0 := assemblySecret_ne_zero Cs models b hCs hClauses
  refine ⟨Module.finrank K V, e s, fun p => (W p).map e.toLinearMap, ?_, ?_⟩
  · apply finrank_span_singleton
    intro he
    apply hs
    apply e.injective
    simpa only [map_zero] using he
  · intro U
    constructor
    · rw [jointSubspace_finrank_map]
      exact assembly_physical_rank Cs models b U hpair
    · rw [jointSubspace_map, finrank_secret_sup_map]
      exact assembly_secret_rank Cs models b U hClauses hpair

/-- The polynomial ingredient supplies T5 over a sufficiently large finite field. -/
theorem clauseAssembly_finiteField_checkpoint [Fintype K]
    (Cs : Finset (Finset E)) (hCs : Cs.Nonempty)
    (hClauses : ∀ C ∈ Cs, C.Nonempty) (b : ℕ) (hb : 1 ≤ b)
    (hpair : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b)
    (hK : ∀ C ∈ Cs, C.card ≤ Fintype.card K) :
    ClauseAssemblyRealizes K Cs b := by
  apply clauseAssembly_checkpoint Cs hCs hClauses b hb hpair
  intro C hC hcard
  exact oneClause_finiteField_checkpoint C hcard (hK C hC)

/-- Every infinite field supplies the clause ingredient. -/
theorem clauseAssembly_infiniteField_checkpoint [Infinite K]
    (Cs : Finset (Finset E)) (hCs : Cs.Nonempty)
    (hClauses : ∀ C ∈ Cs, C.Nonempty) (b : ℕ) (hb : 1 ≤ b)
    (hpair : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b) :
    ClauseAssemblyRealizes K Cs b := by
  apply clauseAssembly_checkpoint Cs hCs hClauses b hb hpair
  intro C _hC hcard
  exact oneClause_infiniteField_checkpoint C hcard

/-- The simultaneous physical/secret identities realize the original
formal table for the access rule given by the clauses. -/
theorem clauseAssembly_realizes_formalTable (Cs : Finset (Finset E))
    (hCs : Cs.Nonempty) (hClauses : ∀ C ∈ Cs, C.Nonempty) (b : ℕ)
    (h : ClauseAssemblyRealizes K Cs b) :
    LinearRankRealizes K (formalTable (clauseAccessStructure Cs hCs hClauses) b) := by
  classical
  obtain ⟨n, s, W, _hs, hrank⟩ := h
  refine ⟨n, withSecret s W, ?_⟩
  intro X
  change formalTable (clauseAccessStructure Cs hCs hClauses) b X =
    Module.finrank K (jointSubspace (withSecret s W) X)
  rw [jointSubspace_withSecret]
  by_cases hx : none ∈ X
  · rw [ite_eq_left hx, (hrank (physicalPart X)).2]
    simp [formalTable, hx]
  · rw [ite_eq_right hx, bot_sup_eq, (hrank (physicalPart X)).1]
    simp [formalTable, hx]

/-- T5 in the full-table representability form needed by later checkpoints. -/
theorem clauseAssembly_formalTable_checkpoint (Cs : Finset (Finset E))
    (hCs : Cs.Nonempty) (hClauses : ∀ C ∈ Cs, C.Nonempty)
    (b : ℕ) (hb : 1 ≤ b)
    (hpair : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b)
    (hmodel : ∀ C ∈ Cs, 2 ≤ C.card → OneClauseRealizes K C) :
    LinearRankRealizes K (formalTable (clauseAccessStructure Cs hCs hClauses) b) :=
  clauseAssembly_realizes_formalTable Cs hCs hClauses b
    (clauseAssembly_checkpoint Cs hCs hClauses b hb hpair hmodel)

theorem clauseAssembly_finiteField_formalTable [Fintype K]
    (Cs : Finset (Finset E)) (hCs : Cs.Nonempty)
    (hClauses : ∀ C ∈ Cs, C.Nonempty) (b : ℕ) (hb : 1 ≤ b)
    (hpair : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b)
    (hK : ∀ C ∈ Cs, C.card ≤ Fintype.card K) :
    LinearRankRealizes K (formalTable (clauseAccessStructure Cs hCs hClauses) b) :=
  clauseAssembly_realizes_formalTable Cs hCs hClauses b
    (clauseAssembly_finiteField_checkpoint Cs hCs hClauses b hb hpair hK)

theorem clauseAssembly_infiniteField_formalTable [Infinite K]
    (Cs : Finset (Finset E)) (hCs : Cs.Nonempty)
    (hClauses : ∀ C ∈ Cs, C.Nonempty) (b : ℕ) (hb : 1 ≤ b)
    (hpair : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b) :
    LinearRankRealizes K (formalTable (clauseAccessStructure Cs hCs hClauses) b) :=
  clauseAssembly_realizes_formalTable Cs hCs hClauses b
    (clauseAssembly_infiniteField_checkpoint Cs hCs hClauses b hb hpair)

end BoundedArity
