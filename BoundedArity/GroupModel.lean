module

public import BoundedArity.ClauseAssembly

/-!
# Grouping observations and preserving the secret

The full group projection is the reviewed E27 union operation. The stronger
physical-group contract records a single secret and a single family of group
subspaces, chosen before every coalition. These helpers assemble independent
coordinate blocks and include the same secret in the requested groups.
-/

@[expose] public section

namespace BoundedArity

section Grouping

variable {K E G V : Type*} [Field K] [DecidableEq E]
  [AddCommGroup V] [Module K V]

/-- Grouped observations reuse the original subspaces on overlaps. -/
theorem jointSubspace_biUnion (W : E → Submodule K V)
    (A : G → Finset E) (I : Finset G) :
    jointSubspace (fun j => jointSubspace W (A j)) I =
      jointSubspace W (I.biUnion A) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro hj
    apply iSup_le
    intro p
    apply iSup_le
    intro hp
    exact le_jointSubspace W _ (Finset.mem_biUnion.mpr ⟨j, hj, hp⟩)
  · apply iSup_le
    intro p
    apply iSup_le
    intro hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (le_jointSubspace W (A j) hpj).trans
      (le_jointSubspace (fun j => jointSubspace W (A j)) I hj)

end Grouping

section IndependentBlocks

variable {K E V R : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup R] [Module K R]

theorem jointSubspace_prod (W : E → Submodule K V)
    (Z : E → Submodule K R) (I : Finset E) :
    jointSubspace (fun i => (W i).prod (Z i)) I =
      (jointSubspace W I).prod (jointSubspace Z I) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      simp only [jointSubspace, Finset.iSup_insert] at *
      rw [ih, Submodule.prod_sup_prod]

theorem finrank_prodSubmodule [FiniteDimensional K V] [FiniteDimensional K R]
    (W : Submodule K V) (Z : Submodule K R) :
    Module.finrank K (W.prod Z) = Module.finrank K W + Module.finrank K Z := by
  calc
    Module.finrank K (W.prod Z) = Module.finrank K (W × Z) :=
      (Submodule.prodEquiv W Z).finrank_eq
    _ = Module.finrank K W + Module.finrank K Z := Module.finrank_prod

/-- Independent padding leaves the secret's rank increment unchanged. -/
theorem finrank_secret_prod [FiniteDimensional K V] [FiniteDimensional K R]
    (s : V) (W : Submodule K V) (Z : Submodule K R) :
    Module.finrank K
      (Submodule.span K {(s, (0 : R))} ⊔ W.prod Z : Submodule K (V × R)) =
      Module.finrank K (Submodule.span K {s} ⊔ W : Submodule K V) +
        Module.finrank K Z := by
  have hmem : (s, (0 : R)) ∈ W.prod Z ↔ s ∈ W :=
    ⟨fun h => h.1, fun h => ⟨h, Z.zero_mem⟩⟩
  rw [finrank_secret_sup, finrank_prodSubmodule, finrank_secret_sup]
  rw [hmem]
  omega

end IndependentBlocks

section FullGroups

variable {P G : Type*} [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- E27: project a table by unions of arbitrary full groups. -/
def groupProjection {Value : Type*} (F : Finset (Option P) → Value)
    (A : G → Finset (Option P)) (I : Finset G) : Value :=
  F (I.biUnion A)

omit [Fintype G] [DecidableEq G] in
theorem physicalPart_biUnion (A : G → Finset (Option P)) (I : Finset G) :
    physicalPart (I.biUnion A) = physicalUnion (fun j => physicalPart (A j)) I := by
  ext p
  simp [physicalUnion]

/-- T6's stronger contract, including the secret even if no group asks for it. -/
def PhysicalGroupRealizes (K : Type*) [Field K] (B : G → Finset P)
    (Γ : AccessStructure P) (b : ℕ) : Prop :=
  ∃ n : ℕ, ∃ s : Fin n → K, ∃ W : G → Submodule K (Fin n → K),
    Module.finrank K (Submodule.span K {s}) = 1 ∧
      ∀ I : Finset G,
        Module.finrank K (jointSubspace W I) = physicalTable b (physicalUnion B I) ∧
        Module.finrank K
          (Submodule.span K {s} ⊔ jointSubspace W I : Submodule K (Fin n → K)) =
          physicalTable b (physicalUnion B I) + unauthorizedBit Γ (physicalUnion B I)

omit [Fintype G] [DecidableEq G] in
theorem physicalGroupRealizes_of_finiteDimensional
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : G → Finset P) (Γ : AccessStructure P) (b : ℕ)
    (s : V) (hs : s ≠ 0) (W : G → Submodule K V)
    (hrank : ∀ I : Finset G,
      Module.finrank K (jointSubspace W I) = physicalTable b (physicalUnion B I) ∧
      Module.finrank K (Submodule.span K {s} ⊔ jointSubspace W I : Submodule K V) =
        physicalTable b (physicalUnion B I) + unauthorizedBit Γ (physicalUnion B I)) :
    PhysicalGroupRealizes K B Γ b := by
  classical
  let e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, e s, fun j => (W j).map e.toLinearMap, ?_, ?_⟩
  · apply finrank_span_singleton
    intro he
    apply hs
    apply e.injective
    simpa only [map_zero] using he
  · intro I
    constructor
    · rw [jointSubspace_finrank_map]
      exact (hrank I).1
    · rw [jointSubspace_map, finrank_secret_sup_map]
      exact (hrank I).2

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Include the same secret observation exactly in the groups that contain it. -/
noncomputable def fullGroupSpace (A : G → Finset (Option P))
    (s : V) (W : G → Submodule K V) (j : G) : Submodule K V := by
  classical
  exact (if none ∈ A j then Submodule.span K {s} else ⊥) ⊔ W j

omit [Fintype P] [Fintype G] [DecidableEq G] in
theorem jointSubspace_fullGroupSpace (A : G → Finset (Option P))
    (s : V) (W : G → Submodule K V) (I : Finset G) :
    jointSubspace (fullGroupSpace A s W) I =
      (if none ∈ I.biUnion A then Submodule.span K {s} else ⊥) ⊔
        jointSubspace W I := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro hj
    apply sup_le
    · by_cases hsecret : none ∈ A j
      · have hsome : none ∈ I.biUnion A := Finset.mem_biUnion.mpr ⟨j, hj, hsecret⟩
        simp only [ite_eq_left hsecret, ite_eq_left hsome]
        exact le_sup_left
      · simp only [ite_eq_right hsecret]
        exact bot_le
    · exact (le_jointSubspace W I hj).trans le_sup_right
  · apply sup_le
    · by_cases hsecret : none ∈ I.biUnion A
      · rw [ite_eq_left hsecret]
        obtain ⟨j, hj, hsj⟩ := Finset.mem_biUnion.mp hsecret
        have hle : Submodule.span K {s} ≤ fullGroupSpace A s W j := by
          simp only [fullGroupSpace, ite_eq_left hsj]
          exact le_sup_left
        exact hle.trans (le_jointSubspace (fullGroupSpace A s W) I hj)
      · simp only [ite_eq_right hsecret]
        exact bot_le
    · apply iSup_le
      intro j
      apply iSup_le
      intro hj
      exact (le_sup_right : W j ≤ fullGroupSpace A s W j).trans
        (le_jointSubspace (fullGroupSpace A s W) I hj)

omit [Fintype G] [DecidableEq G] in
/-- The stronger physical/secret contract gives the original full-group table. -/
theorem physicalGroupRealizes_groupProjection (A : G → Finset (Option P))
    (Γ : AccessStructure P) (b : ℕ)
    (h : PhysicalGroupRealizes K (fun j => physicalPart (A j)) Γ b) :
    LinearRankRealizes K (groupProjection (formalTable Γ b) A) := by
  classical
  obtain ⟨n, s, W, _hs, hrank⟩ := h
  refine ⟨n, fullGroupSpace A s W, ?_⟩
  intro I
  change formalTable Γ b (I.biUnion A) =
    Module.finrank K (jointSubspace (fullGroupSpace A s W) I)
  rw [jointSubspace_fullGroupSpace]
  by_cases hsecret : none ∈ I.biUnion A
  · rw [ite_eq_left hsecret, (hrank I).2]
    simp [formalTable, hsecret, physicalPart_biUnion]
  · rw [ite_eq_right hsecret, bot_sup_eq, (hrank I).1]
    simp [formalTable, hsecret, physicalPart_biUnion]

end FullGroups

end BoundedArity
