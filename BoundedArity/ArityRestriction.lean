module

public import BoundedArity.LocalEntropy

/-!
# Local models at every smaller arity

Pad a k-tuple of full groups with empty groups to obtain an r-tuple. A
single model for that padded grouping restricts to a single model for all
coalitions of the original labels. This includes k = 0 and k = 1 and keeps
the formal table's coefficient fixed at arityConstant r.
-/

@[expose] public section

namespace BoundedArity

section Reindex

variable {K E D V : Type*} [Field K] [DecidableEq E]
  [AddCommGroup V] [Module K V]

/-- Reindexing observations commutes with taking their joint subspace. -/
theorem jointSubspace_reindex (W : E → Submodule K V) (f : D → E)
    (I : Finset D) :
    jointSubspace (fun j => W (f j)) I = jointSubspace W (I.image f) := by
  simp only [jointSubspace, Finset.iSup_finset_image]

end Reindex

/-- Restrict or duplicate labels within one common linear representation. -/
theorem linearRankRealizes_reindex {K E D : Type*} [Field K] [DecidableEq E]
    {g : Finset E → ℕ} (hg : LinearRankRealizes K g) (f : D → E) :
    LinearRankRealizes K (fun I : Finset D => g (I.image f)) := by
  obtain ⟨n, W, hW⟩ := hg
  refine ⟨n, fun j => W (f j), ?_⟩
  intro I
  change g (I.image f) = Module.finrank K (jointSubspace (fun j => W (f j)) I)
  rw [jointSubspace_reindex]
  exact hW (I.image f)

section Padding

variable {P : Type*} {k r : ℕ}

/-- Add empty groups after the original k labels. -/
def padGroups (A : Fin k → Finset (Option P)) : Fin r → Finset (Option P) :=
  fun j => if h : j.val < k then A ⟨j.val, h⟩ else ∅

@[simp] theorem padGroups_castLE (hk : k ≤ r) (A : Fin k → Finset (Option P))
    (j : Fin k) : padGroups A (Fin.castLE hk j) = A j := by
  simp [padGroups, j.isLt]

variable [DecidableEq P]

/-- The union indexed by an original coalition is unchanged by padding. -/
theorem padGroups_union (hk : k ≤ r) (A : Fin k → Finset (Option P))
    (I : Finset (Fin k)) :
    (I.image (Fin.castLE hk)).biUnion (padGroups A) = I.biUnion A := by
  simp only [Finset.image_biUnion, padGroups_castLE]

/-- Every queried table entry agrees with the corresponding padded entry. -/
theorem groupProjection_padGroups {Value : Type*}
    (F : Finset (Option P) → Value) (hk : k ≤ r)
    (A : Fin k → Finset (Option P)) (I : Finset (Fin k)) :
    groupProjection F (padGroups A) (I.image (Fin.castLE hk)) =
      groupProjection F A I := by
  simp only [groupProjection, padGroups_union]

end Padding

section Checkpoints

variable {K P : Type*} [Field K] [Fintype P] [DecidableEq P]

/-- At most r groups have an exact common model over every prescribed field,
including the zero-group and one-group cases. -/
theorem localRepresentability_le_arity_checkpoint (Γ : AccessStructure P)
    (r : ℕ) (hr : 2 ≤ r) (k : ℕ) (hk : k ≤ r)
    (A : Fin k → Finset (Option P)) :
    LinearRankRealizes K
      (groupProjection (formalTable Γ (arityConstant r)) A) := by
  have hpad := localRepresentability_arity_checkpoint (K := K) Γ r hr
    (padGroups (r := r) A)
  have hres := linearRankRealizes_reindex hpad (Fin.castLE hk)
  simpa only [groupProjection_padGroups] using hres

/-- At most r groups have one finite entropy witness in bits, with the
coefficient still fixed at arityConstant r. -/
theorem localEntropy_le_arity_checkpoint (Γ : AccessStructure P)
    (r : ℕ) (hr : 2 ≤ r) (k : ℕ) (hk : k ≤ r)
    (A : Fin k → Finset (Option P)) :
    IsFiniteEntropyTable.{0,0}
      (groupProjection (fun S => (formalTable Γ (arityConstant r) S : ℝ)) A) := by
  exact binary_rank_entropy_checkpoint
    (groupProjection (formalTable Γ (arityConstant r)) A)
    (localRepresentability_le_arity_checkpoint (K := ZMod 2) Γ r hr k hk A)

end Checkpoints

end BoundedArity
