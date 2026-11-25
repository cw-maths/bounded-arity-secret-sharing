module

public import BoundedArity.OneClause
public import BoundedArity.Interpolation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Keys, joint observations, and the one-dimensional secret increment

These are linear-algebra helpers for T5. A clause key is represented by a
nonzero observation row. Independent clause keys are embedded into distinct
coordinate blocks, and their sum is the combined secret row.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators Classical

section ClauseKeys

variable {E : Type*} [DecidableEq E]

/-- A one-clause model with a chosen nonzero row for its rank-one key. -/
structure ClauseVectorModel (K : Type*) [Field K] (C : Finset E) where
  dim : ℕ
  key : Fin dim → K
  key_ne_zero : key ≠ 0
  shares : E → Submodule K (Fin dim → K)
  outside : ∀ p, p ∉ C → shares p = ⊥
  key_mem : ∀ p, p ∈ C → key ∈ shares p
  joint_rank : ∀ U : Finset E,
    Module.finrank K (jointSubspace shares U) = clausePairCoverage C U

/-- Choosing a generator of T4's key subspace preserves its full contract. -/
theorem clauseVectorModel_of_oneClause {K : Type*} [Field K]
    {C : Finset E} (h : OneClauseRealizes K C) :
    Nonempty (ClauseVectorModel K C) := by
  obtain ⟨n, key, W, hdim, hout, hkey, hrank⟩ := h
  have hne : key ≠ ⊥ := by
    intro hzero
    rw [hzero, finrank_bot] at hdim
    omega
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨{
    dim := n
    key := s
    key_ne_zero := hs0
    shares := W
    outside := hout
    key_mem := fun p hp => hkey p hp hs
    joint_rank := hrank
  }⟩

end ClauseKeys

section GenericKey

variable {K E V : Type*} [Field K] [DecidableEq E]
  [AddCommGroup V] [Module K V]

/-- A coalition missing the clause sees zero in that clause's block. -/
theorem jointSubspace_eq_bot_of_miss (W : E → Submodule K V)
    (C U : Finset E) (hout : ∀ p, p ∉ C → W p = ⊥)
    (hmiss : ¬ (U ∩ C).Nonempty) :
    jointSubspace W U = ⊥ := by
  apply le_antisymm
  · apply iSup_le
    intro p
    apply iSup_le
    intro hpU
    have hpC : p ∉ C := by
      intro hpC
      exact hmiss ⟨p, Finset.mem_inter.mpr ⟨hpU, hpC⟩⟩
    rw [hout p hpC]
  · exact bot_le

/-- A nonzero clause key is observed exactly by coalitions meeting the clause. -/
theorem key_mem_joint_iff (W : E → Submodule K V) (C : Finset E)
    (s : V) (hs : s ≠ 0) (hout : ∀ p, p ∉ C → W p = ⊥)
    (hkey : ∀ p, p ∈ C → s ∈ W p) (U : Finset E) :
    s ∈ jointSubspace W U ↔ (U ∩ C).Nonempty := by
  constructor
  · intro hmem
    by_contra hmiss
    rw [jointSubspace_eq_bot_of_miss W C U hout hmiss] at hmem
    exact hs ((Submodule.mem_bot K).mp hmem)
  · rintro ⟨p, hp⟩
    obtain ⟨hpU, hpC⟩ := Finset.mem_inter.mp hp
    exact le_jointSubspace W U hpU (hkey p hpC)

/-- Adjoining a secret row increases dimension by one precisely when it is
not already in the observation space. -/
theorem finrank_secret_sup [FiniteDimensional K V] (s : V)
    (W : Submodule K V) :
    Module.finrank K (Submodule.span K {s} ⊔ W : Submodule K V) =
      Module.finrank K W + (if s ∈ W then 0 else 1) := by
  classical
  by_cases hs : s ∈ W
  · have hle : Submodule.span K {s} ≤ W := by
      apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hs
    rw [sup_eq_right.mpr hle, ite_eq_left hs, add_zero]
  · rw [ite_eq_right hs, sup_comm]
    exact Submodule.finrank_sup_span_singleton hs

end GenericKey

theorem ClauseVectorModel.key_mem_joint_iff {K E : Type*} [Field K]
    [DecidableEq E] {C : Finset E} (M : ClauseVectorModel K C) (U : Finset E) :
    M.key ∈ jointSubspace M.shares U ↔ (U ∩ C).Nonempty :=
  BoundedArity.key_mem_joint_iff M.shares C M.key M.key_ne_zero M.outside M.key_mem U

section CoordinateChanges

variable {K V V' : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

/-- The key and physical observations are transported by the same map. -/
theorem finrank_secret_sup_map (e : V ≃ₗ[K] V') (s : V) (W : Submodule K V) :
    Module.finrank K
      (Submodule.span K {e s} ⊔ W.map e.toLinearMap : Submodule K V') =
      Module.finrank K (Submodule.span K {s} ⊔ W : Submodule K V) := by
  have heq :
      (Submodule.span K {s} ⊔ W).map e.toLinearMap =
        Submodule.span K {e s} ⊔ W.map e.toLinearMap := by
    rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    rfl
  calc
    Module.finrank K
        (Submodule.span K {e s} ⊔ W.map e.toLinearMap : Submodule K V') =
        Module.finrank K ((Submodule.span K {s} ⊔ W).map e.toLinearMap) :=
      congrArg (fun S : Submodule K V' => Module.finrank K S) heq.symm
    _ = Module.finrank K (Submodule.span K {s} ⊔ W : Submodule K V) :=
      e.finrank_map_eq (Submodule.span K {s} ⊔ W)

end CoordinateChanges

section BlockSecret

variable {D : Type*} [Fintype D] [DecidableEq D] {V : D → Type*}
  [∀ d, AddCommMonoid (V d)]

/-- The secret is the sum of its independently embedded block keys. -/
def combinedBlockSecret (key : ∀ d, V d) : ∀ d, V d :=
  ∑ d, Pi.single d (key d)

@[simp] theorem combinedBlockSecret_eq (key : ∀ d, V d) :
    combinedBlockSecret key = key := by
  exact LinearMap.sum_single_apply V key

end BlockSecret

section SecretIndex

variable {K E V : Type*} [Field K] [Fintype E] [DecidableEq E]
  [AddCommGroup V] [Module K V]

/-- Extend physical observation spaces by the secret index `none`. -/
def withSecret (s : V) (W : E → Submodule K V) : Option E → Submodule K V
  | none => Submodule.span K {s}
  | some p => W p

/-- A selected set of physical and secret indices has the expected joint space. -/
theorem jointSubspace_withSecret (s : V) (W : E → Submodule K V)
    (X : Finset (Option E)) :
    jointSubspace (withSecret s W) X =
      (if none ∈ X then Submodule.span K {s} else ⊥) ⊔
        jointSubspace W (physicalPart X) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    cases q with
    | none =>
        simp only [withSecret, ite_eq_left hq]
        exact le_sup_left
    | some p =>
        exact (le_jointSubspace W (physicalPart X) (mem_physicalPart.mpr hq)).trans
          le_sup_right
  · apply sup_le
    · by_cases hnone : none ∈ X
      · rw [ite_eq_left hnone]
        exact le_jointSubspace (withSecret s W) X hnone
      · simp [hnone]
    · apply iSup_le
      intro p
      apply iSup_le
      intro hp
      exact le_jointSubspace (withSecret s W) X (mem_physicalPart.mp hp)

end SecretIndex

end BoundedArity
