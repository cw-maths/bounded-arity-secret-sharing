module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

/-!
# Finite-dimensional joint ranks

This file implements the reviewed interface D18 and the product-space facts
used by the one-clause construction. All coordinates of one representation
belong to a single finite-dimensional space.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators

section JointSpace

variable {K E V V' : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']

/-- The subspace jointly observed by the labels in `I`. -/
noncomputable def jointSubspace (W : E → Submodule K V) (I : Finset E) :
    Submodule K V :=
  ⨆ i, ⨆ (_ : i ∈ I), W i

theorem le_jointSubspace (W : E → Submodule K V) (I : Finset E)
    {i : E} (hi : i ∈ I) : W i ≤ jointSubspace W I := by
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

@[simp] theorem jointSubspace_empty (W : E → Submodule K V) :
    jointSubspace W ∅ = ⊥ := by
  simp [jointSubspace]

/-- Linear coordinate changes commute with the joint-observation subspace. -/
theorem jointSubspace_map (f : V →ₗ[K] V') (W : E → Submodule K V)
    (I : Finset E) :
    jointSubspace (fun i => (W i).map f) I =
      (jointSubspace W I).map f := by
  simp only [jointSubspace, Submodule.map_iSup]

theorem jointSubspace_finrank_map (e : V ≃ₗ[K] V')
    (W : E → Submodule K V) (I : Finset E) :
    Module.finrank K (jointSubspace (fun i => (W i).map e.toLinearMap) I) =
      Module.finrank K (jointSubspace W I) := by
  rw [jointSubspace_map]
  exact e.finrank_map_eq (jointSubspace W I)

/-- Jointly observing one row per label gives the span of the selected rows. -/
theorem jointSubspace_span_singleton (v : E → V) (I : Finset E) :
    jointSubspace (fun i => Submodule.span K {v i}) I =
      Submodule.span K (Set.range (fun i : I => v i)) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact le_jointSubspace (fun j => Submodule.span K {v j}) I i.property
      (Submodule.subset_span (Set.mem_singleton (v i)))

end JointSpace

/-- D18: one finite-dimensional representation realizes all coalition ranks. -/
def LinearRankRealizes (K : Type*) [Field K] {E : Type*}
    (g : Finset E → ℕ) : Prop :=
  ∃ n : ℕ, ∃ W : E → Submodule K (Fin n → K),
    ∀ I : Finset E,
      g I = Module.finrank K
        ((⨆ i, ⨆ (_ : i ∈ I), W i) : Submodule K (Fin n → K))

/-- A finite-dimensional ambient space may be given finite coordinates once,
simultaneously for every label and every coalition. -/
theorem linearRankRealizes_of_finiteDimensional
    {K E V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : E → Submodule K V)
    (g : Finset E → ℕ)
    (hg : ∀ I, g I = Module.finrank K (jointSubspace W I)) :
    LinearRankRealizes K g := by
  classical
  let e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, fun i => (W i).map e.toLinearMap, ?_⟩
  intro I
  change g I =
    Module.finrank K (jointSubspace (fun i => (W i).map e.toLinearMap) I)
  rw [jointSubspace_finrank_map]
  exact hg I

section ProductSpace

variable {K D : Type*} [Field K] {V : D → Type*}
  [∀ d, AddCommGroup (V d)] [∀ d, Module K (V d)]

/-- The product subspace is linearly equivalent to the product of its factors. -/
def piSubmoduleEquiv (W : ∀ d, Submodule K (V d)) :
    Submodule.pi Set.univ W ≃ₗ[K] (∀ d, W d) where
  toFun x d := ⟨x.val d, Submodule.mem_pi.mp x.property d (Set.mem_univ d)⟩
  invFun x := ⟨fun d => (x d).val,
    Submodule.mem_pi.mpr (fun d _ => (x d).property)⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    funext d
    apply Subtype.ext
    rfl
  map_add' x y := by
    funext d
    apply Subtype.ext
    rfl
  map_smul' a x := by
    funext d
    apply Subtype.ext
    rfl

/-- Independent coordinate blocks have additive dimensions. -/
theorem finrank_piSubmodule [Fintype D] [∀ d, FiniteDimensional K (V d)]
    (W : ∀ d, Submodule K (V d)) :
    Module.finrank K (Submodule.pi Set.univ W) =
      ∑ d, Module.finrank K (W d) := by
  calc
    Module.finrank K (Submodule.pi Set.univ W) =
        Module.finrank K (∀ d, W d) := (piSubmoduleEquiv W).finrank_eq
    _ = ∑ d, Module.finrank K (W d) := Module.finrank_pi_fintype K

/-- For finitely many coordinate blocks, their direct-product construction
commutes with arbitrary joins of participant subspaces. -/
theorem iSup_piSubmodule [Finite D] {J : Sort*}
    (W : J → ∀ d, Submodule K (V d)) :
    (⨆ j, Submodule.pi Set.univ (W j)) =
      Submodule.pi Set.univ (fun d => ⨆ j, W j d) := by
  classical
  calc
    (⨆ j, Submodule.pi Set.univ (W j)) =
        ⨆ j, ⨆ d, (W j d).map (LinearMap.single K V d) :=
      iSup_congr (fun j => (Submodule.iSup_map_single (p := W j)).symm)
    _ = ⨆ d, ⨆ j, (W j d).map (LinearMap.single K V d) := iSup_comm
    _ = ⨆ d, (⨆ j, W j d).map (LinearMap.single K V d) :=
      iSup_congr (fun d =>
        (Submodule.map_iSup (LinearMap.single K V d) (fun j => W j d)).symm)
    _ = Submodule.pi Set.univ (fun d => ⨆ j, W j d) :=
      Submodule.iSup_map_single

/-- A coalition's joint space in independent blocks is the product of its
joint spaces in the individual blocks, including for the empty coalition. -/
theorem jointSubspace_pi [Finite D] {E : Type*}
    (W : E → ∀ d, Submodule K (V d)) (I : Finset E) :
    jointSubspace (fun i => Submodule.pi Set.univ (W i)) I =
      Submodule.pi Set.univ (fun d => jointSubspace (fun i => W i d) I) := by
  unfold jointSubspace
  calc
    (⨆ i, ⨆ (_ : i ∈ I), Submodule.pi Set.univ (W i)) =
        ⨆ i, Submodule.pi Set.univ (fun d => ⨆ (_ : i ∈ I), W i d) :=
      iSup_congr (fun i => iSup_piSubmodule (fun (_ : i ∈ I) => W i))
    _ = Submodule.pi Set.univ (fun d => ⨆ i, ⨆ (_ : i ∈ I), W i d) :=
      iSup_piSubmodule (fun i d => ⨆ (_ : i ∈ I), W i d)

end ProductSpace

end BoundedArity
