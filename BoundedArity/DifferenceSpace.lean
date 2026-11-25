module

public import BoundedArity.LinearRank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Differences of coordinate vectors over an arbitrary field

For a finite support set S, pair differences of coordinate vectors span a
space of dimension |S|-1 when S is nonempty. This is the zero-sum coordinate
space, and the proof is valid in every characteristic.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators

variable (K : Type*) [Field K] {D : Type*} [Fintype D] [DecidableEq D]

/-- One standard coordinate direction in the ambient finite function space. -/
def coordinateUnit (x : D) : D → K := Pi.single x 1

/-- Pair differences supported in the selected finite set. -/
noncomputable def differenceSpace (S : Finset D) : Submodule K (D → K) :=
  Submodule.span K {v | ∃ x ∈ S, ∃ y ∈ S,
    v = coordinateUnit K x - coordinateUnit K y}

omit [Fintype D] in
theorem differenceSpace_generator (S : Finset D) {x y : D}
    (hx : x ∈ S) (hy : y ∈ S) :
    coordinateUnit K x - coordinateUnit K y ∈ differenceSpace K S :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

omit [Fintype D] in
theorem differenceSpace_mono {S T : Finset D} (hST : S ⊆ T) :
    differenceSpace K S ≤ differenceSpace K T := by
  apply Submodule.span_le.mpr
  rintro v ⟨x, hx, y, hy, rfl⟩
  exact differenceSpace_generator K T (hST hx) (hST hy)

omit [Fintype D] in
@[simp] theorem differenceSpace_empty :
    differenceSpace K (∅ : Finset D) = ⊥ := by
  simp [differenceSpace]

/-- Summing all coordinate values is a linear functional. -/
def coordinateSum : (D → K) →ₗ[K] K where
  toFun v := ∑ x, v x
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.mul_sum]

@[simp] theorem coordinateSum_coordinateUnit (x : D) :
    coordinateSum K (coordinateUnit K x) = 1 := by
  simp [coordinateSum, coordinateUnit]

theorem differenceSpace_le_ker_coordinateSum (S : Finset D) :
    differenceSpace K S ≤ LinearMap.ker (coordinateSum K : (D → K) →ₗ[K] K) := by
  apply Submodule.span_le.mpr
  rintro v ⟨x, hx, y, hy, rfl⟩
  change coordinateSum K (coordinateUnit K x - coordinateUnit K y) = 0
  simp

/-- A coordinate direction cannot be a sum of zero-sum pair differences. -/
theorem coordinateUnit_not_mem_differenceSpace (S : Finset D) (x : D) :
    coordinateUnit K x ∉ differenceSpace K S := by
  intro hx
  have h := differenceSpace_le_ker_coordinateSum K S hx
  change coordinateSum K (coordinateUnit K x) = 0 at h
  simp at h

theorem coordinateUnit_mem_spanSubset (S : Finset D) {x : D} (hx : x ∈ S) :
    coordinateUnit K x ∈ Pi.spanSubset K (S : Set D) := by
  apply Submodule.subset_span
  exact ⟨x, hx, by simp [coordinateUnit, Pi.basisFun_apply]⟩

theorem differenceSpace_le_spanSubset (S : Finset D) :
    differenceSpace K S ≤ Pi.spanSubset K (S : Set D) := by
  apply Submodule.span_le.mpr
  rintro v ⟨x, hx, y, hy, rfl⟩
  exact Submodule.sub_mem _
    (coordinateUnit_mem_spanSubset K S hx) (coordinateUnit_mem_spanSubset K S hy)

/-- Adding one anchor coordinate recovers every direction on the support set. -/
theorem differenceSpace_sup_anchor (S : Finset D) {a : D} (ha : a ∈ S) :
    differenceSpace K S ⊔ Submodule.span K {coordinateUnit K a} =
      Pi.spanSubset K (S : Set D) := by
  apply le_antisymm
  · apply sup_le (differenceSpace_le_spanSubset K S)
    apply Submodule.span_le.mpr
    rintro v rfl
    exact coordinateUnit_mem_spanSubset K S ha
  · change Submodule.span K (Pi.basisFun K D '' (S : Set D)) ≤ _
    apply Submodule.span_le.mpr
    rintro v ⟨x, hx, rfl⟩
    have hd : coordinateUnit K x - coordinateUnit K a ∈
        differenceSpace K S ⊔ Submodule.span K {coordinateUnit K a} :=
      Submodule.mem_sup_left (differenceSpace_generator K S hx ha)
    have ha' : coordinateUnit K a ∈
        differenceSpace K S ⊔ Submodule.span K {coordinateUnit K a} :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
    have hsum := Submodule.add_mem _ hd ha'
    simpa [coordinateUnit, Pi.basisFun_apply] using hsum

/-- The pair-difference space has codimension one on every nonempty support. -/
theorem differenceSpace_finrank_add_one (S : Finset D) (hS : S.Nonempty) :
    Module.finrank K (differenceSpace K S) + 1 = S.card := by
  obtain ⟨a, ha⟩ := hS
  have hdim := Submodule.finrank_sup_span_singleton
    (coordinateUnit_not_mem_differenceSpace K S a)
  rw [differenceSpace_sup_anchor K S ha, Pi.dim_spanSubset] at hdim
  simpa using hdim.symm

end BoundedArity
