module

public import BoundedArity.LinearRank
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness

/-!
# One common linear observation family for a rank representation

An input is one linear functional on the ambient space. Each observed label
records its restriction to that label's subspace. Jointly observing labels I
has kernel equal to the annihilator of their sum, and hence image dimension
equal to the prescribed joint rank. Over a finite field every observation
alphabet and the common input space are finite.
-/

@[expose] public section

namespace BoundedArity

variable {K G V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- All observations are restrictions of the same input functional. -/
def observationMap (W : G → Submodule K V) :
    Module.Dual K V →ₗ[K] ((j : G) → Module.Dual K (W j)) :=
  LinearMap.pi (fun j => (W j).dualRestrict)

/-- The joint tuple selected by I, in its actual dependent product alphabet. -/
def observationJointMap (W : G → Submodule K V) (I : Finset G) :
    Module.Dual K V →ₗ[K] ((j : I) → Module.Dual K (W j.val)) :=
  LinearMap.pi (fun j => (W j.val).dualRestrict)

@[simp] theorem observationMap_apply (W : G → Submodule K V)
    (φ : Module.Dual K V) (j : G) :
    observationMap W φ j = (W j).dualRestrict φ := rfl

@[simp] theorem observationJointMap_apply (W : G → Submodule K V)
    (I : Finset G) (φ : Module.Dual K V) (j : I) :
    observationJointMap W I φ j = observationMap W φ j.val := rfl

/-- A joint observation vanishes exactly on the annihilator of the joint space. -/
theorem observationJointMap_ker (W : G → Submodule K V) (I : Finset G) :
    LinearMap.ker (observationJointMap W I) =
      (jointSubspace W I).dualAnnihilator := by
  simp only [observationJointMap, LinearMap.ker_pi, jointSubspace,
    Submodule.dualAnnihilator_iSup_eq, Submodule.dualRestrict_ker_eq_dualAnnihilator]
  exact iInf_subtype

/-- Rank-nullity turns the annihilator identity into the desired joint rank. -/
theorem observationJointMap_finrank [FiniteDimensional K V]
    (W : G → Submodule K V) (I : Finset G) :
    Module.finrank K (LinearMap.range (observationJointMap W I)) =
      Module.finrank K (jointSubspace W I) := by
  have h := (observationJointMap W I).finrank_range_add_finrank_ker
  rw [observationJointMap_ker, Subspace.dual_finrank_eq] at h
  have h' := Subspace.finrank_add_finrank_dualAnnihilator_eq (jointSubspace W I)
  omega

/-- The image has exactly q to the joint-rank many possible observations. -/
theorem observationJointMap_natCard_range [FiniteDimensional K V]
    (W : G → Submodule K V) (I : Finset G) :
    Nat.card (LinearMap.range (observationJointMap W I)) =
      Nat.card K ^ Module.finrank K (jointSubspace W I) := by
  rw [Module.natCard_eq_pow_finrank (K := K), observationJointMap_finrank]

/-- A chosen finite basis supplies an actual finite alphabet over a finite field. -/
@[instance_reducible]
noncomputable def finiteVectorSpaceFintype (K V : Type*) [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] : Fintype V :=
  Fintype.ofEquiv _ (Module.finBasis K V).equivFun.toEquiv.symm

end BoundedArity
