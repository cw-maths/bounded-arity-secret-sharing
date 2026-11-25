module

public import BoundedArity.LinearObservation
public import BoundedArity.UniformEntropy
public import BoundedArity.InformationInequalities
public import Mathlib.Data.ZMod.Basic

/-!
# T7: one finite joint law realizes the scaled linear rank table

Use one uniformly random linear functional on the ambient representation
space. Label j observes its restriction to W_j. Every joint observation is a
linear image of that same input, with rank equal to the dimension of the sum
of the selected subspaces. Uniform fibres give the entropy in bits. The
positive common factor cancels in every homogeneous information inequality.
-/

@[expose] public section

universe u v

namespace BoundedArity

variable {G : Type u} [Fintype G]

/-- T7: a finite-field rank table has one finite-valued entropy witness,
with the same factor log₂|K| at every coalition. -/
theorem rank_entropy_checkpoint (K : Type v) [Field K] [Fintype K]
    (g : Finset G → ℕ) (hg : LinearRankRealizes K g) :
    IsFiniteEntropyTable.{u,v}
      (fun I => (g I : ℝ) * (Real.log (Fintype.card K) / Real.log 2)) := by
  classical
  obtain ⟨n, W, hrank⟩ := hg
  let V := Fin n → K
  let D := Module.Dual K V
  let A : G → Type v := fun j => Module.Dual K (W j)
  let : Fintype D := finiteVectorSpaceFintype K D
  let : ∀ j, Fintype (A j) := fun j => finiteVectorSpaceFintype K (A j)
  let p : PMF (∀ j, A j) := (uniformPMF D).map (observationMap W)
  let law : DiscreteJointLaw.{u,v} G := DiscreteJointLaw.ofPMF A p
  have halpha : ∀ j, Finite (law.Alphabet j) := by
    intro j
    change Finite (A j)
    infer_instance
  let : ∀ j, Finite (law.Alphabet j) := halpha
  refine ⟨law, halpha, law.finiteJointEntropy_of_finite, ?_⟩
  intro I
  have hmarginal : law.marginal I = (uniformPMF D).map (observationJointMap W I) := by
    change ((uniformPMF D).map (observationMap W)).map
      (fun (x : ∀ j, A j) (j : I) => x j.val) = _
    rw [PMF.map_comp]
    rfl
  change (g I : ℝ) * (Real.log (Fintype.card K) / Real.log 2) =
    pmfEntropyReal (law.marginal I)
  rw [hmarginal]
  change (g I : ℝ) * (Real.log (Fintype.card K) / Real.log 2) =
    @pmfEntropyReal ((j : I) → Module.Dual K (W j.val))
      ((uniformPMF D).map (observationJointMap W I))
  rw [pmfEntropyReal_map_uniform_linearMap, observationJointMap_finrank]
  rw [hrank I]
  rfl

/-- The finite witness belongs to the full approved countable-alphabet domain. -/
theorem rank_entropy_discrete_checkpoint (K : Type v) [Field K] [Fintype K]
    (g : Finset G → ℕ) (hg : LinearRankRealizes K g) :
    IsDiscreteEntropyTable.{u,v}
      (fun I => (g I : ℝ) * (Real.log (Fintype.card K) / Real.log 2)) :=
  (rank_entropy_checkpoint K g hg).isDiscreteEntropyTable

/-- Every valid homogeneous information inequality holds on finite-field ranks. -/
theorem information_rank_checkpoint (K : Type v) [Field K] [Fintype K]
    (a : Finset G → ℝ) (ha : ValidInformation.{u,v} a)
    (g : Finset G → ℕ) (hg : LinearRankRealizes K g) :
    0 ≤ inequalityValue a (fun I => (g I : ℝ)) := by
  have h := ha.apply_finite (rank_entropy_checkpoint K g hg)
  rw [inequalityValue_mul] at h
  exact (mul_nonneg_iff_of_pos_left (finiteField_entropyScale_pos K)).mp h

/-- Information validity implies rank validity over every finite field. -/
theorem ValidInformation.validRank (K : Type v) [Field K] [Fintype K]
    {a : Finset G → ℝ} (ha : ValidInformation.{u,v} a) : ValidRank K a := by
  intro g hg
  exact information_rank_checkpoint K a ha g hg

/-- Over F₂ the factor is exactly one, so ranks themselves are entropies in bits. -/
theorem binary_rank_entropy_checkpoint (g : Finset G → ℕ)
    (hg : LinearRankRealizes (ZMod 2) g) :
    IsFiniteEntropyTable.{u,0} (fun I => (g I : ℝ)) := by
  have h := rank_entropy_checkpoint (ZMod 2) g hg
  have hscale : Real.log (Fintype.card (ZMod 2)) / Real.log 2 = 1 := by
    rw [ZMod.card]
    norm_num only [Nat.cast_ofNat]
    exact div_self (ne_of_gt log_two_pos)
  simpa only [hscale, mul_one] using h

end BoundedArity
