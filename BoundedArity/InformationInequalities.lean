module

public import BoundedArity.DiscreteJointLaw
public import BoundedArity.LinearRank

/-!
# Homogeneous information and rank inequalities

The coefficients range over arbitrary real families on all coalitions. There
is no constant term. Information validity quantifies over all countable joint
laws with finite full-joint entropy; rank validity quantifies over all common
linear representations over the prescribed field.
-/

@[expose] public section

universe u v

namespace BoundedArity

open scoped BigOperators

variable {G : Type u} [Fintype G]

/-- E29: the homogeneous functional with arbitrary real coalition coefficients. -/
noncomputable def inequalityValue (a h : Finset G → ℝ) : ℝ :=
  ∑ I ∈ Finset.univ.powerset, a I * h I

/-- E29: validity for every countable joint law with finite full-joint entropy. -/
def ValidInformation (a : Finset G → ℝ) : Prop :=
  ∀ h : Finset G → ℝ,
    IsDiscreteEntropyTable.{u,v} h → 0 ≤ inequalityValue a h

/-- E30: validity for all rank tables representable over the prescribed field. -/
def ValidRank (K : Type v) [Field K] (a : Finset G → ℝ) : Prop :=
  ∀ g : Finset G → ℕ,
    LinearRankRealizes K g → 0 ≤ inequalityValue a (fun I => (g I : ℝ))

/-- One common scalar factors out of the homogeneous functional. -/
theorem inequalityValue_smul (a h : Finset G → ℝ) (c : ℝ) :
    inequalityValue a (fun I => c * h I) = c * inequalityValue a h := by
  unfold inequalityValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _hI
  ring

theorem inequalityValue_mul (a h : Finset G → ℝ) (c : ℝ) :
    inequalityValue a (fun I => h I * c) = c * inequalityValue a h := by
  simpa only [mul_comm] using inequalityValue_smul a h c

/-- A positive common scale does not change the inequality's sign. -/
theorem inequalityValue_smul_nonneg_iff (a h : Finset G → ℝ)
    (c : ℝ) (hc : 0 < c) :
    0 ≤ inequalityValue a (fun I => c * h I) ↔ 0 ≤ inequalityValue a h := by
  rw [inequalityValue_smul]
  exact mul_nonneg_iff_of_pos_left hc

theorem inequalityValue_nonneg_of_scaled (a h : Finset G → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hscaled : 0 ≤ inequalityValue a (fun I => c * h I)) :
    0 ≤ inequalityValue a h :=
  (inequalityValue_smul_nonneg_iff a h c hc).mp hscaled

/-- Natural-number rank scaling agrees with real homogeneous scaling. -/
theorem inequalityValue_nat_mul (a : Finset G → ℝ) (g : Finset G → ℕ) (k : ℕ) :
    inequalityValue a (fun I => ((k * g I : ℕ) : ℝ)) =
      (k : ℝ) * inequalityValue a (fun I => (g I : ℝ)) := by
  simpa only [Nat.cast_mul] using
    inequalityValue_smul a (fun I => (g I : ℝ)) (k : ℝ)

/-- Finite-valued witnesses lie in the full information-validity domain. -/
theorem ValidInformation.apply_finite {a h : Finset G → ℝ}
    (ha : ValidInformation.{u,v} a) (hh : IsFiniteEntropyTable.{u,v} h) :
    0 ≤ inequalityValue a h :=
  ha h hh.isDiscreteEntropyTable

end BoundedArity
