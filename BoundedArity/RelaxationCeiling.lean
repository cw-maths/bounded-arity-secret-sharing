module

public import BoundedArity.Barrier
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The maximum-share objective and its infimum

Proper access structures have a nonempty participant type. Consequently the
finite supremum of the physical singleton entries is an attained maximum,
and the reviewed pointwise objective bound is equivalent to bounding it.
The relaxation value is the infimum of those actual maximum-share values.
-/

@[expose] public section

namespace BoundedArity

variable {P : Type*} [Fintype P]

/-- Properness excludes an empty participant type. -/
theorem AccessStructure.nonempty_participants (Γ : AccessStructure P) : Nonempty P := by
  classical
  rcases isEmpty_or_nonempty P with h | h
  · exact False.elim (Γ.empty_unauthorized (by simpa using Γ.univ_authorized))
  · exact h

/-- E32's actual objective: the maximum of the physical singleton entries. -/
noncomputable def maxShare (F : Finset (Option P) → ℝ) : ℝ :=
  ⨆ p : P, F {some p}

/-- The maximum is attained because the participant type is finite and nonempty. -/
theorem maxShare_attained [Nonempty P] (F : Finset (Option P) → ℝ) :
    ∃ p : P, F {some p} = maxShare F :=
  exists_eq_ciSup_of_finite

/-- The approved pointwise bound is exactly a bound on the maximum objective. -/
theorem maxShareAtMost_iff [Nonempty P] (F : Finset (Option P) → ℝ) (L : ℝ) :
    MaxShareAtMost F L ↔ maxShare F ≤ L := by
  exact (ciSup_le_iff (Set.finite_range (fun p : P => F {some p})).bddAbove).symm

theorem singleton_le_maxShare (F : Finset (Option P) → ℝ) (p : P) :
    F {some p} ≤ maxShare F :=
  le_ciSup (Set.finite_range (fun p : P => F {some p})).bddAbove p

variable [DecidableEq P]

omit [Fintype P] in
/-- Every polymatroid entry is nonnegative, by normalization and monotonicity. -/
theorem IsPolymatroid.nonneg {F : Finset (Option P) → ℝ} (hF : IsPolymatroid F)
    (X : Finset (Option P)) : 0 ≤ F X := by
  rw [← hF.1]
  exact hF.2.1 ∅ X (Finset.empty_subset X)

/-- Feasibility will therefore give a genuine lower bound for the infimum. -/
theorem IsPolymatroid.maxShare_nonneg [Nonempty P] {F : Finset (Option P) → ℝ}
    (hF : IsPolymatroid F) : 0 ≤ maxShare F := by
  obtain ⟨p⟩ := ‹Nonempty P›
  exact (hF.nonneg {some p}).trans (singleton_le_maxShare F p)

/-- The fixed witness has exactly the stated maximum, since all its physical
singletons have that value. -/
theorem formalTable_maxShare (Γ : AccessStructure P) (b : ℕ) :
    maxShare (fun X => (formalTable Γ b X : ℝ)) =
      ((1 + b * (Fintype.card P - 1) : ℕ) : ℝ) := by
  let : Nonempty P := Γ.nonempty_participants
  obtain ⟨p, hp⟩ := maxShare_attained (fun X => (formalTable Γ b X : ℝ))
  rw [← hp, formalTable_singleton Γ b p]

/-- The values attained by the actual maximum-share objective on the E31 feasible set. -/
def FeasibleShareValues (r : ℕ) (Γ : AccessStructure P) : Set ℝ :=
  {L | ∃ F : Finset (Option P) → ℝ, FeasibleAtArity r Γ F ∧ maxShare F = L}

/-- The infimum objective value of the information-inequality relaxation. -/
noncomputable def relaxationValue (r : ℕ) (Γ : AccessStructure P) : ℝ :=
  sInf (FeasibleShareValues r Γ)

/-- The objective values when prescribed-field rank constraints are imposed as well. -/
def RankFeasibleShareValues (K : Type*) [Field K] (r : ℕ)
    (Γ : AccessStructure P) : Set ℝ :=
  {L | ∃ F : Finset (Option P) → ℝ,
    RankFeasibleAtArity K r Γ F ∧ maxShare F = L}

/-- The infimum objective for the rank-strengthened information relaxation. -/
noncomputable def rankRelaxationValue (K : Type*) [Field K] (r : ℕ)
    (Γ : AccessStructure P) : ℝ :=
  sInf (RankFeasibleShareValues K r Γ)

theorem feasibleShareValues_bddBelow (Γ : AccessStructure P) (r : ℕ) :
    BddBelow (FeasibleShareValues r Γ) := by
  let : Nonempty P := Γ.nonempty_participants
  refine ⟨0, ?_⟩
  rintro L ⟨F, hF, rfl⟩
  exact hF.1.maxShare_nonneg

theorem rankFeasibleShareValues_bddBelow (K : Type*) [Field K]
    (Γ : AccessStructure P) (r : ℕ) :
    BddBelow (RankFeasibleShareValues K r Γ) := by
  let : Nonempty P := Γ.nonempty_participants
  refine ⟨0, ?_⟩
  rintro L ⟨F, hF, rfl⟩
  exact hF.1.1.maxShare_nonneg

/-- The information feasible set contains a table attaining the ceiling value. -/
theorem formalTable_mem_feasibleShareValues (Γ : AccessStructure P)
    (r : ℕ) (hr : 2 ≤ r) :
    ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ) ∈
      FeasibleShareValues r Γ := by
  exact ⟨fun X => (formalTable Γ (arityConstant r) X : ℝ),
    formalTable_feasibleAtArity Γ r hr, formalTable_maxShare Γ (arityConstant r)⟩

/-- That same table attains the ceiling under the additional rank constraints. -/
theorem formalTable_mem_rankFeasibleShareValues (K : Type*) [Field K]
    (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ) ∈
      RankFeasibleShareValues K r Γ := by
  exact ⟨fun X => (formalTable Γ (arityConstant r) X : ℝ),
    formalTable_rankFeasibleAtArity K Γ r hr,
    formalTable_maxShare Γ (arityConstant r)⟩

theorem feasibleShareValues_nonempty (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    (FeasibleShareValues r Γ).Nonempty :=
  ⟨_, formalTable_mem_feasibleShareValues Γ r hr⟩

theorem rankFeasibleShareValues_nonempty (K : Type*) [Field K]
    (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    (RankFeasibleShareValues K r Γ).Nonempty :=
  ⟨_, formalTable_mem_rankFeasibleShareValues K Γ r hr⟩

/-- The nonempty feasible set has nonnegative objective infimum. -/
theorem relaxationValue_nonneg (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    0 ≤ relaxationValue r Γ := by
  let : Nonempty P := Γ.nonempty_participants
  apply le_csInf (feasibleShareValues_nonempty Γ r hr)
  rintro L ⟨F, hF, rfl⟩
  exact hF.1.maxShare_nonneg

theorem rankRelaxationValue_nonneg (K : Type*) [Field K]
    (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    0 ≤ rankRelaxationValue K r Γ := by
  let : Nonempty P := Γ.nonempty_participants
  apply le_csInf (rankFeasibleShareValues_nonempty K Γ r hr)
  rintro L ⟨F, hF, rfl⟩
  exact hF.1.1.maxShare_nonneg

/-- T8's numerical information-inequality ceiling, for the actual maximum objective. -/
theorem relaxation_ceiling (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    relaxationValue r Γ ≤
      ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ) :=
  csInf_le (feasibleShareValues_bddBelow Γ r)
    (formalTable_mem_feasibleShareValues Γ r hr)

/-- The same ceiling holds after adjoining all prescribed-field rank constraints. -/
theorem rank_relaxation_ceiling (K : Type*) [Field K]
    (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    rankRelaxationValue K r Γ ≤
      ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ) :=
  csInf_le (rankFeasibleShareValues_bddBelow K Γ r)
    (formalTable_mem_rankFeasibleShareValues K Γ r hr)

/-- Adding rank constraints can only increase the objective infimum. -/
theorem relaxationValue_le_rankRelaxationValue (K : Type*) [Field K]
    (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    relaxationValue r Γ ≤ rankRelaxationValue K r Γ := by
  apply csInf_le_csInf (feasibleShareValues_bddBelow Γ r)
    (rankFeasibleShareValues_nonempty K Γ r hr)
  rintro L ⟨F, hF, hL⟩
  exact ⟨F, hF.1, hL⟩

omit [DecidableEq P] in
/-- The six-variable coefficient gives the displayed real bound 6N - 5. -/
theorem six_arity_bound_eq (Γ : AccessStructure P) :
    ((1 + arityConstant 6 * (Fintype.card P - 1) : ℕ) : ℝ) =
      6 * (Fintype.card P : ℝ) - 5 := by
  have hcard : 1 ≤ Fintype.card P :=
    Fintype.card_pos_iff.mpr Γ.nonempty_participants
  rw [arityConstant_six, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hcard]
  norm_num
  ring

/-- The approved six-variable information-inequality instance. -/
theorem relaxation_ceiling_six (Γ : AccessStructure P) :
    relaxationValue 6 Γ ≤ 6 * (Fintype.card P : ℝ) - 5 := by
  rw [← six_arity_bound_eq Γ]
  exact relaxation_ceiling Γ 6 (by omega)

/-- The six-variable ceiling also holds for every prescribed field. -/
theorem rank_relaxation_ceiling_six (K : Type*) [Field K] (Γ : AccessStructure P) :
    rankRelaxationValue K 6 Γ ≤ 6 * (Fintype.card P : ℝ) - 5 := by
  rw [← six_arity_bound_eq Γ]
  exact rank_relaxation_ceiling K Γ 6 (by omega)

end BoundedArity
