module

public import BoundedArity.ArityRestriction

/-!
# T8: the single-table bounded-arity barrier

The real table is fixed by the access structure and the arity bound before
any field, inequality, or grouping is chosen. Every inequality instance is
checked against that same table. The quantification over arities includes
zero and one, through the empty-group padding proved in ArityRestriction.
-/

@[expose] public section

universe u v

namespace BoundedArity

variable {P : Type u} [Fintype P] [DecidableEq P]

/-- E31: whole-table Shannon and access constraints, together with every
valid homogeneous information inequality on every grouping of at most r labels. -/
def FeasibleAtArity (r : ℕ) (Γ : AccessStructure P)
    (F : Finset (Option P) → ℝ) : Prop :=
  IsPolymatroid F ∧ HasNormalizedAccess Γ F ∧
    ∀ k : ℕ, k ≤ r →
    ∀ a : Finset (Fin k) → ℝ, ValidInformation.{0,0} a →
    ∀ A : Fin k → Finset (Option P),
      0 ≤ inequalityValue a (groupProjection F A)

/-- The additional E31 rank constraints over a prescribed field, on the
same full-group projections and with the same arbitrary real coefficients. -/
def RankConstraintsAtArity (K : Type v) [Field K] (r : ℕ)
    (F : Finset (Option P) → ℝ) : Prop :=
  ∀ k : ℕ, k ≤ r →
  ∀ a : Finset (Fin k) → ℝ, ValidRank K a →
  ∀ A : Fin k → Finset (Option P),
    0 ≤ inequalityValue a (groupProjection F A)

/-- The rank-strengthened relaxation appends its constraints to the full
information relaxation; both constrain one and the same table. -/
def RankFeasibleAtArity (K : Type v) [Field K] (r : ℕ)
    (Γ : AccessStructure P) (F : Finset (Option P) → ℝ) : Prop :=
  FeasibleAtArity r Γ F ∧ RankConstraintsAtArity K r F

/-- The fixed formal table satisfies every reviewed information constraint
at every arity at most r, including arities zero and one. -/
theorem formalTable_feasibleAtArity (Γ : AccessStructure P)
    (r : ℕ) (hr : 2 ≤ r) :
    FeasibleAtArity r Γ
      (fun X => (formalTable Γ (arityConstant r) X : ℝ)) := by
  refine ⟨formalTable_isPolymatroid Γ (arityConstant r) (one_le_arityConstant r),
    formalTable_hasNormalizedAccess Γ (arityConstant r), ?_⟩
  intro k hk a ha A
  exact ha.apply_finite (localEntropy_le_arity_checkpoint Γ r hr k hk A)

/-- Every prescribed field's rank inequalities hold on the same fixed table.
There is no field-size or characteristic hypothesis. -/
theorem formalTable_rankConstraintsAtArity (K : Type v) [Field K]
    (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    RankConstraintsAtArity K r
      (fun X => (formalTable Γ (arityConstant r) X : ℝ)) := by
  intro k hk a ha A
  exact ha (groupProjection (formalTable Γ (arityConstant r)) A)
    (localRepresentability_le_arity_checkpoint (K := K) Γ r hr k hk A)

/-- Simultaneous information and prescribed-field rank feasibility. -/
theorem formalTable_rankFeasibleAtArity (K : Type v) [Field K]
    (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    RankFeasibleAtArity K r Γ
      (fun X => (formalTable Γ (arityConstant r) X : ℝ)) :=
  ⟨formalTable_feasibleAtArity Γ r hr,
    formalTable_rankConstraintsAtArity K Γ r hr⟩

/-- Every physical singleton attains the asserted normalized objective value. -/
theorem formalTable_arity_singleton_real (Γ : AccessStructure P)
    (r : ℕ) (p : P) :
    (formalTable Γ (arityConstant r) {some p} : ℝ) =
      ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ) := by
  exact congrArg (fun n : ℕ => (n : ℝ))
    (formalTable_singleton Γ (arityConstant r) p)

/-- T8: one explicit table has full information feasibility, all prescribed-field
rank constraints, and the exact physical-share value. The table uses only Γ and r. -/
theorem barrier_checkpoint (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    FeasibleAtArity r Γ
        (fun X => (formalTable Γ (arityConstant r) X : ℝ)) ∧
      (∀ (K : Type v) [Field K],
        RankConstraintsAtArity K r
          (fun X => (formalTable Γ (arityConstant r) X : ℝ))) ∧
      (∀ p : P, (formalTable Γ (arityConstant r) {some p} : ℝ) =
        ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ)) ∧
      MaxShareAtMost (fun X => (formalTable Γ (arityConstant r) X : ℝ))
        ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ) := by
  refine ⟨formalTable_feasibleAtArity Γ r hr, ?_,
    formalTable_arity_singleton_real Γ r,
    formalTable_maxShareAtMost Γ (arityConstant r)⟩
  intro K inst
  exact formalTable_rankConstraintsAtArity K Γ r hr

/-- The same witness is chosen before the field, inequalities, and groupings.
This is the single feasible table that gives the objective ceiling. -/
theorem barrier_exists_witness (Γ : AccessStructure P) (r : ℕ) (hr : 2 ≤ r) :
    ∃ F : Finset (Option P) → ℝ,
      FeasibleAtArity r Γ F ∧
      (∀ (K : Type v) [Field K], RankConstraintsAtArity K r F) ∧
      (∀ p : P, F {some p} =
        ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ)) ∧
      MaxShareAtMost F
        ((1 + arityConstant r * (Fintype.card P - 1) : ℕ) : ℝ) := by
  exact ⟨fun X => (formalTable Γ (arityConstant r) X : ℝ),
    barrier_checkpoint Γ r hr⟩

end BoundedArity
