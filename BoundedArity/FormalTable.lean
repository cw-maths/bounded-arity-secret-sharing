module

public import BoundedArity.Interpolation
public import BoundedArity.PairCoverage
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# The fixed formal table and its whole-table Shannon constraints

This module implements the mathematical interfaces C13--C17 in the reviewed
specification and supplies the proofs targeted by checkpoint T3. The definition
`physicalPart` is reused from C11 in `Interpolation.lean`; C12 is implemented in
`PairCoverage.lean`.

The final barrier imports these whole-table facts through `Checkpoint3`.
Current build and audit instructions are in the repository README.
-/

@[expose] public section

namespace BoundedArity

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ## Physical parts and the inclusion of physical participants -/

@[simp] theorem physicalPart_empty :
    physicalPart (∅ : Finset (Option P)) = ∅ := by
  ext p
  simp

@[simp] theorem physicalPart_union (X Y : Finset (Option P)) :
    physicalPart (X ∪ Y) = physicalPart X ∪ physicalPart Y := by
  ext p
  simp

@[simp] theorem physicalPart_inter (X Y : Finset (Option P)) :
    physicalPart (X ∩ Y) = physicalPart X ∩ physicalPart Y := by
  ext p
  simp

theorem physicalPart_mono {X Y : Finset (Option P)} (hXY : X ⊆ Y) :
    physicalPart X ⊆ physicalPart Y := by
  intro p hp
  exact mem_physicalPart.mpr (hXY (mem_physicalPart.mp hp))

@[simp] theorem physicalPart_insert_none (X : Finset (Option P)) :
    physicalPart (insert none X) = physicalPart X := by
  ext p
  simp

@[simp] theorem physicalPart_secret :
    physicalPart ({none} : Finset (Option P)) = ∅ := by
  ext p
  simp

@[simp] theorem physicalPart_singleton (p : P) :
    physicalPart ({some p} : Finset (Option P)) = {p} := by
  ext q
  simp

/-- C17: embed a physical coalition in the index type with its extra secret. -/
def physicalLift (U : Finset P) : Finset (Option P) :=
  U.image some

@[simp] theorem physicalPart_physicalLift (U : Finset P) :
    physicalPart (physicalLift U) = U := by
  ext p
  simp [physicalLift]

omit [Fintype P] in
@[simp] theorem none_not_mem_physicalLift (U : Finset P) :
    none ∉ physicalLift U := by
  simp [physicalLift]

/-! ## The physical table -/

/-- C13: one private unit per participant, and `b` units per meeting pair. -/
def physicalTable (b : ℕ) (U : Finset P) : ℕ :=
  U.card + b * pairCoverage U

@[simp] theorem physicalTable_empty (b : ℕ) :
    physicalTable b (∅ : Finset P) = 0 := by
  simp [physicalTable]

@[simp] theorem physicalTable_singleton (b : ℕ) (p : P) :
    physicalTable b {p} = 1 + b * (Fintype.card P - 1) := by
  simp [physicalTable, pairCoverage_singleton]

theorem physicalTable_mono (b : ℕ) {U V : Finset P} (hUV : U ⊆ V) :
    physicalTable b U ≤ physicalTable b V := by
  have hc := Finset.card_le_card hUV
  have he := Nat.mul_le_mul_left b (pairCoverage_mono hUV)
  dsimp [physicalTable]
  omega

/-- The private-cardinality term gives a full unit on a strict inclusion. -/
theorem physicalTable_add_one_le_of_subset_ne (b : ℕ)
    {U V : Finset P} (hUV : U ⊆ V) (hne : U ≠ V) :
    physicalTable b U + 1 ≤ physicalTable b V := by
  have hc : U.card < V.card := by
    by_contra h
    have hcard : V.card ≤ U.card := by omega
    exact hne (Finset.eq_of_subset_of_card_le hUV hcard)
  have he := Nat.mul_le_mul_left b (pairCoverage_mono hUV)
  dsimp [physicalTable]
  omega

theorem physicalTable_submodular (b : ℕ) (U V : Finset P) :
    physicalTable b (U ∪ V) + physicalTable b (U ∩ V) ≤
      physicalTable b U + physicalTable b V := by
  have hc := Finset.card_union_add_card_inter U V
  have he := Nat.mul_le_mul_left b (pairCoverage_submodular U V)
  simp only [Nat.mul_add] at he
  dsimp [physicalTable]
  omega

/-- Incomparable coalitions have at least one crossing pair. For `b ≥ 1`
this supplies the unit needed to absorb the authorization-indicator slack. -/
theorem physicalTable_strict_submodular (b : ℕ) (hb : 1 ≤ b)
    (U V : Finset P) (hUV : ¬ U ⊆ V) (hVU : ¬ V ⊆ U) :
    physicalTable b (U ∪ V) + physicalTable b (U ∩ V) + 1 ≤
      physicalTable b U + physicalTable b V := by
  have hc := Finset.card_union_add_card_inter U V
  have he := Nat.mul_le_mul_left b
    (pairCoverage_strict_submodular U V hUV hVU)
  simp only [Nat.mul_add, Nat.mul_one] at he
  dsimp [physicalTable]
  omega

/-! ## Authorization and the fixed full table -/

/-- C14: one for unauthorized coalitions and zero for authorized ones. -/
noncomputable def unauthorizedBit (Γ : AccessStructure P)
    (U : Finset P) : ℕ := by
  classical
  exact if Γ.Authorized U then 0 else 1

omit [DecidableEq P] in
theorem unauthorizedBit_le_one (Γ : AccessStructure P) (U : Finset P) :
    unauthorizedBit Γ U ≤ 1 := by
  classical
  unfold unauthorizedBit
  split_ifs <;> omega

omit [DecidableEq P] in
@[simp] theorem unauthorizedBit_empty (Γ : AccessStructure P) :
    unauthorizedBit Γ ∅ = 1 := by
  classical
  simp [unauthorizedBit, Γ.empty_unauthorized]

omit [DecidableEq P] in
@[simp] theorem unauthorizedBit_univ (Γ : AccessStructure P) :
    unauthorizedBit Γ Finset.univ = 0 := by
  classical
  simp [unauthorizedBit, Γ.univ_authorized]

omit [DecidableEq P] in
theorem unauthorizedBit_antitone (Γ : AccessStructure P)
    {U V : Finset P} (hUV : U ⊆ V) :
    unauthorizedBit Γ V ≤ unauthorizedBit Γ U := by
  classical
  by_cases hU : Γ.Authorized U
  · have hV : Γ.Authorized V := Γ.upward_closed hUV hU
    simp [unauthorizedBit, hU, hV]
  · have hbit := unauthorizedBit_le_one Γ V
    simpa [unauthorizedBit, hU] using hbit

/-- C15: the one fixed formal table, including its optional secret increment. -/
noncomputable def formalTable (Γ : AccessStructure P)
    (b : ℕ) (X : Finset (Option P)) : ℕ := by
  classical
  exact physicalTable b (physicalPart X) +
    (if none ∈ X then unauthorizedBit Γ (physicalPart X) else 0)

@[simp] theorem formalTable_empty (Γ : AccessStructure P) (b : ℕ) :
    formalTable Γ b ∅ = 0 := by
  classical
  simp [formalTable]

@[simp] theorem formalTable_secret (Γ : AccessStructure P) (b : ℕ) :
    formalTable Γ b {none} = 1 := by
  classical
  simp [formalTable]

@[simp] theorem formalTable_singleton (Γ : AccessStructure P)
    (b : ℕ) (p : P) :
    formalTable Γ b {some p} = 1 + b * (Fintype.card P - 1) := by
  classical
  simp [formalTable]

@[simp] theorem formalTable_physicalLift (Γ : AccessStructure P)
    (b : ℕ) (U : Finset P) :
    formalTable Γ b (physicalLift U) = physicalTable b U := by
  classical
  simp [formalTable]

@[simp] theorem formalTable_insert_secret (Γ : AccessStructure P)
    (b : ℕ) (U : Finset P) :
    formalTable Γ b (insert none (physicalLift U)) =
      physicalTable b U + unauthorizedBit Γ U := by
  classical
  simp [formalTable]

theorem physicalTable_le_formalTable (Γ : AccessStructure P)
    (b : ℕ) (X : Finset (Option P)) :
    physicalTable b (physicalPart X) ≤ formalTable Γ b X := by
  classical
  unfold formalTable
  omega

theorem formalTable_le_physicalTable_add_one (Γ : AccessStructure P)
    (b : ℕ) (X : Finset (Option P)) :
    formalTable Γ b X ≤ physicalTable b (physicalPart X) + 1 := by
  classical
  have hbit := unauthorizedBit_le_one Γ (physicalPart X)
  unfold formalTable
  split_ifs <;> omega

/-- The fixed table is monotone for every nonnegative natural `b`. -/
theorem formalTable_mono (Γ : AccessStructure P) (b : ℕ)
    {X Y : Finset (Option P)} (hXY : X ⊆ Y) :
    formalTable Γ b X ≤ formalTable Γ b Y := by
  classical
  have hparts := physicalPart_mono hXY
  by_cases heq : physicalPart X = physicalPart Y
  · by_cases hx : none ∈ X
    · have hy : none ∈ Y := hXY hx
      simp [formalTable, hx, hy, heq]
    · simp [formalTable, hx, heq]
  · have hgap := physicalTable_add_one_le_of_subset_ne b hparts heq
    have hhi := formalTable_le_physicalTable_add_one Γ b X
    have hlo := physicalTable_le_formalTable Γ b Y
    omega

/-- Global submodularity, for all subsets of the full share-and-secret type. -/
theorem formalTable_submodular (Γ : AccessStructure P) (b : ℕ)
    (hb : 1 ≤ b) (X Y : Finset (Option P)) :
    formalTable Γ b (X ∪ Y) + formalTable Γ b (X ∩ Y) ≤
      formalTable Γ b X + formalTable Γ b Y := by
  classical
  let U := physicalPart X
  let V := physicalPart Y
  have hphys := physicalTable_submodular b U V
  have hleft := unauthorizedBit_antitone Γ
    (Finset.subset_union_left : U ⊆ U ∪ V)
  have hright := unauthorizedBit_antitone Γ
    (Finset.subset_union_right : V ⊆ U ∪ V)
  simp only [formalTable, physicalPart_union, physicalPart_inter,
    Finset.mem_union, Finset.mem_inter]
  change
    (physicalTable b (U ∪ V) +
      (if none ∈ X ∨ none ∈ Y then unauthorizedBit Γ (U ∪ V) else 0)) +
    (physicalTable b (U ∩ V) +
      (if none ∈ X ∧ none ∈ Y then unauthorizedBit Γ (U ∩ V) else 0)) ≤
    (physicalTable b U + (if none ∈ X then unauthorizedBit Γ U else 0)) +
    (physicalTable b V + (if none ∈ Y then unauthorizedBit Γ V else 0))
  by_cases hx : none ∈ X
  · by_cases hy : none ∈ Y
    · have hboth :
          (physicalTable b (U ∪ V) + unauthorizedBit Γ (U ∪ V)) +
          (physicalTable b (U ∩ V) + unauthorizedBit Γ (U ∩ V)) ≤
          (physicalTable b U + unauthorizedBit Γ U) +
          (physicalTable b V + unauthorizedBit Γ V) := by
        by_cases hUV : U ⊆ V
        · rw [Finset.union_eq_right.mpr hUV, Finset.inter_eq_left.mpr hUV]
          omega
        · by_cases hVU : V ⊆ U
          · rw [Finset.union_eq_left.mpr hVU, Finset.inter_eq_right.mpr hVU]
          · have hgap := physicalTable_strict_submodular b hb U V hUV hVU
            have hbit := unauthorizedBit_le_one Γ (U ∩ V)
            omega
      simpa [hx, hy] using hboth
    · have hsingle :
          (physicalTable b (U ∪ V) + unauthorizedBit Γ (U ∪ V)) +
          physicalTable b (U ∩ V) ≤
          (physicalTable b U + unauthorizedBit Γ U) + physicalTable b V := by
        omega
      simpa [hx, hy] using hsingle
  · by_cases hy : none ∈ Y
    · have hsingle :
          (physicalTable b (U ∪ V) + unauthorizedBit Γ (U ∪ V)) +
          physicalTable b (U ∩ V) ≤
          physicalTable b U + (physicalTable b V + unauthorizedBit Γ V) := by
        omega
      simpa [hx, hy] using hsingle
    · simpa [hx, hy] using hphys

/-! ## The approved real-valued predicates and checkpoint T3 -/

/-- C16: the whole-table polymatroid conditions. -/
def IsPolymatroid (F : Finset (Option P) → ℝ) : Prop :=
  F ∅ = 0 ∧
  (∀ U V, U ⊆ V → F U ≤ F V) ∧
  (∀ U V, F (U ∪ V) + F (U ∩ V) ≤ F U + F V)

/-- C17: secret normalization together with every coalition's access equality. -/
def HasNormalizedAccess (Γ : AccessStructure P)
    (F : Finset (Option P) → ℝ) : Prop :=
  F {none} = 1 ∧
  ∀ U, F (insert none (physicalLift U)) =
    F (physicalLift U) + (unauthorizedBit Γ U : ℝ)

/-- T3, Shannon part: the fixed table is a real-valued polymatroid. -/
theorem formalTable_isPolymatroid (Γ : AccessStructure P)
    (b : ℕ) (hb : 1 ≤ b) :
    IsPolymatroid (fun X => (formalTable Γ b X : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro X Y hXY
    change (formalTable Γ b X : ℝ) ≤ (formalTable Γ b Y : ℝ)
    exact (Nat.cast_le (α := ℝ)).2 (formalTable_mono Γ b hXY)
  · intro X Y
    change
      (formalTable Γ b (X ∪ Y) : ℝ) +
        (formalTable Γ b (X ∩ Y) : ℝ) ≤
      (formalTable Γ b X : ℝ) + (formalTable Γ b Y : ℝ)
    have h :
        ((formalTable Γ b (X ∪ Y) + formalTable Γ b (X ∩ Y) : ℕ) : ℝ) ≤
        ((formalTable Γ b X + formalTable Γ b Y : ℕ) : ℝ) :=
      (Nat.cast_le (α := ℝ)).2 (formalTable_submodular Γ b hb X Y)
    simpa only [Nat.cast_add] using h

/-- T3, access part: the fixed table has all normalized access equalities. -/
theorem formalTable_hasNormalizedAccess (Γ : AccessStructure P) (b : ℕ) :
    HasNormalizedAccess Γ (fun X => (formalTable Γ b X : ℝ)) := by
  constructor
  · simp
  · intro U
    simp

end BoundedArity
