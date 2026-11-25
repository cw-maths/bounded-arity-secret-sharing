module

public import BoundedArity.Interpolation
public import Mathlib.Tactic

/-!
# The finite type of occurring membership patterns

The type model has one participant for each nonempty membership pattern
which actually occurs among the original physical participants. This module
expresses that finite ground set as a subtype and transports the visible
coalitions to it.
-/

@[expose] public section

namespace BoundedArity

variable {P G : Type*} [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- The occurring nonempty membership types, now used as a participant type. -/
abbrev OccurringType (B : G → Finset P) :=
  {t : Finset G // t ∈ occurringTypes B}

/-- The visible types as a finite set in the type model's own ground set. -/
def visibleTypeSet (B : G → Finset P) (I : Finset G) :
    Finset (OccurringType B) :=
  (visibleTypes B I).subtype (fun t => t ∈ occurringTypes B)

@[simp] theorem mem_visibleTypeSet_iff_val (B : G → Finset P)
    (I : Finset G) (t : OccurringType B) :
    t ∈ visibleTypeSet B I ↔ t.val ∈ visibleTypes B I := by
  simp [visibleTypeSet]

theorem mem_visibleTypeSet (B : G → Finset P)
    (I : Finset G) (t : OccurringType B) :
    t ∈ visibleTypeSet B I ↔ (t.val ∩ I).Nonempty := by
  simp [t.property]

@[simp] theorem visibleTypeSet_empty (B : G → Finset P) :
    visibleTypeSet B ∅ = ∅ := by
  ext t
  simp

@[simp] theorem visibleTypeSet_univ (B : G → Finset P) :
    visibleTypeSet B Finset.univ = Finset.univ := by
  ext t
  simp [t.property]

/-- The type participants observed by one group. -/
def typeGroup (B : G → Finset P) (j : G) : Finset (OccurringType B) :=
  Finset.univ.filter (fun t => j ∈ t.val)

@[simp] theorem mem_typeGroup (B : G → Finset P) (j : G)
    (t : OccurringType B) : t ∈ typeGroup B j ↔ j ∈ t.val := by
  simp [typeGroup]

/-- Unioning the types in individual groups gives precisely the visible set. -/
theorem visibleTypeSet_eq_biUnion (B : G → Finset P) (I : Finset G) :
    visibleTypeSet B I = I.biUnion (typeGroup B) := by
  ext t
  simp only [mem_visibleTypeSet, Finset.mem_biUnion, mem_typeGroup]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (Finset.mem_inter.mp hj).2, (Finset.mem_inter.mp hj).1⟩
  · rintro ⟨j, hjI, hjt⟩
    exact ⟨j, Finset.mem_inter.mpr ⟨hjt, hjI⟩⟩

/-- There are at most as many occurring types as nonempty subsets of G. -/
theorem occurringType_card_le (B : G → Finset P) :
    Fintype.card (OccurringType B) ≤ 2 ^ Fintype.card G - 1 := by
  classical
  have hsub : occurringTypes B ⊆ (Finset.univ : Finset G).powerset.erase ∅ := by
    intro t ht
    apply Finset.mem_erase.mpr
    exact ⟨((mem_occurringTypes B).mp ht).2.ne_empty,
      Finset.mem_powerset.mpr (Finset.subset_univ t)⟩
  calc
    Fintype.card (OccurringType B) = (occurringTypes B).card := by
      simp [OccurringType]
    _ ≤ ((Finset.univ : Finset G).powerset.erase ∅).card := Finset.card_le_card hsub
    _ = 2 ^ Fintype.card G - 1 := by
      rw [Finset.card_erase_of_mem (by simp)]
      simp

end BoundedArity
