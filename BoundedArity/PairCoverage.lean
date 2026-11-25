module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic

/-!
# Pair coverage for the fixed formal table

This file implements the pair-coverage definitions in C12 of the approved
review packet. A pair is a two-element finset, so its endpoints are distinct
and the order of its endpoints does not affect its identity.

The strict submodularity lemma uses a pair with one endpoint in each of the
two set differences. It is the unit of slack needed for the access indicator
in the fixed table.

These facts are used by `FormalTable` and the local linear constructions.
-/

@[expose] public section

namespace BoundedArity

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The unordered pairs of distinct participants meeting `U`. -/
def pairsMeeting (U : Finset P) : Finset (Finset P) :=
  (Finset.univ.powersetCard 2).filter (fun e => (e ∩ U).Nonempty)

/-- The number of unordered physical pairs meeting `U`. -/
def pairCoverage (U : Finset P) : ℕ :=
  (pairsMeeting U).card

@[simp] theorem mem_pairsMeeting {U e : Finset P} :
    e ∈ pairsMeeting U ↔ e.card = 2 ∧ (e ∩ U).Nonempty := by
  simp [pairsMeeting, Finset.mem_powersetCard]

@[simp] theorem pairsMeeting_empty : pairsMeeting (∅ : Finset P) = ∅ := by
  ext e
  simp

@[simp] theorem pairCoverage_empty : pairCoverage (∅ : Finset P) = 0 := by
  simp [pairCoverage]

/-- Meeting a smaller coalition implies meeting a larger one. -/
theorem pairsMeeting_mono {U V : Finset P} (hUV : U ⊆ V) :
    pairsMeeting U ⊆ pairsMeeting V := by
  intro e he
  obtain ⟨hecard, x, hx⟩ := mem_pairsMeeting.mp he
  exact mem_pairsMeeting.mpr
    ⟨hecard, x, Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx).1, hUV (Finset.mem_inter.mp hx).2⟩⟩

theorem pairCoverage_mono {U V : Finset P} (hUV : U ⊆ V) :
    pairCoverage U ≤ pairCoverage V :=
  Finset.card_le_card (pairsMeeting_mono hUV)

/-- A pair meets a union exactly when it meets at least one member. -/
theorem pairsMeeting_union (U V : Finset P) :
    pairsMeeting (U ∪ V) = pairsMeeting U ∪ pairsMeeting V := by
  ext e
  constructor
  · intro he
    obtain ⟨hecard, x, hx⟩ := mem_pairsMeeting.mp he
    have hxe : x ∈ e := (Finset.mem_inter.mp hx).1
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).2 with hxU | hxV
    · exact Finset.mem_union.mpr (Or.inl
        (mem_pairsMeeting.mpr ⟨hecard, x, Finset.mem_inter.mpr ⟨hxe, hxU⟩⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (mem_pairsMeeting.mpr ⟨hecard, x, Finset.mem_inter.mpr ⟨hxe, hxV⟩⟩))
  · intro he
    rcases Finset.mem_union.mp he with heU | heV
    · exact pairsMeeting_mono (Finset.subset_union_left) heU
    · exact pairsMeeting_mono (Finset.subset_union_right) heV

/-- A pair meeting an intersection meets each set separately. -/
theorem pairsMeeting_inter_subset (U V : Finset P) :
    pairsMeeting (U ∩ V) ⊆ pairsMeeting U ∩ pairsMeeting V := by
  intro e he
  exact Finset.mem_inter.mpr
    ⟨pairsMeeting_mono (Finset.inter_subset_left) he,
      pairsMeeting_mono (Finset.inter_subset_right) he⟩

/-- Pair coverage is a submodular set function. -/
theorem pairCoverage_submodular (U V : Finset P) :
    pairCoverage (U ∪ V) + pairCoverage (U ∩ V) ≤
      pairCoverage U + pairCoverage V := by
  have hle := Finset.card_le_card (pairsMeeting_inter_subset U V)
  have heq := Finset.card_union_add_card_inter (pairsMeeting U) (pairsMeeting V)
  unfold pairCoverage
  rw [pairsMeeting_union]
  omega

/-- For incomparable coalitions, pair coverage has at least one unit of
submodularity slack. The witness is a pair crossing their two differences. -/
theorem pairCoverage_strict_submodular (U V : Finset P)
    (hUV : ¬ U ⊆ V) (hVU : ¬ V ⊆ U) :
    pairCoverage (U ∪ V) + pairCoverage (U ∩ V) + 1 ≤
      pairCoverage U + pairCoverage V := by
  classical
  have hx_exists : ∃ x : P, x ∈ U ∧ x ∉ V := by
    by_contra h
    apply hUV
    intro x hxU
    by_contra hxV
    exact h ⟨x, hxU, hxV⟩
  have hy_exists : ∃ y : P, y ∈ V ∧ y ∉ U := by
    by_contra h
    apply hVU
    intro y hyV
    by_contra hyU
    exact h ⟨y, hyV, hyU⟩
  obtain ⟨x, hxU, hxV⟩ := hx_exists
  obtain ⟨y, hyV, hyU⟩ := hy_exists
  have hxy : x ≠ y := by
    intro h
    apply hxV
    simpa [h] using hyV
  let e : Finset P := {x, y}
  have hecard : e.card = 2 := by simp [e, hxy]
  have heU : e ∈ pairsMeeting U :=
    mem_pairsMeeting.mpr
      ⟨hecard, x, Finset.mem_inter.mpr ⟨by simp [e], hxU⟩⟩
  have heV : e ∈ pairsMeeting V :=
    mem_pairsMeeting.mpr
      ⟨hecard, y, Finset.mem_inter.mpr ⟨by simp [e], hyV⟩⟩
  have henot : e ∉ pairsMeeting (U ∩ V) := by
    intro he
    obtain ⟨z, hz⟩ := (mem_pairsMeeting.mp he).2
    have hze : z ∈ e := (Finset.mem_inter.mp hz).1
    have hzU : z ∈ U := (Finset.mem_inter.mp (Finset.mem_inter.mp hz).2).1
    have hzV : z ∈ V := (Finset.mem_inter.mp (Finset.mem_inter.mp hz).2).2
    have hzxy : z = x ∨ z = y := by simpa [e] using hze
    rcases hzxy with hzx | hzy
    · subst z
      exact hxV hzV
    · subst z
      exact hyU hzU
  have hins : insert e (pairsMeeting (U ∩ V)) ⊆
      pairsMeeting U ∩ pairsMeeting V := by
    intro f hf
    rcases Finset.mem_insert.mp hf with hfe | hf
    · subst f
      exact Finset.mem_inter.mpr ⟨heU, heV⟩
    · exact pairsMeeting_inter_subset U V hf
  have hcard := Finset.card_le_card hins
  rw [Finset.card_insert_of_notMem henot] at hcard
  have heq := Finset.card_union_add_card_inter (pairsMeeting U) (pairsMeeting V)
  unfold pairCoverage
  rw [pairsMeeting_union]
  omega

/-- The pairs meeting a singleton are in bijection with its other possible
endpoints. This includes the one-participant case, when both sets are empty. -/
@[simp] theorem pairCoverage_singleton (p : P) :
    pairCoverage {p} = Fintype.card P - 1 := by
  have hcount : (Finset.univ.erase p).card = (pairsMeeting {p}).card := by
    refine Finset.card_bij (fun q _ => ({p, q} : Finset P)) ?_ ?_ ?_
    · intro q hq
      have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
      apply mem_pairsMeeting.mpr
      refine ⟨?_, p, ?_⟩
      · simp [Ne.symm hqp]
      · simp
    · intro q hq t ht heq
      have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
      have hqmem : q ∈ ({p, t} : Finset P) := by
        rw [← heq]
        simp
      simpa [hqp] using hqmem
    · intro e he
      obtain ⟨hecard, hinter⟩ := mem_pairsMeeting.mp he
      have hp : p ∈ e := by
        obtain ⟨x, hx⟩ := hinter
        have hxp : x = p := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).2
        exact hxp ▸ (Finset.mem_inter.mp hx).1
      obtain ⟨x, y, hxy, heq⟩ := Finset.card_eq_two.mp hecard
      have hpxy : p = x ∨ p = y := by simpa [heq] using hp
      rcases hpxy with hpx | hpy
      · subst x
        exact ⟨y, Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ _⟩,
          heq.symm⟩
      · subst y
        refine ⟨x, Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ _⟩, ?_⟩
        rw [heq]
        ext z
        simp [or_comm]
  calc
    pairCoverage {p} = (Finset.univ.erase p).card := hcount.symm
    _ = Fintype.card P - 1 := by simp

end BoundedArity
