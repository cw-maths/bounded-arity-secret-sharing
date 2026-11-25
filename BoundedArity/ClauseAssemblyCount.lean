module

public import BoundedArity.ClauseCount
public import Mathlib.Tactic

/-!
# Clause incidence and pair-padding counts

The clauses form a finset, so a singleton clause occurs at most once.
Every pair is an unordered two-element finset. Double counting the
clause/pair incidences gives the physical rank identity in T5.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators

variable {E : Type*} [DecidableEq E]

/-- D21: a coalition is authorised precisely when it meets every clause. -/
def HitsAll (Cs : Finset (Finset E)) (U : Finset E) : Prop :=
  ∀ C ∈ Cs, (U ∩ C).Nonempty

/-- D21: the number of clauses containing both specified participants. -/
def clausePairCount (Cs : Finset (Finset E)) (i j : E) : ℕ :=
  (Cs.filter (fun C => i ∈ C ∧ j ∈ C)).card

/-- D23: additional copies of one scalar for this pair. -/
def paddingCount (Cs : Finset (Finset E)) (b : ℕ) (i j : E) : ℕ :=
  b - clausePairCount Cs i j

/-- Clauses whose keys need their own one-clause component. -/
def nonsingletonClauses (Cs : Finset (Finset E)) : Finset (Finset E) :=
  Cs.filter (fun C => 2 ≤ C.card)

omit [DecidableEq E] in
@[simp] theorem mem_nonsingletonClauses (Cs : Finset (Finset E)) (C : Finset E) :
    C ∈ nonsingletonClauses Cs ↔ C ∈ Cs ∧ 2 ≤ C.card := by
  simp [nonsingletonClauses]

/-- The incidence multiplicity of an unordered pair. -/
def pairMultiplicity (Cs : Finset (Finset E)) (e : Finset E) : ℕ :=
  (Cs.filter (fun C => e ⊆ C)).card

@[simp] theorem pairMultiplicity_pair (Cs : Finset (Finset E)) (i j : E) :
    pairMultiplicity Cs {i, j} = clausePairCount Cs i j := by
  unfold pairMultiplicity clausePairCount
  congr 1
  ext C
  simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]

theorem pairMultiplicity_le_of_card_two (Cs : Finset (Finset E)) (b : ℕ)
    (hb : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b)
    (e : Finset E) (he : e.card = 2) : pairMultiplicity Cs e ≤ b := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp he
  simpa only [pairMultiplicity_pair] using hb i j hij

theorem hitsAll_mono (Cs : Finset (Finset E)) {U V : Finset E}
    (hUV : U ⊆ V) (hU : HitsAll Cs U) : HitsAll Cs V := by
  intro C hC
  obtain ⟨p, hp⟩ := hU C hC
  exact ⟨p, Finset.mem_inter.mpr
    ⟨hUV (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩⟩

theorem not_hitsAll_empty (Cs : Finset (Finset E)) (hCs : Cs.Nonempty) :
    ¬ HitsAll Cs ∅ := by
  intro h
  obtain ⟨C, hC⟩ := hCs
  simpa using h C hC

/-- Singleton clauses use exactly their holder's private coordinate. -/
theorem hitsAll_iff_nonsingletons_singletons (Cs : Finset (Finset E))
    (U : Finset E) (hCs : ∀ C ∈ Cs, C.Nonempty) :
    HitsAll Cs U ↔
      (∀ C ∈ nonsingletonClauses Cs, (U ∩ C).Nonempty) ∧
      (∀ p : E, {p} ∈ Cs → p ∈ U) := by
  constructor
  · intro h
    constructor
    · intro C hC
      exact h C (mem_nonsingletonClauses Cs C |>.mp hC).1
    · intro p hp
      obtain ⟨x, hx⟩ := h {p} hp
      have hxp : x = p := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).2
      exact hxp ▸ (Finset.mem_inter.mp hx).1
  · rintro ⟨hnon, hsingle⟩ C hC
    by_cases hcard : 2 ≤ C.card
    · exact hnon C ((mem_nonsingletonClauses Cs C).mpr ⟨hC, hcard⟩)
    · have hpos := Finset.card_pos.mpr (hCs C hC)
      have hone : C.card = 1 := by omega
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hone
      exact ⟨p, Finset.mem_inter.mpr ⟨hsingle p hC, Finset.mem_singleton_self p⟩⟩

theorem hitsAll_iff_nonsingletons_singletons_subtype (Cs : Finset (Finset E))
    (U : Finset E) (hCs : ∀ C ∈ Cs, C.Nonempty) :
    HitsAll Cs U ↔
      (∀ C : nonsingletonClauses Cs, (U ∩ C.val).Nonempty) ∧
      (∀ p : E, {p} ∈ Cs → p ∈ U) := by
  simpa only [Subtype.forall] using hitsAll_iff_nonsingletons_singletons Cs U hCs

theorem clausePairCoverage_eq_zero_of_card_lt_two (C U : Finset E)
    (hC : C.card < 2) : clausePairCoverage C U = 0 := by
  simp [clausePairCoverage, Nat.choose_eq_zero_of_lt hC]

section FiniteParticipants

variable [Fintype E]

/-- Unordered pairs of distinct members of the ambient finite population. -/
abbrev ParticipantPair (E : Type*) [Fintype E] [DecidableEq E] :=
  {e : Finset E // e ∈ Finset.univ.powersetCard 2}

@[simp] theorem participantPair_card (e : ParticipantPair E) : e.val.card = 2 := by
  exact (Finset.mem_powersetCard.mp e.property).2

theorem pairMultiplicity_le (Cs : Finset (Finset E)) (b : ℕ)
    (hb : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b)
    (e : ParticipantPair E) : pairMultiplicity Cs e.val ≤ b :=
  pairMultiplicity_le_of_card_two Cs b hb e.val (participantPair_card e)

theorem hitsAll_univ (Cs : Finset (Finset E))
    (hCs : ∀ C ∈ Cs, C.Nonempty) : HitsAll Cs Finset.univ := by
  intro C hC
  simpa using hCs C hC

/-- Count the clause pairs by filtering the ambient pairs that meet U. -/
theorem clausePairCoverage_eq_card_filter_pairsMeeting (C U : Finset E) :
    clausePairCoverage C U = ((pairsMeeting U).filter (fun e => e ⊆ C)).card := by
  rw [clausePairCoverage_eq_card]
  congr 1
  ext e
  simp [pairsMeeting, Finset.mem_powersetCard, and_left_comm, and_comm]

theorem clausePairCoverage_eq_sum_pairsMeeting (C U : Finset E) :
    clausePairCoverage C U = ∑ e ∈ pairsMeeting U, if e ⊆ C then 1 else 0 := by
  rw [clausePairCoverage_eq_card_filter_pairsMeeting,
    Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Double counting: a pair contributes once for every clause containing it. -/
theorem sum_clausePairCoverage (Cs : Finset (Finset E)) (U : Finset E) :
    (∑ C ∈ Cs, clausePairCoverage C U) =
      ∑ e ∈ pairsMeeting U, pairMultiplicity Cs e := by
  simp_rw [clausePairCoverage_eq_sum_pairsMeeting]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [pairMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Empty and singleton clauses have zero pair-coverage contribution. -/
theorem sum_nonsingleton_clausePairCoverage (Cs : Finset (Finset E)) (U : Finset E) :
    (∑ C : nonsingletonClauses Cs, clausePairCoverage C.val U) =
      ∑ e ∈ pairsMeeting U, pairMultiplicity Cs e := by
  rw [Finset.sum_coe_sort (nonsingletonClauses Cs) (fun C => clausePairCoverage C U)]
  calc
    (∑ C ∈ nonsingletonClauses Cs, clausePairCoverage C U) =
        ∑ C ∈ Cs, clausePairCoverage C U := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hcard : C.card < 2 := by
        have : ¬ 2 ≤ C.card := by
          intro hc
          exact hnot ((mem_nonsingletonClauses Cs C).mpr ⟨hC, hc⟩)
        omega
      exact clausePairCoverage_eq_zero_of_card_lt_two C U hcard
    _ = ∑ e ∈ pairsMeeting U, pairMultiplicity Cs e := sum_clausePairCoverage Cs U

/-- Padding blocks are observed exactly when the coalition meets their pair. -/
theorem sum_pair_padding (Cs : Finset (Finset E)) (b : ℕ) (U : Finset E) :
    (∑ e : ParticipantPair E,
      if (U ∩ e.val).Nonempty then b - pairMultiplicity Cs e.val else 0) =
      ∑ e ∈ pairsMeeting U, (b - pairMultiplicity Cs e) := by
  rw [Finset.sum_coe_sort (Finset.univ.powersetCard 2)
    (fun e => if (U ∩ e).Nonempty then b - pairMultiplicity Cs e else 0)]
  unfold pairsMeeting
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Finset.inter_comm U e]

/-- The clause ranks plus the padding ranks give exactly b units per pair. -/
theorem clauseAssembly_pair_rank_sum (Cs : Finset (Finset E)) (b : ℕ)
    (U : Finset E) (hb : ∀ i j, i ≠ j → clausePairCount Cs i j ≤ b) :
    (∑ C : nonsingletonClauses Cs, clausePairCoverage C.val U) +
      (∑ e : ParticipantPair E,
        if (U ∩ e.val).Nonempty then b - pairMultiplicity Cs e.val else 0) =
      b * pairCoverage U := by
  rw [sum_nonsingleton_clausePairCoverage, sum_pair_padding,
    ← Finset.sum_add_distrib]
  calc
    (∑ e ∈ pairsMeeting U, (pairMultiplicity Cs e + (b - pairMultiplicity Cs e))) =
        ∑ _e ∈ pairsMeeting U, b := by
      apply Finset.sum_congr rfl
      intro e he
      exact Nat.add_sub_of_le
        (pairMultiplicity_le_of_card_two Cs b hb e (mem_pairsMeeting.mp he).1)
    _ = b * pairCoverage U := by simp [pairCoverage, Nat.mul_comm]

end FiniteParticipants

end BoundedArity
