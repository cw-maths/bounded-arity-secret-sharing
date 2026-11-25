module

public import BoundedArity.DifferenceSpace
public import BoundedArity.SecretRank
public import BoundedArity.ClauseAssemblyCount

/-!
# An exact one-clause model over every field

Give each unordered pair one coordinate. A participant's residual share is
spanned by differences of its incident pair coordinates. Any two stars meet,
so a coalition's residual span is the zero-sum hyperplane on all pairs it
meets. Appending the same independent key gives exactly the pair-coverage
rank. This construction works in every characteristic, including two.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators

section PairStars

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The pair coordinates incident to a specified participant. -/
def pairStar (i : E) : Finset (ParticipantPair E) :=
  Finset.univ.filter (fun e => i ∈ e.val)

@[simp] theorem mem_pairStar (i : E) (e : ParticipantPair E) :
    e ∈ pairStar i ↔ i ∈ e.val := by
  simp [pairStar]

/-- The actual pair coordinates seen by a coalition. -/
def pairCoordinatesMet (U : Finset E) : Finset (ParticipantPair E) :=
  Finset.univ.filter (fun e => (e.val ∩ U).Nonempty)

@[simp] theorem mem_pairCoordinatesMet (U : Finset E) (e : ParticipantPair E) :
    e ∈ pairCoordinatesMet U ↔ (e.val ∩ U).Nonempty := by
  simp [pairCoordinatesMet]

/-- Coordinate subtyping preserves the already verified pair count. -/
theorem pairCoordinatesMet_card (U : Finset E) :
    (pairCoordinatesMet U).card = pairCoverage U := by
  unfold pairCoverage
  refine Finset.card_bij (fun e _ => e.val) ?_ ?_ ?_
  · intro e he
    exact mem_pairsMeeting.mpr ⟨participantPair_card e,
      (mem_pairCoordinatesMet U e).mp he⟩
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro e he
    obtain ⟨hc, hm⟩ := mem_pairsMeeting.mp he
    let e' : ParticipantPair E := ⟨e, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hc⟩⟩
    exact ⟨e', (mem_pairCoordinatesMet U e').mpr hm, rfl⟩

theorem pairStar_subset_met {i : E} {U : Finset E} (hi : i ∈ U) :
    pairStar i ⊆ pairCoordinatesMet U := by
  intro e he
  exact (mem_pairCoordinatesMet U e).mpr
    ⟨i, Finset.mem_inter.mpr ⟨(mem_pairStar i e).mp he, hi⟩⟩

/-- Two different stars intersect at their common unordered pair. -/
theorem pairStars_inter_nonempty {i j : E} (hij : i ≠ j) :
    (pairStar i ∩ pairStar j).Nonempty := by
  let e : ParticipantPair E := ⟨{i, j}, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, Finset.card_pair hij⟩⟩
  refine ⟨e, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩ <;> simp [pairStar, e]

/-- A nonempty coalition meets at least one pair when there are two members. -/
theorem pairCoordinatesMet_nonempty (hm : 2 ≤ Fintype.card E)
    {U : Finset E} (hU : U.Nonempty) : (pairCoordinatesMet U).Nonempty := by
  obtain ⟨i, hi⟩ := hU
  have hcard : 1 < (Finset.univ : Finset E).card := by
    simpa only [Finset.card_univ] using (show 1 < Fintype.card E by omega)
  obtain ⟨j, _, hji⟩ := Finset.exists_mem_ne hcard i
  obtain ⟨e, he⟩ := pairStars_inter_nonempty hji.symm
  exact ⟨e, pairStar_subset_met hi (Finset.mem_inter.mp he).1⟩

/-- Every difference of covered coordinates can pass through the pair
joining their two observing participants. -/
theorem jointSubspace_pairDifferences (K : Type*) [Field K]
    (U : Finset E) :
    jointSubspace (fun i => differenceSpace K (pairStar i)) U =
      differenceSpace K (pairCoordinatesMet U) := by
  classical
  apply le_antisymm
  · unfold jointSubspace
    exact iSup_le (fun i => iSup_le (fun hi =>
      differenceSpace_mono K (pairStar_subset_met hi)))
  · apply Submodule.span_le.mpr
    rintro v ⟨e, he, f, hf, rfl⟩
    obtain ⟨i, hi⟩ := (mem_pairCoordinatesMet U e).mp he
    obtain ⟨hie, hiU⟩ := Finset.mem_inter.mp hi
    obtain ⟨j, hj⟩ := (mem_pairCoordinatesMet U f).mp hf
    obtain ⟨hjf, hjU⟩ := Finset.mem_inter.mp hj
    have heStar : e ∈ pairStar i := (mem_pairStar i e).mpr hie
    have hfStar : f ∈ pairStar j := (mem_pairStar j f).mpr hjf
    by_cases hij : i = j
    · subst j
      exact le_jointSubspace _ U hiU (differenceSpace_generator K (pairStar i) heStar hfStar)
    · obtain ⟨q, hq⟩ := pairStars_inter_nonempty hij
      have h1 := le_jointSubspace (fun k => differenceSpace K (pairStar k)) U hiU
        (differenceSpace_generator K (pairStar i) heStar (Finset.mem_inter.mp hq).1)
      have h2 := le_jointSubspace (fun k => differenceSpace K (pairStar k)) U hjU
        (differenceSpace_generator K (pairStar j) (Finset.mem_inter.mp hq).2 hfStar)
      simpa only [sub_add_sub_cancel, SetLike.mem_coe] using
        (jointSubspace (fun k => differenceSpace K (pairStar k)) U).add_mem h1 h2

end PairStars

section CommonKey

variable {K E : Type*} [Field K] [Fintype E] [DecidableEq E]

abbrev ExactClauseAmbient (K E : Type*) [Fintype E] [DecidableEq E] :=
  K × (ParticipantPair E → K)

/-- A common independent scalar and the residual differences at this star. -/
noncomputable def exactClauseShare (i : E) : Submodule K (ExactClauseAmbient K E) :=
  Submodule.span K {(1, 0)} ⊔
    (differenceSpace K (pairStar i)).map (LinearMap.inr K K (ParticipantPair E → K))

theorem exactClause_joint_nonempty (U : Finset E) (hU : U.Nonempty) :
    jointSubspace (exactClauseShare (K := K)) U =
      Submodule.span K {(1, 0)} ⊔
        (differenceSpace K (pairCoordinatesMet U)).map
          (LinearMap.inr K K (ParticipantPair E → K)) := by
  classical
  unfold exactClauseShare jointSubspace
  rw [← sup_biSup hU]
  congr 1
  rw [← jointSubspace, jointSubspace_map, jointSubspace_pairDifferences]

/-- The common independent key contributes exactly one rank unit. -/
theorem exactClause_joint_finrank (hm : 2 ≤ Fintype.card E) (U : Finset E) :
    Module.finrank K (jointSubspace (exactClauseShare (K := K)) U) = pairCoverage U := by
  classical
  by_cases hU : U.Nonempty
  · rw [exactClause_joint_nonempty U hU]
    let L := differenceSpace K (pairCoordinatesMet U)
    let f := LinearMap.inr K K (ParticipantPair E → K)
    have hnot : ((1, 0) : ExactClauseAmbient K E) ∉ L.map f := by
      rintro ⟨x, hx, heq⟩
      have hh := congrArg Prod.fst heq
      simp [f] at hh
    rw [finrank_secret_sup, ite_eq_right hnot]
    have hr : Module.finrank K (L.map f) = Module.finrank K L :=
      (Submodule.equivMapOfInjective f (LinearMap.inr_injective) L).finrank_eq.symm
    rw [hr]
    exact (differenceSpace_finrank_add_one K (pairCoordinatesMet U)
      (pairCoordinatesMet_nonempty hm hU)).trans (pairCoordinatesMet_card U)
  · have h0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    simp

/-- The all-members exact model uses one coordinate change for the key and
all coalition observations. -/
theorem oneClause_exact_all_members (K : Type*) [Field K]
    (E : Type*) [Fintype E] [DecidableEq E] (hm : 2 ≤ Fintype.card E) :
    ∃ n : ℕ, ∃ key : Submodule K (Fin n → K),
      ∃ W : E → Submodule K (Fin n → K),
        Module.finrank K key = 1 ∧
        (∀ i, key ≤ W i) ∧
        (∀ U : Finset E,
          Module.finrank K (jointSubspace W U) =
            (Fintype.card E).choose 2 - (Fintype.card E - U.card).choose 2) := by
  classical
  let V := ExactClauseAmbient K E
  let key : Submodule K V := Submodule.span K {(1, 0)}
  let W : E → Submodule K V := exactClauseShare
  let e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, key.map e.toLinearMap,
    fun i => (W i).map e.toLinearMap, ?_, ?_, ?_⟩
  · rw [e.finrank_map_eq]
    apply finrank_span_singleton
    intro h
    have hh := congrArg Prod.fst h
    simp at hh
  · intro i
    exact Submodule.map_mono le_sup_left
  · intro U
    rw [jointSubspace_finrank_map]
    exact (exactClause_joint_finrank hm U).trans (pairCoverage_eq_choose_sub U)

end CommonKey

/-- Exact T4 ingredient over every prescribed field. There is no field-size
or characteristic hypothesis, and the representation is not scaled. -/
theorem oneClause_exact_checkpoint {K E : Type*} [Field K] [DecidableEq E]
    (C : Finset E) (hm : 2 ≤ C.card) : OneClauseRealizes K C := by
  classical
  have hm' : 2 ≤ Fintype.card C := by simpa only [Fintype.card_coe] using hm
  obtain ⟨n, key, W, hkey, hle, hrank⟩ := oneClause_exact_all_members K C hm'
  refine ⟨n, key, extendClauseShares C W, hkey, ?_, ?_, ?_⟩
  · intro p hp
    simp [extendClauseShares, hp]
  · intro p hp
    simpa only [extendClauseShares, dite_eq_left hp] using hle ⟨p, hp⟩
  · intro U
    rw [jointSubspace_extendClauseShares, hrank]
    simp only [Fintype.card_coe, clauseCoalition_card]
    unfold clausePairCoverage
    have hdiff : C.card - (C ∩ U).card = (C \ U).card := by
      have h := Finset.card_sdiff_add_card_inter C U
      omega
    rw [hdiff]

end BoundedArity
