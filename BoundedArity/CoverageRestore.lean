module

public import BoundedArity.TypeInterface
public import BoundedArity.CoverageBlocks
public import BoundedArity.ClauseAssemblyCount
public import BoundedArity.FormalTable

/-!
# Restoring physical coverage after membership-type compression

Choose one representative of each occurring type. Retain precisely the
private coordinates of nonrepresentatives and the pair coordinates whose
two endpoints are not both representatives. The retained coordinates form
an explicit independent linear model; their rank restores the full physical
table on every queried union.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators Classical

section GenericCounts

variable {E P : Type*} [Fintype E] [Fintype P]
  [DecidableEq E] [DecidableEq P]

/-- The physical representatives of the compressed participants. -/
def representativeSet (f : E → P) : Finset P := Finset.univ.image f

/-- The retained private sources visible in a physical coalition. -/
def retainedPrivateSet (f : E → P) (U : Finset P) : Finset P :=
  U \ representativeSet f

/-- The retained unordered pair sources visible in a physical coalition. -/
def retainedPairSet (f : E → P) (U : Finset P) : Finset (Finset P) :=
  (pairsMeeting U).filter (fun e => ¬ e ⊆ representativeSet f)

/-- The explicit count of retained independent coordinates. -/
def retainedCount (f : E → P) (b : ℕ) (U : Finset P) : ℕ :=
  (retainedPrivateSet f U).card + b * (retainedPairSet f U).card

omit [Fintype P] [DecidableEq E] in
@[simp] theorem mem_representativeSet (f : E → P) (p : P) :
    p ∈ representativeSet f ↔ ∃ t, f t = p := by
  simp [representativeSet]

omit [Fintype P] [DecidableEq E] in
theorem representative_inter_eq_image (f : E → P)
    (U : Finset P) (V : Finset E)
    (hUV : ∀ t, f t ∈ U ↔ t ∈ V) :
    U ∩ representativeSet f = V.image f := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpU, hpR⟩ := Finset.mem_inter.mp hp
    obtain ⟨t, rfl⟩ := (mem_representativeSet f p).mp hpR
    exact Finset.mem_image.mpr ⟨t, (hUV t).mp hpU, rfl⟩
  · intro hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_inter.mpr
      ⟨(hUV t).mpr ht, (mem_representativeSet f (f t)).mpr ⟨t, rfl⟩⟩

omit [Fintype P] [DecidableEq E] in
theorem private_coverage_restore (f : E → P) (hf : Function.Injective f)
    (U : Finset P) (V : Finset E)
    (hUV : ∀ t, f t ∈ U ↔ t ∈ V) :
    V.card + (retainedPrivateSet f U).card = U.card := by
  have h := Finset.card_inter_add_card_sdiff U (representativeSet f)
  rw [representative_inter_eq_image f U V hUV,
    Finset.card_image_of_injective V hf] at h
  exact h

omit [Fintype E] [Fintype P] in
theorem image_meets_iff (f : E → P)
    (U : Finset P) (V e : Finset E)
    (hUV : ∀ t, f t ∈ U ↔ t ∈ V) :
    (e.image f ∩ U).Nonempty ↔ (e ∩ V).Nonempty := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨hpE, hpU⟩ := Finset.mem_inter.mp hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hpE
    exact ⟨t, Finset.mem_inter.mpr ⟨ht, (hUV t).mp hpU⟩⟩
  · rintro ⟨t, ht⟩
    obtain ⟨htE, htV⟩ := Finset.mem_inter.mp ht
    exact ⟨f t, Finset.mem_inter.mpr
      ⟨Finset.mem_image_of_mem f htE, (hUV t).mpr htV⟩⟩

/-- The removed pairs are in bijection with pairs of compressed participants. -/
theorem removed_pairs_card (f : E → P) (hf : Function.Injective f)
    (U : Finset P) (V : Finset E)
    (hUV : ∀ t, f t ∈ U ↔ t ∈ V) :
    ((pairsMeeting U).filter (fun e => e ⊆ representativeSet f)).card =
      pairCoverage V := by
  symm
  unfold pairCoverage
  refine Finset.card_bij (fun e _ => e.image f) ?_ ?_ ?_
  · intro e he
    obtain ⟨hecard, heV⟩ := mem_pairsMeeting.mp he
    apply Finset.mem_filter.mpr
    constructor
    · exact mem_pairsMeeting.mpr
        ⟨by rw [Finset.card_image_of_injective e hf]; exact hecard,
          (image_meets_iff f U V e hUV).mpr heV⟩
    · intro p hp
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hp
      exact (mem_representativeSet f (f t)).mpr ⟨t, rfl⟩
  · intro e _ e' _ heq
    exact Finset.image_injective hf heq
  · intro e he
    obtain ⟨hePairs, heSub⟩ := Finset.mem_filter.mp he
    obtain ⟨heCard, heU⟩ := mem_pairsMeeting.mp hePairs
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp heCard
    obtain ⟨t, ht⟩ := (mem_representativeSet f p).mp (heSub (by simp))
    obtain ⟨u, hu⟩ := (mem_representativeSet f q).mp (heSub (by simp))
    have htu : t ≠ u := by
      intro h
      apply hpq
      rw [← ht, ← hu, h]
    have himage : ({t, u} : Finset E).image f = {p, q} := by
      simp [ht, hu]
    refine ⟨{t, u}, mem_pairsMeeting.mpr ⟨by simp [htu], ?_⟩, himage⟩
    apply (image_meets_iff f U V {t, u} hUV).mp
    simpa only [himage] using heU

/-- Pair coverage splits into removed representative pairs and retained pairs. -/
theorem pair_coverage_restore (f : E → P) (hf : Function.Injective f)
    (U : Finset P) (V : Finset E)
    (hUV : ∀ t, f t ∈ U ↔ t ∈ V) :
    pairCoverage V + (retainedPairSet f U).card = pairCoverage U := by
  have h := Finset.card_filter_add_card_filter_not
    (s := pairsMeeting U) (fun e => e ⊆ representativeSet f)
  rw [removed_pairs_card f hf U V hUV] at h
  exact h

/-- D24's rank restoration identity is the count of explicit retained sources. -/
theorem physicalTable_restore (f : E → P) (hf : Function.Injective f)
    (b : ℕ) (U : Finset P) (V : Finset E)
    (hUV : ∀ t, f t ∈ U ↔ t ∈ V) :
    physicalTable b V + retainedCount f b U = physicalTable b U := by
  unfold physicalTable retainedCount
  calc
    V.card + b * pairCoverage V +
        ((retainedPrivateSet f U).card + b * (retainedPairSet f U).card) =
      (V.card + (retainedPrivateSet f U).card) +
        b * (pairCoverage V + (retainedPairSet f U).card) := by ring
    _ = U.card + b * pairCoverage U := by
      rw [private_coverage_restore f hf U V hUV,
        pair_coverage_restore f hf U V hUV]

end GenericCounts

section RetainedModel

variable {E P : Type*} [Fintype E] [Fintype P]
  [DecidableEq E] [DecidableEq P]

/-- Private blocks and unordered-pair blocks in the retained construction. -/
abbrev RetainedIndex (P : Type*) [Fintype P] [DecidableEq P] :=
  P ⊕ ParticipantPair P

def retainedBlockDim (f : E → P) (b : ℕ) : RetainedIndex P → ℕ
  | Sum.inl p => if p ∈ representativeSet f then 0 else 1
  | Sum.inr e => if e.val ⊆ representativeSet f then 0 else b

def retainedBlockHolders : RetainedIndex P → Finset P
  | Sum.inl p => {p}
  | Sum.inr e => e.val

abbrev RetainedAmbient (K : Type*) (f : E → P) (b : ℕ) :=
  (d : RetainedIndex P) → (Fin (retainedBlockDim f b d) → K)

/-- Every physical participant observes precisely the retained blocks it holds. -/
noncomputable def retainedShares (K : Type*) [Field K]
    (f : E → P) (b : ℕ) (p : P) : Submodule K (RetainedAmbient K f b) :=
  Submodule.pi Set.univ (fun d =>
    heldSpace K (retainedBlockHolders d) (retainedBlockDim f b d) p)

omit [DecidableEq E] in
theorem sum_retained_private (f : E → P) (U : Finset P) :
    (∑ p : P, if p ∈ U then (if p ∈ representativeSet f then 0 else 1) else 0) =
      (retainedPrivateSet f U).card := by
  have hpoint : ∀ p : P,
      (if p ∈ U then (if p ∈ representativeSet f then 0 else 1) else 0) =
        if p ∈ retainedPrivateSet f U then 1 else 0 := by
    intro p
    by_cases hU : p ∈ U <;> by_cases hR : p ∈ representativeSet f <;>
      simp [retainedPrivateSet, hU, hR]
  simp_rw [hpoint]
  simp

omit [DecidableEq E] in
theorem sum_retained_pairs (f : E → P) (b : ℕ) (U : Finset P) :
    (∑ e : ParticipantPair P,
      if (U ∩ e.val).Nonempty then
        (if e.val ⊆ representativeSet f then 0 else b) else 0) =
      b * (retainedPairSet f U).card := by
  rw [Finset.sum_coe_sort (Finset.univ.powersetCard 2)
    (fun e => if (U ∩ e).Nonempty then
      (if e ⊆ representativeSet f then 0 else b) else 0)]
  calc
    (∑ e ∈ Finset.univ.powersetCard 2,
      if (U ∩ e).Nonempty then
        (if e ⊆ representativeSet f then 0 else b) else 0) =
        ∑ _e ∈ retainedPairSet f U, b := by
      unfold retainedPairSet pairsMeeting
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hU : (U ∩ e).Nonempty <;>
        by_cases hR : e ⊆ representativeSet f <;>
        simp [hU, hR, Finset.inter_comm e U]
    _ = b * (retainedPairSet f U).card := by simp [Nat.mul_comm]

omit [DecidableEq E] in
/-- Retained rank is proved from an explicit independent-coordinate model. -/
theorem retainedShares_joint_finrank (K : Type*) [Field K]
    (f : E → P) (b : ℕ) (U : Finset P) :
    Module.finrank K (jointSubspace (retainedShares K f b) U) =
      retainedCount f b U := by
  unfold retainedShares
  rw [jointSubspace_pi, finrank_piSubmodule]
  simp only [Fintype.sum_sum_type]
  change
    (∑ p : P, Module.finrank K
      (jointSubspace (heldSpace K {p} (if p ∈ representativeSet f then 0 else 1)) U)) +
    (∑ e : ParticipantPair P, Module.finrank K
      (jointSubspace (heldSpace K e.val (if e.val ⊆ representativeSet f then 0 else b)) U)) =
    retainedCount f b U
  simp_rw [heldSpace_joint_finrank, inter_singleton_nonempty_iff]
  rw [sum_retained_private, sum_retained_pairs]
  rfl

omit [DecidableEq E] in
/-- The retained profile has one common finite-dimensional representation. -/
theorem retainedCount_linearlyRepresentable (K : Type*) [Field K]
    (f : E → P) (b : ℕ) : LinearRankRealizes K (retainedCount f b) := by
  apply linearRankRealizes_of_finiteDimensional (retainedShares K f b)
  intro U
  exact (retainedShares_joint_finrank K f b U).symm

end RetainedModel

/-- With no representatives, every ordinary coverage source is retained. -/
@[simp] theorem retainedCount_empty {P : Type*} [Fintype P] [DecidableEq P]
    (f : Empty → P) (b : ℕ) (U : Finset P) :
    retainedCount f b U = physicalTable b U := by
  have h := physicalTable_restore f (by intro x; cases x) b U ∅
    (by intro x; cases x)
  simpa using h

section TypeRepresentatives

variable {P G : Type*} [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- A physical representative is chosen for each occurring membership type. -/
noncomputable def typeRepresentative (B : G → Finset P) (t : OccurringType B) : P :=
  Classical.choose ((mem_occurringTypes B).mp t.property).1

@[simp] theorem membershipType_typeRepresentative (B : G → Finset P)
    (t : OccurringType B) : membershipType B (typeRepresentative B t) = t.val :=
  Classical.choose_spec ((mem_occurringTypes B).mp t.property).1

theorem typeRepresentative_injective (B : G → Finset P) :
    Function.Injective (typeRepresentative B) := by
  intro t u h
  apply Subtype.ext
  have ht := membershipType_typeRepresentative B t
  have hu := membershipType_typeRepresentative B u
  rw [h] at ht
  exact ht.symm.trans hu

/-- A representative is visible precisely when its membership type is visible. -/
theorem representative_mem_physicalUnion_iff (B : G → Finset P)
    (I : Finset G) (t : OccurringType B) :
    typeRepresentative B t ∈ physicalUnion B I ↔ t ∈ visibleTypeSet B I := by
  rw [mem_visibleTypeSet_iff_val, ← membershipType_typeRepresentative B t]
  exact (membershipType_mem_visibleTypes_iff B).symm

/-- The retained sources restore the physical profile on every group union. -/
theorem type_coverage_restore (B : G → Finset P) (b : ℕ) (I : Finset G) :
    physicalTable b (visibleTypeSet B I) +
      retainedCount (typeRepresentative B) b (physicalUnion B I) =
        physicalTable b (physicalUnion B I) :=
  physicalTable_restore (typeRepresentative B) (typeRepresentative_injective B)
    b (physicalUnion B I) (visibleTypeSet B I)
    (representative_mem_physicalUnion_iff B I)

end TypeRepresentatives

end BoundedArity
