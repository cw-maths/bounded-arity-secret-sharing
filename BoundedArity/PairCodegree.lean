module

public import BoundedArity.Interpolation
public import Mathlib.Combinatorics.SetFamily.LYM

/-!
# The pair-codegree bound

This file formalises the Pair codegree lemma in Section 4 of Christopher
Williamson's 16 November 2026 expanded review draft. A pair of distinct,
nonempty occurring membership types belongs to at most
`Nat.choose (r - 2) ((r - 2) / 2)` distinct interpolation clauses.

The proof restricts maximal unauthorized index sets to the complement of the
two types' union, applies Sperner's theorem on that smaller ground set, and
uses the fact that taking the image that defines the clauses removes rather
than adds duplicates.
-/

@[expose] public section

namespace BoundedArity

/-- The largest binomial coefficient in a row is nondecreasing with the row. -/
theorem middle_choose_mono : Monotone (fun n : ℕ => n.choose (n / 2)) := by
  intro m n hmn
  exact (Nat.choose_le_choose (m / 2) hmn).trans (Nat.choose_le_middle (m / 2) n)

/-- Sperner's bound for an antichain whose members are subsets of one finite
ground set E, without requiring the whole ambient type to have size |E|. -/
theorem card_le_middle_choose_of_antichain_subsets {G : Type*}
    (E : Finset G) (A : Finset (Finset G))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset G)))
    (hsub : ∀ I ∈ A, I ⊆ E) :
    A.card ≤ E.card.choose (E.card / 2) := by
  classical
  let f : Finset G → Finset E := fun I => I.subtype (fun j => j ∈ E)
  have hreflect {I J : Finset G} (hI : I ∈ A) (hIJ : f I ⊆ f J) : I ⊆ J := by
    intro j hj
    have hjE : j ∈ E := hsub I hI hj
    have hjI : (⟨j, hjE⟩ : E) ∈ f I := by simpa [f] using hj
    have hjJ := hIJ hjI
    simpa [f] using hjJ
  have hinj : Set.InjOn f (A : Set (Finset G)) := by
    intro I hI J hJ heq
    apply Finset.Subset.antisymm
    · apply hreflect hI
      rw [heq]
    · apply hreflect hJ
      rw [heq]
  have himage : IsAntichain (· ⊆ ·) (A.image f : Set (Finset E)) := by
    intro s hs t ht hst hsubset
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp ht
    have hIJ : I = J := hA.eq hI hJ (hreflect hI hsubset)
    exact hst (congrArg f hIJ)
  have hbound := himage.sperner
  rw [Finset.card_image_of_injOn hinj] at hbound
  simpa using hbound

/-- Two distinct nonempty finite sets have a union with at least two members. -/
theorem two_le_card_union_of_nonempty_ne {G : Type*} [DecidableEq G]
    {t u : Finset G} (ht : t.Nonempty) (hu : u.Nonempty) (hne : t ≠ u) :
    2 ≤ (t ∪ u).card := by
  by_contra hsmall
  have hcard : (t ∪ u).card ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hsmall)
  have heq := Finset.card_le_one.mp hcard
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hu
  apply hne
  ext j
  constructor
  · intro hj
    have hjb : j = b := heq j (Finset.mem_union_left u hj) b (Finset.mem_union_right t hb)
    rw [hjb]
    exact hb
  · intro hj
    have hja : j = a := heq j (Finset.mem_union_right t hj) a (Finset.mem_union_left u ha)
    rw [hja]
    exact ha

variable {P G : Type*} [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]
  (B : G → Finset P) (Γ : AccessStructure P)

omit [DecidableEq G] in
/-- The maximal unauthorized group-index sets form an antichain. -/
theorem maximalUnauthorized_isAntichain :
    IsAntichain (· ⊆ ·) (maximalUnauthorized B Γ : Set (Finset G)) := by
  intro I hI J hJ hne hIJ
  exact hne (maximalUnauthorized_no_strict_inclusion B Γ hI hJ hIJ)

/-- A clause contains two occurring types precisely when its index set avoids
their union. -/
theorem pair_mem_clause_iff_subset_compl {t u I : Finset G}
    (ht : t ∈ occurringTypes B) (hu : u ∈ occurringTypes B) :
    (t ∈ clause B I ∧ u ∈ clause B I) ↔ I ⊆ (t ∪ u)ᶜ := by
  constructor
  · rintro ⟨htD, huD⟩ j hj
    apply Finset.mem_compl.mpr
    intro hjtu
    rcases Finset.mem_union.mp hjtu with hjt | hju
    · exact (Finset.mem_sdiff.mp htD).2
        ((mem_visibleTypes B).mpr ⟨ht, ⟨j, Finset.mem_inter.mpr ⟨hjt, hj⟩⟩⟩)
    · exact (Finset.mem_sdiff.mp huD).2
        ((mem_visibleTypes B).mpr ⟨hu, ⟨j, Finset.mem_inter.mpr ⟨hju, hj⟩⟩⟩)
  · intro hI
    constructor
    · apply Finset.mem_sdiff.mpr
      refine ⟨ht, ?_⟩
      intro htV
      obtain ⟨j, hj⟩ := ((mem_visibleTypes B).mp htV).2
      have hj' := Finset.mem_inter.mp hj
      exact (Finset.mem_compl.mp (hI hj'.2)) (Finset.mem_union_left u hj'.1)
    · apply Finset.mem_sdiff.mpr
      refine ⟨hu, ?_⟩
      intro huV
      obtain ⟨j, hj⟩ := ((mem_visibleTypes B).mp huV).2
      have hj' := Finset.mem_inter.mp hj
      exact (Finset.mem_compl.mp (hI hj'.2)) (Finset.mem_union_right t hj'.1)

/-- The distinct interpolation clauses containing both specified types. -/
noncomputable def clausesContainingPair (t u : Finset G) :
    Finset (Finset (Finset G)) :=
  (clauses B Γ).filter (fun D => t ∈ D ∧ u ∈ D)

/-- Counting distinct clauses cannot exceed counting their maximal
unauthorized preimages. The preimages that matter lie in the complement
of the two types' union. -/
theorem card_clausesContainingPair_le_restricted_maximal {t u : Finset G}
    (ht : t ∈ occurringTypes B) (hu : u ∈ occurringTypes B) :
    (clausesContainingPair B Γ t u).card ≤
      ((maximalUnauthorized B Γ).filter (fun I => I ⊆ (t ∪ u)ᶜ)).card := by
  classical
  let M := (maximalUnauthorized B Γ).filter (fun I => I ⊆ (t ∪ u)ᶜ)
  have hsub : clausesContainingPair B Γ t u ⊆ M.image (clause B) := by
    intro D hD
    have hD' := Finset.mem_filter.mp hD
    obtain ⟨I, hI, hclause⟩ := (mem_clauses B Γ).mp hD'.1
    apply Finset.mem_image.mpr
    refine ⟨I, ?_, hclause⟩
    apply Finset.mem_filter.mpr
    refine ⟨hI, ?_⟩
    apply (pair_mem_clause_iff_subset_compl B ht hu).mp
    simpa only [hclause] using hD'.2
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

/-- The manuscript's Pair codegree lemma: each pair of distinct occurring
types belongs to at most the central binomial coefficient for r - 2 labels.
No extra assumption r ≥ 2 is needed: it follows from the existence of the
two distinct nonempty types. -/
theorem pair_codegree_le {t u : Finset G}
    (ht : t ∈ occurringTypes B) (hu : u ∈ occurringTypes B) (hne : t ≠ u) :
    (clausesContainingPair B Γ t u).card ≤
      (Fintype.card G - 2).choose ((Fintype.card G - 2) / 2) := by
  classical
  let E := (t ∪ u)ᶜ
  let M := (maximalUnauthorized B Γ).filter (fun I => I ⊆ E)
  have hanti : IsAntichain (· ⊆ ·) (M : Set (Finset G)) := by
    apply (maximalUnauthorized_isAntichain B Γ).subset
    intro I hI
    exact (Finset.mem_filter.mp hI).1
  have hSperner : M.card ≤ E.card.choose (E.card / 2) :=
    card_le_middle_choose_of_antichain_subsets E M hanti
      (fun I hI => (Finset.mem_filter.mp hI).2)
  have htwo : 2 ≤ (t ∪ u).card :=
    two_le_card_union_of_nonempty_ne
      ((mem_occurringTypes B).mp ht).2 ((mem_occurringTypes B).mp hu).2 hne
  have hE : E.card ≤ Fintype.card G - 2 := by
    dsimp [E]
    rw [Finset.card_compl]
    exact Nat.sub_le_sub_left htwo (Fintype.card G)
  exact (card_clausesContainingPair_le_restricted_maximal B Γ ht hu).trans
    (hSperner.trans (middle_choose_mono hE))

end BoundedArity
