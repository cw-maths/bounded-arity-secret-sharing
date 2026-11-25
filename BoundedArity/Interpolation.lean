module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset

/-!
# Interpolation of authorization on queried group unions

This file formalises the finite-set construction and the Interpolation lemma
in Section 4 of Christopher Williamson's expanded review draft of
"A Linear Barrier for Information Inequalities of Bounded Arity in Secret
Sharing", dated 16 November 2026.

`P` is the finite type of physical participants. `G` is a finite type of group
labels (the manuscript takes `G = Fin r`). `B j` is the physical part of group j.
Groups may be empty, repeated, or overlapping. No restriction is placed on
their sizes.

This module supplies the combinatorial interpolation lemma and its
prerequisites for the later local rank and entropy representations.
-/

@[expose] public section

namespace BoundedArity

/-- A proper monotone access structure on a finite participant type. -/
structure AccessStructure (P : Type*) [Fintype P] where
  Authorized : Finset P → Prop
  upward_closed : ∀ {U V : Finset P}, U ⊆ V → Authorized U → Authorized V
  empty_unauthorized : ¬ Authorized ∅
  univ_authorized : Authorized Finset.univ

variable {P G : Type*} [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- The physical part of a group on `Option P`; `none` denotes the secret. -/
def physicalPart (A : Finset (Option P)) : Finset P :=
  Finset.univ.filter (fun p => some p ∈ A)

@[simp] theorem mem_physicalPart {A : Finset (Option P)} {p : P} :
    p ∈ physicalPart A ↔ some p ∈ A := by
  simp [physicalPart]

variable (B : G → Finset P)

/-- `U_I`: all physical participants occurring in groups labelled by I. -/
def physicalUnion (I : Finset G) : Finset P := I.biUnion B

omit [Fintype P] [Fintype G] [DecidableEq G] in
@[simp] theorem mem_physicalUnion {I : Finset G} {p : P} :
    p ∈ physicalUnion B I ↔ ∃ j ∈ I, p ∈ B j := by
  simp [physicalUnion]

omit [Fintype P] [Fintype G] [DecidableEq G] in
@[simp] theorem physicalUnion_empty : physicalUnion B ∅ = ∅ := by
  simp [physicalUnion]

omit [Fintype P] [Fintype G] [DecidableEq G] in
theorem physicalUnion_mono {I J : Finset G} (hIJ : I ⊆ J) :
    physicalUnion B I ⊆ physicalUnion B J := by
  intro p hp
  obtain ⟨j, hj, hpj⟩ := (mem_physicalUnion B).mp hp
  exact (mem_physicalUnion B).mpr ⟨j, hIJ hj, hpj⟩

/-- `t(p)`: the group labels at which participant p occurs. -/
def membershipType (p : P) : Finset G :=
  Finset.univ.filter (fun j => p ∈ B j)

omit [Fintype P] [DecidableEq G] in
@[simp] theorem mem_membershipType {p : P} {j : G} :
    j ∈ membershipType B p ↔ p ∈ B j := by
  simp [membershipType]

/-- `T`: the distinct nonempty membership types actually present. -/
def occurringTypes : Finset (Finset G) :=
  (Finset.univ.image (membershipType B)).filter Finset.Nonempty

theorem mem_occurringTypes {t : Finset G} :
    t ∈ occurringTypes B ↔ (∃ p : P, membershipType B p = t) ∧ t.Nonempty := by
  simp [occurringTypes]

/-- `V_I`: the occurring types visible in at least one group labelled by I. -/
def visibleTypes (I : Finset G) : Finset (Finset G) :=
  (occurringTypes B).filter (fun t => (t ∩ I).Nonempty)

@[simp] theorem mem_visibleTypes {I t : Finset G} :
    t ∈ visibleTypes B I ↔ t ∈ occurringTypes B ∧ (t ∩ I).Nonempty := by
  simp [visibleTypes]

theorem visibleTypes_subset (I : Finset G) :
    visibleTypes B I ⊆ occurringTypes B := by
  intro t ht
  exact ((mem_visibleTypes B).mp ht).1

/-- A participant is visible exactly when its membership type is visible. -/
theorem membershipType_mem_visibleTypes_iff {p : P} {I : Finset G} :
    membershipType B p ∈ visibleTypes B I ↔ p ∈ physicalUnion B I := by
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := ((mem_visibleTypes B).mp hp).2
    have hj' := Finset.mem_inter.mp hj
    exact (mem_physicalUnion B).mpr
      ⟨j, hj'.2, (mem_membershipType B).mp hj'.1⟩
  · intro hp
    obtain ⟨j, hj, hpj⟩ := (mem_physicalUnion B).mp hp
    have hjt : j ∈ membershipType B p := (mem_membershipType B).mpr hpj
    apply (mem_visibleTypes B).mpr
    exact ⟨(mem_occurringTypes B).mpr ⟨⟨p, rfl⟩, ⟨j, hjt⟩⟩,
      ⟨j, Finset.mem_inter.mpr ⟨hjt, hj⟩⟩⟩

/-- Membership types preserve all inclusions between queried unions. -/
theorem visibleTypes_subset_iff {I J : Finset G} :
    visibleTypes B J ⊆ visibleTypes B I ↔
      physicalUnion B J ⊆ physicalUnion B I := by
  constructor
  · intro h p hp
    apply (membershipType_mem_visibleTypes_iff B).mp
    exact h ((membershipType_mem_visibleTypes_iff B).mpr hp)
  · intro h t ht
    have htT := ((mem_visibleTypes B).mp ht).1
    obtain ⟨p, hp⟩ := ((mem_occurringTypes B).mp htT).1
    subst t
    apply (membershipType_mem_visibleTypes_iff B).mpr
    exact h ((membershipType_mem_visibleTypes_iff B).mp ht)

theorem visibleTypes_mono {I J : Finset G} (hIJ : I ⊆ J) :
    visibleTypes B I ⊆ visibleTypes B J :=
  (visibleTypes_subset_iff B).mpr (physicalUnion_mono B hIJ)

@[simp] theorem visibleTypes_univ :
    visibleTypes B Finset.univ = occurringTypes B := by
  apply Finset.Subset.antisymm
  · exact visibleTypes_subset B _
  · intro t ht
    apply (mem_visibleTypes B).mpr
    have htn := ((mem_occurringTypes B).mp ht).2
    simpa using And.intro ht htn

variable (Γ : AccessStructure P)

/-- An inclusion-maximal unauthorized set of group labels. -/
def IsMaximalUnauthorized (I : Finset G) : Prop :=
  ¬ Γ.Authorized (physicalUnion B I) ∧
    ∀ J : Finset G, I ⊆ J → ¬ Γ.Authorized (physicalUnion B J) → J = I

/-- `M`: the family of all maximal unauthorized group-index sets. -/
noncomputable def maximalUnauthorized : Finset (Finset G) := by
  classical
  exact Finset.univ.powerset.filter (IsMaximalUnauthorized B Γ)

omit [DecidableEq G] in
@[simp] theorem mem_maximalUnauthorized {I : Finset G} :
    I ∈ maximalUnauthorized B Γ ↔ IsMaximalUnauthorized B Γ I := by
  classical
  simp [maximalUnauthorized]

/-- Every unauthorized group-index set has a maximal unauthorized extension. -/
theorem exists_maximalUnauthorized_superset (J : Finset G)
    (hJ : ¬ Γ.Authorized (physicalUnion B J)) :
    ∃ I ∈ maximalUnauthorized B Γ, J ⊆ I := by
  classical
  let candidates := Finset.univ.powerset.filter
    (fun I : Finset G => J ⊆ I ∧ ¬ Γ.Authorized (physicalUnion B I))
  have hJc : J ∈ candidates := by simp [candidates, hJ]
  obtain ⟨I, hIc, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨J, hJc⟩
  have hI : J ⊆ I ∧ ¬ Γ.Authorized (physicalUnion B I) := by
    simpa [candidates] using hIc
  refine ⟨I, (mem_maximalUnauthorized B Γ).mpr ⟨hI.2, ?_⟩, hI.1⟩
  intro K hIK hK
  have hKc : K ∈ candidates := by
    simp [candidates, Finset.Subset.trans hI.1 hIK, hK]
  exact (Finset.eq_of_subset_of_card_le hIK (hmax K hKc)).symm

theorem maximalUnauthorized_nonempty : (maximalUnauthorized B Γ).Nonempty := by
  have h0 : ¬ Γ.Authorized (physicalUnion B ∅) := by
    simpa using Γ.empty_unauthorized
  obtain ⟨I, hI, _⟩ := exists_maximalUnauthorized_superset B Γ ∅ h0
  exact ⟨I, hI⟩

omit [DecidableEq G] in
/-- Distinct maximal unauthorized sets cannot contain one another. -/
theorem maximalUnauthorized_no_strict_inclusion {I J : Finset G}
    (hI : I ∈ maximalUnauthorized B Γ) (hJ : J ∈ maximalUnauthorized B Γ)
    (hIJ : I ⊆ J) : I = J := by
  have hI' := (mem_maximalUnauthorized B Γ).mp hI
  have hJ' := (mem_maximalUnauthorized B Γ).mp hJ
  exact (hI'.2 J hIJ hJ'.1).symm

/-- `D_I`: the occurring types missed by the maximal unauthorized index set I. -/
def clause (I : Finset G) : Finset (Finset G) :=
  occurringTypes B \ visibleTypes B I

/-- `D`: the family of clauses, with duplicates removed by finset image. -/
noncomputable def clauses : Finset (Finset (Finset G)) := by
  classical
  exact (maximalUnauthorized B Γ).image (clause B)

theorem mem_clauses {D : Finset (Finset G)} :
    D ∈ clauses B Γ ↔ ∃ I ∈ maximalUnauthorized B Γ, clause B I = D := by
  classical
  simp [clauses]

/-- The clause access rule: V meets every clause. -/
def InterpolatedAuthorized (V : Finset (Finset G)) : Prop :=
  ∀ D ∈ clauses B Γ, (V ∩ D).Nonempty

/-- Section 4, Interpolation lemma: the clause access rule agrees with the
original access structure on every queried group union. -/
theorem interpolation (J : Finset G) :
    InterpolatedAuthorized B Γ (visibleTypes B J) ↔
      Γ.Authorized (physicalUnion B J) := by
  classical
  constructor
  · intro h
    by_contra hJ
    obtain ⟨I, hI, hJI⟩ := exists_maximalUnauthorized_superset B Γ J hJ
    have hD : clause B I ∈ clauses B Γ :=
      (mem_clauses B Γ).mpr ⟨I, hI, rfl⟩
    obtain ⟨t, ht⟩ := h (clause B I) hD
    have htJ : t ∈ visibleTypes B J := (Finset.mem_inter.mp ht).1
    have htD : t ∈ clause B I := (Finset.mem_inter.mp ht).2
    have htNotI : t ∉ visibleTypes B I := (Finset.mem_sdiff.mp htD).2
    exact htNotI (visibleTypes_mono B hJI htJ)
  · intro hJ D hD
    obtain ⟨I, hI, rfl⟩ := (mem_clauses B Γ).mp hD
    by_contra hmiss
    have hVI : visibleTypes B J ⊆ visibleTypes B I := by
      intro t htJ
      by_contra htI
      apply hmiss
      exact ⟨t, Finset.mem_inter.mpr ⟨htJ,
        Finset.mem_sdiff.mpr ⟨visibleTypes_subset B J htJ, htI⟩⟩⟩
    have hUI : physicalUnion B J ⊆ physicalUnion B I :=
      (visibleTypes_subset_iff B).mp hVI
    exact ((mem_maximalUnauthorized B Γ).mp hI).1
      (Γ.upward_closed hUI hJ)

/-- When all queried groups together are authorized (the manuscript's
nontrivial case), every interpolation clause is nonempty. -/
theorem clause_nonempty (hfull : Γ.Authorized (physicalUnion B Finset.univ))
    {I : Finset G} (hI : I ∈ maximalUnauthorized B Γ) :
    (clause B I).Nonempty := by
  classical
  by_contra hempty
  have hsub : occurringTypes B ⊆ visibleTypes B I := by
    intro t ht
    by_contra htI
    exact hempty ⟨t, Finset.mem_sdiff.mpr ⟨ht, htI⟩⟩
  have hVI : visibleTypes B Finset.univ ⊆ visibleTypes B I := by
    simpa using hsub
  have hUI := (visibleTypes_subset_iff B).mp hVI
  exact ((mem_maximalUnauthorized B Γ).mp hI).1
    (Γ.upward_closed hUI hfull)

theorem clauses_nonempty : (clauses B Γ).Nonempty := by
  classical
  obtain ⟨I, hI⟩ := maximalUnauthorized_nonempty B Γ
  exact ⟨clause B I, (mem_clauses B Γ).mpr ⟨I, hI, rfl⟩⟩

/-- The interpolated clause rule is monotone. -/
theorem interpolatedAuthorized_mono {V W : Finset (Finset G)} (hVW : V ⊆ W)
    (hV : InterpolatedAuthorized B Γ V) : InterpolatedAuthorized B Γ W := by
  intro D hD
  obtain ⟨t, ht⟩ := hV D hD
  have ht' := Finset.mem_inter.mp ht
  exact ⟨t, Finset.mem_inter.mpr ⟨hVW ht'.1, ht'.2⟩⟩

/-- The empty coalition is unauthorized under the interpolated rule. -/
theorem interpolatedAuthorized_empty : ¬ InterpolatedAuthorized B Γ ∅ := by
  intro h
  obtain ⟨D, hD⟩ := clauses_nonempty B Γ
  simpa using h D hD

/-- Under the manuscript's nontrivial-case hypothesis, the full type set is
authorized. Thus restricting the clause rule to subsets of T gives a proper
access structure on T. -/
theorem interpolatedAuthorized_full
    (hfull : Γ.Authorized (physicalUnion B Finset.univ)) :
    InterpolatedAuthorized B Γ (occurringTypes B) := by
  intro D hD
  obtain ⟨I, hI, rfl⟩ := (mem_clauses B Γ).mp hD
  obtain ⟨t, ht⟩ := clause_nonempty B Γ hfull hI
  exact ⟨t, Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp ht).1, ht⟩⟩

end BoundedArity
