module

public import BoundedArity.LinearRank
public import BoundedArity.PolynomialEvaluation
public import BoundedArity.ClauseCount
public import Mathlib.Data.Fintype.EquivFin

/-!
# One clause, with a common key and all coalition ranks

This is the large-field one-clause construction D20 / T4. For a clause of
size `m`, the independent coefficient blocks have dimensions `1,...,m-1`.
The first block is the common scalar key. All participant spaces and the
key are placed in one finite coordinate space before taking any coalition.

The field-size hypothesis is an embedding of the clause members into the
field. This expresses the existence of enough distinct evaluation points
and applies to both finite and infinite fields. Numerical finite-field and
infinite-field corollaries are included below.

Compilation and the axiom audit are required before marking T4 verified.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators

/-- Independent coefficient blocks of dimensions `1,...,m-1`. -/
abbrev OneClauseAmbient (K : Type*) (m : ℕ) :=
  (d : Fin (m - 1)) → (Fin (d.val + 1) → K)

/-- The common key occupies only the first, one-dimensional block. -/
def oneClauseKeyVector (K : Type*) [Field K] (m : ℕ) :
    OneClauseAmbient K m :=
  fun d _ => if d.val = 0 then 1 else 0

/-- The key's observation subspace. -/
def oneClauseKey (K : Type*) [Field K] (m : ℕ) :
    Submodule K (OneClauseAmbient K m) :=
  Submodule.span K {oneClauseKeyVector K m}

/-- One evaluation row in each independent coefficient block. -/
def oneClauseShare {K : Type*} [Field K] (m : ℕ) (a : K) :
    Submodule K (OneClauseAmbient K m) :=
  Submodule.pi Set.univ
    (fun d => Submodule.span K {evaluationVector a (d.val + 1)})

theorem oneClauseKeyVector_ne_zero (K : Type*) [Field K]
    (m : ℕ) (hm : 2 ≤ m) :
    oneClauseKeyVector K m ≠ 0 := by
  intro h
  let d : Fin (m - 1) := ⟨0, by omega⟩
  let j : Fin (d.val + 1) := ⟨0, by simp [d]⟩
  have hcoord := congrFun (congrFun h d) j
  simp [oneClauseKeyVector, d] at hcoord

theorem oneClauseKey_finrank (K : Type*) [Field K]
    (m : ℕ) (hm : 2 ≤ m) :
    Module.finrank K (oneClauseKey K m) = 1 := by
  exact finrank_span_singleton (oneClauseKeyVector_ne_zero K m hm)

/-- Every clause member observes the same key, in the first block. -/
theorem oneClauseKey_le_share {K : Type*} [Field K] (m : ℕ) (a : K) :
    oneClauseKey K m ≤ oneClauseShare m a := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  apply Submodule.mem_pi.mpr
  intro d _
  by_cases hd : d.val = 0
  · have heq : oneClauseKeyVector K m d =
        evaluationVector a (d.val + 1) := by
      ext j
      have hj : j.val = 0 := by omega
      simp [oneClauseKeyVector, evaluationVector, hd, hj]
    rw [heq]
    exact Submodule.subset_span (Set.mem_singleton _)
  · have heq : oneClauseKeyVector K m d = 0 := by
      ext j
      simp [oneClauseKeyVector, hd]
    rw [heq]
    exact Submodule.zero_mem _

/-- All coalition ranks of the polynomial-block model, in the same space. -/
theorem oneClauseShare_joint_finrank {K E : Type*} [Field K] [Fintype E]
    (α : E → K) (hα : Function.Injective α) (U : Finset E) :
    Module.finrank K
      (jointSubspace (fun i => oneClauseShare (Fintype.card E) (α i)) U) =
      (Fintype.card E).choose 2 - (Fintype.card E - U.card).choose 2 := by
  classical
  have hcard : U.card ≤ Fintype.card E := by
    simpa only [Finset.card_univ] using
      (Finset.card_le_card (Finset.subset_univ U))
  calc
    Module.finrank K
        (jointSubspace (fun i => oneClauseShare (Fintype.card E) (α i)) U) =
        ∑ d : Fin (Fintype.card E - 1),
          Module.finrank K
            (jointSubspace
              (fun i => Submodule.span K {evaluationVector (α i) (d.val + 1)}) U) := by
      unfold oneClauseShare
      rw [jointSubspace_pi, finrank_piSubmodule]
    _ = ∑ d : Fin (Fintype.card E - 1), min U.card (d.val + 1) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [jointSubspace_span_singleton]
      simpa only [Fintype.card_coe] using
        (evaluationSpan_finrank (fun i : U => α i)
          (hα.comp Subtype.val_injective) (d.val + 1))
    _ = (Fintype.card E).choose 2 - (Fintype.card E - U.card).choose 2 :=
      sum_fin_min_eq_choose_sub (Fintype.card E) U.card hcard

/-- One finite coordinate change preserves the key and every coalition rank. -/
theorem oneClause_all_members {K E : Type*} [Field K] [Fintype E]
    (α : E → K) (hα : Function.Injective α) (hm : 2 ≤ Fintype.card E) :
    ∃ n : ℕ, ∃ key : Submodule K (Fin n → K),
      ∃ W : E → Submodule K (Fin n → K),
        Module.finrank K key = 1 ∧
        (∀ i, key ≤ W i) ∧
        (∀ U : Finset E,
          Module.finrank K (jointSubspace W U) =
            (Fintype.card E).choose 2 - (Fintype.card E - U.card).choose 2) := by
  classical
  let V := OneClauseAmbient K (Fintype.card E)
  let key : Submodule K V := oneClauseKey K (Fintype.card E)
  let W : E → Submodule K V := fun i => oneClauseShare (Fintype.card E) (α i)
  let e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, key.map e.toLinearMap,
    fun i => (W i).map e.toLinearMap, ?_, ?_, ?_⟩
  · rw [e.finrank_map_eq]
    exact oneClauseKey_finrank K (Fintype.card E) hm
  · intro i
    exact Submodule.map_mono (oneClauseKey_le_share (Fintype.card E) (α i))
  · intro U
    rw [jointSubspace_finrank_map]
    exact oneClauseShare_joint_finrank α hα U

section PhysicalClause

variable {K E : Type*} [Field K] [DecidableEq E]

/-- The selected members of a clause, viewed as elements of its subtype. -/
def clauseCoalition (C U : Finset E) : Finset C :=
  Finset.univ.filter (fun i => i.val ∈ U)

@[simp] theorem mem_clauseCoalition (C U : Finset E) (i : C) :
    i ∈ clauseCoalition C U ↔ i.val ∈ U := by
  simp [clauseCoalition]

theorem clauseCoalition_card (C U : Finset E) :
    (clauseCoalition C U).card = (C ∩ U).card := by
  classical
  refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_inter.mpr ⟨i.property, (mem_clauseCoalition C U i).mp hi⟩
  · intro i hi j hj hij
    exact Subtype.ext hij
  · intro p hp
    obtain ⟨hpC, hpU⟩ := Finset.mem_inter.mp hp
    exact ⟨⟨p, hpC⟩, (mem_clauseCoalition C U ⟨p, hpC⟩).mpr hpU, rfl⟩

/-- Participants outside the clause receive the zero observation space. -/
def extendClauseShares {V : Type*} [AddCommGroup V] [Module K V]
    (C : Finset E) (W : C → Submodule K V) : E → Submodule K V :=
  fun p => if hp : p ∈ C then W ⟨p, hp⟩ else ⊥

theorem jointSubspace_extendClauseShares {V : Type*}
    [AddCommGroup V] [Module K V]
    (C U : Finset E) (W : C → Submodule K V) :
    jointSubspace (extendClauseShares C W) U =
      jointSubspace W (clauseCoalition C U) := by
  classical
  unfold jointSubspace
  apply le_antisymm
  · refine iSup_le (fun p => iSup_le (fun hpU => ?_))
    by_cases hpC : p ∈ C
    · simp only [extendClauseShares, dite_eq_left hpC]
      exact le_iSup_of_le ⟨p, hpC⟩
        (le_iSup_of_le ((mem_clauseCoalition C U ⟨p, hpC⟩).mpr hpU) le_rfl)
    · simp [extendClauseShares, hpC]
  · refine iSup_le (fun i => iSup_le (fun hi => ?_))
    have hiU : i.val ∈ U := (mem_clauseCoalition C U i).mp hi
    have hle : W i ≤ extendClauseShares C W i.val := by
      simp [extendClauseShares, i.property]
    exact hle.trans (le_iSup_of_le i.val (le_iSup_of_le hiU le_rfl))

/-- D20 / T4: one model simultaneously supplies a rank-one key, key recovery,
zero observations outside the clause, and every required coalition rank. -/
def OneClauseRealizes (K : Type*) [Field K] (C : Finset E) : Prop :=
  ∃ n : ℕ, ∃ key : Submodule K (Fin n → K),
    ∃ W : E → Submodule K (Fin n → K),
      Module.finrank K key = 1 ∧
      (∀ p, p ∉ C → W p = ⊥) ∧
      (∀ p, p ∈ C → key ≤ W p) ∧
      (∀ U : Finset E,
        Module.finrank K (jointSubspace W U) = clausePairCoverage C U)

/-- T4. The embedding hypothesis means that the field has at least `C.card`
distinct elements. The key and all coalition ranks share the same witnesses. -/
theorem oneClause_checkpoint (C : Finset E) (hm : 2 ≤ C.card)
    (hK : Nonempty (C ↪ K)) : OneClauseRealizes K C := by
  classical
  obtain ⟨α⟩ := hK
  have hm' : 2 ≤ Fintype.card C := by simpa only [Fintype.card_coe] using hm
  obtain ⟨n, key, W, hkey, hle, hrank⟩ :=
    oneClause_all_members (α : C → K) α.injective hm'
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

/-- Numerical field-size form for a finite field. -/
theorem oneClause_finiteField_checkpoint [Fintype K]
    (C : Finset E) (hm : 2 ≤ C.card) (hK : C.card ≤ Fintype.card K) :
    OneClauseRealizes K C := by
  apply oneClause_checkpoint C hm
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using hK

/-- Every infinite field supplies enough distinct evaluation points. -/
theorem oneClause_infiniteField_checkpoint [Infinite K]
    (C : Finset E) (hm : 2 ≤ C.card) : OneClauseRealizes K C := by
  classical
  apply oneClause_checkpoint C hm
  refine ⟨{
    toFun := fun i => Infinite.natEmbedding K (C.equivFin i).val
    inj' := ?_
  }⟩
  intro i j h
  exact C.equivFin.injective
    (Fin.ext ((Infinite.natEmbedding K).injective h))

/-- The same clause model gives D18's rank representation when the key is
not explicitly requested by the caller. -/
theorem oneClause_linearRankRealizes (C : Finset E) (hm : 2 ≤ C.card)
    (hK : Nonempty (C ↪ K)) : LinearRankRealizes K (clausePairCoverage C) := by
  obtain ⟨n, key, W, hkey, hout, hle, hrank⟩ := oneClause_checkpoint C hm hK
  refine ⟨n, W, ?_⟩
  intro U
  exact (hrank U).symm

end PhysicalClause

end BoundedArity
