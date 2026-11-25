module

public import BoundedArity.PairCoverage
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

/-!
# The rank sum for one clause

This file supplies the numerical identity used in T4 and connects the
binomial expression for clause coverage with the actual unordered pairs
meeting a coalition. Natural-number subtraction is justified by an
additive counting identity, so the empty coalition and the full coalition
are included.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators

private theorem choose_two_succ (m : ℕ) :
    (m + 1).choose 2 = m + m.choose 2 := by
  simpa only [Nat.choose_one_right] using Nat.choose_succ_succ m 1

/-- An additive form avoids any cancellation assumptions for subtraction. -/
theorem sum_fin_min_add_choose (m k : ℕ) (hkm : k ≤ m) :
    (∑ d : Fin m, min k d.val) + (m - k).choose 2 = m.choose 2 := by
  induction m generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp
  | succ m ih =>
      by_cases hsmall : k ≤ m
      · have hprev := ih k hsmall
        have hsub : m + 1 - k = (m - k) + 1 := by omega
        rw [Fin.sum_univ_castSucc]
        change
          ((∑ d : Fin m, min k d.val) + min k m) +
            (m + 1 - k).choose 2 = (m + 1).choose 2
        rw [min_eq_left hsmall, hsub, choose_two_succ (m - k),
          choose_two_succ m]
        omega
      · have hk : k = m + 1 := by omega
        subst k
        have hprev := ih m (le_refl m)
        simp only [Nat.sub_self, Nat.choose_zero_succ, add_zero] at hprev
        have hsum :
            (∑ d : Fin m, min (m + 1) d.val) =
              ∑ d : Fin m, min m d.val := by
          apply Finset.sum_congr rfl
          intro d _
          have hd : d.val ≤ m := Nat.le_of_lt d.isLt
          have hd' : d.val ≤ m + 1 := by omega
          rw [min_eq_right hd', min_eq_right hd]
        rw [Fin.sum_univ_castSucc]
        change
          ((∑ d : Fin m, min (m + 1) d.val) + min (m + 1) m) +
            (m + 1 - (m + 1)).choose 2 = (m + 1).choose 2
        rw [hsum, min_eq_right (Nat.le_succ m), Nat.sub_self,
          Nat.choose_zero_succ, add_zero, choose_two_succ m]
        omega

/-- The independent blocks have dimensions `1,...,m-1`; their observed
ranks sum to the number of clause pairs meeting the selected members. -/
theorem sum_fin_min_eq_choose_sub (m k : ℕ) (hkm : k ≤ m) :
    (∑ d : Fin (m - 1), min k (d.val + 1)) =
      m.choose 2 - (m - k).choose 2 := by
  cases m with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp
  | succ m =>
      have h := sum_fin_min_add_choose (m + 1) k hkm
      rw [Fin.sum_univ_succ] at h
      change
        (min k 0 + (∑ d : Fin m, min k (d.val + 1))) +
          (m + 1 - k).choose 2 = (m + 1).choose 2 at h
      simp only [min_zero, zero_add] at h
      change
        (∑ d : Fin m, min k (d.val + 1)) =
          (m + 1).choose 2 - (m + 1 - k).choose 2
      omega

variable {E : Type*} [DecidableEq E]

/-- D20: the unordered pairs inside `C` that meet the coalition `U`. -/
def clausePairCoverage (C U : Finset E) : ℕ :=
  C.card.choose 2 - (C \ U).card.choose 2

@[simp] theorem clausePairCoverage_empty (C : Finset E) :
    clausePairCoverage C ∅ = 0 := by
  simp [clausePairCoverage]

/-- The binomial expression counts exactly the indicated two-element sets. -/
theorem clausePairCoverage_eq_card (C U : Finset E) :
    clausePairCoverage C U =
      ((C.powersetCard 2).filter (fun e => (e ∩ U).Nonempty)).card := by
  classical
  have hmiss :
      (C.powersetCard 2).filter (fun e => ¬ (e ∩ U).Nonempty) =
        (C \ U).powersetCard 2 := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨heC, hecard⟩, hmiss⟩
      refine ⟨?_, hecard⟩
      intro p hp
      refine Finset.mem_sdiff.mpr ⟨heC hp, ?_⟩
      intro hpU
      exact hmiss ⟨p, Finset.mem_inter.mpr ⟨hp, hpU⟩⟩
    · rintro ⟨heCU, hecard⟩
      refine ⟨⟨?_, hecard⟩, ?_⟩
      · intro p hp
        exact (Finset.mem_sdiff.mp (heCU hp)).1
      · rintro ⟨p, hp⟩
        have hp' := Finset.mem_inter.mp hp
        exact (Finset.mem_sdiff.mp (heCU hp'.1)).2 hp'.2
  have hcount := Finset.card_filter_add_card_filter_not
    (s := C.powersetCard 2) (fun e => (e ∩ U).Nonempty)
  rw [hmiss, Finset.card_powersetCard, Finset.card_powersetCard] at hcount
  unfold clausePairCoverage
  omega

/-- The rank sum in T4, with the number of selected members expressed by
the intersection of the clause and the physical coalition. -/
theorem sum_fin_min_eq_clausePairCoverage (C U : Finset E) :
    (∑ d : Fin (C.card - 1), min (C ∩ U).card (d.val + 1)) =
      clausePairCoverage C U := by
  have hcard : (C \ U).card = C.card - (C ∩ U).card := by
    have h := Finset.card_sdiff_add_card_inter C U
    omega
  rw [sum_fin_min_eq_choose_sub C.card (C ∩ U).card
    (Finset.card_le_card Finset.inter_subset_left)]
  unfold clausePairCoverage
  rw [hcard]

/-- A version matching the coalition-first intersection convention. -/
theorem sum_fin_min_eq_clausePairCoverage' (C U : Finset E) :
    (∑ d : Fin (C.card - 1), min (U ∩ C).card (d.val + 1)) =
      clausePairCoverage C U := by
  simpa only [Finset.inter_comm U C] using
    sum_fin_min_eq_clausePairCoverage C U

/-- The whole-participant pair count used by T3 has the same closed form. -/
theorem pairCoverage_eq_choose_sub [Fintype E] (U : Finset E) :
    pairCoverage U =
      (Fintype.card E).choose 2 - (Fintype.card E - U.card).choose 2 := by
  calc
    pairCoverage U = clausePairCoverage Finset.univ U :=
      (clausePairCoverage_eq_card Finset.univ U).symm
    _ = (Fintype.card E).choose 2 - (Fintype.card E - U.card).choose 2 := by
      simp [clausePairCoverage, Finset.card_sdiff]

end BoundedArity
