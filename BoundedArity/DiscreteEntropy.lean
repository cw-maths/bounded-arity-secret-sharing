module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Tactic

/-!
# Discrete Shannon entropy in bits

Entropy is first an extended nonnegative real sum, so infinite entropy is
represented by infinity. Each summand is the usual `-p log₂ p`, with the
zero convention supplied by `Real.negMulLog_zero`. Real entropy is its
real conversion and is used only for laws with finite entropy.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators ENNReal NNReal

/-- A single Shannon-entropy contribution in bits. -/
noncomputable def pmfEntropyTerm (p : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.negMulLog p.toReal / Real.log 2)

/-- Discrete entropy as a nonnegative sum, possibly infinite. -/
noncomputable def pmfEntropy {α : Type*} (p : PMF α) : ℝ≥0∞ :=
  ∑' x, pmfEntropyTerm (p x)

/-- Real entropy in bits; finiteness is imposed by the table interface. -/
noncomputable def pmfEntropyReal {α : Type*} (p : PMF α) : ℝ :=
  (pmfEntropy p).toReal

@[simp] theorem pmfEntropyTerm_zero : pmfEntropyTerm 0 = 0 := by
  simp [pmfEntropyTerm]

@[simp] theorem pmfEntropyTerm_one : pmfEntropyTerm 1 = 0 := by
  simp [pmfEntropyTerm]

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem pmf_entropy_summand_nonneg {α : Type*} (p : PMF α) (x : α) :
    0 ≤ Real.negMulLog (p x).toReal / Real.log 2 := by
  apply div_nonneg
  · apply Real.negMulLog_nonneg ENNReal.toReal_nonneg
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one x)
  · exact log_two_pos.le

theorem pmfEntropyTerm_toReal {α : Type*} (p : PMF α) (x : α) :
    (pmfEntropyTerm (p x)).toReal =
      Real.negMulLog (p x).toReal / Real.log 2 :=
  ENNReal.toReal_ofReal (pmf_entropy_summand_nonneg p x)

@[simp] theorem pmfEntropyTerm_ne_top (p : ℝ≥0∞) : pmfEntropyTerm p ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- Finite alphabets always have finite entropy. -/
theorem pmfEntropy_ne_top {α : Type*} [Finite α] (p : PMF α) :
    pmfEntropy p ≠ ⊤ := by
  classical
  let := Fintype.ofFinite α
  unfold pmfEntropy
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr (fun x _ => pmfEntropyTerm_ne_top (p x))

/-- On a finite alphabet, this is exactly the ordinary Shannon sum in bits. -/
theorem pmfEntropyReal_eq_sum {α : Type*} [Fintype α] (p : PMF α) :
    pmfEntropyReal p = ∑ x, Real.negMulLog (p x).toReal / Real.log 2 := by
  unfold pmfEntropyReal pmfEntropy
  rw [tsum_fintype, ENNReal.toReal_sum (fun x _ => pmfEntropyTerm_ne_top (p x))]
  exact Finset.sum_congr rfl (fun x _ => pmfEntropyTerm_toReal p x)

/-- Finite extended entropy gives a convergent real Shannon sum. -/
theorem pmfEntropyReal_hasSum {α : Type*} (p : PMF α)
    (hfinite : pmfEntropy p ≠ ⊤) :
    HasSum (fun x => Real.negMulLog (p x).toReal / Real.log 2) (pmfEntropyReal p) := by
  have hs : Summable (fun x => (pmfEntropyTerm (p x)).toReal) :=
    ENNReal.summable_toReal hfinite
  have hsum := hs.hasSum
  rw [← ENNReal.tsum_toReal_eq (fun x => pmfEntropyTerm_ne_top (p x))] at hsum
  unfold pmfEntropyReal pmfEntropy
  simpa only [pmfEntropyTerm_toReal] using hsum

theorem pmfEntropyReal_eq_tsum {α : Type*} (p : PMF α)
    (hfinite : pmfEntropy p ≠ ⊤) :
    pmfEntropyReal p = ∑' x, Real.negMulLog (p x).toReal / Real.log 2 :=
  (pmfEntropyReal_hasSum p hfinite).tsum_eq.symm

/-- Every probability law on a subsingleton alphabet is deterministic. -/
theorem pmfEntropy_subsingleton {α : Type*} [Subsingleton α] (p : PMF α) :
    pmfEntropy p = 0 := by
  have hp (a : α) : p a = 1 := by
    calc
      p a = ∑' b, p b := (tsum_eq_single a (fun b hba =>
        False.elim (hba (Subsingleton.elim b a)))).symm
      _ = 1 := p.tsum_coe
  simp [pmfEntropy, hp]

@[simp] theorem pmfEntropyReal_subsingleton {α : Type*} [Subsingleton α]
    (p : PMF α) : pmfEntropyReal p = 0 := by
  rw [pmfEntropyReal, pmfEntropy_subsingleton]
  rfl

end BoundedArity
