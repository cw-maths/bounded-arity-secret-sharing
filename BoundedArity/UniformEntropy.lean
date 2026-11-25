module

public import BoundedArity.DiscreteEntropy
public import Mathlib.FieldTheory.Finiteness

/-!
# Uniform finite laws and the entropy of a linear image

The input law is the genuine uniform PMF on a finite nonempty type. A linear
map has equally sized nonempty fibres, so its output law is uniform on its
range. The Shannon sum in bits is therefore the logarithm of the range size.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators ENNReal Classical

/-- The uniform probability mass function on a finite nonempty alphabet. -/
noncomputable def uniformPMF (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ => (Fintype.card α : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp))

@[simp] theorem uniformPMF_apply (α : Type*) [Fintype α] [Nonempty α] (x : α) :
    uniformPMF α x = (Fintype.card α : ℝ≥0∞)⁻¹ := rfl

/-- The elementary finite fibre formula for a pushforward of a uniform PMF. -/
theorem map_uniformPMF_apply {α β : Type*} [Fintype α] [Nonempty α]
    (f : α → β) (y : β) :
    ((uniformPMF α).map f) y =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ≥0∞) /
        (Fintype.card α : ℝ≥0∞) := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp only [uniformPMF_apply, div_eq_mul_inv]
  rw [← Finset.sum_filter]
  simp [eq_comm, nsmul_eq_mul]

/-- Entropy of a uniform finite alphabet is its base-two logarithmic size. -/
theorem pmfEntropyReal_uniformPMF (α : Type*) [Fintype α] [Nonempty α] :
    pmfEntropyReal (uniformPMF α) = Real.log (Fintype.card α) / Real.log 2 := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [pmfEntropyReal_eq_sum]
  simp only [uniformPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Real.negMulLog_def, Real.log_inv, neg_mul, mul_neg, neg_neg,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

section LinearFibres

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [Fintype V] [Fintype W]

/-- Translation by a preimage gives a bijection between its fibre and the kernel. -/
def linearFibreEquivKernel (f : V →ₗ[K] W) (v : V) :
    {x : V // f x = f v} ≃ LinearMap.ker f where
  toFun x := ⟨x.val - v, by change f (x.val - v) = 0; rw [map_sub, x.property, sub_self]⟩
  invFun x := ⟨x.val + v, by
    rw [map_add]
    change f x.val + f v = f v
    rw [show f x.val = 0 from x.property, zero_add]⟩
  left_inv x := by apply Subtype.ext; exact sub_add_cancel _ _
  right_inv x := by apply Subtype.ext; exact add_sub_cancel_right _ _

omit [Fintype W] in
theorem linear_fibre_card (f : V →ₗ[K] W) (y : W) (hy : y ∈ LinearMap.range f) :
    (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = 0)).card := by
  classical
  obtain ⟨v, rfl⟩ := hy
  have h := Fintype.card_congr (linearFibreEquivKernel f v)
  simpa only [Fintype.card_subtype, LinearMap.mem_ker] using h

/-- The point probabilities of a finite linear image are uniform on its range. -/
theorem map_uniformPMF_linear_toReal (f : V →ₗ[K] W) (y : W) :
    (((uniformPMF V).map f) y).toReal =
      if y ∈ LinearMap.range f then
        (Fintype.card (LinearMap.range f) : ℝ)⁻¹ else 0 := by
  classical
  let S : Finset W := Finset.univ.filter (fun y => y ∈ LinearMap.range f)
  let n : ℕ := (Finset.univ.filter (fun x => f x = 0)).card
  have hn : n ≠ 0 := by
    apply Nat.ne_of_gt
    apply Finset.card_pos.mpr
    exact ⟨0, by simp⟩
  have hSn : S.card * n = Fintype.card V := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset V) S f
    have hconst : (∑ y ∈ S, (Finset.univ.filter (fun x => f x = y)).card) =
        S.card * n := by
      apply Finset.sum_const_nat
      intro y hy
      exact linear_fibre_card f y (Finset.mem_filter.mp hy).2
    have hall : (Finset.univ.filter (fun x : V => f x ∈ S)) = Finset.univ := by
      ext x
      simp [S, LinearMap.mem_range]
    rw [hconst, hall, Finset.card_univ] at h
    exact h
  have hS : S.card = Fintype.card (LinearMap.range f) := by
    simp only [S, Fintype.card_subtype]
  rw [map_uniformPMF_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  by_cases hy : y ∈ LinearMap.range f
  · rw [ite_eq_left hy, linear_fibre_card f y hy]
    change (n : ℝ) / (Fintype.card V : ℝ) = _
    rw [← hSn, Nat.cast_mul, hS]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  · rw [ite_eq_right hy]
    have hnone : Finset.univ.filter (fun x : V => f x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [hnone]

/-- The Shannon entropy of a uniform finite linear image is log₂ of its size. -/
theorem pmfEntropyReal_map_uniform_linear_log (f : V →ₗ[K] W) :
    pmfEntropyReal ((uniformPMF V).map f) =
      Real.log (Fintype.card (LinearMap.range f)) / Real.log 2 := by
  classical
  have hn : (Fintype.card (LinearMap.range f) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [pmfEntropyReal_eq_sum]
  simp_rw [map_uniformPMF_linear_toReal]
  have hterm (y : W) :
      Real.negMulLog
          (if y ∈ LinearMap.range f then (Fintype.card (LinearMap.range f) : ℝ)⁻¹ else 0) /
          Real.log 2 =
        if y ∈ LinearMap.range f then
          Real.negMulLog (Fintype.card (LinearMap.range f) : ℝ)⁻¹ / Real.log 2 else 0 := by
    by_cases hy : y ∈ LinearMap.range f <;> simp [hy]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype]
  simp only [Real.negMulLog_def, Real.log_inv]
  field_simp

/-- The entropy/rank identity for every finite-field linear observation. -/
theorem pmfEntropyReal_map_uniform_linearMap [Fintype K] (f : V →ₗ[K] W) :
    pmfEntropyReal ((uniformPMF V).map f) =
      (Module.finrank K (LinearMap.range f) : ℝ) *
        (Real.log (Fintype.card K) / Real.log 2) := by
  classical
  rw [pmfEntropyReal_map_uniform_linear_log, Module.card_eq_pow_finrank (K := K),
    Nat.cast_pow, Real.log_pow]
  ring

end LinearFibres

/-- Every finite field has at least two elements, so the entropy scale is positive. -/
theorem finiteField_entropyScale_pos (K : Type*) [Field K] [Fintype K] :
    0 < Real.log (Fintype.card K) / Real.log 2 := by
  apply div_pos _ log_two_pos
  apply Real.log_pos
  exact_mod_cast Fintype.one_lt_card

end BoundedArity
