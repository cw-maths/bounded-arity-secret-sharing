module

public import BoundedArity.DiscreteEntropy

/-!
# Entropy under a deterministic map

Combining outcomes cannot increase discrete entropy. The proof works with
extended nonnegative sums, so it includes countably infinite alphabets and
does not assume entropy is finite. It justifies the real marginal entries
of the approved finite-joint-entropy interface.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators ENNReal NNReal

/-- The nonnegative information content of a probability, in bits. -/
noncomputable def pmfSurprisal (p : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (-Real.log p.toReal / Real.log 2)

theorem pmfEntropyTerm_eq_mul_surprisal (a : ℝ≥0∞) (ha : a ≠ ⊤) :
    pmfEntropyTerm a = a * pmfSurprisal a := by
  calc
    pmfEntropyTerm a =
        ENNReal.ofReal (a.toReal * (-Real.log a.toReal / Real.log 2)) := by
      unfold pmfEntropyTerm
      congr 1
      rw [Real.negMulLog_def]
      ring
    _ = ENNReal.ofReal a.toReal *
        ENNReal.ofReal (-Real.log a.toReal / Real.log 2) :=
      ENNReal.ofReal_mul ENNReal.toReal_nonneg
    _ = a * pmfSurprisal a := by rw [ENNReal.ofReal_toReal ha]; rfl

theorem pmfSurprisal_antitone {a b : ℝ≥0∞}
    (ha0 : a ≠ 0) (hb : b ≠ ⊤) (hab : a ≤ b) :
    pmfSurprisal b ≤ pmfSurprisal a := by
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top hb hab
  have hpos : 0 < a.toReal := ENNReal.toReal_pos ha0 ha
  have hle : a.toReal ≤ b.toReal := ENNReal.toReal_mono hb hab
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right
    (neg_le_neg (Real.log_le_log hpos hle)) log_two_pos.le

theorem pmf_apply_le_map {α β : Type*} (p : PMF α) (f : α → β) (a : α) :
    p a ≤ (p.map f) (f a) := by
  classical
  rw [PMF.map_apply]
  simpa using (le_tsum (fun x => if f a = f x then p x else 0) a)

/-- Regrouping the weighted information terms uses only nonnegative sums. -/
theorem pmfEntropy_map_eq_weighted_sum {α β : Type*} (p : PMF α) (f : α → β) :
    pmfEntropy (p.map f) =
      ∑' a, p a * pmfSurprisal ((p.map f) (f a)) := by
  classical
  calc
    pmfEntropy (p.map f) =
        ∑' b, (p.map f) b * pmfSurprisal ((p.map f) b) := by
      exact tsum_congr (fun b => pmfEntropyTerm_eq_mul_surprisal _ ((p.map f).apply_ne_top b))
    _ = ∑' b, ∑' a, if b = f a then p a * pmfSurprisal ((p.map f) b) else 0 := by
      apply tsum_congr
      intro b
      calc
        (p.map f) b * pmfSurprisal ((p.map f) b) =
            (∑' a, if b = f a then p a else 0) * pmfSurprisal ((p.map f) b) :=
          congrArg (fun x => x * pmfSurprisal ((p.map f) b)) (PMF.map_apply f p b)
        _ = ∑' a, (if b = f a then p a else 0) * pmfSurprisal ((p.map f) b) :=
          ENNReal.tsum_mul_right.symm
        _ = ∑' a, if b = f a then p a * pmfSurprisal ((p.map f) b) else 0 := by
          apply tsum_congr
          intro a
          split_ifs <;> simp
    _ = ∑' a, ∑' b, if b = f a then p a * pmfSurprisal ((p.map f) b) else 0 :=
      tsum_comm
    _ = ∑' a, p a * pmfSurprisal ((p.map f) (f a)) := by
      apply tsum_congr
      intro a
      simp

/-- Every deterministic observation has entropy at most the original law. -/
theorem pmfEntropy_map_le {α β : Type*} (p : PMF α) (f : α → β) :
    pmfEntropy (p.map f) ≤ pmfEntropy p := by
  rw [pmfEntropy_map_eq_weighted_sum]
  apply tsum_le_tsum
  intro a
  change p a * pmfSurprisal ((p.map f) (f a)) ≤ pmfEntropyTerm (p a)
  rw [pmfEntropyTerm_eq_mul_surprisal _ (p.apply_ne_top a)]
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul' le_rfl (pmfSurprisal_antitone ha ((p.map f).apply_ne_top (f a))
      (pmf_apply_le_map p f a))

theorem pmfEntropy_map_ne_top {α β : Type*} (p : PMF α) (f : α → β)
    (hp : pmfEntropy p ≠ ⊤) : pmfEntropy (p.map f) ≠ ⊤ :=
  ne_top_of_le_ne_top hp (pmfEntropy_map_le p f)

/-- A relabelling with a left inverse preserves even extended entropy. -/
theorem pmfEntropy_map_of_leftInverse {α β : Type*} (p : PMF α)
    (f : α → β) (g : β → α) (hgf : Function.LeftInverse g f) :
    pmfEntropy (p.map f) = pmfEntropy p := by
  apply le_antisymm (pmfEntropy_map_le p f)
  have hmap : (p.map f).map g = p := by
    rw [PMF.map_comp]
    have hid : g ∘ f = id := funext hgf
    rw [hid, PMF.map_id]
  have h := pmfEntropy_map_le (p.map f) g
  rwa [hmap] at h

end BoundedArity
