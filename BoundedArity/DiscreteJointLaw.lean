module

public import BoundedArity.EntropyMap

/-!
# One countable joint law and its entropy table

This is the reviewed E28 specification. The alphabets are data of the law,
not fixed in advance. They may be any countable types in the indicated
universe. There is one probability mass function on their full dependent
product. Every table entry is the entropy of a marginal of that same law.
-/

@[expose] public section

universe u v

namespace BoundedArity

open scoped ENNReal NNReal

/-- Arbitrary countable alphabets together with one common joint law. -/
structure DiscreteJointLaw (G : Type u) where
  Alphabet : G → Type v
  countableAlphabet : ∀ j, Countable (Alphabet j)
  pmf : PMF (∀ j, Alphabet j)

attribute [instance] DiscreteJointLaw.countableAlphabet

namespace DiscreteJointLaw

variable {G : Type u}

/-- Bundle a PMF on any countable family of alphabets. -/
def ofPMF (A : G → Type v) [∀ j, Countable (A j)] (p : PMF (∀ j, A j)) :
    DiscreteJointLaw.{u,v} G :=
  ⟨A, fun _ => inferInstance, p⟩

/-- The marginal is the pushforward along coordinate restriction. -/
noncomputable def marginal (law : DiscreteJointLaw.{u,v} G) (I : Finset G) :
    PMF (∀ j : I, law.Alphabet j.val) :=
  law.pmf.map (fun x j => x j.val)

/-- Joint marginal entropy, initially allowed to be infinity. -/
noncomputable def jointEntropyENN (law : DiscreteJointLaw.{u,v} G)
    (I : Finset G) : ℝ≥0∞ := pmfEntropy (law.marginal I)

/-- Joint marginal entropy in bits, used under finite full-joint entropy. -/
noncomputable def jointEntropy (law : DiscreteJointLaw.{u,v} G)
    (I : Finset G) : ℝ := pmfEntropyReal (law.marginal I)

/-- Exactly the finiteness of entropy of the full joint distribution. -/
def FiniteJointEntropy (law : DiscreteJointLaw.{u,v} G) : Prop :=
  pmfEntropy law.pmf ≠ ⊤

/-- The full marginal is only a relabelling of the original joint tuple. -/
@[simp] theorem jointEntropyENN_univ [Fintype G]
    (law : DiscreteJointLaw.{u,v} G) :
    law.jointEntropyENN Finset.univ = pmfEntropy law.pmf := by
  let f : (∀ j, law.Alphabet j) →
      ((j : (Finset.univ : Finset G)) → law.Alphabet j.val) := fun x j => x j.val
  let g : ((j : (Finset.univ : Finset G)) → law.Alphabet j.val) →
      (∀ j, law.Alphabet j) := fun y j => y ⟨j, Finset.mem_univ j⟩
  have hgf : Function.LeftInverse g f := by intro x; rfl
  exact pmfEntropy_map_of_leftInverse law.pmf f g hgf

theorem finiteJointEntropy_iff_univ [Fintype G]
    (law : DiscreteJointLaw.{u,v} G) :
    law.FiniteJointEntropy ↔ law.jointEntropyENN Finset.univ ≠ ⊤ := by
  rw [jointEntropyENN_univ]
  rfl

/-- Every marginal is a deterministic observation of the common joint law. -/
theorem jointEntropyENN_le_full (law : DiscreteJointLaw.{u,v} G) (I : Finset G) :
    law.jointEntropyENN I ≤ pmfEntropy law.pmf := by
  unfold jointEntropyENN marginal
  exact pmfEntropy_map_le law.pmf
    (fun (x : ∀ j, law.Alphabet j) (j : I) => x j.val)

/-- Finite full-joint entropy implies finiteness of every entry, as required in E28. -/
theorem jointEntropyENN_ne_top (law : DiscreteJointLaw.{u,v} G)
    (hfinite : law.FiniteJointEntropy) (I : Finset G) :
    law.jointEntropyENN I ≠ ⊤ :=
  ne_top_of_le_ne_top hfinite (law.jointEntropyENN_le_full I)

/-- Every real table entry is the convergent base-two Shannon series of its marginal. -/
theorem jointEntropy_hasSum (law : DiscreteJointLaw.{u,v} G)
    (hfinite : law.FiniteJointEntropy) (I : Finset G) :
    HasSum (fun x => Real.negMulLog ((law.marginal I) x).toReal / Real.log 2)
      (law.jointEntropy I) :=
  pmfEntropyReal_hasSum (law.marginal I) (law.jointEntropyENN_ne_top hfinite I)

theorem jointEntropy_eq_tsum (law : DiscreteJointLaw.{u,v} G)
    (hfinite : law.FiniteJointEntropy) (I : Finset G) :
    law.jointEntropy I =
      ∑' x, Real.negMulLog ((law.marginal I) x).toReal / Real.log 2 :=
  (law.jointEntropy_hasSum hfinite I).tsum_eq.symm

/-- Finite-valued joint laws satisfy the required full-joint finiteness. -/
theorem finiteJointEntropy_of_finite [Finite G]
    (law : DiscreteJointLaw.{u,v} G) [∀ j, Finite (law.Alphabet j)] :
    law.FiniteJointEntropy := pmfEntropy_ne_top law.pmf

theorem jointEntropyENN_ne_top_of_finite
    (law : DiscreteJointLaw.{u,v} G) [∀ j, Finite (law.Alphabet j)] (I : Finset G) :
    law.jointEntropyENN I ≠ ⊤ := pmfEntropy_ne_top (law.marginal I)

/-- The empty tuple is deterministic, so its entropy is zero. -/
@[simp] theorem jointEntropyENN_empty (law : DiscreteJointLaw.{u,v} G) :
    law.jointEntropyENN ∅ = 0 := pmfEntropy_subsingleton _

@[simp] theorem jointEntropy_empty (law : DiscreteJointLaw.{u,v} G) :
    law.jointEntropy ∅ = 0 := pmfEntropyReal_subsingleton _

end DiscreteJointLaw

/-- E28: one discrete law, with finite full-joint entropy, gives every entry. -/
def IsDiscreteEntropyTable {G : Type u} (h : Finset G → ℝ) : Prop :=
  ∃ law : DiscreteJointLaw.{u,v} G,
    law.FiniteJointEntropy ∧ ∀ I, h I = law.jointEntropy I

/-- The stronger finite-valued witness constructed by the rank-to-entropy bridge. -/
def IsFiniteEntropyTable {G : Type u} (h : Finset G → ℝ) : Prop :=
  ∃ law : DiscreteJointLaw.{u,v} G,
    (∀ j, Finite (law.Alphabet j)) ∧
      law.FiniteJointEntropy ∧ ∀ I, h I = law.jointEntropy I

theorem IsFiniteEntropyTable.isDiscreteEntropyTable {G : Type u}
    {h : Finset G → ℝ} (hh : IsFiniteEntropyTable.{u,v} h) :
    IsDiscreteEntropyTable.{u,v} h := by
  obtain ⟨law, _hfinite, hentropy, htable⟩ := hh
  exact ⟨law, hentropy, htable⟩

theorem IsDiscreteEntropyTable.empty {G : Type u} {h : Finset G → ℝ}
    (hh : IsDiscreteEntropyTable.{u,v} h) : h ∅ = 0 := by
  obtain ⟨law, _hfinite, htable⟩ := hh
  rw [htable, law.jointEntropy_empty]

end BoundedArity
