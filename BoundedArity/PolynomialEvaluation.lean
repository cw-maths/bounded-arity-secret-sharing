module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic

/-!
# Polynomial evaluation and its observation spaces

D19 of the approved specification. The proof uses a square Vandermonde
minor of size `min (Fintype.card E) d`; consequently it also covers an empty
label type and degree bound zero without separate nonemptiness assumptions.

The row-space version is used to assemble the independent polynomial
blocks in the one-clause construction. All dimensions refer to subspaces
of finite coordinate spaces.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators

variable {K : Type*} {E : Type*} [Field K]

/-- The observation row for evaluating a polynomial with `d` coefficients. -/
def evaluationVector (a : K) (d : ℕ) : Fin d → K :=
  fun j => a ^ j.val

/-- A rectangular Vandermonde matrix: rows are evaluation points and
columns are the coefficient positions `0, ..., d - 1`. -/
def evaluationMatrix (α : E → K) (d : ℕ) : Matrix E (Fin d) K :=
  fun i => evaluationVector (α i) d

/-- D19: evaluation on polynomials of degree strictly less than `d`. -/
noncomputable def polynomialEvaluation (α : E → K) (d : ℕ) :
    Polynomial.degreeLT K d →ₗ[K] (E → K) where
  toFun p i := Polynomial.eval (α i) (p : Polynomial K)
  map_add' p q := by
    ext i
    simp
  map_smul' c p := by
    ext i
    simp

@[simp] theorem polynomialEvaluation_apply (α : E → K) (d : ℕ)
    (p : Polynomial.degreeLT K d) (i : E) :
    polynomialEvaluation α d p i = Polynomial.eval (α i) (p : Polynomial K) :=
  rfl

variable [Fintype E]

/-- Distinct evaluation points give the expected rectangular matrix rank. -/
theorem evaluationMatrix_rank (α : E → K) (hα : Function.Injective α)
    (d : ℕ) :
    (evaluationMatrix α d).rank = min (Fintype.card E) d := by
  classical
  apply le_antisymm
  · apply le_min (Matrix.rank_le_card_height (evaluationMatrix α d))
    simpa only [Fintype.card_fin] using
      (Matrix.rank_le_card_width (evaluationMatrix α d))
  · let t := min (Fintype.card E) d
    let r : Fin t → E := fun i => (Fintype.equivFin E).symm
      ⟨i.val, lt_of_lt_of_le i.isLt (min_le_left _ _)⟩
    let c : Fin t → Fin d := fun i =>
      ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right _ _)⟩
    have hr : Function.Injective r := by
      intro i j hij
      apply Fin.ext
      exact congrArg (fun x : Fin (Fintype.card E) => x.val)
        ((Fintype.equivFin E).symm.injective hij)
    have hdet : (Matrix.vandermonde (α ∘ r)).det ≠ 0 :=
      Matrix.det_vandermonde_ne_zero_iff.mpr (hα.comp hr)
    have hsub : (evaluationMatrix α d).submatrix r c =
        Matrix.vandermonde (α ∘ r) := by
      ext i j
      simp [evaluationMatrix, evaluationVector, Matrix.submatrix, c]
    have hminor := Matrix.rank_submatrix_le (evaluationMatrix α d) r c
    rw [hsub, Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hminor
    exact hminor

/-- The evaluation rows span a space of dimension `min (number of points) d`.
This is the rank statement used by each block of the one-clause model. -/
theorem evaluationSpan_finrank (α : E → K) (hα : Function.Injective α)
    (d : ℕ) :
    Module.finrank K
      (Submodule.span K (Set.range (fun i : E => evaluationVector (α i) d))) =
      min (Fintype.card E) d := by
  calc
    Module.finrank K
        (Submodule.span K (Set.range (fun i : E => evaluationVector (α i) d))) =
        (evaluationMatrix α d).rank :=
      (Matrix.rank_eq_finrank_span_row (evaluationMatrix α d)).symm
    _ = min (Fintype.card E) d := evaluationMatrix_rank α hα d

omit [Fintype E] in
/-- The coefficient equivalence identifies polynomial evaluation with the
rectangular Vandermonde linear map. -/
theorem polynomialEvaluation_eq_matrix (α : E → K) (d : ℕ) :
    polynomialEvaluation α d =
      (evaluationMatrix α d).mulVecLin.comp
        (Polynomial.degreeLTEquiv K d).toLinearMap := by
  ext p i
  change Polynomial.eval (α i) (p : Polynomial K) =
    ∑ j : Fin d, (α i) ^ j.val * (Polynomial.degreeLTEquiv K d p) j
  rw [Polynomial.eval_eq_sum_degreeLTEquiv p.property]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [Fintype E] in
/-- The polynomial evaluation map and its coefficient matrix have the same
range, since every coefficient vector comes from a degree-bounded polynomial. -/
theorem polynomialEvaluation_range (α : E → K) (d : ℕ) :
    LinearMap.range (polynomialEvaluation α d) =
      LinearMap.range (evaluationMatrix α d).mulVecLin := by
  rw [polynomialEvaluation_eq_matrix]
  ext y
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨Polynomial.degreeLTEquiv K d p, hp⟩
  · rintro ⟨v, hv⟩
    refine ⟨(Polynomial.degreeLTEquiv K d).symm v, ?_⟩
    change (evaluationMatrix α d).mulVecLin
      ((Polynomial.degreeLTEquiv K d) ((Polynomial.degreeLTEquiv K d).symm v)) = y
    simpa only [LinearEquiv.apply_symm_apply] using hv

/-- D19's rank formula, including `d = 0` and an empty label type. -/
theorem polynomialEvaluation_finrank (α : E → K)
    (hα : Function.Injective α) (d : ℕ) :
    Module.finrank K (LinearMap.range (polynomialEvaluation α d)) =
      min d (Fintype.card E) := by
  rw [polynomialEvaluation_range]
  change (evaluationMatrix α d).rank = min d (Fintype.card E)
  simpa only [min_comm] using evaluationMatrix_rank α hα d

end BoundedArity
