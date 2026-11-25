module

public import BoundedArity.ExactLocalRepresentation
public import BoundedArity.RankEntropy

/-!
# Exact finite-valued entropy witnesses for each local projection

T6 supplies an exact representation over the binary field. T7 turns that
representation into one finite joint law whose entropy entries, in bits,
equal the queried entries of the fixed formal table. The law is chosen after
the grouping and before its coalition quantifier.
-/

@[expose] public section

universe uP uG

namespace BoundedArity

variable {P : Type uP} {G : Type uG} [Fintype P] [Fintype G]
  [DecidableEq P] [DecidableEq G]

/-- Every local projection of the formal table is exactly a finite entropy table. -/
theorem localEntropy_checkpoint (Γ : AccessStructure P) (b : ℕ)
    (hr : 2 ≤ Fintype.card G) (hb : arityConstant (Fintype.card G) ≤ b)
    (A : G → Finset (Option P)) :
    IsFiniteEntropyTable.{uG,0}
      (groupProjection (fun S => (formalTable Γ b S : ℝ)) A) := by
  exact binary_rank_entropy_checkpoint (groupProjection (formalTable Γ b) A)
    (localRepresentability_checkpoint (K := ZMod 2) Γ b hr hb A)

/-- The constructed finite witnesses belong to the full countable validity domain. -/
theorem localEntropy_discrete_checkpoint (Γ : AccessStructure P) (b : ℕ)
    (hr : 2 ≤ Fintype.card G) (hb : arityConstant (Fintype.card G) ≤ b)
    (A : G → Finset (Option P)) :
    IsDiscreteEntropyTable.{uG,0}
      (groupProjection (fun S => (formalTable Γ b S : ℝ)) A) :=
  (localEntropy_checkpoint Γ b hr hb A).isDiscreteEntropyTable

/-- Exact local entropy at the arity coefficient used by the barrier. -/
theorem localEntropy_arity_checkpoint (Γ : AccessStructure P)
    (r : ℕ) (hr : 2 ≤ r) (A : Fin r → Finset (Option P)) :
    IsFiniteEntropyTable.{0,0}
      (groupProjection (fun S => (formalTable Γ (arityConstant r) S : ℝ)) A) := by
  exact binary_rank_entropy_checkpoint
    (groupProjection (formalTable Γ (arityConstant r)) A)
    (localRepresentability_arity_checkpoint (K := ZMod 2) Γ r hr A)

end BoundedArity
