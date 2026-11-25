# A result-oriented review

This repository can be reviewed without an expository paper or a reading of
the intermediate proof method. There are two separate jobs:

1. Run the verification command in the README. This checks proofs against the
   actual formal statements and enforces the accepted axiom list.
2. Read the definitions and final statements below to check that they express
   the intended mathematics. The checker cannot decide that correspondence.

All names in the table are in the namespace `BoundedArity`. A reader can use
VS Code's **Go to Definition** on a name. The proof after `:= by` is optional
reading for this specification review.

## Start with the conclusion

| What to inspect | File and declarations |
| --- | --- |
| Maximum-share objective, infima, and numerical conclusions | [RelaxationCeiling.lean](../BoundedArity/RelaxationCeiling.lean): `maxShare`, `FeasibleShareValues`, `relaxationValue`, `RankFeasibleShareValues`, `rankRelaxationValue`, `relaxation_ceiling`, `rank_relaxation_ceiling`, and their `_six` specializations |
| Exactly which constraints are imposed; order of quantifiers | [Barrier.lean](../BoundedArity/Barrier.lean): `FeasibleAtArity`, `RankConstraintsAtArity`, `RankFeasibleAtArity`, `barrier_checkpoint`, `barrier_exists_witness` |
| Arbitrary real coefficients and meanings of valid information/rank inequalities | [InformationInequalities.lean](../BoundedArity/InformationInequalities.lean): `inequalityValue`, `ValidInformation`, `ValidRank` |
| One joint law, its alphabets and all its marginals | [DiscreteJointLaw.lean](../BoundedArity/DiscreteJointLaw.lean): `DiscreteJointLaw`, `DiscreteJointLaw.FiniteJointEntropy`, `DiscreteJointLaw.jointEntropy`, `IsDiscreteEntropyTable`, `IsFiniteEntropyTable` |
| Actual Shannon entropy, in bits | [DiscreteEntropy.lean](../BoundedArity/DiscreteEntropy.lean): `pmfEntropyTerm`, `pmfEntropy`, `pmfEntropyReal`; the proved finite-entropy sum identities connect these definitions to the usual sum |
| One common finite-dimensional rank representation | [LinearRank.lean](../BoundedArity/LinearRank.lean): `LinearRankRealizes` |
| Proper monotone access structure | [Interpolation.lean](../BoundedArity/Interpolation.lean): `AccessStructure` |
| Polymatroid and normalized privacy/reconstruction conditions | [FormalTable.lean](../BoundedArity/FormalTable.lean): `IsPolymatroid`, `HasNormalizedAccess`, `physicalLift`, `unauthorizedBit` |
| The fixed witness and its coefficient | [FormalTable.lean](../BoundedArity/FormalTable.lean): `physicalTable`, `formalTable`; [PairCoverage.lean](../BoundedArity/PairCoverage.lean): `pairsMeeting`, `pairCoverage`; [Checkpoint3.lean](../BoundedArity/Checkpoint3.lean): `arityConstant` |
| How an inequality is applied to groups | [GroupModel.lean](../BoundedArity/GroupModel.lean): `groupProjection`; [ArityRestriction.lean](../BoundedArity/ArityRestriction.lean): `localRepresentability_le_arity_checkpoint`, `localEntropy_le_arity_checkpoint` |

## Details that matter for the statement

- The participant type is finite. Properness implies that there is at least
  one participant; `AccessStructure.nonempty_participants` proves this.
- `Option P` represents the full index set: `none` is the secret and `some p`
  is participant `p`. The secret has normalized value one.
- The bound has `r >= 2`. The constraints quantify over every `k <= r`,
  including zero and one.
- Each group is an arbitrary subset of the full index set. Groups may overlap,
  repeat, be empty, contain the secret, and contain arbitrarily many shares.
  Arity counts groups, not physical participants.
- Information validity quantifies over arbitrary countable alphabets and one
  joint law with finite full-joint entropy. Its finite marginals have finite
  entropy. The particular witnesses constructed here have finite alphabets.
- Rank validity uses one finite-dimensional ambient space for all subspaces
  in a representation. The field can be any field; there is no field-size or
  characteristic condition.
- The same explicit formal table depends only on the access structure and
  `r`. It is chosen before fields, coefficients, and groupings. Different
  groupings may have different local representations.
- The displayed value is exactly the maximum of the witness's physical
  singletons. The optimum of the relaxation is **at most** this value; equality
  of the optimum is not claimed.

## Scope of the formal theorem

The code proves a theorem about the explicitly defined entropy/rank
relaxations. It includes the entropy construction used to verify their
inequalities. It does not define a separate bundled perfect-secret-sharing
scheme and formalize the general conversion from every such scheme to a
normalized entropy table. The usual interpretation of a feasible-table
ceiling as a limitation of the stated lower-bound method is explained in
the README.

It also does not assert a global small-share scheme, compatibility with
arbitrary auxiliary-variable extensions, or secret-alphabet-specific
constraints. The optional common-conditioning extension with the **same
coefficient** and the later asymptotic/counting statements from the working
manuscript are outside this implementation.

The maintained entry point is `BoundedArity.lean`, which imports the final
theorems. Historical milestone reports are retained in `verification/`.

## Review provenance

Christopher Williamson reviewed every section marked VERIFY in a 35-page
specification packet. The milestone records distinguish that human review
from subsequent assistant comparisons of the implementation with it.
Those records do not represent an independent external mathematical review.
