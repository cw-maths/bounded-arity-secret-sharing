# Bounded-arity barrier: main formalization complete

**Milestones T1–T8 are implemented and verified.** Milestone 8 assembles the
single-table barrier from the reviewed specification and proves its numerical
ceiling, including the prescribed-field rank version and the six-variable
bound `6*N - 5`.

## Verification

The full project was built and audited on 24 November 2026:

- `lake build`: completed successfully, **7458 jobs**.
- `lake env lean AxiomAudit.lean`: exit code 0, no warnings or errors.
- **138 declarations audited**; every reported axiom set is a subset of
  `propext`, `Classical.choice`, and `Quot.sound`.
- No proof placeholders, project axioms, unsafe declarations, or `native_decide`
  calls occur in the project sources.
- All 32 earlier proof modules are byte-for-byte unchanged.
- All three new modules compile without warnings. The existing harmless
  unused-section-variable warning in `FormalTable.lean` remains.

Complete command output is in `verification/milestone_8.txt`. Dependency
revisions and source hashes are in `verification/milestone_8.json`.
`verification/FINAL_SPECIFICATION.txt` maps the final definitions and statements
to approved E31, E32 and T8. The E28 comparison from milestone 7 is preserved.
Earlier verification records and historical module introductions describe
their original milestones; the verification status above applies to the
complete current project.

## The final theorem

Let Gamma be a proper monotone access structure on N finite participants and
let r >= 2. Put

    c_r = choose(r - 2, floor((r - 2)/2)),
    F(X) = (formalTable Gamma (arityConstant r) X : Real).

This SAME explicit table has all the following properties:

1. It is a polymatroid and satisfies every normalized access equality,
   including secret value one.
2. It satisfies every valid homogeneous information inequality on k <= r
   grouped variables, for every grouping of original share/secret indices.
3. For every prescribed field K, it also satisfies every homogeneous
   K-linear-rank inequality at arity at most r.
4. Every physical singleton has value exactly `1 + c_r*(N - 1)`.

The information-validity domain remains arbitrary countable alphabets with
finite full-joint entropy. Coefficients are arbitrary real numbers. Groups
may be empty, repeated, overlapping, of any size, and may contain the secret.
The quantifiers explicitly include k=0 and k=1. There is no field-size or
characteristic condition for the rank conclusion.

The table is fixed before fields, inequalities and groupings are chosen.
The local models used to verify different groupings may be different.

## The objective ceiling

`maxShare F` is the actual maximum of the physical singleton entries. The code
proves it is attained and proves its equivalence with the reviewed pointwise
predicate `MaxShareAtMost`. Properness gives at least one participant.

`relaxationValue r Gamma` is the infimum of `maxShare F` over information-feasible
tables. `rankRelaxationValue K r Gamma` is the analogous infimum after adding
all prescribed-field rank constraints. Their sets of objective values are
proved nonempty and bounded below. The final conclusions are

    relaxationValue r Gamma <= 1 + c_r*(N - 1),
    rankRelaxationValue K r Gamma <= 1 + c_r*(N - 1).

These are upper bounds on the relaxation optima. For r=6 both are formally
specialized to `6*N - 5`. The witness itself attains the displayed ceiling;
the infimum may be smaller for a particular access structure.

## Principal declarations

All names below are in namespace `BoundedArity`.

| Declaration | Meaning |
| --- | --- |
| `FeasibleAtArity` | The exact E31 information relaxation |
| `RankConstraintsAtArity` | All prescribed-field rank constraints |
| `RankFeasibleAtArity` | Information and rank constraints on one table |
| `localRepresentability_le_arity_checkpoint` | Exact local ranks for every k <= r |
| `localEntropy_le_arity_checkpoint` | Exact finite entropy witnesses for every k <= r |
| `barrier_checkpoint` | T8 for the explicitly fixed formal table |
| `barrier_exists_witness` | One witness before all fields, inequalities and groupings |
| `maxShareAtMost_iff` | The reviewed pointwise bound equals a maximum bound |
| `formalTable_maxShare` | Exact maximum physical-share value of the witness |
| `relaxation_ceiling` | The information-relaxation infimum bound |
| `rank_relaxation_ceiling` | The rank-strengthened infimum bound over every field |
| `relaxation_ceiling_six` | The information bound `6*N - 5` |
| `rank_relaxation_ceiling_six` | The rank-strengthened bound `6*N - 5` |

## Update the Mac project

Save `bounded_arity_lean_milestone_8.zip` in Downloads, then run these commands
one line at a time in Terminal:

```sh
unzip -o "$HOME/Downloads/bounded_arity_lean_milestone_8.zip" -d "$HOME/Documents"
cd "$HOME/Documents/bounded_arity_lean"
lake build
lake env lean AxiomAudit.lean
```

An existing milestone-7 installation has the needed dependencies. The source
archive preserves its dependency caches when extracted over the same project
folder. For a fresh installation, run `lake exe cache get` before the build
to obtain the full pinned mathlib cache.

The audit prints the exact feasible-set definitions, the maximum and infimum
definitions, the final theorem types, and their transitive axiom dependencies.
It preserves all previous audit entries as well.

## New modules

| File | Purpose |
| --- | --- |
| `BoundedArity/ArityRestriction.lean` | Pad with empty groups and restrict one common model; includes k=0,1 |
| `BoundedArity/Barrier.lean` | Approved E31 definitions and final T8 witness, independent of all tests |
| `BoundedArity/RelaxationCeiling.lean` | Actual maximum objective, nonempty/lower-bounded infimum sets, both ceilings and six-variable specializations |

## Proof outline — optional reading

A query with k <= r groups is padded with empty groups. The existing exact
T6 model for r groups restricts to one common model for the original labels,
with the coefficient still fixed at c_r. This includes zero and one groups.

For information inequalities, take the binary-field model and apply T7 to
obtain one finite joint law with exactly those entropies in bits. For rank
inequalities, use the exact model over the prescribed field directly. In each
case, universal validity applies to the chosen model and verifies an inequality
on the corresponding entries of the same global formal table.

T3 supplies the whole-table polymatroid and access conditions and the exact
physical singleton values. Consequently this table belongs to both feasible
sets and its actual maximum is `1 + c_r*(N - 1)`. Each objective infimum is at
most that attained value. At r=6, properness ensures N>=1 and the arithmetic
simplifies to `6*N - 5`.

## Completed scope

The main reviewed milestones **T1–T8 are complete**. The result is a ceiling on
the specified relaxation. Local models can vary with the grouping; the theorem
does not assert a global small-share scheme for each access structure.

Optional common conditioning from Appendix B and the arity-growth/counting
consequences from Section 6 remain separate extensions outside this main scope.
The exact every-field construction makes the alternate restriction-of-scalars
route unnecessary. This package does not claim that alternate proof or the
optional extensions.

## Version pins

- Package version: `0.8.0`.
- Lean: `leanprover/lean4:v4.36.0`.
- Lean executable commit: `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`.
- mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
- All nine dependency revisions: unchanged `lake-manifest.json`.

Specification sources: the approved 35-page review packet, particularly E31,
E32 and T8, and the main theorem / ceiling corollary of the expanded manuscript.
