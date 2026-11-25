# A linear barrier for bounded-arity information inequalities

Lean 4 formalization developed by Christopher Williamson with substantial
ChatGPT assistance. This is a **private review snapshot**, prepared for
checking and mathematical discussion. It is self-contained as a formal
project; an expository paper is not needed to run the checks.

## The result

For every proper monotone access structure on a finite set of $N$ participants
and every integer $r\ge2$, put

$$c_r=\binom{r-2}{\lfloor(r-2)/2\rfloor}.$$

There is **one fixed normalized formal entropy table** that satisfies:

- all whole-table polymatroid (Shannon) conditions;
- every privacy and reconstruction equality, with secret value one;
- every valid homogeneous information inequality on at most $r$ grouped
  variables, applied to every choice of groups;
- all the corresponding homogeneous linear-rank inequalities over every
  prescribed field, on that same table.

Every physical singleton of the table, and hence its maximum-share objective,
has the exact value

$$1+c_r(N-1).$$

Consequently the information relaxation, and its strengthening by all
prescribed-field rank constraints, have optimum **at most** this value. For
$r=6$, the bound is **$6N-5$**.

### What this says about lower-bound methods

A lower bound certified by these constraints must hold for every feasible
table. The displayed feasible table therefore limits the lower bound that
these constraints can certify. For any **fixed** $r$, this ceiling is linear
in $N$, even if every valid inequality of that arity is available and they
are used together. The coefficient depends on $r$.

This is a limitation of the specified relaxation. It does not construct a
single secret-sharing scheme with these share sizes. The local models for
different choices of groups may differ.

### Exact scope

Arity counts **groups**, not participants. Each group is an arbitrary subset
of the original share and secret indices. Groups may be empty, repeated,
overlapping, arbitrarily large, or contain the secret. All $k\le r$ are
included, even $k=0,1$.

Information inequalities have arbitrary real coefficients and are homogeneous.
Validity is defined for arbitrary countable alphabets with finite full-joint
entropy. The constructed local witnesses have finite alphabets and realize
the table exactly in bits. Every grouped projection is also exactly linearly
representable in a common finite-dimensional space over **any field**, without
a field-size or characteristic restriction.

The explicit table depends only on the access structure and $r$, before any
fields, inequalities, or groups are chosen. The core formal statements are
`BoundedArity.barrier_checkpoint`, `barrier_exists_witness`,
`relaxation_ceiling`, and `rank_relaxation_ceiling`. Their six-variable
specializations end in `_six`.

## Verify the repository

Install the [Lean 4 VS Code extension / Lean toolchain manager](https://lean-lang.org/install/)
if needed. In a terminal at the repository root, run:

```sh
lake exe cache get
bash scripts/verify.sh --fresh-build
```

The first command retrieves compiled dependencies at the committed versions.
The second rebuilds this project's sources with warnings treated as failures,
prints the selected theorem statements and axioms, enforces an axiom allowlist
for every declaration defined in the project's proof modules, and replays
the compiled declarations and imports through Lean's kernel. It exits
unsuccessfully if a required check fails.
`--fresh-build` clears only this project's build output, retaining dependency
caches. Logs are kept in `.verification/`.

The accepted axioms are exactly the allowlist
`propext`, `Classical.choice`, and `Quot.sound`; each audited declaration may
use a subset. The audit rejects proof placeholders and unexpected axioms in
transitive dependencies. [AxiomAudit.lean](AxiomAudit.lean) also provides a
readable report of 138 selected declarations; that printout alone is not the
automated gate.

The included GitHub Actions workflow runs verification on pushes, pull
requests, and manual requests. A workflow file is a recipe: the first actual
GitHub run happens after the repository is uploaded. Check the run's result
for the exact commit you are reviewing.

**Kernel replay uses the same Lean kernel implementation.** It starts from
an empty checking environment and checks the stored proof objects and their
imports again, without rerunning the tactics that produced them. It is an
additional check of the stored proof/dependency chain, not a check by a
separately implemented logic engine. See
[Lean's validation guide](https://lean-lang.org/doc/reference/4.36.0/ValidatingProofs/).

The release's observed checks and limitations are recorded in
[verification/RELEASE_CHECK.txt](verification/RELEASE_CHECK.txt). Earlier
milestone logs are historical evidence for their original source versions.

### Inspect the meaning

Start with [Barrier.lean](BoundedArity/Barrier.lean) and
[RelaxationCeiling.lean](BoundedArity/RelaxationCeiling.lean). The compact
[review guide](docs/REVIEW_GUIDE.md) points to the definitions needed to assess
the result, without requiring a reading of the intermediate proof method.
A successful check establishes the formal propositions; a mathematical reader
still checks that those propositions mean what is intended.

## Relationship to earlier work

The main advance is the **linear ceiling for every fixed arity**.

| Earlier result | Ceiling on the maximum-share lower bound certifiable by the stated constraints |
| --- | --- |
| Csirmaz, Shannon constraints | Linear in $N$ |
| Beimel–Orlov, all four- and five-variable rank/information inequalities | Linear in $N$; also treats specified higher-arity families |
| Martín–Padró–Yang, all fixed-arity rank/information inequalities | $\sum_{i=0}^{r-2}\binom{N-1}{i}=O_r(N^{r-2})$ |
| This formalization, every fixed arity $r$ | $1+c_r(N-1)=O_r(N)$ |

The earlier literature already permits groups of original indices and uses
local representations. Those features by themselves are not the novelty.
The improvement is retaining a linear objective for every fixed arity,
including six and above, while satisfying all the stated constraints together.

References:

1. László Csirmaz, *The Size of a Share Must Be Large*, Journal of Cryptology
   10 (1997), 223–231, Theorem 3.5.
   [Paper](https://www.cs.umd.edu/~gasarch/TOPICS/secretsharing/sizelarge.pdf).
2. Amos Beimel and Ilan Orlov, *Secret Sharing and Non-Shannon Information
   Inequalities*, IEEE Transactions on Information Theory 57(9) (2011),
   5634–5649. Preliminary version: TCC 2009.
   [Publication record](https://cris.bgu.ac.il/en/publications/secret-sharing-and-non-shannon-information-inequalities-2/).
3. Sebastià Martín, Carles Padró, and An Yang, *Secret Sharing, Rank
   Inequalities, and Information Inequalities*, IEEE Transactions on
   Information Theory 62(1) (2016), 599–609, Theorem 6.2.
   [Final manuscript](https://eprint.iacr.org/2013/082).

The sum in the table is the final Martín–Padró–Yang bound. Its October 2014
[earlier draft](https://web.mat.upc.edu/carles.padro/papers/ssriii.pdf), Theorem
5.2, instead states $\binom{N+r-3}{r-2}$; both have the same polynomial order.
A targeted literature check supports the comparison above, but is not an
exhaustive certification of historical priority.

Useful discussion questions include what growing arity can achieve, which
auxiliary-variable compatibility constraints go beyond this relaxation, and
whether the coefficient $c_r$ can be improved. The ceiling still permits
better constants and better bounds for particular access structures.

## Formalized scope and provenance

The main reviewed milestones T1–T8 are implemented. The separate
common-conditioning extension with the same coefficient, later asymptotic
and counting results, and arbitrary auxiliary-variable extension systems
are outside this implementation. A separate bundled definition of a
secret-sharing scheme and its general translation into the relaxation is
also not part of this project's formal interface.

[AI_ASSISTANCE.md](AI_ASSISTANCE.md) records the development assistance and
human specification review. [REVIEW_STATUS.json](REVIEW_STATUS.json) and the
historical logs preserve the review history. This snapshot has not received
independent external mathematical review.

## Versions and sharing

- Project version: `0.8.1` (repository preparation of the verified `0.8.0`).
- Lean: `leanprover/lean4:v4.36.0`.
- mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
- All dependency revisions are committed in `lake-manifest.json`.

The final mathematical definitions and main theorem statements are preserved.
Cleanup removes obsolete source-status comments and an unused typeclass
parameter from one helper theorem; it adds reproducible verification and
review documentation.

For a small initial audience, use a private GitHub repository and invite
reviewers with Read access. [GitHub setup directions](docs/GITHUB_SETUP.md)
explain how to create an organization under your existing personal login and
upload this repository. `CITATION.cff` identifies this review snapshot; its
commit is the precise version to discuss. Public release, archival DOI,
publication-stage licensing and the expository paper can be addressed later.
