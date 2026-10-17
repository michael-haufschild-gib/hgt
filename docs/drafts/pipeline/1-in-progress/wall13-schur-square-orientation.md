# Wall 13: Schur-square transfer and signed reconstruction

- **ID:** BSU-W13-SSO
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; dependency-closed paper proof recorded below
- **Scope:** BiScaleUncertainty, Wall 13 (cone mismatch). No RH work.
- **Goal:** Identify precisely what information a pointwise-positive Bochner transfer loses, and construct its signed recovery within an actual compact-source family.

## Plan

1. Audit corpus for modulus, tensor-square, and separated-copy results.
2. Prove an actual diagonal tensor realization, exact Lévy energy defect, and a complete separated-copy classification.
3. Formalize concrete constructions without unproved analytic premises.
4. Wire leaves, run serial direct Lean checks, audit axioms, refresh index, run lint, and record remaining wall.

`update_plan` is unavailable in this session; this card is the persistent plan.

## Corpus audit

Existing parents: `DistantCopyPolarEnforcement`, `DistantCopyCorrelationTopology`,
`DistantCopyPolarTopology`, `MultiNodeSignedCliqueWeilCoercivity`,
`SignedDyadicCollarPartition`, and `CompactSourceNodalVariance`.
Existing modulus-loss and one-sign rigidity results are not new contributions.

Search evidence: `/tmp/bsu-wall13-{corpus,modulus-search,square-search,sign-search}.json`.
All returned candidate and source-argument statements inspected. Modulus deep search
is partial (reranking deadline); other searches completed. Semantic coverage is
unmeasured, some snapshots older than current generation, compiler applicability
mostly source-only. No exhaustive novelty claim. Search results are discovery
evidence, not proof certification.

## Conjecture loop and paper proof

Let h(x)=integral f(u)f(u+x)du and R=h(0), for a compact continuous real source.

**C1: the square profile preserves the Bochner cone and every zero. PROVED ON PAPER.**
Set F_x(u,v)=f(u+x)f(v+x). Product integration gives
integral F_x F_y=h(y-x)^2. Therefore every finite Gram quadratic form of h^2
is the integral of a literal square. Also h(x)^2=0 iff h(x)=0. This is the
classical Schur product mechanism, with an actual product-space realization.
Reference for the classical parent: mathlib `Matrix.PosSemidef.hadamard`,
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Order.html.
Local APIs must still be checked against the installed toolchain.

The exact increment identity is

    (R^2-h(x)^2)+(R-h(x))^2=2R(R-h(x)).

Both summands are nonnegative since |h(x)|<=R. Integration against the positive
Lévy-sinh weight gives an exact extended-energy decomposition, without an
integrability premise or subtraction of infinities. This is the positive survivor.

**C2: squared data determine signed polar balance. FALSE ON PAPER.**
Choose a positive correlation support radius D from compactness and T=2D+1.
For g_a(u)=f(u)-a f(u-T), k(a)=a/(1+a^2), and H=h/R (division interpreted
as zero for the zero source), the existing exact copy formula gives

    H_a(x)=H(x)-k(a)[H(x-T)+H(x+T)].

The three packets have disjoint supports, hence

    H_a(x)^2=H(x)^2+k(a)^2[H(x-T)^2+H(x+T)^2].

For R>0, evaluation at T gives H_a(T)=-k(a). Consequently the complete squared
profiles agree iff k(a)^2=k(b)^2; the complete signed profiles agree iff
k(a)=k(b). In all cases, one signed anchor recovers the entire profile:

    H_a(x)=H(x)+H_a(T)[H(x-T)+H(x+T)].

For R=0 every correlation vanishes, covering the degenerate case explicitly.
The square equivalence is exactly the union of k(a)=k(b) and k(a)=-k(b).
No global phase-retrieval theorem is asserted.

For the concrete smooth nonnegative bump supplied by
`exists_smooth_source_positive_polar_moment`, take a=exp(-T/2).
The minus-copy g_a is polar-neutral. The plus-copy g_(-a) has the same squared
correlation at every real lag, the same mass, and exactly twice the seed's
normalized polar moment: the existing polar multiplier and
2a cosh(T/2)=1+a^2 give these assertions. Its moment is strictly positive.
Thus even all squared lag samples and the complete zero set cannot decide
polar neutrality. Smoothness and compact support are preserved by the explicit copies.

## No-go closure

- **Rejected claim:** a Schur-square profile can decide the original signed polar constraint.
- **Killing mechanism:** actual smooth opposite-copy sources with identical squared correlation and distinct polar moments.
- **Positive survivor:** literal tensor Gram realization, exact nonnegative quartic energy decomposition, complete copy-family ambiguity classification, and one-anchor signed reconstruction.
- **New insight:** blindness survives the nonlinear cone transfer, but orientation does not; retaining one oriented scalar suffices for the separated two-copy family.
- **Boundary:** arbitrary sources may have many independent correlation components. This does not prove any blind-source lower bound or close Wall 13.
- **Representation boundary:** the square has a literal source on the product plane with diagonal translations. No scalar one-dimensional factorization or decomposition into individually blind fibres is asserted.
- **Paper status:** proofs above use only compact integrability, existing copy identities, and polynomial identities.
- **Lean status:** pending.

## Next conjecture from the obstruction (unproved)

**C3: fixed-order closed correlation cycles cannot recover the missing orientation.**
For every m, choose a copy gap T>mD as well as T>2D. Conjecture: the plus/minus
copy sources have identical products along every closed lag cycle of length at
most m, despite their different polar moments. Candidate mechanism: each nonzero
lag belongs to one of the three disjoint packets centered at 0,+T,-T. Write each
lag as c_i T+e_i with c_i in {-1,0,1} and |e_i|<=D. Closure and T>mD force
sum c_i=0, so the number of signed outer-packet factors is even. This would imply
agreement of all Gram determinants of size at most m, by permutation cycles.

The prospective positive theorem is an exact separation/order bound for when
closed-cycle data can detect sign; the already identified signed anchor avoids
that order cost. The converse/sharp threshold, boundary cases, full determinant
statement and any extension to arbitrary sources remain unaudited and unformalized.
Do not count C3 as proved. Corpus search `/tmp/bsu-wall13-cycle-search.json`
completed; all 20 candidate and 20 source statements inspected. No matching cycle
classification returned. The results include this session's uncompiled draft,
which is not independent evidence. Semantic coverage remains unmeasured.

## Gates

- [x] Corpus audit and concrete wall-specific mechanism.
- [x] Dependency-closed paper proof.
- [ ] Exact theorem package formalized and axiom-audited.
- [ ] Leaf checks, wiring, index and lint inspected.
- [ ] Record next conjecture and remaining full-goal scope.

## Log

- 2026-10-18 — New active wall-specific task. Prior paused/cleared contribution-count programs are not revived. Full goal remains walls 2–15; this package is not completion.
