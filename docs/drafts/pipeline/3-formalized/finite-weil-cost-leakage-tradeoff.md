# Native cost versus unavoidable coefficient leakage

- **ID:** finite-weil-cost-leakage-tradeoff
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** local Lean cluster envelope and the now-compiled coordinate-isolation obstruction.
- **Statement:** Retaining the obstruction's finite dual vector gives a quantitative tradeoff between native cost and unwanted coefficients, including an inverse-cutoff lower bound on leakage at low cost.

## Exact target

There exist B>0 and K>=2 such that for every N>=2K, writing q=N/K and E=2^q, there exist a coordinate i:range N and d:range N->Real with

    norm(d)=1, |d_i|=1, sum_(j!=i) |d_j| <= q-1,

such that every actual Gram test w, with coefficient vector y and native unit cost C(w), satisfies both

    E |y_i| <= B C(w) + E sum_(j!=i) |d_j| |y_j|,
    E |y_i| <= B C(w) + E (q-1) norm(y - Pi.single i y_i).

The coordinate and dual vector are fixed before w. Consequences for y_i=1:

- Cost <= E/(2B) forces off-coordinate supremum norm >= 1/(2(q-1)).
- Off-coordinate supremum norm <= 1/(2(q-1)) forces cost >= E/(2B).

The exact isolation bound is the zero-leakage specialization. The weighted version preserves finer information than the supremum-norm corollary.

## Local audit and attack

`research 'Gram leakage cost' --mode lexical --no-refresh --module WeilLogShift --json` returned no hits; exhaustive `leakage|crosstalk|cross.talk` source search over WeilLogShift leaves returned none. The source proof of coordinate isolation already constructs the required dual vector and discards it after evaluating a coordinate spike. The conjecture strengthens the receiver by retaining that witness and applying a finite-sum triangle inequality.

Verdict: **BRIDGE**; a positive quantitative survivor of the exact-isolation obstruction. No external sources, computations, or priority claims. The result concerns a selected coordinate at each cutoff. It does not require or imply instability at every coordinate.

## Dependency-closed paper proof [PROVED HERE]

1. Reuse the exact cutoff construction in the coordinate-obstruction proof: q=N/K>=2, r=q-2, k=N-q, and a cluster vector a:Fin(q)->Real of supremum norm one. Its kernel envelope has reciprocal cost scale Q=(k+2)^2 2^r>=E. Choose j0 with |a_j0|=1 and set i=k+j0. Extend a by zero to d on range N. This gives norm(d)=1 and |d_i|=1. Each of the other q-1 cluster coefficients has absolute value at most one, and every coefficient outside the cluster is zero. Therefore sum_(j!=i)|d_j|<=q-1.

2. The existing native sensitivity transfer gives, for every actual w,

       |sum_j y_j d_j| Q <= B C(w).

   Since Q>=E and the absolute value is nonnegative, the same inequality holds with E in place of Q. All constants and witnesses come from the unconditional geometric envelope; no new analytic estimate is assumed.

3. Split the finite sum into its i term and the remaining terms. Because |d_i|=1, the triangle inequality gives

       |y_i| <= |sum_j y_j d_j| + sum_(j!=i)|d_j||y_j|.

   Multiply by E>0 and apply step 2 to obtain the weighted cost-leakage inequality.

4. Put z=y-Pi.single i y_i. For j!=i, z_j=y_j, so |y_j|<=norm(z). Multiplying by the nonnegative |d_j| and summing, then using step 1, bounds weighted leakage by (q-1)norm(z). This proves the second inequality.

5. For y_i=1 the inequality becomes E<=B C(w)+E(q-1)norm(z). Both B and E(q-1) are positive. If C(w)<=E/(2B), rearrangement yields norm(z)>=1/(2(q-1)). If norm(z)<=1/(2(q-1)), rearrangement yields C(w)>=E/(2B). Boundary equality is retained. These are exact quantitative statements, without an additional asymptotic-growth lemma.

The existing polynomial-cost unit-response producer supplies actual cheap responses whenever its budget meets the stated threshold; exact realizability supplies actual zero-leakage responses at higher cost. No mathematical open core remains.

## Formalization plan

- [x] Local source audit, exact conjecture and complete paper proof.
- [ ] Strengthen the cluster producer to retain i,d, off-coordinate weight budget, and universal sensitivity; keep the existing exact-obstruction API as a consequence.
- [ ] Prove the weighted finite-sum cost/leakage inequality and supremum-norm corollary.
- [ ] Carry the existing cutoff budget into the unconditional all-test receiver and its two threshold consequences.
- [ ] Rebuild affected descendants; audit all public declarations, wiring, index and lint.
- 2026-10-10: Recorded before Lean edits. No code for this card exists. The coordinate-isolation final audit passed for all six public declarations and 110 API terms; all three native artifacts are fresh. Its card is now `../3-formalized/finite-weil-coordinate-isolation-cost.md`. All owned processes are terminal. This leakage-tradeoff card is now the active research step.


## Formalization completed — 2026-10-10

Stage: **3 — formalized**. This entry supersedes the earlier implementation plan.

The unconditional receiver `exists_finiteWeilGram_exponential_cost_leakage` is in
`formal/GaloisForLFunctions/RHTower/WeilLogShiftGramCostLeakage.lean:12`.
It chooses B > 0 and K >= 2 before the cutoff, then i and d before every actual
Gram test. It proves both the weighted leakage law and its sup-norm consequence.
The same file's `exists_finiteWeilGram_exponential_cost_leakage_threshold` at line 48
proves both half-budget implications for unit response.

`WeilLogShiftGramCoordinateObstruction.lean` now exposes the cluster and exponential
dual witnesses. Both old coordinate-obstruction statements remain unchanged as
corollaries. `WeilLogShiftGramLeakageAlgebra.lean` contains the finite extension,
coordinate-pairing, off-coordinate norm, and threshold algebra.

Verification: all four affected native leaves pass, including the existing
`WeilLogShiftGramIsolationSeparation.lean` receiver. All 13 affected public
declarations were audited in `/tmp/hgt-cost-leakage-audit.lean`; each uses only
`propext`, `Classical.choice`, and `Quot.sound`. The scratch audit also verifies
21 mathlib API terms. Source and direct-dependency artifacts are fresh; all four
leaves have exactly one umbrella import. The corpus index was refreshed and both
new receivers are discoverable by the documented research command.

Repository lint exits 1 solely for five unrelated missing umbrella imports:
`RHTower.XiReciprocalSliceNearestZero`,
`HTGeometry.PaperMoebiusPrimePrefixEscape`,
`HTGeometry.PaperPrimeEscapeAnalyticCost`,
`HTGeometry.QKrawtchoukCompanionTriangular`, and
`HTGeometry.ReciprocalPositivityMinimumModulus`.
No shared-worktree files were repaired outside this task.

Classification: corpus-internal quantitative bridge and positive survivor of
exact-isolation cost obstruction. No external novelty or priority claim. Research
sources are restricted to the local Lean corpus and installed Lean/mathlib.

Remaining question: determine from the actual cluster-envelope construction
whether its dual coefficients support a smaller off-coordinate absolute sum
than q - 1. The present theorem does not assert that its leakage factor is sharp.


## Moment-preserving follow-up — 2026-10-10

[Logarithmic-background leakage](finite-weil-moment-background-leakage.md) is now
formalized. Retaining the exact cluster moments makes the cost law invariant
under subtraction of arbitrary centered-log polynomial backgrounds through
order N/K-2. Every background-plus-spike target is realizable and still has an
exponential lower cost bound. The q-1 absolute-sum factor is not claimed sharp.
