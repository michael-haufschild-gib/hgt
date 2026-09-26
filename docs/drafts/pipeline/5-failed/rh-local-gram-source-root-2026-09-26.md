# Local Gram realizations of the complete theta form

- **Owner:** root; own research card.
- **Type:** [BRIDGE], source representation test; no RH conclusion.
- **Goal:** Test whether the missing all-degree source sign can come from a local weighted
  odd-monomial Gram energy, including a fixed finite number of derivatives.
- **Stage:** 5-failed: C4 and C5 refuted; positive survivor fully formalized.
- **Status:** Named leaf build and all 24 public theorem axiom audits pass.

## Source and whole-route relevance

`theta-all-degree-hankel-producer.md` leaves an actual positive operator in the odd-source
Gram space open. `ThetaRawGramGrowthObstruction` proves raw moment ratios tend to infinity
and excludes equality with the unweighted Gram matrix. `MonotoneSourceGramContraction`
defines the full cleared matrix. The new charge-line Hardy rigidity is already in
`ThetaCuspChargeHardyRigidity`; reproducing it would not add knowledge.

The live problem is an all-degree sign producer. A local integral of squares would supply
one if it reproduced the actual coefficients. This test asks whether that mechanism is
even compatible with the full arithmetic source. It does not assume RH or any zero location.

## Mechanism tests

**C4, weighted multiplication.** Could one change the source weight so that the cleared
matrix becomes its odd-monomial Gram matrix? **Paper failure:** its entire first row already
fixes every positive moment. Thus every such Gram matrix equals the unweighted one, which
the existing exact second-row theorem excludes. This argument permits arbitrary signed
moment sequences; boundedness, positivity and moment determinacy are unnecessary.

**C5, fixed finite local differential energy.** Could a fixed finite collection of local
derivative pairings represent the cleared form? This is a derived mechanism test, not a
primary universal conjecture. A pairing of derivatives of orders at most r has factorial-
rescaled entries on every anti-diagonal equal to a polynomial in the row index of degree
at most 2r. Arbitrary cross terms and signed coefficient weights are allowed.

## Exact paper argument and positive survivor

Write m_j for normalized theta even moments and

`B_ij = 2 sum_(k<=min(i,j)) (i+j+1-2k) m_(i+j+1-k) m_k /
         ((2(i+j+1-k))! (2k)!)`,

`A_ij = (2i+1)! (2j+1)! B_ij`.

1. `A_0j=m_(j+1)` exactly, since m_0=1.
2. For every fixed i>0, `A_ij/m_(i+j+1) -> 0` as j tends to infinity.
   In the k=0 summand, cancellation of the largest factorial factor leaves a factorial
   ratio bounded by `1/(j+1)`. For 1<=k<=i, the remaining factorial factor is uniformly
   bounded, while `m_(i+j+1-k)/m_(i+j+1) -> 0`. The latter follows by multiplying k
   successive inverse moment ratios; the corpus proves every such ratio tends to infinity.
   There are only i+1 summands. All moments and summands are nonnegative.
3. On a common anti-diagonal n, therefore, `A_(i,n-i)/m_(n+1)` tends to 1 at i=0
   and to 0 at every fixed positive integer i.
4. These values cannot be restrictions of polynomials of uniformly bounded degree d.
   Interpolation at 1,...,d+1 expresses the value at 0 as a fixed linear combination
   of those d+1 values. Its limit would be both 1 and 0.
5. For a local pairing of derivatives of monomials, rescaling cancels the original
   factorials. The remaining factors are falling factorials of 2i+1 and 2(n-i)+1;
   the coefficient moment depends only on n and the two derivative orders. Thus each
   anti-diagonal has degree bounded by their maximal sum. Step 4 excludes every fixed
   finite-order realization of this type.

**Positive survivor:** the complete source has the exact normalized anti-diagonal limit
in steps 1–3. This is a constraint on every prospective realization, not merely a negative
answer for one weight. An admissible representation must use nonlocal features, unbounded
derivative order, or a different degree-dependent feature map. No arbitrary positive
operator, arbitrary integration-by-parts proof, or RH proof is excluded.

## Verification scope

1. Check novelty against corpus mechanism, deep and lexical search; source-check hits.
2. Verify C4, the normalized row limit and polynomial interpolation obstruction in Lean.
3. State the exact formal scope of the finite-derivative consequence; do not equate a paper
   translation with a checked theorem about arbitrary measurable differential forms.
4. Named leaf build, axiom audit, umbrella wiring, corpus index and lint. No git or numerical
   experiment. Update only root's facts and this card.

## Closed Lean result

`formal/GaloisForLFunctions/RHTower/ThetaLocalGramObstruction.lean`, namespace
`RHTower.LocalGram`, proves the precise coefficient-level exclusion

`not exists r w, forall i j,
   A_ij = sum_(a,b<=r) (2i+1)_a (2j+1)_b w(a,b,i+j)`,

where falling factorials are literal `Nat.descFactorial` and w is arbitrary real data.
`localJetPolynomial_eval` and `localJetPolynomial_degree` prove that this entire class
has anti-diagonal polynomial degree at most 2r. Thus the fixed finite-derivative
translation is checked algebraically, including signed cross terms and vanishing
high derivatives. No regularity or positivity of w is assumed. The formal theorem is
about the displayed matrix class; an individual integral implementation must still
identify its coefficients with that class.

Principal checked statements:
- `theta_no_weighted_moment_gram`: even signed reweighting cannot repair the matrix.
- `rescaled_row_tendsto_zero`: generic positive moments with divergent successive ratios.
- `theta_antidiagonal_limit`: exact literal-theta positive survivor.
- `theta_no_bounded_degree_antidiagonals`: excludes every uniform polynomial degree.
- `theta_no_finite_local_jet_gram`: excludes all fixed finite local derivative orders.

Scratch `/tmp/rh-local-gram.lean` passed. Named leaf build
`/tmp/rh-local-gram-build.log` passed (9027 jobs). All 24 public theorem axiom reports
in `/tmp/rh-local-gram-axioms.log` contain only `propext`, `Classical.choice`,
`Quot.sound`, none missing. Leaf wired into `RHTower.lean`.

The corpus searches inspected candidate lemmas, source arguments and method ingredient
sets. Retrieval completed, source inventory complete; compiler metadata largely
pending/stale. The closest inspected parent is `ThetaRawGramGrowthObstruction`:
its literal unweighted-row obstruction does not state this arbitrary-weight or all-fixed-
derivative-order result. No global novelty claim is made.

**Whole route:** this closes a concrete all-degree local-energy mechanism. It does not
exclude a nonlocal positive operator, an order growing with polynomial degree, a different
feature map, or an integration-by-parts argument that does not assert this fixed local
Gram identity. Those distinctions are necessary; RH remains open. Do not spend the next
attack increasing a fixed derivative cutoff: the theorem already quantifies over all of them.

## Repository gate at closure

Index regeneration succeeded twice. Final `lint --check-generated` failed on three
concurrently added modules missing umbrella imports: `ThetaCuspChargePowFarField`,
`ThetaCuspChargePowSaddle`, `ThetaCuspChargePowWindow`, and generated API/overview
staleness as these source additions continued. No error names the new local-Gram leaf.
Those other modules were not edited. Logs: `/tmp/rh-local-gram-index-final.log`,
`/tmp/rh-local-gram-lint-final.log`. Global lint is not claimed to pass.
All owned Lean, search, index and lint handles exited. No numerical experiments or git commands.
