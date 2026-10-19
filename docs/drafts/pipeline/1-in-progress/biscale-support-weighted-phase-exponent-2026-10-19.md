# Support-weighted arithmetic phase degree and local inverse exponents

- **ID:** biscale-support-weighted-phase-exponent-2026-10-19
- **Stage:** 1-in-progress
- **Type:** Conjecture and proof outline; uncounted
- **Source:** [100-contribution programme](biscale-100-contribution-programme-2026-10-18.md)
- **Dependency:** [Parity-neighborhood package](../3-formalized/biscale-parity-neighborhood-phase-transitions-2026-10-19.md) is formalized and audited as package 7. This route remains uncounted.

## Question

Can a finite arithmetic invariant determine the optimal pairwise fifth/sixth-array Hölder exponent near every nonzero actual sieve signal, including arbitrary changes of zero support? The invariant must use explicit resonance tuples and dyadic phase patterns, not assume an inverse estimate or hide it in a predicate.

The parity cutoff result suggests that counting the factors whose base coordinates vanish is the relevant degree. A general theorem must also account for magnitude recovery and first-order visibility. A blanket lower floor of degree two would miss locally Lipschitz strata.

## Prior evidence and limits

The searches `/tmp/bsu-100-next-{anchor-arithmetic,weighted-phase,support-strata}-search.json` were fully reviewed at the returned candidate/source-statement and prose/passage-inventory level. All are non-partial; inventory sizes are 74,353, 74,353 and 74,354. Semantic coverage is unmeasured and compiler refresh incomplete. Some indexed statements stop at `let`; those are not full applicability checks. The broad weighted query was mostly unrelated. Its proposed energy-perturbation chain does not prove an inverse modulus. The focused proposed chain only rescales an already known Hölder property and is rejected.

Existing exact canonical translation, fixed-block sixth stability, arithmetic edge phase codes, highest-mode cubic stability, parity-neighborhood bounds, and general Fourier/monomial mechanisms are prior ingredients. The older mixed-stability card explicitly rules out using a support-dependent coefficient quotient as a global physical metric. This route must retain actual translations throughout. No mathematical novelty follows from a missing search hit. Primary-literature comparison for the proposed general invariant remains open.

Whole-corpus `/tmp/bsu-100-next-local-monomial-search.json` is non-partial with 74,356 inventoried files. All 40 candidate/source statements, prose/passage inventories and the generated proposal were inspected. It mostly retrieves unrelated orbit-degree and local-inverse results. The orbit-degree linearity proposal does not prove any inverse modulus. Semantic coverage is unmeasured and compiler refresh incomplete; a focused native resonance query follows.

[Cahill–Iverson–Mixon, Theorem 21 and Example 22](https://arxiv.org/pdf/2305.17241) already explain differentiability obstructions to Lipschitz invariant recovery at nontrivial stabilizers and the role of vanishing Fourier coefficients in bispectrum recovery. Those mechanisms are not new here. Their theorem concerns a group representation on an invariant ambient space; the actual sieve coordinate family is not closed under arbitrary translations, so application to its restricted metric requires checking the domain. [Bürgisser–Doğan–Makam–Walter–Wigderson, Theorem 1.3 and Corollary 1.5](https://drops.dagstuhl.de/storage/00lipics/lipics-vol200-ccc2021/LIPIcs.CCC.2021.32/LIPIcs.CCC.2021.32.pdf) give fixed-support Laurent generators and separating monomials for torus orbit problems. They establish prior algebraic separation tools; the displayed statements do not give the proposed optimal local exponent for literal fifth/sixth sieve arrays. A general weighted-monomial argument alone still earns no contribution without a substantive native arithmetic consequence.

## Candidate invariant

Fix N and a nonzero base profile with admitted support S. Let I be the admitted orders 1 through N. For each T contained in I minus S, consider sign assignments σ on T, extending by +1 on S. Put U=S∪T and v=max of the two-adic valuations of orders in U.

The allowed patterns are identity and, only when v>0 and no element of S has depth v, reversal of every order in the highest block. This is the existing actual-translation classification; it is not an independently assumed group action on all coefficient space.

A word is a zero-sum frequency tuple of length five or six whose additive orders lie in U. Its cost is the number of entries with order outside S, with repetitions. It detects σ when the product of its signs is −1. For a nonallowed σ, let its detection cost be the least cost of a detecting word. Exact fifth/sixth recovery should show such a word exists and its cost is at most six.

An order q outside S is linearly visible if some word of length five or six has exactly one entry of order q and all remaining entries in S. Set the magnitude degree to one when every missing order is linearly visible, and to two otherwise. Let D be the maximum of that magnitude degree and all the detection costs over all T and all nonallowed σ; an empty phase maximum contributes zero.

**Conjecture:** the optimal actual local pairwise exponent is exactly 1/D. This would give a finite arithmetic classification, with 1≤D≤6, rather than a bound carrying an unproved recovery premise. The complete theorem and a substantive new arithmetic application must pass novelty and Lean audits together before any contribution is counted.

## Proof outline requiring audit

1. Rescale the nonzero base coordinates away from zero, and choose a bounded physical neighborhood. Sixth pure-coordinate readouts give linear control on all coordinates in S. One fixed nonzero anchor gives square-magnitude control for every missing coordinate. All these are actual raw-array consequences.
2. If D≥2, threshold missing coordinates at a constant times ε^(1/D), keeping S. Round competitor magnitudes to source magnitudes. A detecting word of cost at most D cannot change sign: retained missing factors exceed the threshold and base factors have a positive lower bound. The definition of D then forces an allowed phase pattern, realized by the existing canonical natural translation. Coordinate error bounds give the physical modulus.
3. If D=1, each missing coordinate has a linear monomial readout with all other factors in S. Linear control of the S factors and a finite product-difference estimate give linear control of that coordinate. No square-root rounding loss is used.
4. If the magnitude degree is two, an invisible missing order gives the pair consisting of the base and the base plus t times that Ramanujan mode. Every changed resonant product has at least two small factors. The missing Fourier coefficient forces physical distance at least t under every translation.
5. A maximal-cost nonallowed sign pattern gives base plus t times its chosen missing modes, with the two signs prescribed by σ. Every changed raw product has at least D small factors. For each shift, normalized Fourier coefficients detect a nonzero phase discrepancy. There are finitely many shifts modulo N!, so the smallest positive discrepancy is positive. Taking t below every nonzero base magnitude gives a uniform lower bound c*t for every translation. This avoids replacing physical distance by a changing coefficient quotient.
6. Apply the existing small-power obstruction. For D=1, also prove no exponent above one by a local amplitude perturbation; the main theorem cannot omit this endpoint.

## Arithmetic leads, not established claims

Pure dyadic anchors suggest thresholds governed by cutoff relative to anchor depth. Those alone may be a routine rescaling of the parity argument and must not be counted separately. Odd factors of an anchor can alter detection cost: they can remove the singleton-prime obstruction used in a parity witness. Prime-power exponents, not only prime support, may matter. A general classification needs an actual arithmetic application beyond renaming this observation.

As a small diagnostic case, a base supported at order three at cutoff three appears to have a square-root local exponent: the constant direction is linear and the sole parity perturbation is seen quadratically modulo its actual sign-changing translation. This has not been checked in Lean or through a complete prior-work audit and is not a separate proposed contribution.

## Gates

- [ ] Complete applicability and classical-content comparison.
- [ ] Audit every step of the proposed invariant theorem on paper, including empty missing support and D=1.
- [ ] Prove a substantive arithmetic consequence not already in the corpus.
- [ ] Formalize unconditional actual-object conclusions and audit all dependencies.
- [ ] Named-source checks, exact-once umbrellas, index/lint, cleanup, separate significance decision.

No new Lean code or accepted contribution for this route.

## Selected next subproblem

The [first-order visibility and prime-power regularity candidate](biscale-prime-power-local-regularity-2026-10-19.md) narrows the first implementation target to bases with the highest admitted dyadic mode active. The existing cubic upper bound suggests an exact Lipschitz/cubic dichotomy, with a prime-power-supported family whose local exponent changes when admitted orders require six distinct prime factors. Its paper proof and specific corpus/literature audit must close before new Lean work. The general support-weighted classification remains open and receives no separate credit from this selection.
