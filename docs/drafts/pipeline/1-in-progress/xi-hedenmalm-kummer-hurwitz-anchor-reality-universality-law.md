# Xi Hedenmalm-Kummer/Hurwitz-anchor reality universality law

- **ID:** xi-hedenmalm-kummer-hurwitz-anchor-reality-universality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of the Xi/Hedenmalm common-Kummer-root criterion and the
  critical-anchor Hurwitz pair-Vandermonde criterion
- **Statement:** For every degree `d > 1`, a common analytic degree-`d` Kummer cover of `XiC` and
  its Hedenmalm source on the centered upper half-plane exists iff the Xi divisor contains a
  critical-line anchor and every critical anchor has real two-node Hurwitz Vandermonde separators.

## Goal

Eliminate the shared RH intermediary between two independently developed terminal mechanisms.
The result must directly identify all-degree analytic root divisibility with arithmetic
critical-anchor reality, not merely bundle two RH criteria.

## Gates

- [x] 0 → 1 in-progress: fresh terminal-graph delta, complete source read, corpus research search,
  well-posed source-pure statement
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check and umbrella verification
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `riemannHypothesis_of_xiHedenmalmCommonKummerRootUpperHalf`
- `xiHedenmalmCommonKummerRootUpperHalf_of_rh`
- `xiDivisorSupport_infinite`
- `xi_divisor_support_re_eq_half_of_rh`
- `xiHurwitzAnchoredPairVandermondeReal_of_rh`
- `riemannHypothesis_iff_xiHurwitzAnchoredPairVandermondeReal`

## Proof

**[PROVED HERE]** Fix `d > 1`.

Suppose `XiC` and its Hedenmalm source admit a common analytic degree-`d` Kummer cover on the
centered upper half-plane. The existing Kummer-collision theorem gives RH. The Xi divisor is
infinite, hence nonempty; choose one divisor point `τ`. RH places `τ` on `Re = 1/2`. The anchored
Hurwitz orientation theorem under RH makes every two-node separator real at every such critical
anchor. This yields both the required anchor and the universal reality chamber.

Conversely, suppose a critical-line Xi-divisor anchor `τ` exists and every critical anchor has
real two-node Hurwitz separators. Apply the universal chamber at `τ`. The anchored orientation
criterion gives RH. Under RH, `XiC` and the Hedenmalm source are zero-free on the simply connected
centered upper half-plane, so the existing analytic Kummer construction supplies common roots of
every positive degree, in particular degree `d`. ∎

## Strict gain over corpus endpoints

Existing endpoint theorems compare each mechanism only with RH. The new law removes RH from the
interface and identifies an arbitrary nontrivial analytic covering degree directly with existence
and universal reality of arithmetic two-node separator data. Neither side mentions the invariant
used to define the other.

## Lean formalization

- Main theorem:
  `xiHedenmalmKummerRoot_iff_hurwitzCriticalAnchorRealityUniversality`
- Module:
  `GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH`
- Verification:
  `lake env lean GaloisForLFunctions/RHTower/XiHedenmalmKummerRootRH.lean`
  passed without warnings.
- Umbrella:
  module is already imported by `GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Post-proof searches found classical Xi zero-localization criteria, analytic half-plane
reformulations, superzeta/Hurwitz relations, and Hurwitz-zeta critical-line moment results. They
did not find a theorem equating all-degree common Kummer covers of `XiC` and its Hedenmalm source
with a critical Xi anchor and universal reality of anchored two-node Hurwitz Vandermonde
separators. Relevant comparison points:

- Sondow--Dumitrescu, “A monotonicity property of Riemann's xi function and a reformulation of the
  Riemann Hypothesis”: `https://arxiv.org/abs/1005.1104`
- Voros, “Zeta functions over zeros of Zeta functions and an exponential-asymptotic view of the
  Riemann Hypothesis”: `https://arxiv.org/abs/1403.4558`
- Sahay, “Moments of the Hurwitz zeta function on the critical line”:
  `https://arxiv.org/abs/2103.13542`

Novelty remains a negative-search conclusion, not a claim of bibliographic completeness.

## Log

- 2026-07-23 — generated from fresh post-LAW437 terminal-symbol delta after reading the two new
  terminal theorem chains.
- 2026-07-23 — corpus research found component criteria but no direct Kummer/Hurwitz equivalence.
- 2026-07-23 — dependency-closed proof completed before Lean implementation and literature search.
- 2026-07-23 — exact Lean theorem added to the already-umbrella-wired Hedenmalm Kummer-root
  module; exact-file verification passed without warnings.
- 2026-07-23 — post-proof literature audit found no exact or equivalent law.
