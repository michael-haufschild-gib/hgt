# Wall 13: exact cycle-detection order

- **ID:** BSU-W13-MINIMAL-CYCLE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scope:** BiScaleUncertainty; no RH work.
- **Statement:** construct a smooth compact seed whose opposite-copy orientation first becomes visible at closed-product order floor(T)+1 when the gap is T>2.

## Concrete target

Construct one actual smooth compact real source b with autocorrelation strictly positive exactly on (-1,1). For every T>2 and nonzero amplitude a, compare b(u)-a b(u-T) with b(u)+a b(u-T). Conjecture: the least length of a closed lag list on which their correlation products differ is floor(T)+1.

The final theorem must construct and verify the seed. Do not replace its exact correlation support and positivity with assumed premises.

## Mechanism to audit

The packet-charge law gives a necessary bound: a distinguishing product is nonzero with odd nonzero integer charge Q. Strict interior packet errors imply |Q|T<n, so n>T.

For n>T use one lag T-T/n and n-1 copies of -T/n. Their sum is zero. All packet errors equal -T/n, hence lie strictly inside (-1,1). Exactly one factor belongs to the outer packet, giving odd charge and a nonzero distinguishing product. Endpoint equality n=T is excluded by vanishing at the support boundary.

Whether the same exact threshold holds for Gram determinants requires a separate cancellation audit; do not infer it solely from one distinguishing cycle product.

## Evidence and boundary

Parents: `SeparatedCopyCycleCharge.lean`, `SeparatedCopyCyclePolarAmbiguity.lean`, and `ClosedCorrelationCycleRecovery.lean`. All three now pass direct Lean checks and a complete public-declaration axiom audit; see [formalized package](../3-formalized/wall13-closed-cycle-order-obstruction.md).

Corpus search `/tmp/bsu-wall13-cycle-threshold-search.json` completed, with all 20 candidate and 20 source statements inspected. Related hits supply small correlation support, positive mass and local increment bounds, but did not supply the exact interior-positivity construction. Semantic coverage unmeasured, background refresh incomplete. No exhaustive absence or novelty claim.

No complete dependency audit or Lean proof yet. Do not count this conjecture as proved. It would supply a sharp detection scale, not a coercive lower bound or closure of Wall 13.

## Active plan

1. Construct the literal `ContDiffBump` with inner radius 1/4 and outer radius 1/2; prove its autocorrelation positive exactly on (-1,1), including endpoint vanishing.
2. Define actual opposite copies at arbitrary gap T in (2,infinity). Prove strict packet-error bounds and the necessary inequality T<n for every distinguishing closed product.
3. Construct the explicit n-edge witness for each n>T, classify detection exactly (including a=0), and derive the first order floor(T)+1.
4. Connect exponentially attenuated copies to polar-neutral versus positive polar moment. Run serial direct leaf checks, complete axiom/signature audits, wiring, index and lint; record the next conjecture.

`update_plan` unavailable; this card persists the plan. Current corpus audit `/tmp/bsu-wall13-minimal-order-frontier.json` completed with 20 candidate and 20 source statements inspected. It supplied related support/correlation parents, not the exact sharp-order theorem. Semantic coverage unmeasured; background refresh incomplete. Existing `DyadicDifferenceSource` and `DistantCopyPolarTopology` demonstrate concrete bump construction and integral positivity. Installed mathlib bump support and pointwise positivity APIs are being checked directly.

## Paper proof of the concrete seed

Choose the literal smooth nonnegative bump b supported on (-1/2,1/2), positive everywhere in that interval. If |x|>=1, b(u)b(u+x)=0 for every u: otherwise |x|<=|u|+|u+x|<1. If |x|<1, at u=-x/2 both factors are positive. The product is continuous, nonnegative and compactly supported, so its integral is strictly positive. Thus h(x)>0 exactly for |x|<1, and h(x)=0 exactly for |x|>=1. Positive mass and polar moment follow from the same literal bump and the existing exponential-moment factorization.

The sharp classification target is stronger than a single first-order claim:

    exists a distinguishing closed list of length n
      iff a != 0 and T < n.

All analytic support and positivity inputs must be proved for this seed. The only gap parameter is a point of the mathematical domain (2,infinity).

## Cancellation checkpoint and renewed goal

2026-10-18 — User cleared the goal. Research stopped; no automatic continuation authorized.

Draft leaves are preserved, not wired or certified: `UnitCorrelationBump.lean`, `StrictCopyCycleCharge.lean`, and `SharpCycleDetectionOrder.lean`. Installed API probe `/tmp/bsu_wall13_sharp_api.lean` passed. The first unit-bump check found a field-notation error and a coercion rewrite error; both were edited. Its replacement check was terminated at user cancellation before a verified result. The strict-charge and sharp-order leaves have not passed a check. No axiom audit, umbrella wiring, index refresh or lint completion is claimed for this draft package. Earlier completed packages remain separate.

2026-10-18 — New user goal authorizes continued development of BiScaleUncertainty and/or BezoutValuationIncidence. Both field READMEs, including every trap, were read fully. Wall 13 remains the selected wall; the broader goal covers all walls and remains open. Resume this concrete sharp-order package with fresh serial checks; no earlier interrupted check counts as validation. Both READMEs and the walls ledger remain read-only. No RH work.

## Resumed validation

`UnitCorrelationBump.lean` passed its fresh direct check with empty log `/tmp/bsu-wall13-unit-bump-resumed.log`. `StrictCopyCycleCharge.lean` passed with empty log `/tmp/bsu-wall13-strict-charge-r2.log` after exposing interval membership explicitly as ordered bounds for `linarith`. No change to the mathematical statement. The sharp classification leaf is now being checked; package remains uncertified until that check and the complete audit pass.

Next conjecture: [sharp Gram-determinant detection order](../0-backlog/wall13-sharp-gram-order.md), with an explicit chordless-cycle construction and a separate determinant-cancellation argument. It remains unproved in Lean.
