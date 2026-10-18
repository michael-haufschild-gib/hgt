# Fixed-order polar recovery fails; the full closed-product hierarchy is complete

- **ID:** BSU-W13-FINITE-CYCLE-NOGO
- **Stage:** 5-failed
- **Type:** FALSIFIED (Lean)
- **Scope:** BiScaleUncertainty, Wall 13; no RH conclusion.
- **Rejected statement:** some fixed order of all closed correlation products and autocorrelation Gram determinants recovers polar balance for every compact source.

## Exact killing theorem

`SeparatedCycle.polarMoment_not_factor_through_finite_data` in
`formal/GaloisForLFunctions/BiScaleUncertainty/SeparatedCopyCyclePolarAmbiguity.lean`
excludes every recovery functional of the joint complete data through order m,
for each natural m.

`exists_smooth_same_finite_data_distinct_polar` constructs the witnesses: smooth
compact sources with equal positive mass, identical closed products of every
length <=m and identical Gram determinants of every size <=m at all real sample
configurations, but zero versus strictly positive normalized polar moment.

## Strongest positive survivor

`SeparatedCopyCycleCharge.lean` proves the exact orientation law for actual
separated copies. Every lag receives its integer packet label c in {0,1,-1}.
For any lag list L, packet charge Q=sum c governs sign reversal:

    P_(-a)(L)=(-1)^Q P_a(L).

The products agree exactly when P_a vanishes or Q is even. If the product is
nonzero, `packetCharge_bound` proves

    |sum L-Q T| <= length(L) D.

Closed products of order m cannot detect the sign when T>mD. The determinant
claim follows term by term from the actual permutation expansion.

The stronger replacement holds for arbitrary compact continuous sources:
`SeparatedCycle.closedProduct_eq_iff_autocorr_eq` in
`ClosedCorrelationCycleRecovery.lean` proves that equality of all closed products is equivalent to
equality of the signed autocorrelation. One-edge products identify mass;
two-edge products identify squares; continuity fixes a positive sign near zero;
a sufficiently long small-increment cycle recovers every remaining lag. Zero
mass is handled explicitly.

The concrete noncomputable functional `SeparatedCycle.polarRecovery` satisfies
`polarRecovery_closedProduct` for every actual source. Its independence from
the choice of realizing source is proved by the preceding injectivity theorem.

## New insight and boundary

Detection order is unbounded over compact sources, but the full hierarchy loses
no signed correlation information. This is a positive recovery theorem, not
only a restated failure of finite observations. It concerns exact data, provides
no stability estimate, and does not prove that Gram determinants alone recover
the full correlation. Original sources need not be unique.

No blind-source coercivity or cone-transfer theorem is obtained. Wall 13 remains
open. The [sharp minimal cycle order](../3-formalized/wall13-minimal-cycle-order.md)
is now proved for a literal smooth seed: detection at order n is equivalent to
a!=0 and T<n, with first order floor(T)+1. All 41 declarations in that successor
package passed direct checks and the complete axiom audit. The matching
[Gram-determinant threshold](../3-formalized/wall13-sharp-gram-order.md) is now
fully Lean-verified for the same concrete family, including the exact determinant
difference, detection at every larger order, and the polar-neutral/positive pair.
All 26 public declarations passed signature and axiom inspection; only the three
standard Lean axioms occur. This sharp boundary strengthens the positive survivor
without reviving fixed-order recovery or closing Wall 13.

## Verification

All three leaves and the final direct recovery audit passed with empty logs.
All 27 public declarations audited: only `propext`, `Classical.choice`,
`Quot.sound`. Umbrella imports and index refresh complete. Global lint has two
unrelated concurrent errors, recorded in the [formalized package](../3-formalized/wall13-closed-cycle-order-obstruction.md).

## Log

- 2026-10-18 — Retired fixed-order recovery after formalizing both exact packet-charge classification and the full-hierarchy recovery theorem.
