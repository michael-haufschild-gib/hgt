# CCM-FU: retained support thresholds and common source head

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], source-derived structure and cofinal cost analysis.
- **Parent:** [finite source control and cofinal coverage](ccm-fu-finite-source-cone-exhaustion.md).
- **Closed:** Exact support, full-field witness/aperture lower bounds, initial sign chamber, and all coordinates/full energy from one coprime head.
- **Open:** Uniform control of the changing head and its product-scale energy along an exhaustive compatible order.
- **Primary goal:** Unconditional RH via complete compatible source coverage under one energy budget; unchanged.

## Full chain

Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints
→ signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green
→ RH. Arbitrary fixed-field actual batches and finite preparation budgets
are closed. Uniform costs through changing fields and exhaustive compatible
coverage remain open.

## Exact closed source statements

The [retained-support and common-head certificate](../3-formalized/ccm-fu-retained-support-and-common-head.md)
proves that an R-labelled coordinate vanishes whenever `M<=product(R)`.
For every actual processed state, the complete energy equals the sum over
remaining subset labels with `product(R)<M`, with no remainder. There are at
most M-1 such possible labels.

Every finite family detecting all nonzero directions of the complete retained
field must reach beyond product(S). If S contains all primes below q, the
full coordinate keeps its initial Möbius orientation through
`M<=q*product(S)`. Complete directional witnesses must leave that chamber;
copying them as prime quotients requires a parent cutoff above
`2*q*product(S)`. These are witness/aperture costs, not energy lower bounds.
They do not exclude strategies using the actual correlated source states.

For `s=product(S)`, define the complete arithmetic head
`G_s(N)=sum_(d<=N, gcd(s,d)=1) C_d(N)`.
Every subset R has r=product(R) and the exact coordinate identity

`V_S(M,R)=sqrt(r)*mu(r)*[(1-w_r)G_s(floor(M/r))+w_r G_s(floor(M/r)+1)]`,

where w_r is the literal square-root clipping coefficient. The coprime mask
uses the full field product s, including when R is a proper subset. Shared
prime exclusions and every terminal/clipped endpoint are formal.

After complementary active-prime processing, the full energy is exactly

`sum_(R subset S) r*[(1-w_r)G_s(floor(M/r))+w_r G_s(floor(M/r)+1)]^2`.

Thus the source coordinates are correlated product-scale samples of one
head for fixed S. The absolute energy formula requires S to be the entire
unprocessed active parent field. A smaller batch-steering field controls the
exact energy change, not all parent energy by itself. This is stronger source
structure than arbitrary-vector margins; it is not a uniform bound on the
weighted sum.

## Remaining source-production target

Processing a prime changes both the coprime head and the remaining scales.
The next producer must control that joint change and the entire weighted
energy within one compatible exhaustive history. The head is not fixed
across changing fields. Exact support restriction cannot omit nonzero source
terms, and an aperture cost cannot be promoted to an energy obstruction.

The full-field batches remain available under `722*2^|core|*M^2`, with every
preparation subset included. Their constants depend on the field. The known
middle-singleton obstruction still prevents assuming that a growing
complementary core can be prepared first under a fixed quadratic ceiling.

## Computation decision

No numerical experiment was run or is scheduled. The support, sign-chamber
and homothety statements follow from the literal source algebra. Computing
those predictable outcomes would add no evidence. A later experiment must
isolate an unresolved quantitative interleaving mechanism with genuinely
competing predictions under the scientific-method rules.

## Lean

`RetainedPrimeSupportThreshold`, `RetainedPrimeTopHomothety` and
`RetainedPrimeCoordinateHomothety` contain the exact closed bridge.
Complete cofinal coverage, PE4/PE4G/PE4C, SD1 and RH remain open.
