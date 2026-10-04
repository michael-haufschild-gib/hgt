# TG: bounded assembly of the explicit clock-divided Gamma ground family

- **ID:** TG-C9.14-negative
- **Stage:** 5-failed
- **Type:** FALSIFIED (explicit kernel candidate only)
- **Route:** TG, Gamma lower endpoint
- **Rejected statement:** For a>0, the literal vectors integral_[eps,1] gamma(u)/u (D_exp(u)+D_exp(-u)-2I) f_a du have a finite L2 limit as eps->0+.

## Exact killing mechanism

The actual annulus S_eps=B_a(0)-B_a(eps) has mass
2a(1-exp(-eps)). Its exact pairing with the literal finite Gamma vector
is negative with magnitude at least mass/(16eps), for 0<eps<=1/2.
Cauchy-Schwarz gives eps times the vector's squared norm >=a/256.
Thus `gammaGroundTruncated_norm_tendsto_atTop` proves norm divergence,
not merely failure of one proposed proof or one cutoff subsequence.

## Strongest positive survivor

Retain the forced homogeneous term 1/(2u^2), and define the remainder
exactly as gamma(u)/u-1/(2u^2). `gammaClockRemainder_ground_integrable`
proves its absolute Bochner admission on the actual ground vector over
(0,infinity). `gammaGroundTruncated_sub_homogeneous` preserves the full
finite source, and `gammaGroundTruncated_sub_homogeneous_tendsto` proves
one unique relative limit for arbitrary cofinal endpoints. This is the
positive, dependency-closed paper and Lean survivor, rather than a renamed
negation or an arbitrary counterterm. Paper proof: `tg-gamma-clock-principal-remainder`.

## New insight and remaining obligations

The literal Gamma observable has a forced singular principal domain.
Its ground remainder is admitted, but the principal term must remain as
an unbounded reference. The completed TG source identification, full Sonin
remainder response, exact reference domain, Hardy compatibility and
sub-unit estimate remain open. The distant-clock cancellation strengthening C9.16 and logarithmic Gamma
source identity C9.15 are now formalized; see their P3 cards.
Neither the completed TG route nor RH is falsified here.

## Audit

`formal/GaloisForLFunctions/RHTower/SoninGammaClockEndpoint.lean` passes the
targeted `lake --old env lean ... -o ...` audit with empty diagnostics.
Umbrella wired; all fifteen public declarations indexed. All fifteen foundation queries pass with only propext, Classical.choice
and Quot.sound. Global lint reports twelve unrelated unreachable modules, no
finding in this leaf; see `/tmp/tg-c914-lint.log`.
