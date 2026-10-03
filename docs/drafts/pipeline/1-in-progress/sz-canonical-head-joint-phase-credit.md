# SZ: direct joint phase credit on canonical heads

- **ID:** SZ-JOINT-PHASE-CREDIT
- **Stage:** 1-in-progress
- **Type:** OPEN hard arithmetic target; no new proof claimed
- **Source:** actual coherent Gamma phase square, canonical head energy,
  SZ-SHIFT-EDGE and SZ-ACTUAL-DEFECT-QUASIMODE.

## Exact target

For each actual positive aperture a, set

    u_n = ccmRestrictedWeilCanonicalGroundHead a n,
    f_n = ccmArchimedeanFormToAperture a u_n,
    N = floor(exp(2*a))+1.

Prove eventually in n:

    ccmActualHeadGammaHigherBinetModeEnergy f_n
      + ccmActualHeadCoherentQuantileGammaChiSquare (2*a) N f_n
    <= ccmActualHeadCoherentQuantileGammaPhaseSquare (2*a) N f_n
      + (2*gammaHardyPhaseRate 0+4)*norm(f_n)^2.

The exact source equivalence is already in
`CCMActualHeadCoherentQuantileGammaPhaseSquare` lines190-201. Do not add
another equivalence or use this inequality as an input hypothesis. The
task is to establish its arithmetic sign for the actual canonical heads.

## What the completed source research supplies, and what it does not

Every admissible fixed-source Xi schedule must approach the relative
spectral floor. Its actual amplified defect is eventually nonzero and a
relative normalized-covariance quasimode. These are audited restrictions
on a proposed identifying family. They do not construct such a family,
identify its defect with a canonical head, or prove the phase credit here.

## Constraints learned from existing failures

- Separate chi-square payment by the central scalar is already disproved:
  that scalar is negative. Keep the exact joint phase square and cross term.
- Ground stationarity is invariant under a scalar shift of the operator;
  it alone cannot decide the required absolute arithmetic sign.
- Relative covariance residual tending to zero gives no uniform spectral
  gap or closeness to a single ground eigenspace. Do not insert either.
- The proved limiting-logarithmic ground simplicity concerns a different
  operator. Its modulus argument does not automatically control the
  actual polar term.

## Current proof investigation

The phase square retains the actual Gamma-weighted translation increment
and the complete coherent prime--polar field. Investigate a joint
logarithmic uncertainty/phase-credit argument for those fields evaluated
on the actual head, preserving finite-cell cross terms and the terminal
polar current. The missing result is that these correlations pay the
displayed negative correction. No claimed norm estimate supplies it.

Search1191371 returned actual source identities, canonical Birman--Schwinger
fixed-point identities and the existing ground-plus-tail formulas; its
suggested ingredient set did not prove the sign. Search1191399 (older
coverage1191398) returned finite prime-log phase recurrence and arithmetic
phase source identities. The recurrence statement is an UPPER bound on
a return time; it is not a lower bound on the Gamma cost of coherence.
Neither search certifies completeness or novelty; both were partial and
source-only. Existing recurrence must be used with its actual direction.

## Log

- 2026-10-02: direct hard target recorded after actual-defect quasimode
  closure. No paper proof or Lean theorem for the phase credit is claimed.
  RH remains unresolved. Continue at this sign problem, not at another
  packaging of its equivalent RH receiver.

### Concrete phase-preserving ingredient to investigate next

Current source inspection of
`CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracTwoShear` (intro,
lines245-315) displays a two-shear representation retaining real and
imaginary components of the actual oriented prime-power phase symbol.
Its joint crossing energy is exactly
`4*gauge^4*normSq(orientedSymbol)` and positive away from the spectral
center. The source explicitly leaves transport to the global scalar
receiver open. This is a candidate for a phase-preserving decomposition
of the displayed canonical-head gap; it is not itself scalar positivity.
Next attempt must carry its orientation through the actual coherent
quantile/Gamma transport with every cross term retained. A positive norm
of the oriented symbol cannot be substituted for a signed real pairing.
No new Lean audit of that candidate module was run in this turn.
