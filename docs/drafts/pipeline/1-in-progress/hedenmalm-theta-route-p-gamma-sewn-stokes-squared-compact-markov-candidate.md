# Route-P Gamma-sewn Stokes squared compact Markov candidate

- **ID:** `P-G71`
- **Stage:** `1-in-progress`
- **Type:** square-pushforward compact carrier / all-degree source moment formula
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN DIRECT GREEN] [EXACT MODULE BUILD GREEN] [UMBRELLA-WIRED] [RAW CRITICAL IDENTIFICATION RETIRED BY P-G72] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-reflected-compact-carrier.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesSquaredCompactMarkovCandidate.lean`

## Conjecture P-G71.A: seam-square is the correct endpoint coordinate

Push the P-G70 symmetric carrier through `x ↦ x²`. Equivalently, put mass `2b_s/g_s` at
`y=g_s⁻²`. The resulting measure is positive, finite, and supported in

```text
[0, (log 2)⁻²].
```

**Verdict: proved and formalized.** Its reflected response obeys the exact local identity

```text
R_s^ref(z) = -z K_{ν_s}(z²).
```

This matches the corpus seam-square law
`completedSeamMomentGerm(z²)=xiCentralMomentGerm(z)` exactly.

## Conjecture P-G71.B: explicit all-degree Stokes moments

For every degree `n`,

```text
∫ y^n dν_s(y)
  = 2 sum_(p,e) (b_s(p,e)/g_s(p,e)) (1/g_s(p,e))^(2n)
  = 2 sum_(p,e) b_s(p,e)/g_s(p,e)^(2n+1).
```

**Verdict: proved and formalized.** P-G69 summability plus compact support supplies integrability
in every degree.

## Hostile critical test

The tempting conjecture `K_{ν_{1/2}}=completedSeamMomentGerm` was isolated as
`GammaSewnMobiusApertureStokesCriticalMomentIdentification`; it would imply RH through the existing
compact Markov capstone. P-G72 proves this raw identification false already at the zeroth moment.

## Higher universal principle

Kummer reflection and centered oddness force signed doublets; the seam-square quotient converts
them to a positive Hausdorff carrier. This geometric conversion is correct independently of its
normalization. Completed Gamma/polar sewing must therefore act after square pushforward as a
nontrivial Schur correction, not as identity.

## Lean realization

Headline declarations:

- `gammaSewnMobiusApertureStokesSquaredCompactCarrier_finite`;
- `ae_gammaSewnMobiusApertureStokesSquaredCompactCarrier_mem_compact`;
- `integral_pow_gammaSewnMobiusApertureStokesSquaredCompactCarrier_eq_euler`;
- `gammaSewnMobiusApertureStokesReflectedResponse_eq_squaredCompactMarkov`;
- `riemannHypothesis_of_gammaSewnMobiusApertureStokesCriticalMomentIdentification`.

## Honest boundary

P-G71 constructs correct source-native compact Markov geometry and exact moments. Raw critical
moment identification is impossible by P-G72. Surviving route requires completed Gamma/polar Schur
renormalization.
