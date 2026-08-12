# Route-P Gamma-sewn Stokes critical mass no-go

- **ID:** `P-G72`
- **Stage:** `1-in-progress`
- **Type:** raw critical-normalization obstruction / negative Schur-budget survivor
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN DIRECT GREEN] [EXACT MODULE BUILD GREEN] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-squared-compact-markov-candidate.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalMassNoGo.lean`

## Conjecture P-G72.A: raw critical carrier matches completed mass

**Verdict: false, retired unconditionally.** At `s=1/2`, exact source algebra gives

```text
weight(p,e)
 = 2 c_p² (1/(p+1))² (1-r_p)² r_p^e
   / ((e+1)² log(p) r_p),       r_p=p^(-1/2).
```

Using only rational analytic bounds, Lean proves depths zero and one over primes two and three
already have combined mass strictly above `29/625`. Independently, corpus endpoint analysis proves

```text
normalizedPrimeArchMoment(0) < 29/625.
```

Therefore four raw Stokes atoms outweigh the complete seam zeroth moment. The full critical
carrier cannot represent the completed seam germ.

The obstruction is not removable by a scalar normalization counterterm. Lean also proves the
prime-two depth-zero squared reciprocal-gap node exceeds `256/11025`; together with its weight
floor, that one atom already contributes more than `9/50000` to first moment. Corpus endpoint
analysis proves the complete first seam moment is below `9/50000`. Thus raw carrier exceeds target
in degrees zero and one.

## Positive survivor: forced negative completed correction

Any additive Gamma/polar correction `C` satisfying

```text
mass(ν_1/2) + C = normalizedPrimeArchMoment(0)
```

must have `C<0`. Its first-moment correction must also be strictly negative. Hence positive
orthogonal completion and constant subtraction are impossible. Completed sewing must be a
genuinely coupled Schur/Feshbach elimination whose negative central correction acts before final
positive-carrier extraction.

This is stronger than a failed candidate: it determines sign of missing channel and rules out an
entire producer class.

## Lean realization

Headline declarations:

- `gammaSewnMobiusApertureStokesCriticalPrimeTwoDepthZero_lower`;
- `gammaSewnMobiusApertureStokesCriticalPrimeThreeDepthZero_lower`;
- `gammaSewnMobiusApertureStokesCriticalFourAtomMass_lower`;
- `normalizedPrimeArchMoment_zero_lt_integral_criticalSquaredCompactCarrier`;
- `normalizedPrimeArchMoment_one_lt_integral_criticalSquaredCompactCarrier`;
- `not_gammaSewnMobiusApertureStokesCriticalMomentIdentification`;
- `gammaSewnMobiusApertureStokesCriticalCorrection_mass_neg`.
- `gammaSewnMobiusApertureStokesCriticalCorrection_firstMoment_neg`.

## Next conjecture

Construct completed Gamma/polar channel as source-native Schur complement of reflected Stokes
response. Required central correction is negative, while resulting reduced response must remain
anti-Herglotz and its square-coordinate carrier positive. Test zeroth and first moments before any
all-degree claim.

## Honest boundary

P-G72 disproves raw identification and proves correction sign. It does not construct the required
Schur channel, identify corrected moments, or prove RH.
