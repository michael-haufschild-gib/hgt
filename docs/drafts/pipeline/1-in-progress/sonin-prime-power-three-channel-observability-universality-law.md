# Sonin prime-power three-channel observability universality law

- **ID:** sonin-prime-power-three-channel-observability-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of Sonin Koplienko orientation, semilocal logarithmic
  readout, and weak prime-power tomography obstruction
- **Statement:** One narrow nonzero wavepacket exposes a universal three-channel hierarchy for
  every retained Sonin prime power: quadratic data lose coefficient sign, the semilocal linear
  channel recovers it, and arbitrary finite combinations of retained translation coefficients
  cannot recover the identity coefficient.

## Goal

Classify together three terminal observability mechanisms that currently occur in separate Sonin
modules. The closure must retain their exact quantifiers: uniformity over every prime power and
over every sequence of finite coefficient combinations, with no topological or analytic patch.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed warning-free
- [x] 3 → 4 novelty audit: completed; negative priority result

## Corpus inputs

- `centralSoninPrimePower_quadraticBlind_linearSemilocalOrientation`
- `retainedPrimePower_symmetricLogCorrelation_eq_zero`
- `retainedPrimePower_symmetricLogCorrelation_ne_selfCorrelation`
- `not_tendsto_finite_retainedPrimePowerLogCorrelations_to_selfCorrelation`

## Proof

**[PROVED HERE]** Fix `1 < λ` with `λ² < 4` and a complex wavepacket `f` supported in
`[-log λ, log λ]` whose self-correlation is nonzero.

For every retained prime-power label `pk` and real central parameter `a`, the
Koplienko--semilocal orientation theorem proves simultaneously that the actual logarithmic Euler
coefficient differs from its negative, that the second-order Gram remainder is unchanged by this
sign reversal, and that the central semilocal tail is the oriented value `-2 Re(c)` and differs
from its reversal `2 Re(c)`.

The common-wavepacket theorem uses only the same retained scale and the support inequalities. It
proves for every `pk` that the symmetric logarithmic-translation correlation is zero. Since the
self-correlation is nonzero, this retained correlation differs from the identity correlation.
Finally, the weak-tomography theorem quantifies over arbitrary sequences of finite prime-power
sets and arbitrary complex coefficients and forbids their scalar correlations from converging to
the nonzero self-correlation.

Conjoining these already universal conclusions gives the stated three-channel classification.
The wavepacket is shared by every retained prime power and every attempted finite-combination
sequence. No computation is used. ∎

## Strict gain over corpus endpoints

The orientation law compares quadratic and semilocal channels but says nothing about weak
translation tomography. The tomography no-go separates the identity coefficient but says nothing
about coefficient sign or the channel that retains it. Their closure identifies the exact
observability hierarchy: second-order sign loss, linear sign recovery, and persistent
identity-recovery failure coexist for the complete retained prime-power family.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.SoninPrimePowerThreeChannelObservabilityUniversalityLaw`
- Main theorem:
  `soninPrimePower_threeChannelObservabilityUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/SoninPrimePowerThreeChannelObservabilityUniversalityLaw.lean`
- Result: passed warning-free.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Performed only after the dependency-closed Lean proof passed. Closest literature found treats
Koplienko spectral-shift formulas for Hilbert--Schmidt perturbations, semilocal adelic/Sonin
operators, and prolate Sonin-space spectral models separately. No source located states the exact
prime-power three-channel conjunction of quadratic sign blindness, linear semilocal sign
recovery, and failure of arbitrary finite weak-tomography combinations to recover the identity
coefficient. This is a negative search result, not a priority claim.

## Log

- 2026-07-23 — terminal-pair scan exposed the shared exact Sonin prime-power scale.
- 2026-07-23 — corpus research found the three mechanisms only in separate terminal theorems.
- 2026-07-23 — dependency-closed proof completed before Lean source or literature search.
- 2026-07-23 — Lean source passed the required exact-file check warning-free and was wired into
  `GaloisForLFunctions/RHTower.lean`.
- 2026-07-23 — post-proof literature audit found separate Koplienko and semilocal Sonin
  frameworks, but not the exact three-channel observability classification.
