# Suzuki reporter-secant exact transition core

## Status

Formalized in Lean 4. Route map remains read-only. Results sharpen literal Mangoldt Cauchy-energy
localization, prove a complete sign classification, and close bounded-transition-core strategy by
showing exact positive core diverges. They do not prove RH.

## Corpus-first conjecturing loop

Search of reporter-secant Ward, transition-polynomial, natural-aperture, energy-escape, and
atomic--continuous modules exposed three successive conjectures.

1. Exact continuous transition should replace factor-two arithmetic cutoff.
2. Complement of transition separation should be exactly positive Gram sector, not merely a
   possible positive remainder.
3. Resulting positive core might admit missing cofinal upper bound.

First two conjectures were proved. Third failed decisively: corpus already proves full raw energy
has linear lower bound on apertures `8n`, while sharp localization places full energy below positive
transition core. Therefore core itself tends to positive infinity.

## Exact transition arithmetic localization

For every nonzero shallow lag `p`, corpus transition depth lies strictly in `(3p/2,2p)`. Lean now
transports that root into literal natural-aperture Mangoldt packet:

```text
transitionDepth(p) ≤ q -> Gram(p,q) ≤ 0
transitionDepth(p) < q -> Gram(p,q) < 0
```

There is always a strictly negative lag before old factor-two boundary. Symmetric transition
separation satisfies complete classifier

```text
Gram(p,q) > 0 <-> not TransitionSeparated(p,q)
TransitionSeparated(p,q) <-> Gram(p,q) ≤ 0.
```

Thus full weighted energy decomposes exactly into nonpositive separated energy plus nonnegative
transition-core energy, and full energy is bounded above by core without absolute-value loss.

## Exact-core escape no-go

Along apertures `8n`,

```text
n / 288 ≤ fullNaturalCauchyEnergy(8n)
          ≤ transitionCoreCauchyEnergy(8n)
```

eventually. Hence exact positive core tends to `+∞`. Deleting every favorable cross-scale term
cannot produce bounded Ward source. Compensation or renormalization must happen before Gram limit.

## Prime-charge bridge and universal principle

Natural packet lower-Hardy anchor is exactly coherent prime outgoing charge. Therefore

```text
primeOutgoingCharge(N)^2 ≤ transitionCoreCauchyEnergy(N).
```

Subtracting regular-screw continuum at amplitude level yields completed natural anchor, exactly
Suzuki Green and exactly lower-Hardy value of literal prime--polar--Gamma Ward wall. Uniform
boundedness of completed anchor is equivalent to RH.

This formally isolates order-of-operations principle:

```text
atomic Gram first, then compensate  -> divergent positive core
atomic-continuous compensate first  -> exact RH-bearing completed amplitude
```

## Lean certificates

- `formal/GaloisForLFunctions/RHTower/SuzukiCauchyReporterSecantSharpArithmeticLocalization.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiCauchyReporterSecantTransitionCoreEscape.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiCauchyReporterSecantPrimeChargeBridge.lean`

Key declarations:

```text
suzukiReporterSecantCauchyGram_pos_iff_not_transitionSeparated
suzukiReporterSecantTransitionSeparated_iff_gram_nonpos
suzukiNaturalApertureCauchyEnergy_eq_transitionSeparated_add_core
suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg
tendsto_suzukiNaturalApertureTransitionCoreCauchyEnergy_eight_mul_atTop
suzukiNaturalApertureLowerHardyAmplitude_eq_primeOutgoingCharge
unitRieszCoherentPrimeOutgoingCharge_sq_le_transitionCore
suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_gammaCompletedWall
riemannHypothesis_iff_suzukiNaturalCauchyCompletedAnchorBounded
```

## Hostile audit

- Literal `criticalMellinAtomWeight`, `suzukiNaturalApertureLag`, finite Mangoldt pair set, and
  regular-screw mass are used; no divisor-fitted receiver enters.
- Core divergence rules out proposed bounded-core continuation rather than relabeling it.
- RH equivalence is a frontier classification only; no unconditional completed-anchor bound is
  claimed.
- No computation, added axiom, `sorry`, or umbrella build is used.

## Next hard conjecture

Construct source-native atomic--continuous Cauchy packet for full Gamma-completed wall and prove a
uniform upper bound only after amplitude-level compensation. Any candidate must include cross
atomic--continuous energy; separate positive atomic and continuum estimates cannot close RH.

## Log

- 2026-08-21 — Proved sharp arithmetic transition localization and strict improvement before
  factor two.
- 2026-08-21 — Proved complete exact sign classifier and canonical signed energy decomposition.
- 2026-08-21 — Proved transition-core linear escape, closing bounded-core strategy.
- 2026-08-21 — Proved prime-charge identity and amplitude-before-energy RH bridge.
