# Prime/Gamma wall cubic raw-magnitude overshoot

- **ID:** route-p-prime-gamma-wall-cubic-raw-magnitude-overshoot
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED]` `[LEAN-PROVED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]` `[MALGRANGE-JET]` `[NO-GO]` `[NOVELTY-UNVERIFIED]`
- **Source:** completed theta-source moments and renormalized Euler/Gamma--Wold cubic current
- **Statement:** Raw source cubic magnitude exceeds `2000` times canonical wall--Xi cubic
  Malgrange magnitude; identity-scale landing is impossible.

## Exact source statement

Set

`T = -(normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0^3/4)`

and

`S = sum' n, sourceHorizontalEulerGammaWoldCubicNaturalDefect n`.

Then

`0 < T < 1/10000 < 1/5 < S`, hence `2000 T < S`. Equivalently, raw renormalized source
current `-S` strictly overshoots wall--Xi target `-T` by factor greater than `2000`.

## Closed paper proof

Write `A = thetaCuspNormalizedEvenMoment 1`,
`B = thetaCuspNormalizedEvenMoment 2`, and
`C = thetaCuspNormalizedEvenMoment 3`. Existing exact moment transport gives

`T = AB/8 - C/120`.

Positivity gives `C >= 0`. Strict factorial-normalized theta-moment contraction gives
`B < 6A^2`. The proved rational first-moment bound gives

`A = normalizedPrimeArchMoment 0 < 29/625 < 1/20`.

Therefore

`T <= AB/8 < 3A^3/4 < 3/(4*20^3) < 1/10000`.

For the source, every natural defect is nonnegative and the defect series is summable, so its sum
dominates the prime-`2` term. Direct reduction of the complete Euler/Gamma atom against its Wold
counterterm gives

`sourceHorizontalEulerGammaWoldCubicNaturalDefect 2 = (95/16)(log 2)^3`.

The proved elementary bound `1/3 < log 2` yields

`S >= (95/16)(log 2)^3 > 95/432 > 1/5`.

The existing strict negative Xi cubic residual gives `0 < T`. Combining bounds gives
`2000T < 1/5 < S`.

## Hostile audit

- Comparison uses raw summable Euler/Gamma--Wold defect, before prime-clock normalization and
  without target-fitted scaling.
- Prime `2` alone supplies source lower bound; no numerical approximation or finite-prime sampling
  enters.
- Xi upper bound uses exact theta moment identities and rational inequalities only.
- Result rules out identity-scale magnitude landing. It does not rule out a source-derived
  contraction, nor construct the missing microlocal incidence map.

## No-go closure

- **Exact killing theorem/mechanism:** `2000T < S`; hence raw current `-S` cannot equal target `-T`.
- **Strongest positive survivor:** quantitative scale aperture: every viable coefficient-faithful
  cubic landing must supply more than factor-`2000` contraction between raw source magnitude and
  canonical Xi Malgrange magnitude.
- **New insight:** sign agreement is far too weak. Missing irregular-RH transport must contain a
  genuine source-derived attenuation mechanism; identity transport and grade-forgetting collapse
  occupy opposite failed extremes.
- **Status:** dependency-closed paper proof and exact unconditional Lean theorem. Corpus and
  primary-source audit found no exact raw Euler/Gamma--Wold versus Xi Malgrange magnitude theorem.

## Corpus and literature audit

- Corpus contains raw-current negativity, same-chamber landing, and normalized collapse to zero,
  but no raw source/target magnitude order or factor-`2000` aperture.
- Primary-source searches found general irregular Riemann--Hilbert solvability, Malgrange
  differentials, Fredholm tau functions, and log-concave moment comparison, but no completed-Xi
  cubic Euler/Wold magnitude comparison.
- Relevant background: Bolibruch--Malek--Mitschi, arXiv:math/0410483; Bertola,
  arXiv:0902.4716; Cafasso--Gavrylenko--Lisovyy, arXiv:1712.08546; Murawski,
  arXiv:2211.05210.
- Absence is audit inference, not priority claim.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure claim and attack frozen
- [x] 1 -> 2 fully-proven: dependency-closed proof and hostile audit above
- [x] 2 -> 3 formalized: unconditional Lean theorem and new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent novelty review

## Lean realization

- `neg_normalizedPrimeArchMoment_two_sub_zero_cube_div_four_lt_one_div_tenThousand`
- `sourceHorizontalEulerGammaWoldCubicNaturalDefect_two_eq`
- `one_div_five_lt_tsum_sourceHorizontalEulerGammaWoldCubicNaturalDefect`
- `twoThousand_mul_neg_xiCubicMalgrangeMagnitude_lt_rawSource`
- `neg_tsum_sourceHorizontalEulerGammaWoldCubicNaturalDefect_lt_xiCubicResidual`
- `routePPrimitiveGammaJuliaStokesPrimeGammaWallCubicRawMagnitudeOvershoot`
- Module:
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicRawMagnitudeOvershoot.lean`
- Direct Lean check and direct `.olean` emission passed; no Lake target or umbrella build ran.
- Axiom audit of all six new public theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Log

- 2026-08-25 — exact rational separation derived; corpus and primary-literature audits completed.
- 2026-08-25 — hostile audit closed no-go and factor-`2000` positive survivor; promoted to Stage 2.
- 2026-08-25 — unconditional Lean theorem, direct module check, and new-declaration axiom audit
  passed; promoted to Stage 3.
