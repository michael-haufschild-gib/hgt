# Prime/Gamma wall finite-range Malgrange alternation

- **ID:** route-p-prime-gamma-wall-finite-range-malgrange-alternation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED]` `[LEAN-PROVED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]` `[MALGRANGE-JET]` `[NOVELTY-UNVERIFIED]`
- **Source:** cold all-order Malgrange jet law, Schwarz-pair height gap, and centered Xi sector cone
- **Statement:** Every cold residual at index `5 <= n <= 14` is strictly negative, so cold
  Malgrange targets at orders six through fifteen have exact alternating orientation.

## Exact statement

For every natural `n` with `5 <= n <= 14`,

`normalizedPrimeArchMoment n`

`  < normalizedPrimeArchMoment 0^(n+1) / 2^n`.

Consequently the parity-corrected scalar form of the all-order cold irregular-RH target is positive:

`0 < (-1)^(n+1) * ((-1)^n * n! *`

`  (normalizedPrimeArchMoment n / 2 - (normalizedPrimeArchMoment 0 / 2)^(n+1)))`.

Thus raw target orientation is positive for odd `n` and negative for even `n`, covering Malgrange
jet orders `n+1 = 6,...,15`.

## Closed paper proof

Let `z_q` be centered reciprocal-square Xi atom and
`A_s = sum_q |z_q|^(s+1)`. Unconditional Schwarz-pair height gap gives
`|z_q| < r := 231/9769`. Therefore, for every `s,k`,

`A_(s+k) <= r^k A_s`.

Triangle inequality transfers this to actual centered moments:

`|normalizedPrimeArchMoment(s+k)| <= r^k A_s`.

At `s=1`, existing centered-sector and source bounds give

`(41/42) A_1 <= normalizedPrimeArchMoment 1 < 17/200000`.

Hence, for `5 <= n <= 14`,

`normalizedPrimeArchMoment n <= |normalizedPrimeArchMoment n|`

`  < r^(n-1) * (42/41) * (17/200000)`

`  < (1/25)^(n+1) / 2^n`

`  < normalizedPrimeArchMoment 0^(n+1) / 2^n`,

using existing source floor `1/25 < normalizedPrimeArchMoment 0`. This proves every residual sign.
The parity identity `(-1)^(n+1)(-1)^n=-1` then gives signed target positivity.

## Hostile audit

- Radius estimate is global and unconditional; no critical-line premise or selected zero enters.
- Sector conversion uses a one-sided absolute-mass inequality, not RH-equivalent Hermitian/source
  saturation.
- Exponent shift is exact: `n-1` radius powers compare moment index `n` to index `1`.
- Strict rational separation is checked for every index in the closed range; no sampling.
- The theorem makes no claim at index `15` or above and does not extrapolate alternation.
- Result determines finite cold-jet orientation; it does not construct global Stokes data or prove
  RH.

## Corpus and literature audit

- Corpus search found the all-order cold Malgrange limit and individual orientations through sixth
  jet, but no uniform residual range or orientation theorem through fifteenth jet.
- Primary-source searches found general Malgrange/Jimbo--Miwa--Ueno differentials, irregular
  isomonodromic tau functions, and Fredholm/Widom tau realizations, but no completed-Riemann-Xi
  finite-range cold-wall alternation or this Schwarz-pair radius argument.
- Relevant background: Bertola, arXiv:0902.4716; Its--Lisovyy--Prokhorov,
  arXiv:1604.03082; Cafasso--Gavrylenko--Lisovyy, arXiv:1712.08546.
- Absence is audit inference, not priority claim.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure range and attack frozen
- [x] 1 -> 2 fully-proven: dependency-closed proof and hostile audit above
- [x] 2 -> 3 formalized: targeted Lean module and new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent novelty review

## Lean realization

- `xiShiftAbsoluteTail_le_schwarzPairRadius`
- `abs_normalizedPrimeArchMoment_add_le_schwarzPairRadius_mul_xiShiftAbsoluteMass`
- `normalizedPrimeArchMoment_sub_firstJetScale_neg_of_five_le_of_le_fourteen`
- `routePPrimitiveGammaJuliaStokesPrimeGammaWallColdMalgrangeTarget_signed_pos_of_five_le_of_le_fourteen`
- Module:
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallSexticMalgrangePositiveOrientation.lean`
- Direct module check passed cleanly. Axiom audit of four range declarations reports only `propext`,
  `Classical.choice`, and `Quot.sound`. No Lake target, lint sweep, or umbrella build ran.

## Log

- 2026-08-25 — sharp all-shift absolute-mass contraction derived from Schwarz-pair radius.
- 2026-08-25 — residual and signed Malgrange range theorems formalized for all `5 <= n <= 14`;
  promoted directly through Stage 3 after targeted axiom audit.
