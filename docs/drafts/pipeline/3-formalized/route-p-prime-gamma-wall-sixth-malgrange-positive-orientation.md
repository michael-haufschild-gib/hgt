# Prime/Gamma wall sixth Malgrange positive orientation

- **ID:** route-p-prime-gamma-wall-sixth-malgrange-positive-orientation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED]` `[LEAN-PROVED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]` `[MALGRANGE-JET]` `[NOVELTY-UNVERIFIED]`
- **Source:** cold all-order Malgrange jet law, Schwarz-pair height gap, and centered Xi sector cone
- **Statement:** After canonical first-jet scaling, cold sixth Malgrange correction has strictly
  positive real orientation.

## Goal

Prove unconditionally

`normalizedPrimeArchMoment 5 < normalizedPrimeArchMoment 0 ^ 6 / 32`,

so all-order irregular-RH law at `n = 5` gives positive sixth cold target

`-60 * (normalizedPrimeArchMoment 5 - normalizedPrimeArchMoment 0 ^ 6 / 32) > 0`.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, dependency-closed attack identified
- [x] 1 -> 2 fully-proven: closed paper proof below, no open dependency
- [x] 2 -> 3 formalized: targeted Lean module and new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent novelty review

## Closed paper proof

Let `z_q` be centered reciprocal-square Xi atom and
`A_s = sum_q |z_q|^(s+1)`. Existing unconditional Schwarz-pair height gap gives

`|z_q| < 231 / 9769`.

Therefore `A_5 <= (231/9769)^4 A_1`. Existing centered sector law at power two gives

`(41/42) A_1 <= normalizedPrimeArchMoment 1`,

and source budget gives `normalizedPrimeArchMoment 1 < 17/200000`. Triangle inequality for
centered divisor trace gives `normalizedPrimeArchMoment 5 <= A_5`. Hence

`normalizedPrimeArchMoment 5`

`  < (231/9769)^4 * (42/41) * (17/200000)`

`  < (1/25)^6 / 32`

`  < normalizedPrimeArchMoment 0^6 / 32`,

using existing source floor `1/25 < normalizedPrimeArchMoment 0`. No RH premise, zero selection,
fitted wall clock, or numerical computation enters.

## Hostile audit

- Height input is global and unconditional; it does not assume critical-line location.
- Absolute-mass conversion uses existing atomwise sector positivity, not Hermitian/source equality
  (which would be RH-equivalent).
- Radius loses four powers because order six is compared against order two; exponents match exactly.
- Final rational separation is strict before source floor is applied.
- Result determines sixth cold orientation only; it does not construct global Stokes data or prove
  RH.

## Corpus and literature audit

- Corpus search found all-order cold Malgrange law, orientations through fifth jet, centered-sector
  bounds, and Xi height/source budgets, but no sixth residual or sixth cold orientation theorem.
- Primary-source searches found general Malgrange/Jimbo--Miwa--Ueno differentials, irregular
  isomonodromic tau functions, and Fredholm/Widom tau realizations, but no completed-Riemann-Xi
  sixth cold-wall sign or this radius/sector contraction.
- Relevant background: Bertola, arXiv:0902.4716; Its--Lisovyy--Prokhorov,
  arXiv:1604.03082; Cafasso--Gavrylenko--Lisovyy, arXiv:1712.08546.
- Absence is audit inference, not priority claim.

## Lean realization

- `norm_xiZeroCopyReciprocalSquare_lt_twoHundredThirtyOne_over_nineThousandSevenHundredSixtyNine`
- `xiShiftAbsoluteMass_five_le_radius_pow_four_mul_one`
- `normalizedPrimeArchMoment_five_le_xiShiftAbsoluteMass_five`
- `normalizedPrimeArchMoment_five_sub_zero_pow_six_div_thirtyTwo_neg`
- `routePPrimitiveGammaJuliaStokesPrimeGammaWallColdSixthMalgrangeTarget_pos`
- Module:
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallSexticMalgrangePositiveOrientation.lean`
- Direct module check passed. Axiom audit of all five declarations reports only `propext`,
  `Classical.choice`, and `Quot.sound`. No Lake target, lint sweep, or umbrella build ran.

## Log

- 2026-08-25 — spectral-radius/sector proof derived; promoted through Stage 1 to Stage 2 on paper.
- 2026-08-25 — targeted Lean formalization and new-declaration axiom audit passed; promoted to
  Stage 3.
