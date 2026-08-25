# Prime/Gamma wall quintic Malgrange negative orientation

- **ID:** route-p-prime-gamma-wall-quintic-malgrange-negative-orientation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED]` `[LEAN-PROVED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]` `[MALGRANGE-JET]` `[NOVELTY-UNVERIFIED]`
- **Source:** cold all-order Malgrange jet law and completed theta-source moment geometry
- **Statement:** After canonical first-jet scaling, cold fifth Malgrange correction has strictly
  negative real orientation.

## Exact source statement

Write `u_j = thetaCuspNormalizedEvenMoment j` and
`m_j = normalizedPrimeArchMoment j`. Order-nine theta/Xi recurrence gives

`362880 m_4 = u_5 - 45u_1u_4 + 1260u_1^2u_3 - 210u_2u_3`

`                 + 3150u_1u_2^2 - 18900u_1^3u_2 + 22680u_1^5`.

Consequently

`362880(m_4-m_0^5/16)`

`  = (u_5-45u_1u_4) + 210(6u_1^2-u_2)(u_3-15u_1u_2) < 0`.

The all-order irregular-RH law at `n=4` has cold target

`24(m_4/2-(m_0/2)^5) = 12(m_4-m_0^5/16) < 0`.

## Closed paper proof

Strict factorial-normalized theta-moment contraction gives

`u_2 < 6u_1^2`, `u_3 < 15u_1u_2`, and `u_5 < 45u_1u_4`.

The first two inequalities were previously proved. For the third, let

`r_k = thetaCuspHalfMoment(k)/(k thetaCuspHalfMoment(k-1))`.

Strict log-concavity gives `r_(k+1) < r_k`. Hence `r_10 r_9 < r_2 r_1`; clearing
positive denominators and using `thetaCuspRawEvenMoment j = 2 thetaCuspHalfMoment(2j)` gives

`thetaCuspRawEvenMoment 5 * thetaCuspRawEvenMoment 0`

`  < 45 thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 4`.

Normalization yields `u_5 < 45u_1u_4`. Therefore first summand in residual factorization is
strictly negative. Since `6u_1^2-u_2>0` and `u_3-15u_1u_2<0`, second summand is strictly negative.
This proves residual and fifth-target signs. No Xi-zero location, RH premise, fitted wall clock, or
numerical computation enters.

## Hostile audit

- Order-nine recurrence coefficients come directly from parity-coded Leibniz expansion; newest
  cumulant coefficient is `9!`.
- Forced first-jet scale cancels exactly `u_1^5/16`; no sign estimate is applied before cancellation.
- Factor `45` is exact ratio `(10*9)/(2*1)` from strict factorial moment-ratio descent.
- Both terms in factored residual are independently strict; no division by a possibly zero moment.
- Result fixes fifth orientation, not source/target magnitude equality or global Xi-divisor
  contraction.

## Corpus and literature audit

- Corpus contains all-order cold Malgrange law and explicit orientations through fourth jet, but no
  formula for `m_4` or fifth cold orientation.
- Primary-source searches found general irregular Riemann--Hilbert solvability and general
  isomonodromic tau constructions, but no completed-Riemann-Xi fifth cold-wall sign or this
  factorization.
- Relevant background: Bolibruch--Malek--Mitschi, arXiv:math/0410483; Bertola,
  arXiv:0902.4716; Cafasso--Gavrylenko--Lisovyy, arXiv:1712.08546.
- Absence is audit inference, not priority claim.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure claim and attack frozen
- [x] 1 -> 2 fully-proven: dependency-closed proof and hostile audit above
- [x] 2 -> 3 formalized: unconditional Lean theorem and new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent novelty review

## Lean realization

- `thetaCuspRawEvenMoment_five_mul_zero_lt_fortyFive_mul_one_mul_four`
- `normalizedPrimeArchMoment_four_eq_thetaCuspNormalizedEvenMoment`
- `normalizedPrimeArchMoment_four_sub_zero_pow_five_div_sixteen_neg`
- `routePPrimitiveGammaJuliaStokesPrimeGammaWallColdFifthMalgrangeTarget_neg`
- Module:
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallQuinticMalgrangeNegativeOrientation.lean`
- Direct checks of supporting and fifth-jet modules passed; direct `.olean` emission used only for
  axiom audit. No Lake target or umbrella build ran.
- Axiom audit of all four created declarations reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Log

- 2026-08-25 — order-nine cumulant polynomial derived and factored exactly.
- 2026-08-25 — strict factor-`45` source contraction closed sign proof; corpus and literature audits
  completed; promoted through Stage 1 to Stage 2.
- 2026-08-25 — exact Lean theorems, targeted module checks, and new-declaration axiom audit passed;
  promoted to Stage 3.
