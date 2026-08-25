# Prime/Gamma wall quartic Malgrange positive orientation

- **ID:** route-p-prime-gamma-wall-quartic-malgrange-positive-orientation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED]` `[LEAN-PROVED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]` `[MALGRANGE-JET]` `[NOVELTY-UNVERIFIED]`
- **Source:** cold all-order Malgrange jet law and completed theta-source moment geometry
- **Statement:** After canonical first-jet scaling, cold fourth Malgrange correction has strictly
  positive real orientation.

## Exact source statement

Write `u_j = thetaCuspNormalizedEvenMoment(j)` and `m_j = normalizedPrimeArchMoment(j)`.
The order-seven theta/Xi recurrence gives

`5040 m_3 = -u_4 + 28u_1u_3 + 35u_2^2 - 420u_1^2u_2 + 630u_1^4`.

Consequently

`m_3 - m_0^4/8 = (-u_4 + 28u_1u_3 + 35u_2^2 - 420u_1^2u_2)/5040 < 0`.

The all-order irregular-RH law at `n=3` then has cold target

`-6 (m_3/2 - (m_0/2)^4) = -3(m_3-m_0^4/8) > 0`.

## Closed paper proof

Let `M_k = thetaCuspRawEvenMoment(k)` and `u_k=M_k/M_0`. Positivity gives
`u_1,u_2,u_3,u_4>0`. Ordinary Stieltjes moment log-convexity gives

`u_3^2 <= u_2 u_4`.

Strict log-concavity of the completed theta density, score integration by parts, and the two-copy
monotone-likelihood identity give strict decrease of

`r_k = (integral x^k f(x) dx)/(k integral x^(k-1) f(x) dx)`.

Applying `r_4r_3 < r_2r_1` and clearing positive denominators gives

`u_2 < 6u_1^2`.

Set `A=u_1`, `B=u_2`, `C=u_3`, `D=u_4`, and
`P=-D+28AC+35B^2-420A^2B`. Since `B>0`,

`BP <= -C^2 + 28ABC + 35B^3 - 420A^2B^2`

`= -(C-14AB)^2 + 35B^3 - 224A^2B^2`

`< 35B^2(6A^2) - 224A^2B^2 < 0`.

Hence `P<0`. Substitution into the exact order-seven recurrence proves
`m_3-m_0^4/8<0`; specialization of the existing all-order cold Malgrange theorem proves the
strictly positive fourth-jet orientation. No Xi-zero location, RH premise, fitted wall clock, or
numerical computation enters.

## Hostile audit

- Strictness comes solely from strict theta-density log-concavity; no division by a possibly zero
  moment occurs.
- The Stieltjes inequality is used in its safe direction `u_3^2 <= u_2u_4`.
- Forced first-jet scale cancels the `630u_1^4` cumulant term exactly; omitting this cancellation
  reverses interpretation of the fourth wall datum.
- Result fixes orientation, not source/target magnitude equality and not global Xi-divisor
  contraction.

## Corpus and literature audit

- Corpus contains all-order cold Malgrange jets, order-zero through order-two explicit theta
  cumulants, and ordinary moment log-convexity, but no explicit `m_3` source formula or fourth
  Malgrange orientation theorem.
- Primary-source searches found general Malgrange/isomonodromic tau differentials, Fredholm tau
  representations, and general log-concave moment comparison, but no completed-Riemann-Xi fourth
  cold-wall sign or this source polynomial.
- Relevant background: Bertola, arXiv:0902.4716; Cafasso--Gavrylenko--Lisovyy,
  arXiv:1712.08546; Murawski, arXiv:2211.05210.
- Absence is audit inference, not priority claim.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure claim and attack frozen
- [x] 1 -> 2 fully-proven: dependency-closed proof and hostile audit above
- [x] 2 -> 3 formalized: unconditional Lean theorem, direct module check, new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent novelty review

## Lean realization

- `thetaCuspRawEvenMoment_two_mul_zero_lt_six_mul_one_sq`
- `normalizedPrimeArchMoment_three_eq_thetaCuspNormalizedEvenMoment`
- `normalizedPrimeArchMoment_three_sub_zero_pow_four_div_eight_neg`
- `routePPrimitiveGammaJuliaStokesPrimeGammaWallColdFourthMalgrangeTarget_pos`
- Module:
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallQuarticMalgrangePositiveOrientation.lean`
- Direct Lean check and direct `.olean` emission passed. Lake's targeted dependency request expanded
  into a large replay and was terminated per build constraints; no umbrella build was run.
- Axiom audit of all four new public theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Log

- 2026-08-25 — exact fourth-jet source polynomial derived from order-seven recurrence.
- 2026-08-25 — corpus and primary-literature audit found no existing fourth cold-wall orientation.
- 2026-08-25 — hostile audit closed sign via strict factorial moment contraction plus Stieltjes
  log-convexity; promoted through Stage 1 to Stage 2.
- 2026-08-25 — exact unconditional Lean theorem formalized; direct checks and new-declaration axiom
  audit passed; promoted to Stage 3.
