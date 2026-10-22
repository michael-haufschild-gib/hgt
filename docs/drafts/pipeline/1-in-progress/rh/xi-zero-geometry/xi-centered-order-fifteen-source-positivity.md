# Xi centered order-fifteen source positivity

- **ID:** xi-centered-order-fifteen-source-positivity
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of the Xi height gap, fourth reciprocal-trace source
  budget, FE--Schwarz quartet symmetry, and order-fifteen complex-sector lemma
- **Statement:** Every centered reciprocal-square Xi atom has positive fifteenth-power real
  part; consequently `normalizedPrimeArchMoment 14 > 0`.

## Goal

Remove the first unresolved centered moment sign and enlarge unconditional prime--Gamma
trace--Hankel positivity from the degree-seven endpoint-pair cone to every degree-seven
polynomial whose real square has nonnegative coefficients.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and exact rational attack
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem and exact-file check passed; final axiom/umbrella audit pending
- [ ] 3 → 4 publication-ready: post-proof collision audit

## Corpus inputs

- `xiZeroCopy_offLine_eightyFive_lt_im_sq`
- `xi_divisor_support_re_mem_open_unit`
- `orderFifteenReciprocalPower_re_pos_of_sectorRatio`
- `xiFourthReciprocalTraceAtom_nonneg`
- `tsum_xiFourthReciprocalTraceAtom_eq_source`
- `normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand`
- FE--Schwarz copy equivalences and fourth-trace invariance lemmas in
  `XiOrderFourteenCornerSourceExclusion`

## Approach

For centered coordinates
`u = (Re rho - 1/2)^2`, `v = (Im rho)^2`, set `A = v-u` and
`B = 2 (Re rho - 1/2) Im rho`.

1. If `u ≤ 1/6` and `v > 85`, prove `100 B^2 < A^2`.
2. If `v ≥ 101` and `u < 1/4`, prove the same inequality.
3. Hence failure lies in the compact corner
   `1/6 < u < 1/4`, `85 < v < 101`.
4. On that corner, prove
   `1/20000 < Re (xiZeroCopyReciprocalSquare rho)^2`.
   Four distinct FE--Schwarz copies then force
   `1/5000 < normalizedPrimeArchMoment 1`, contradicting the existing
   upper bound `normalizedPrimeArchMoment 1 < 9/50000`.
5. Apply the existing order-fifteen sector lemma to every atom and sum the absolutely
   convergent series.

No zero table, numerical integration, RH assumption, or new analytic premise enters.

## Proof

**[PROVED HERE]** Let
`u = (Re rho - 1/2)^2`, `v = (Im rho)^2`,
`A = v-u`, and `B^2 = 4uv`.
Every off-line Xi zero satisfies `v > 85`, while the critical strip gives `u < 1/4`.

If `u ≤ 1/6`, then
`100 B^2 ≤ (200/3)v < A^2`.
If `v ≥ 101`, then
`100 B^2 < 100v < (v-1/4)^2 < A^2`.
Therefore failure of `100 B^2 < A^2` lies in
`1/6 < u < 1/4`, `85 < v < 101`.

On this corner put `w=u+v`. Then `85 < w < 405/4`, `uv < 101/4`, and

`Re (xiZeroCopyReciprocalSquare rho)^2
 = (w^2 - 8uv)/w^4
 > 7023/(405/4)^4
 > 1/20000`.

The functional-equation and Schwarz involutions give four distinct copies with the same
nonnegative fourth reciprocal-trace atom. Hence one corner zero would imply
`1/5000 < normalizedPrimeArchMoment 1`, contradicting the existing bound
`normalizedPrimeArchMoment 1 < 9/50000`.

The corner is empty. The existing complex-sector theorem now gives positive real part for the
fifteenth power of every centered reciprocal-square atom. Absolute summation identifies its
sum with `normalizedPrimeArchMoment 14`, proving strict positivity. ∎

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiCenteredOrderFourteenSourcePositivity`
- Atom theorem:
  `xiZeroCopyReciprocalSquare_pow_fifteen_re_pos`
- Source theorem:
  `normalizedPrimeArchMoment_fourteen_pos`
- Consumer:
  `re_primeArchSourceTraceHankel_nonneg_of_degreeSevenSquareCoeffCone`
- Exact-file checks passed on 2026-07-25 for the new source module,
  `PrimeArchCoefficientSignCone`, and `PrimeArchCombinedResidualSonin`.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Post-proof searches found literature on superzeta functions and RH-equivalent combinations of
centered reciprocal powers, but no exact unconditional positivity result for the fifteenth power
of the centered reciprocal-square Xi spectrum:

- André Voros, *Zeta functions over zeros of Zeta functions and an exponential-asymptotic view
  of the Riemann Hypothesis*, <https://arxiv.org/abs/1403.4558>, develops shifted superzeta
  functions and centered expansion coefficients.
- André Voros, *Zeta functions for Riemann zeros*,
  <https://arxiv.org/abs/math/0104051>, develops meromorphic continuation and special values of
  zero superzeta functions.
- Sergey Sekatskii, *Analysis of Voros criterion*,
  <https://arxiv.org/abs/1407.5758>, studies RH-equivalent nonnegative combinations of centered
  reciprocal-power sums, not this unconditional single-order sign.

## Log

- 2026-07-25 — corpus audit found shifted order-fifteen positivity but no centered consumer.
- 2026-07-25 — exact rational corner and fourth-trace source-budget attack formulated.
- 2026-07-25 — dependency-closed proof completed and formalized; moment fourteen discharged.
- 2026-07-25 — full degree-seven square-coefficient cone wired into combined Sonin residual.
- 2026-07-25 — post-proof collision audit found no exact literature match.
