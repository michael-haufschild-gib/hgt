# Xi centered order-fifteen source positivity

- **ID:** xi-centered-order-fifteen-source-positivity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
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
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, exact-file check, axiom audit, umbrella build
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

## Log

- 2026-07-25 — corpus audit found shifted order-fifteen positivity but no centered consumer.
- 2026-07-25 — exact rational corner and fourth-trace source-budget attack formulated.
