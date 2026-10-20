# Arithmetic Incidence Positivity (AIP): programme card

- **ID:** aip-2026-10-20
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** docs/reports/review-2010/hard-obstacles-summary-2010.md §2.3 (the field described there)
- **Statement:** Develop the field whose object is the sign of the critical arithmetic form as a
  property of the incidence structure of the integers (which integers are multiples of which, which
  are consecutive), read pair by pair through the gauge-free conductance kernel
  `k(x,y) = dm(|x−y|) + sinh(x/2) sinh(y/2)` of the zero form. Every contribution is an unconditional
  Lean theorem in `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/`, wired into the umbrella
  `GaloisForLFunctions.ArithmeticIncidencePositivity` (registered in `MainTheorems.lean`).

## Goal
Make the negative conductance of the zero form an explicit arithmetic object: where it sits (which
pairs of points, which pairs of integers), how large it is, and what pays it. RH is the statement
that the form is nonnegative on all even profiles in every odd gauge (ACT). The field studies the
form's conductance geometry unconditionally; the open core is the prime-side inequality between
anti-diagonal atoms `|x| + y = log n` and same-side atoms `|x − y| = log m` plus the variance.

## Gates
- [x] 0 → 1 in-progress: folder, umbrella, registration, three modules compiled with `lake env lean`
- [x] README written
- [ ] 1 → 2 fully-proven: the first analytic bridge theorem (bump profiles) proved on paper
- [ ] 2 → 3 formalized: bridge theorem in Lean, axioms `propext, Classical.choice, Quot.sound`
- [ ] 3 → 4 not pursued (user rule: no stage 4)

## Approach
Work in ACT's gauge-free coordinates (odd gauge `M`, even profile `u`, conductance
`M(x)M(y)k(x,y)`): same-side pairs positive, crossing pairs negative where `k > 0`. Separate the
archimedean density (continuous) from the prime atoms (lattice). Prove exact sign laws for the
archimedean part, exact incidence laws for the atoms, then the bridge to profiles built from bumps
at lattice points, then dyadic-window incidence, then the first-prime-window gauge problem.

## Contribution ledger (append-only; statements are for the kernel `ω + 2 sinh sinh`, see the normalization note)

### Normalization note
ACT's identity `Z = J_M(u) + V_μ(u)` (`zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`) has
`J_M` over `t > 0` (each unordered pair once) and `V_μ` over all ordered pairs (each unordered pair
twice, `μ = M sinh(x/2)`). The gauge-free kernel per unordered pair is therefore
`dm(|x−y|) + 2 sinh(x/2) sinh(y/2)`. ACT's docstring/README and review-2010 §2.3 wrote the polar term
without the factor `2`; AIP inherited it in C2, C3, C5–C10 and was re-derived for the correct kernel.
The user's check: at `(−log 2, log 5)` the actual total kernel is `−98/(99√10) < 0`. C1 and C4 (atoms
and windows only) are unaffected.

### C1 — Prime-power incidence dominance (`PrimePowerIncidenceDominance.lean`)
- `ratioAtom a b = Λ(b/a)/√(b/a)` (same side, `a ∣ b`), `productAtom a b = Λ(ab)/√(ab)` (crossing),
  `netAtom = ratioAtom − productAtom`.
- `exists_prime_pow_of_isPrimePow_mul`: `ab` a prime power ⇒ `a = p^i`, `b = p^j`.
- `productAtom_le_ratioAtom` (`1 ≤ a < b`), `productAtom_lt_ratioAtom` (`2 ≤ a`, `ab` prime power),
  `productAtom_one_left` (`a = 1`: equality). `skeletonEnergy_nonneg`, `productEnergy_le_ratioEnergy`,
  `productEnergy_eq_zero_of_tower_constant`. Axioms: standard.

### C2 — Archimedean crossing sign law (`CrossingConductanceSignLaw.lean`)
- `archPairKernel x y = ω(|x−y|) + 2 sinh(x/2) sinh(y/2)`; `crossingSymbol s = cosh(s/2) − ω(s)`;
  `archLevyDensity_log_nat` (`ω(log n) = n²/((n²−1)√n)`), `crossingSymbol_log_nat`.
- `archPairKernel_pos_of_sameSide`; `archPairKernel_pos_iff` (`x<y`): `k > 0 ⟺ S(y−x) < cosh((x+y)/2)`.
- `crossingSymbol_strictMonoOn`, `crossingSymbol_log_five_lt_one`, `one_lt_crossingSymbol_log_six`,
  `crossingThreshold ∈ (log 5, log 6)`, `crossingSymbol_lt_one_iff`.
- `archPairKernel_pos_of_lt_threshold`, `archPairKernel_pos_iff_of_eq_threshold`,
  `archPairKernel_balanced_neg_iff`; `archPairKernel_reflection_pos_iff` (`a ≥ 2`: iff `a = 2`).
- `min_lt_of_archPairKernel_pos`: `s ≥ 4 log 2` ⇒ `min(|x|,y) < 3 e^{−3s/4}`. Axioms: standard.

### C3 — Negative lattice crossing pairs (`LatticeCrossingClassification.lean`)
- `archPairKernel_neg_log_log`: `(2(ab)² − (a−1)(b−1)((ab)²−1)) / (2√(ab)((ab)²−1))`.
- `archPairKernel_neg_log_log_pos_iff`: `k > 0 ⟺ (a−1)(b−1)((ab)²−1) < 2(ab)²`.
- `latticeCrossing_inequality_iff`, `archPairKernel_neg_log_log_pos_iff_of_two_le`: for `a, b ≥ 2`
  exactly `{2,2}` (`15 < 32`) and `{2,3}` (`70 < 72`); `archPairKernel_zero_pos` (axis pairs);
  `archPairKernel_neg_log_log_neg_of_three_le`. Axioms: standard.

### C4 — Incidence inside a dyadic window (`DyadicWindowIncidence.lean`)
- `InDyadicWindow`, `eq_two_mul_or_three_mul_of_dvd`, `ratioAtom_inDyadicWindow`,
  `exponent_sub_le_one_of_inDyadicWindow`, `exponent_eq_of_inDyadicWindow_of_five_le`,
  `consecutive_powers_of_isPrimePow_mul`, `productAtom_lt_of_inDyadicWindow` (`< 2 log 3 / X`);
  SRT bridge `inDyadicWindow_of_mem_lagPrimeWindow`, `productAtom_lt_of_mem_lagPrimeWindow`. Axioms: standard.

### C5 — Polar compensation on the anti-diagonals (`AntiDiagonalPolarCompensation.lean`)
- `crossingPolarWeight s a = 2 sinh(a/2) sinh((s−a)/2) = cosh(s/2) − cosh(s/2 − a)`; symmetric, zero
  at both ends, maximum `cosh(s/2) − 1 = 2 sinh²(s/4)` at the midpoint; `tendsto_…_zero` (axis law);
  `continuous_crossingPolarWeight`; `archPairKernel_antiDiagonal_eq` (`k = ω(s) − P_s(a)`).
- `archPairKernel_antiDiagonal_pos_of_le_five` (`2 ≤ n ≤ 5`: whole anti-diagonal negative);
  `antiDiagonal_collar_of_sixteen_le` (`n ≥ 16`: within `3 n^{−3/4}` of an axis).
- Pointwise payment: `archLevyDensity_le_polar_of_kernel_nonpos`,
  `archCrossing_le_variance_of_kernel_nonpos` (variance of the unordered pair `2μμ`),
  `lintegral_archCrossingDensity_offCollar_le`.
- `polarPaymentScale n = atom/(2 sinh²(log n/4)) = 2Λ(n)/(√n−1)²`, `≤ 8 log n / n` (`n ≥ 4`). Axioms: standard.

### C6 — Collar measure and the five moduli (`PrimeAtomVersusPoleClassification.lean`)
- `antiDiagonalCollar`, `antiDiagonalCollar_subset` (within `3e^{−3s/4}`), `volume_… ≤ 6e^{−3s/4}`,
  `lintegral_antiDiagonalCollar_le` (unpaid mass `≤ 6ω(s)e^{−3s/4}`), `s ≥ 4 log 2`.
- `log_add_one_sub_div_le_log`, `two_mul_log_le_sqrt_sub_one_sq` (`x ≥ 11`, fourth root, `r³ − r ≥ 4`),
  `sqrt_sub_one_sq_lt_two_log_of_prime_le_seven`.
- `sqrt_sub_one_sq_lt_two_vonMangoldt_iff`: `n ≥ 2`, `(√n−1)² < 2Λ(n)` iff
  `n ∈ atomDominatedModuli = {2,3,4,5,7}`; `one_lt_polarPaymentScale_iff`,
  `crossingPolarWeight_lt_vonMangoldtAtom`, `antiDiagonal_total_pos_of_mem`,
  `vonMangoldtAtom_le_crossingPolarWeight_midpoint`. Axioms: standard.

### C7 — Collar sandwich (`CollarSandwichLaw.lean`)
- `le_crossingPolarWeight` (`a sinh(s/2 − a) ≤ P`), `crossingPolarWeight_le` (`P ≤ a sinh(s/2)`).
- `collarInnerEnd = ω/sinh(s/2) = 2e^{−s}/((1−e^{−2s})(1−e^{−s}))`, in `[2e^{−s}, (256/239)2e^{−s}]`;
  `collarOuterEnd = ω/sinh(s/2 − 3e^{−3s/4})`, `collarOuterEnd_eq` (ratio).
- `innerEnds_subset_antiDiagonalCollar`, `antiDiagonalCollar_subset_outer`,
  `volume_antiDiagonalCollar_le_outer` (`≤ 2L`), `lintegral_antiDiagonalCollar_le_outer` (`≤ 2ωL`, order `4e^{−3s/2}`).

### C8 — Total lattice crossing law (`TotalLatticeCrossingLaw.lean`)
- `totalLatticeCrossingKernel_pow_pow_eq` (closed form with the atom), coefficient regimes
  (`p = 2`: `C ≥ 7`, `N ≥ 16`; `p = 3`: `C ≥ 16`, `N ≥ 27`; `p ≥ 5`: `C ≥ (p−1)²`, `N ≥ 25`).
- `totalLatticeCrossingKernel_pos_iff`: `a, b ≥ 2`, positive exactly on `{2,2},{2,3},{2,4},{3,3}`;
  the atom flips `{2,4}` (`126 log 2 > 61`) and `{3,3}` (`160 log 3 > 158`), no other
  (`totalLatticeCrossingKernel_pos_iff_archPairKernel_pos_or`).

### C9 — The pole against the whole anti-diagonal (`TotalAntiDiagonalClassification.lean`)
- `totalAntiDiagonalKernel n a = ω(log n) + Λ(n)/√n − P(a)`; midpoint value
  `(2n²/(n²−1) + 2Λ − (√n−1)²)/(2√n)`; `two_sq_div_add_two_log_le` (`x ≥ 17`).
- `total_midpoint_inequality_iff`: `(√n−1)² < 2n²/(n²−1) + 2Λ(n)` iff
  `n ∈ totalDominatedModuli = {2,3,4,5,7,8,9,11,13}`; `totalAntiDiagonalKernel_pos_forall_iff`,
  `totalAntiDiagonalKernel_midpoint_nonpos`. First paid modulus `6`, first paid prime `17`; near
  misses `8` (`3.344` vs `3.418`) and `9` (`4` vs `4.07`).

### C10 — Unpaid axis intervals (`UnpaidAxisIntervals.lean`)
- `crossingPolarWeight_mono`; `unpaidSet s E`; ends `E/sinh(s/2)`, `E/sinh(s/4)`,
  `E/sinh(s/2 − min(s/4, E/sinh(s/4)))`; `innerEnds_subset_unpaidSet`, `unpaidSet_subset_outer`
  (under `E ≤ P(s/4)`), `unpaidOuterEnd_eq`.
- Level `E_n = ω(log n) + Λ(n)/√n`; `unpaidInnerEnd_level_eq = 2(n²/(n²−1) + Λ(n))/(n−1)`;
  `antiDiagonalLevel_le_quarter` (`n ≥ 23`); `unpaid_level_subset_outer`,
  `totalAntiDiagonalKernel_pos_imp_near_axis`.

## Conjecture queue
1. (done as C4) Dyadic-window incidence.
2. Bump-profile bridge: for even `u` built from bumps at `± log a`, the prime-atom part of ACT's
   `signedJumpEnergy` decomposes into ratio and product pairs with the common gauge factor; the
   archimedean self-energy of a bump of width `w` is `≍ w log(1/w)` and dominates as `w → 0`.
3. (done as C7, up to the ratio `sinh(s/2)/sinh(s/2 − 6e^{−3s/4})`) Sharp collar asymptotic.
4. Total lattice kernel (archimedean + atoms) sign law on `(−log a, log b)`; the five pairs with the
   prime atoms added (`{2,2}`: `ab = 4`, product atom `log 2 / 2`; `{2,4}`: `ab = 8`; `{3,3}`: `ab = 9`).
7. Integrated polar payment against a gauge: for odd `M`, atom mass vs polar mass along the
   anti-diagonal of `n`; which gauges pay every `n ∉ atomDominatedModuli`; the axis law makes the
   answer depend on the decay of `M` at `0`.
8. (done as C7) Sharp unpaid mass `≤ 2ω(s)L(s)`.
9. (done as C8) Total lattice crossing law; with the correct normalization the atoms flip `{2,4}`, `{3,3}`.
10. Integrated polar payment against the ACT gauge `shiftedGroundState a` along the anti-diagonal of
    `n`: atom mass vs polar mass; search ACT for the gauge's values at `± log n` first.
11. Axis region of an anti-diagonal: for a bump of width `w` at `(−a, log n − a)` with `a ≤ w`,
    compare the same-side atoms reachable at ratios `log m` with the atom `Λ(n)/√n` (first-prime-window
    gauge problem, open core). C10 localizes the problem: `a < L_n ≍ 4(1+Λ(n))/n`.
12. Quarter-point classification for `14 ≤ n ≤ 22` (proved from `23`; the nine moduli fail).
13. Gauge-weighted unpaid mass: for an odd gauge `M`, `∫_{unpaid} |M(−a)M(log n − a)| (E_n − P(a)) da`
    against the same-side atoms at ratios reachable from the axis interval (needs the gauge's
    behaviour at `0`; search ACT `shiftedGroundState`).
5. Parity pair: complete-period sieve forms are even in the Selberg coordinates (invariant under all
   sign characters); the first-octave response is not.
6. Open core: extend a gauge argument through the first prime window past `log 2 / 2`, paying the
   single atom `Λ(2)/√2` by the potential (summary §2.3, mechanism 1).

## Log
- 2026-10-20 — folder, umbrella and registration created; C1–C3 compiled with `lake env lean`,
  oleans produced with `lake --old env lean -j 1 -o`; README pending.
- 2026-10-20 — C4 (dyadic window incidence, SRT bridge) compiled and wired; README written; umbrella
  compiles; all audited theorems depend only on `propext, Classical.choice, Quot.sound`.
- 2026-10-20 — C5 (polar compensation) and C6 (collar measure, ten-moduli classification) compiled,
  wired, oleans built, umbrella recompiled; README extended with the continuum section. Audited
  theorems depend only on `propext, Classical.choice, Quot.sound`.
- 2026-10-20 — C7 (collar sandwich) compiled, wired; README mechanism 19; open problem 3 restated as
  the collar ratio.
- 2026-10-20 — C8 (total lattice crossing law) compiled and wired; README mechanism 20 and a trap added.
- 2026-10-20 — C9 (thirteen-moduli classification of the total anti-diagonal kernel) compiled and wired;
  README mechanism 21, trap, open problem 3′.
- 2026-10-20 — C10 (unpaid axis intervals; quarter point paid for `n ≥ 41`) compiled and wired; README
  mechanism 22; open problem 3′ restated as the range `24 ≤ n ≤ 40`.
- 2026-10-20 — Normalization correction: polar weight doubled (`2 sinh sinh`, forced by ACT's
  `Z = J_M + V_μ` with `V_μ` over ordered pairs). C2, C3, C5–C10 re-derived and recompiled for the correct
  kernel; README rewritten. New constants: threshold in `(log 5, log 6)`; reflection `a = 2`; lattice
  pairs `{2,2},{2,3}`; total lattice pairs `{2,2},{2,3},{2,4},{3,3}`; five moduli `{2,3,4,5,7}`; nine
  moduli `{2,3,4,5,7,8,9,11,13}`; collar `≍ 2e^{−s}`; quarter point from `n ≥ 23`.
