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

### C11 — Odd-sector Weil positivity on [−7/25, 7/25]: the folded odd plateau (`OddPlateauFoldedWindowPositivity.lean`)
- Goal-loop contribution G1 (criterion 1: support increase). Every odd `F ∈ C²_c` vanishing outside
  `[−7/25, 7/25]` has `Ẑ(F) ≥ (1/40)∫F²` (`fullZeroForm_ge_of_odd_support_le`), i.e. `J_M(u)+V_μ(u) ≥ 0`
  for all even profiles with `Mu` supported there, in every odd gauge. Support `21/200 → 7/25` (2.67×).
- Mechanism: even plateau `P` (= odd gauge `sign·P`), odd test; crossing pair `(−a,b)` carries
  `(F(a)+F(b))²` at `ω(a+b)`, same-side `(a,b)` carries `(F(a)−F(b))²` at `ω(|a−b|) ≥ ω(a+b)` ⇒ killing
  `2ω(a+b)(F(a)²+F(b)²)`; `fourKilling_le_archJump`: `J_P(F) ≥ 4∫_{x>0}F²(Ω(x)−Ω(x+r))`
  (Z-type law in test coordinates `archCrossingDiff_le_two_mul_archSame`, three Fubini swaps).
  Pole not converted (no plastic threshold); odd pole `2S² ≤ (R³/3)cosh²(R/2)∫F²` (`sq_oddPoleMoment_le_cosh`).
- Exact plateau potential: edge function `E = Ω − N` (`windowEdgeFunction`), `∫_0^∞(ν − ω1_{u≤a}) = Ω(a) − E(0)`,
  `E(0) = ½log 8 + π/4` (`integral_one_sided_window_eq`); `−𝒲P(x) ≥ Ω(R−x)+Ω(R+x) − log 8 − π/2 − (γ+log π)`
  (`neg_poleFreeWeilOperator_ge_antideriv`).
- Ω bounds `½log(4/y) + π/4 − y/4 ≤ Ω(y) ≤ … + y²/96 + 5y³/384` (via `sinh z ≤ z cosh z`,
  `z cosh z ≤ sinh z(1+z²/3)`, `arctan(e^{−2z}) + arctan(tanh z) = π/4`); golden-point cubic
  `(R−x)x² ≤ R²(R+x)/11`; numerics `γ < 0.577216`, `log π ≤ 1.1448`, `e^{3.5318} ≤ 34.3`.
- Axioms: `propext, Classical.choice, Quot.sound`. Olean built, wired into the AIP umbrella. README mechanism 23.
- Limit of this gauge: total potential `≈ −log(2R) + (5/2)log φ − (γ+log π) − O(R²)` vanishes at `R ≈ 0.297`.
- Overlap check: corpus RHTower `reflectedArchLevy_killing_term_le_jump_add_collar` (pointwise only,
  Φ-gauge), ACT `ArchimedeanZTypeLaw` (m_a gauges only), odd-window corpus best `1/130`
  (`two_mul_sinh_sq_le_markovEnergy_of_odd_support_Icc_le_inv_130`). Another agent works on ACT
  `CurvedGauge*` (all profiles, pole converted) — adjacent, not overlapping.

### C12 — Selectivity: odd-window positivity past the plastic threshold fails for ζ(s−a)ζ(s+a) (`ShiftedPairOddWindowSelectivity.lean`)
- Goal-loop contribution G2 (criterion 5). `shiftedPairZeroForm a F = 2(Ẑ(F cosh(a·)) − Ẑ(F sinh(a·)))`, the
  zero form of `Λ(s−a)Λ(s+a)` (zeros `ρ ± a`); justified by `autoCorr_cosh_sub_autoCorr_sinh`
  (`A_{F cosh} − A_{F sinh} = cosh(a·) A_F`, so it is `2W_ζ(cosh(a·) A_F)`).
- Exact comparison (`shiftedPairZeroForm_eq`, supports `2r < log 2`):
  `Ẑ_a(F) = 2Ẑ(F) + 4∫_0^∞ (cosh(at) − 1)(2cosh(t/2) − ω(t)) A_F(t) dt` — from the Markov-window
  representation `fullZeroForm_eq_window` and the jump identity `gaugeJumpProfile_cosh_sub_sinh`.
- `exists_odd_shiftedPairZeroForm_neg`: for every `r` with `t* < 2r` (`t* = log ρ`, plastic) some odd
  `F ∈ C²_c` on `[−r, r]` has `Ẑ_a(F) < 0` for all large `a` (odd two-bump, width `2w ≤ t*`, separation
  in `(t*, min(2r, log 2))`; `Ẑ_a(F) ≤ 2Ẑ(F) − 2a²t₁²κ(t₁)w²`). `odd_window_selective`: on every window
  `t*/2 < r ≤ 7/25`, ζ's odd form is coercive (C11) but the shifted pair's is not.
- Axioms standard; olean built; wired. Corpus overlap: `SuzukiScrewDisjointCrossCoupling` (disjoint bumps
  beyond t* have positive screw cross pairing ⇒ no Beurling–Deny) — mechanism-adjacent, different
  statement (no shifted-pair system, no selectivity). `NonTemperedShiftedZetaPairCountermodel` defines the
  countermodel's structural properties but no zero form.

### C13 — The infinite-shift Hankel limit: ζ(s−a)ζ(s+a) fails at support 13/125 < 21/200 (`ShiftedPairHankelSelectivity.lean`)
- Goal-loop contribution G3 (criterion 5, sharpened). For `H` on `[y₀, r]`, `G_a = e^{−ay}H`, odd `F_a = G_a − G_a(−·)`:
  `Ẑ_a(F_a) = 2Ẑ(F_a) + 8∫(cosh(at)−1)κ A_{G_a} + 2∫(1−e^{−at})² f (H∗H)` (`shiftedPairZeroForm_oddReweightedHankel`;
  `autoCorr_sub_reflect`, `selfConv_exp_mul`, `(cosh u − 1)e^{−u} = (1−e^{−u})²/2`). The first two terms are
  `O(a² e^{−2ay₀})` (`exists_fullZeroForm_le_lipschitz`: `Ẑ(F) ≤ K² + C∫F²` on windows `2r < log 2`;
  `abs_integral_correction_reweightedHankel_le`), the last tends to the Hankel form `2∫∫f(y+z)H(y)H(z)` of the
  screw weight `f = ω − 2cosh(t/2)`.
- `f` is not log-convex: `f(0.1198) ≤ 2.43`, `1.35 ≤ f(0.1602)`, `f(0.1998) ≤ 0.74` (`screwWeight_values`),
  so `H = φ_{0.06} − (93/50)φ_{0.10}` (half-width 10⁻⁴) has Hankel form `≤ m²(2.43 − 2.7c + 0.74c²) < 0`, `c = 93/50`
  (`integral_weighted_hankelProfile_le`, bump-convolution calculus `integral_mul_bumpConv_bounds`).
- `exists_odd_shiftedPairZeroForm_neg_below_markovWindow`: ∀ large `a` ∃ odd `F ∈ C²_c` on `[−13/125, 13/125]`
  with `Ẑ_a(F) < 0`. `markovWindow_selective`: paired with ACT C27 (`Ẑ ≥ (1/30)∫F²` on `[−21/200, 21/200]`).
  Refutes the G2 conjecture "`2r ≤ t*` ⇒ shifted pair odd-positive" (here `2r = 0.208 < t* ≈ 0.281`).
- Consequence: the existing 21/200 theorem is already selective; selectivity is not a feature of new support
  only. Any proof of window positivity at 21/200 must use a property of ζ that ζ(s−a)ζ(s+a) lacks at large `a`
  — here the Hankel positivity of `ω − 2cosh(t/2)` is replaced by the `cosh(at)`-weighted kernel.
- Axioms standard; olean built; wired into the AIP umbrella. README mechanism 25.

### C14 — The curved fold: odd window 17/50 (`FoldedSurplusGroundStatePotential`, `CubicGaugeSurplusPotential`, `CurvedFoldOddWindowPositivity`)
- Goal-loop contribution G4 (criterion 1: support 7/25 → 17/50 = 0.98·½log 2, for all even profiles in every odd gauge).
- Exact fold: `2S_arch − D_arch = 2S_P(F)`, `S_P = ∫_{x>0}∫_{s>0}(ω(s) − ω(s+2x))J_s(x)` (`two_mul_archSame_sub_archCrossingDiff_eq`);
  `J_P(F) ≥ 4·killing + 2S_P(F)` (`fourKilling_add_surplusEnergy_le_archJump`). G1 discarded `S_P`.
- Ground-state transform of the surplus: pairwise `(a−b)² ≥ a²(1−q/p) + b²(1−p/q)` ⇒ `S_P ≥ ∫_{x>0}F²U_h`,
  `U_h(x) = ∫_{(0,r]} k(x,y)(1 − h(y)/h(x))` for any `h ≥ a₀ > 0`, Lipschitz on `[0,r]` (`surplusEnergy_ge_potential`;
  one Fubini swap + translations).
- Cubic gauge closed form: `ω(t) = 1/(4sinh(t/2)) + 1/(4cosh(t/2))`, `1/(2t) + 1/4 − t/16 − t²/32 ≤ ω ≤ 1/(2t) + 1/4`;
  `∫_0^r k₀(h(x) − h(y)) = a₁x(1−ℓ) + a₂(3x²/2 − rx) + a₃(11x³/6 − r²x/2 − x³ℓ)` (`integral_principalSurplus_cubicGauge`);
  remainder ≤ `L∫((x+y)/16 + (x+y)²/32)|x−y|` (`mul_surplusPotential_cubicGauge_ge`).
- Gauge `h = 1/500 + (3/5)y − y² − (6/5)y³` (peak 0.216 ≈ r/φ, `h(r)/h_max ≈ 0.6`), R = 681/2000; numerator
  `(1/500 − x²)ℓ + h(λ − κ − …) + P₁ − (3/5)ρ ≥ 0` on (0, 17/50] (`curvedOddNumerator_nonneg`): 12 tangent intervals
  (7-smooth anchors; log 3, 5, 7 to 1e-7 via `Real.abs_log_sub_add_sum_range_le`) + origin/collar/edge/rim pieces,
  each closed by nlinarith on a quartic. Min slack ≈ 0.0016 (in h-units) near x ≈ 0.22–0.24.
- `fullZeroForm_ge_of_odd_support_le_curved`: odd `F ∈ C²_c` on `[−17/50, 17/50]` ⇒ `Ẑ(F) ≥ (1/100)∫F²`.
  Pole `2S² ≤ (271/20000)∫F²`. Axioms standard; oleans built; wired. README mechanism 26.
- Asymptotics: odd-sector constant = second eigenvalue of `log|ξ|` on an interval (Kwaśnicki: `≈ log(3π/4) ≈ 0.86`);
  flat fold gives `−γ + (5/2)log φ ≈ 0.63`; main-term odd positivity would reach ≈ 0.375 (> ½log 2).

### C15 — Past ½ log 2: the prime atom paid on the first prime window (`QuarticGaugeSurplusPotential`, `FirstPrimeWindowOddStrip`, `OddWindowPastFirstPrime`)
- Goal-loop contribution G5 — the goal statement itself: `J_M(u) + V_μ(u) ≥ 0` for all even profiles with support
  347/1000 > ½log 2 (past 21/200), every odd gauge, prime atom `Λ(2)/√2` paid on the first prime window, no pole-free margin.
- Prime-2 representation (`2R < log 3`): `signedJumpEnergy = arch + Λ₂·gJP(log 2)`, `profilePrimeSum = Λ₂(P(x+L)+P(x−L))`;
  `gJP(L) − ∫F²P(P(·+L)+P(·−L)) = −2∫F(x)F(x+L)` when `P = 1` on supp F (`gaugeJumpProfile_sub_primePotential_eq`);
  odd strip `∫F(x)F(x+L) ≤ ∫_{[L−r,r]}F²` (`integral_mul_shift_le_strip`, pointwise AM-GM + reflection); `Λ₂ ≤ 0.4902`.
  Plateau bound with prime returned (`neg_poleFreeWeilOperator_add_primeSum_ge`, no window restriction).
- Quartic gauge closed form (`integral_principalSurplus_quarticGauge`: extra `a₄(25x⁴/12 − rx³ − r³x/3)`).
  Gauge `1/500 + (119/200)y − y² − (3/10)y³ − (5/2)y⁴` (window units `0.017 + 1.715s − s² − 0.108s³ − 0.30s⁴`: found by
  shifting the cubic's b₃ up and adding b₄ < 0, b₁ down — flattens W over s ∈ [0.35, 0.9]). L = 63/100. R = 139/400.
- Certificate: 14 tangent intervals + origin + 2 collars + 4 monotone edge pieces + strip [0.346, 0.347] (numerator ≥ 0.4902·h).
  Margins ≈ 0.001–0.0015 (h-units) in the middle; strip margin ≈ 0.013. Pole `2S² ≤ (289/20000)∫F²`.
- `fullZeroForm_ge_of_odd_support_le_pastFirstPrime`: odd F on [−347/1000, 347/1000] ⇒ Ẑ ≥ (1/100)∫F². Axioms standard;
  oleans built; wired. README mechanism 27.
- Insight: crossing ½log 2 costs nothing at the prime — on the strip the plateau potential ≥ 1.7 ≫ Λ₂; the binding constraint
  is the archimedean middle. Archimedean odd positivity should persist to ≈ 0.375; past that the atom's sign must be used.

### C16 — The micro-fold: Harnack across ½ log 2, the first prime window is atom-free (`FirstPrimeMicroFold.lean`)
- Goal-loop contribution G6 (criterion 3: Harnack inequality across a prime shift with explicit constant).
- Even/odd split about L/2 on S = [L − r, r]: F(a)F(L − a) = F_e² − α², α = (F(a) − F(L − a))/2 (`reflectedOddPart`); the atom
  costs only ∫_S α² (`integral_mul_shift_le_reflectedOdd`, sharper than the AM-GM strip bound of C15).
- Quadruple inequality (`microFold_quadruple_ge`) with k₀(t) = ω(t) − ω(2p) (`microFoldKernel`): even parts drop out.
  Integrated (`microFold_strip_ge`): ∫_S∫_S k(Fx − Fy)² ≥ (2K + 2η k₀(2η))∫_S α², K = Ω(η) − Ω(2η) − ηω(2p), η = r − L/2.
- `microFoldConstant_ge`: constant ≥ 0.9804 ≥ 2Λ(2)/√2 for every r ∈ (L/2, 2/5] (C ≥ log2 + ½ − d/(2p) − O(d²), d = 2η).
- `two_mul_primeShift_le_stripSurplus`: 2Λ₂∫F(x)F(x+L) ≤ 2·stripSurplus for odd F on [−r, r], r ≤ 2/5.
- `integral_strip_eq_two_mul_stripSurplus` (box = 2 × triangle), `surplusEnergy_ge_potentialOff_add_strip` (GS transform with
  the S×S pairs exact), `fourKilling_add_potentialOff_le_archJump_sub_prime`: 4·killing + 2∫F²U_off ≤ J_arch − prime term.
  Up to 2/5 the window problem is purely archimedean (U_off potential, no strip charge). Axioms standard; olean built; wired;
  README mechanism 28.
- Insight: limit constant log 2 + ½ is shift-independent ⇒ the local test is Λ(n)/√n < ½log 2 + ¼ ≈ 0.597: holds for n = 2,
  fails for n = 3 (0.634). The second prime window needs more than the micro-fold.
- Next: certificate for U_off at r = 7/20 (support record); loss on S vs U bounded by ∫_S |k(1 − h(y)/h(x))| ≤ (½ + d/4)·L_h·d/h_S.

### C17 — Odd window 7/20 without a strip charge (`AtomFreeOddWindowSevenTwentieths.lean`)
- Goal-loop contribution G7 (criterion 1: support 347/1000 → 7/20, all even profiles, every odd gauge, atom paid).
- Strip loss: h(x)(U − U_off)(x) ≤ L|S|(½ + |S|/4) (`mul_surplusPotential_le_off_add`); at r = 7/20 this is ≤ 0.0023.
- R = 701/2000, gauge (1/500, 3/5, −1, −3/10, −49/20), L = 16/25, c₀ = 397/20000, pole ≤ 297/20000.
- Certificate: origin + 2 collars + 14 tangent intervals (a-anchors re-centred on R − x: 4/15, 15/64, 50/243, 9/50, 4/25, 7/50,
  3/25, 1/10, 2/25, 3/50, 3/70, 3/100, 3/140, 3/200) + 2 monotone edges + 4 strip pieces (≥ 0.0023). All passed first try.
- `fullZeroForm_ge_of_odd_support_le_sevenTwentieths`: odd F on [−7/20, 7/20] ⇒ Ẑ ≥ (1/200)∫F². Axioms standard; olean; wired;
  README mechanism 29.
- Lean traps: `linarith` timed out (isDefEq on `surplusPotentialOff`'s `if` via let-bound equalities) → `clear_value` the
  `set` variables + `linarith only`; `set c₀` is an opaque atom for linarith → `rw [hc₀]` first.
- Next: the middle margin (≈ 0.001 h-units) is the bottleneck; push toward 0.36–0.375 needs a better gauge (quintic/sextic or
  log-corrected) and/or keeping part of the S×S surplus in the transform.

### C18 — The sharp micro-fold: Harnack across every prime-power shift (`SharpMicroFoldHarnack.lean`)
- Goal-loop contribution G8 (criterion 3, all prime shifts, explicit constant).
- Scaling limit: strip problem = regional log kernel 1/(2|s−t|) on [−1,1]; odd ground state g(s) = s EXACTLY,
  eigenvalue 2 (∫ sign(s−t) dt = 2s). The G6 constant log 2 + ½ was not sharp (dropped surplus, crude second variable).
- `sharpQuadruple_ge` (fold onto [m,r], same-side |u−v| vs crossing u+v, 4 sign cases), `sharpFold_core`, `sharpFold_folded`.
- `sharpFold_potential_ge`: 2U_g + 4K ≥ 1.9 − η/p − 3η² with g = η/10 + t (cubicGauge closed form, logs cancel).
- `integral_sharpFoldWeight`, `integral_abs_sub_symm`, `integral_integral_swap_box` (Fubini on a box), `abs_foldedWeight_le`.
- `sharpMicroFold_strip_ge`: ∫_S∫_S k(Fx−Fy)² ≥ (1.9 − η/p − 3η²)∫_S α² (η ≤ 1/12).
- `vonMangoldtAtom_le`: Λ(n)/√n ≤ 2/e < 0.7358. `two_mul_primePowerShift_le_stripSurplus`: for all n ≥ 2 and windows
  ½log n < r ≤ ½log n + 1/12: 2Λ(n)/√n ∫F F(+log n) ≤ 2·stripSurplus F (log n − r) r. Axioms standard; olean; wired.
- README: mechanism 28's "fails for n = 3" corrected; mechanism 30 added.
- Consequence for the support push: the micro-fold needs only θ = 2Λ₂/λ ≈ 0.98/1.9 ≈ 0.52 of the S×S surplus; the rest can stay
  in the ground-state transform, halving the inner-edge loss (next: G9 window 0.353–0.355 with θ-split).

### C19 — Second-order surplus kernel and antiderivative (`SecondOrderSurplusPotential.lean`)
- Infrastructure for G9 (and reusable for the all-profile sector): `mul_archLevyDensity_le_second`
  (uω ≤ ½ + u/4 − u²/48 − u³/32 + u⁴/250 on (0, 3/4]), `archLevyDensity_secondOrder_bounds`, `abs_surplusKernel_sub_secondOrder_le`
  (k = k₀ + (x+y−|x−y|)/48 + xy/8 ± (x+y)³/250), `firstOrderSurplus` + `integral_firstOrder_quarticGauge` (exact polynomial),
  `mul_surplusPotential_quarticGauge_ge_second` (remainder L(4/125)r⁵ instead of L·rem), `tanh_le_quintic`,
  `archLevyAntideriv_ge_second` (Ω ≥ −½log(y/4) + π/4 − y/4 + y²/96 on (0,1]). Imports ACT `CurvedGaugeArchimedeanBounds` (Taylor six).
- Gain ≈ 0.0009 (surplus) + 0.0004 (Ω) h-units in the middle of the window: doubles the margin.

### C20 — Odd window 353/1000: the strip shared (`SharpFoldOddWindowPastSevenTwentieths.lean`)
- Goal-loop contribution G9 (criterion 1: support 7/20 → 353/1000).
- θ-split: convex combination of `surplusEnergy_ge_potential` and `surplusEnergy_ge_potentialOff_add_strip`
  (`fourKilling_add_potentialMix_le_archJump_sub_prime`), θ = 53/100 (sharp micro-fold λ ≥ 1.88).
- R − r = 1/20000 (collar is free), c₀ = 41/2500, pole ≤ 757/50000, L = 13/20, a-anchors re-centred for R = 7061/20000.
- Certificate: origin + 2 collars + 14 tangent + 1 monotone edge [0.338, 0.3401] + 7 strip pieces (≥ 0.0023); all passed after one
  constant fix (strip G Llam 3270410 → 3270409: worst-case log bounds must be recomputed with exact y/s).
- `fullZeroForm_ge_of_odd_support_le_threeHundredFiftyThreeThousandths`: Ẑ ≥ (1/1000)∫F². Axioms standard; olean; wired; README 31.
- Wall: at 0.355 the inner edge needs N(p) ≥ 0.0030 vs 0.0017 available; structural (see ledger wall analysis).

### C21 — Odd window 356/1000: the ground-state remainder carries potential (`SchurAbsorbedGroundState`, `SchurFoldWindowNumeratorBounds`, `SchurFoldOddWindowThreeHundredFiftySixThousandths`)
- Goal-loop contribution G10+G11 (criterion 1: support 353/1000 → 356/1000, through the inner-edge wall of C20).
- New mechanism: Schur step on the dropped ground-state remainder k h(x)h(y)(f(x)−f(y))². `sq_sub_ge_groundState_schur`:
  k(a−b)² ≥ a²(k(1−q) + kβq²/(k+βq)) + b²(k(1−1/q) − β); `surplusEnergy_ge_potential_add_schur`:
  S_P(F) ≥ ∫F²U_h + s₀|H|∫_Z F² − β|Z|∫_H F² when s₀ ≤ kβq²/(k+βq) on Z×H. The potential becomes nonlocal.
- `fourKilling_add_potentialMixSchur_le_archJump_sub_prime`: θ-split + Schur rectangle (Schur on the (1−θ) full-GS part).
- Certificate: Z = [0.337, 0.343], H = [0.35, 0.356], β = 40, s₀ = 21/2 (k ≥ 128/5 from the second-order ω bounds, q ≥ 31/40);
  gauge 1/500 + (3/5)y − y² − (11/50)y³ − (49/20)y⁴ (L = 16/25), R = 7121/20000, c₀ = 331/20000, pole ≤ 7767/500000.
  Numerator ≥ 0 on (0, 0.337], ≥ 2/1000 on Z, ≥ 33/10000 on [0.343, 0.35], ≥ 85/10000 on H (18 tangent + 3 monotone pieces);
  every piece passed on the first attempt.
- `fullZeroForm_ge_of_odd_support_le_threeHundredFiftySixThousandths`: Ẑ ≥ (1/1000)∫F². Axioms standard; oleans; wired; README 32.
- Insight: the structural inner-edge loss of C20 is a loss of the LOCAL potential only; with the remainder kept, the wall
  moves to where the hub's spare potential runs out.

### C22 — Odd window 9/25: the prime atom pays the strip (`PrimeAtomEvenPartPotential`, `PrimeEvenPartWindowNumeratorBounds`, `PrimeEvenPartOddWindowNineTwentyFifths`)
- Goal-loop contribution G12 (criterion 1: support 356/1000 → 9/25 = 0.36).
- Exact identity for odd F on [−r, r], L/2 < r: ∫F(x)F(x+L) = 2∫_S α² − ∫_S F² (`integral_mul_shift_eq_two_reflectedOdd_sub`);
  the atom is a GAIN 2Λ₂∫_S F² on the even (ground-state) part, a cost 4Λ₂∫_S α² on the odd part. Interpolation
  `integral_mul_shift_le_interp` (t ≤ 1); `vonMangoldtAtom_two_ge` (Λ₂ ≥ 49/100);
  `fourKilling_add_potentialMixPrime_le_archJump_sub_prime` (θ-split with (1+t)·cost; strip potential (49/100)t).
- Certificate: t = 1/2, θ = 4/5 (λ ≥ 1.858), strip loss ≤ 7/1000 < (49/200)h (h ≥ 79/2000 on S); numerator N ≥ 0 on the
  whole window suffices; gauge = the 356/1000 gauge dilated by 90/89; R = 7201/20000, c₀ = 171/10000, pole ≤ 8038/500000;
  origin + 2 collars + 24 tangent + 3 monotone pieces (refined to width 0.01 on [0.18, 0.24], the slack minimum).
- `fullZeroForm_ge_of_odd_support_le_nineTwentyFifths`: Ẑ ≥ (1/1000)∫F². Axioms standard; oleans; wired; README 33.
- Insight: mechanisms 28–32 discarded the even part of the atom, which is the ground-state direction; with it kept the
  first prime window has no inner-edge wall, and the support is limited by the archimedean middle only (dilation
  costs log s in potential; hand slack min ≈ 0.0155 at x ≈ 0.2 for r = 0.356).

### C23 — Odd window 181/500: lending potential to the middle (`OffStripGroundStateSchurRectangles`, `SchurLendingWindowNumeratorBounds`, `SchurLendingOddWindowThreeHundredSixtyTwoThousandths`)
- Goal-loop contribution G13 (criterion 1: support 9/25 → 181/500 = 0.362). Lead "lend potential from the origin to x ≈ 0.2".
- Generic: `surplusEnergy_ge_potentialOff_add_strip_add_schur` (off-strip GS transform with a hub-below rectangle
  H_A < Z_A and a hub-above rectangle Z_B < H_B ≤ r, disjoint as pair sets); `sq_sub_ge_schur_pair`, `rectDensity`
  (+ measurable/integrable/integral), `offStrip_schur_pointwise`; reduction
  `fourKilling_add_potentialMixPrimeSchur_le_archJump_sub_prime` (Schur with weight θ of the off-strip part).
- Certificate: t = 4/5, θ = 24/25; Z = [7/50, 27/100]; H_A = [11/250, 7/100] (β = 9/25, s = 33/1000; k ≥ 31/50, q ≥ 1/3);
  H_B = [207/625, 181/500] (β = 1, s = 89/500; k ≥ 5/4, q ≥ 1/2); gauge 1/500 + (59/100)y − (29/30)y² − (21/100)y³ − (16/7)y⁴;
  R = 7241/20000, c₀ = 347/20000, pole ≤ 8174/500000. Numerator: ≥ 0 off the hubs, ≥ 173/100000 on H_A, ≥ −38/100000 on Z.
- Finding: the origin hub is intrinsically weak (gain per pair ≤ kq² ≈ 0.07, 14% of the total); the strip hub (fed by
  the prime even part) carries 86%.
- `fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`: Ẑ ≥ (1/1000)∫F². Axioms standard; oleans; wired; README 34.

### C24 — Harnack across prime-power shifts with the even part (`PrimePowerEvenPartHarnack`)
- Goal-loop contribution G14 (criterion 3: Harnack across the shifts log 3, log 4 with explicit constants and a gain).
  Lead "the same even-part identity for n = 3, 4".
- `two_mul_primePowerShift_le_stripSurplus_sub_evenPart` (all n ≥ 2, windows ½log n < r ≤ ½log n + 1/12, (1+t)2Λ_n ≤ θλ):
  2Λ_n∫FF(+log n) ≤ θ·2·stripSurplus − 2Λ_n t∫_{S_n}F².
- n = 3: Λ₃ ∈ [0.634, 0.6344], λ ≥ 1.7, t = 1/3, θ = 1: gain (2/5)∫_{S₃}F² (`two_mul_primeThreeShift_le_stripSurplus_sub`).
- n = 4: Λ₄ = ½log 2 (`vonMangoldtAtom_four`), t = 1, θ = 4/5: gain log 2·∫_{S₄}F², 20% of the strip surplus left over
  (`two_mul_primeFourShift_le_stripSurplus_sub`). Axioms standard; olean; wired; README 35.

### C25 — Overlapping strips of 2 and 3: the wide fold and the shared S₃×S₃ (`WideMicroFoldExactRates`, `OverlappingPrimeStripsJointHarnack`)
- Goal-loop contribution G15 (criterion 3: joint Harnack across the shifts log 2 and log 3 past ½ log 3, explicit
  constants and gains). Request: "windows past ½ log 3, where the strips of 2 and 3 overlap and would have to share the
  surplus on S₃×S₃".
- Wide fold (`WideMicroFoldExactRates`): exact quadruple rates R₋ = ω(|u−v|) − ω(L−u−v), R₊ = ω(u+v) − ω(L−|u−v|),
  R₋ ≥ R₊ by complete monotonicity (`archLevyDensity_sub_shift_le`), weight W = 2(R₋−R₊)(1−q) + 4R₊; valid for any
  strip width with p > 0 (no η ≤ p, η ≤ 1/12). Band version with the pairs of [c, r]² withheld (`withheldKernel`,
  `wideFoldWeightBand`, `wideBandMicroFold_strip_ge`).
- Integrated weight: W = 2k(1−q) − 2D(1−q) + 4R₊; defect ≤ (c₁u³/6 + c₀u²/2)/(β+u), c₁ ≥ 1/(L(L−2η)) + 1/24 + L/8,
  c₀ ≥ L³/250; 4∫R₊ ≥ 2ℓ − 2log(L/(L−η)) − (3η²+7η³)/24 − 8L⁴/1000; ∫_a^b ω to second order (both sides).
- Certificate at r = 221/400, β = 1/50: ∫_0^η W_band ≥ 1 at every folded point (`wideBandFold_potential_logTwo`); band
  cost ≤ 0.044 (M = 6.8804 on the band × (η − b) ≤ 0.0063878); polynomial core margin ≈ 0.026 in G·P units.
- Sharing: T(S₂) = withheld box + T(S₃) (`integral_box_eq_withheld_add`). Joint theorem
  `two_mul_primeTwoThreeShifts_le_stripSurplus_sub`: odd F on [−221/400, 221/400] ⇒
  2Λ₂∫FF(+log2) + 2Λ₃∫FF(+log3) ≤ 2 stripSurplus_{S₂} − (1/62)∫_{S₂}F² − ½∫_{S₃}F² (t₂ = 1/60, t₃ = 2/5, λ₃ ≥ 1.8939).
  Since e^{2r} < 4 this is the whole prime side at this window.
- Relation: `NestedStripShellMicroFold` / `SharedStripSurplusAllocation` (other agent) share nested *thin* strips with
  the sharp shell constant; the outer strip of 2 at r = 221/400 has λ₀ = 1.9 − η/p − 3η² ≈ 0.31 < √2 log 2, out of
  their reach. `integral_box_eq_withheld_add` is the closed-box analogue of `integral_shellIntegrand_eq` (open box).
- Axioms standard (propext, choice, Quot.sound); oleans built; both modules wired; README mechanism 40, open problem 8.

### C26 — The incidence ledger at every aperture and the global incidence allocation condition (`OddFoldCrossingPotentialAtEveryAperture`, `GlobalIncidenceAllocationCondition`)
- Request (2026-10-21): an explicit global incidence/allocation condition covering every relevant prime-power
  shift, the favorable components, the axial collars and the pole/gauge remainder, with a proved transfer to
  complete odd Weil positivity and RH; every declaration without unproven premises (iff theorems, no reduction lemmas).
- Fold at every aperture: `archLevyDensity_mul_sq_le` (`ω(t)t² ≤ 3/2 + 4B²` on `(0, 2B]`) replaces `2B ≤ 1`;
  `integrable_archLevy_mul_signedShiftJump_prod_everyAperture`, `integrable_foldedCrossingIntegrand_everyAperture`,
  `two_mul_archSame_sub_archCrossingDiff_eq_everyAperture`; crossing potential `crossingPotential P x = ∫_{t>x} ω(t)P(t−x)`,
  integrand `crossingKillingIntegrand` (Fubini on the quadrant, `integrable_crossingKillingIntegrand`);
  exact fold `archJump_eq_two_mul_surplus_add_crossingPotential`: `J_P(F) = 2S_P(F) + 4∫_{x>0}F²Π_P`.
  `crossingPotential_eq_killing_add_collar`: `Π_P = (Ω(x) − Ω(x+r)) + collarCrossingPotential`, `0 ≤ collar ≤ Ω(x+r) − Ω(x+B)`
  (`collarCrossingPotential_bounds`).
- Ledger: `relevantShifts r = {n ≥ 2 : log n < 2r}` (`mem_relevantShifts`, `relevantShifts_mono`); components
  `oddStripCost`, `evenStripGain`, `surplusPool`, `crossingPotentialTerm`, `gaugeRemainder`, `poleCharge`,
  `aperturePlateau r R = plateauGauge R (R − r)`; signs (`surplusEnergy_nonneg`, `crossingPotentialTerm_nonneg`,
  `sum_oddStripCost_nonneg`, `sum_evenStripGain_nonneg`, `poleCharge_nonneg`); boundary vanishing
  `eq_zero_at_support_radius`, `integral_mul_shift_eq_zero_of_two_mul_le` (shift `≥ 2r`).
  `fullZeroForm_eq_incidenceLedger`: odd `F ∈ C²_c` on `[−r, r]`, `0 < r < R` ⇒
  `Ẑ(F) = pool + crossing + Σ gains − Σ costs + remainder − pole` (prime tsum → finite sum over `relevantShifts R`,
  the shifts in `[2r, 2R)` cancel between jump and potential, those below `2r` split by C22's identity).
- Condition and transfer: `GlobalIncidenceAllocation r R F` (costs + pole ≤ pool + crossing + gains + remainder);
  `globalIncidenceAllocation_iff_fullZeroForm_nonneg` (test by test); `riemannHypothesis_iff_forall_odd_fullZeroForm_nonneg`
  (via ACT `riemannHypothesis_iff_forall_odd_zeroForm_nonneg`, `zeroForm_eq_fullZeroForm_of_odd`, `phiDoobInv`);
  `forall_odd_fullZeroForm_nonneg_iff_globalIncidenceAllocation`; `riemannHypothesis_iff_globalIncidenceAllocation`
  (RH ⟺ condition at every aperture `r > 0`, plateau `R > r`, odd compact test);
  `riemannHypothesis_iff_exists_plateau_globalIncidenceAllocation` (one plateau per test).
- Axioms `propext, Classical.choice, Quot.sound` for all nine audited theorems; oleans built (`lake --old env lean -j 1`);
  both modules wired into the umbrella; README mechanism 43, table rows, trap, research topic 6.
- Relation to the sibling's C-loop: `GlobalSharedSurplusAllocation` (mechanism 42) bounds the prime side by cone surplus
  plus strip masses for `r ≥ 2`; the ledger is the exact identity it is a sub-inequality of. Not duplicated:
  their `integral_mul_shift_eq_zero_of_lt` needs `L > 2r` and no continuity, the ledger's version covers `L = 2r`.
- Lean notes: `Σ` cannot start an identifier (`hΣi`); `rw [hPB (x + L) ?_, hPB (x − L) ?_]` produces the side goals in
  reverse order; `Set.indicator_of_notMem` needs the set ascribed (`show t ∉ Ioi x from …`) or it elaborates `Real.lt`;
  `integrable_finset_sum` is deprecated → `integrable_finsetSum`; `Finset.sum_subset` with an explicit type on the
  `have` avoids beta-redexes.
- C26 addendum (explicit remainder): `continuous_integral_profileArchTerm` (standalone copy of the `hA` block of ACT's
  `continuous_poleFreeWeilOperator`); `gaugeRemainder_eq_arch` (the prime part of `−𝒲P` cancels the returned prime sum:
  remainder = `∫F²P(∫_{u>0}profileArchTerm P x u − 2γ'P)`); `plateauPotentialFloor R x = Ω(R−x)+Ω(R+x) − 2E(0) − 2γ'`,
  `measurable_archLevyAntideriv`, `abs_plateauPotentialFloor_le` (`≤ 2Ω(R−r) + |2E(0)+2γ'|` on `|x| ≤ r`, via
  `antitoneOn_archLevyAntideriv`), `integrable_sq_mul_plateauPotentialFloor`, `gaugeRemainder_ge_plateauPotentialFloor`
  (integral_mono of mechanism 27's pointwise bound), `fullZeroForm_ge_explicitLedgerFloor`:
  `pool + crossing + Σ gains − Σ costs + ∫F²·plateauPotentialFloor R − (R³/3)cosh²(R/2)∫F² ≤ Ẑ(F)` — all terms explicit
  functionals of `F`. Axioms standard. README mechanism 43 extended.
