# RH = ZAL ∧ AAL: large-height gauges, attainment producers, weak recurrence

- **ID:** rh-zal-aal-split-lean
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, standard axioms)
- **Source:** Opus goal loop rows 1053–1077 (`1-in-progress/rh-goal-loop-opus-2026-09-29.md`); STATUS MUST-1346–1351, 1353, 1355 (+adds), 1356 (+add), 1358 (+adds), 1360, 1361, 1362 (+add)
- **Statement:** RH ⟺ ZAL ∧ AAL. ZAL ("zeros approach the line") says `Θ∞ := limsup_{|γ|→∞}(Re ρ − ½)` is `0`. AAL (the asymptotic abscissa law) says `Θ∞ = Θ := sup(Re ρ − ½)`. Height-local large-height receivers produce exactly ZAL, with exact gauges in `Θ∞`. Every corpus "RH ∨ non-attained / chain" receiver produces AAL. Density-free weak recurrence of `ζ` around off-line zeros is an equivalent completion of ZAL to RH.

## Goal
Pin down what every large-height (asymptotic) receiver can and cannot deliver, and isolate the exact non-asymptotic remainder of RH.

## Gates
- [x] 0 → 1 well-posed (rows 1053–1056)
- [x] 1 → 2 paper proofs (each row)
- [x] 2 → 3 formalized: all modules below build with `lake build --old`, standard axioms, wired into `RHTower`
- [ ] 3 → 4 publication-ready (not intended; structural)

## Modules and main theorems
- `RHTower/GaussianCentralGapLargeHeightFiniteOffLine` — TG Gaussian central gap.
  - FOL rung: `eventualFilteredCentralGapBudget_iff_finiteOffLine`.
  - ZAL rung: `eventualFilteredCentralGapSubexponential_iff_zerosApproachLine`.
  - Exact large-height rate law: `eventualFilteredCentralGapRate_iff`, `..._iff_finite_re_gt`. The rate is `Θ∞ + Θ∞²/8`.
  - All-height rate law: `filteredCentralGapRate_iff`, `..._iff_re_le`. The unconditional rate is `17/32`.
- `RHTower/GaussianCentralGapRatePowerSaving` — every TG rate `s > 0` holds off a power-saving set of heights, unconditionally (Ingham–Huxley).
- `RHTower/XiLogDerivEventualPositivityAbscissa` — Hadamard positivity on `Re s > ½ + h` above some height ⟺ finitely many zeros with `Re ρ > ½ + h`. This gives the FOL cell.
- `RHTower/XiLogDerivGaugePositivity` — moving gauge: positivity right of `½ + g(|Im s|)` ⟺ zero-approach rate `g` (up to a unit shift).
- `RHTower/WeilLagAsymptoticAbscissa` — subtracted lag `Φ_S ≤ Me^{au}` ⟺ finitely many zeros with `Re ρ > ½ + a`.
- `RHTower/ZerosApproachLineAttainment` — ZAL ∧ ¬RH ⟹ attained top. RH ⟺ ZAL ∧ bounded lags along `b^m`, also on log-dense sets and with eventual Hadamard positivity. ZAL + twisted plateau nonnegativity ⟹ RH.
- `RHTower/ZerosApproachLineLowerSideLag` — one ordinate resonates with at most one prime. RH ⟺ ZAL ∧ lower lag bounds along `p^m` for all `p` in any infinite set of primes.
- `RHTower/ZetaWeakRecurrenceLadderCollapse`:
  - `ZetaWeaklyRecurrent` and `ZetaZeroDiscWeaklyRecurrent`;
  - transport of off-line zeros to unbounded heights;
  - `AsymptoticAbscissaLaw`, `riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`, `riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent`;
  - ladder collapse under weak recurrence (RH ⟺ FOL ⟺ ZAL ⟺ eventual Hadamard ⟺ bounded large-height TG budget).
- `RHTower/AsymptoticAbscissaLawProducers` — AAL from a non-attained top, no attained top excess, an off-line chain, bounded single-base lags, bounded log-dense lags, twisted plateau Weil energies, JAS real-amplitude positivity, and JAS dressed positivity.
- `RHTower/PolarGroundEnergySubexponentialZerosApproachLine` (MUST-1370) — restricted Weil route: RH ⟺ ZAL ∧ (subexponential floor for `μ₀`). Under ZAL the decay rate of `μ₀` reads the top excess.
- `RHTower/JointAncestryTypicalAsymptoticAbscissa` (MUST-1369) — typical JAS positivity at every level in `(½, 1)` gives AAL. With ZAL it gives RH.
- `RHTower/PrimeSideRiemannHypothesisSplit`:
  - RH ⟺ TG subexponential at large heights ∧ bounded lags along `b^m`, plus the lower-side version;
  - three pillars: RH ⟺ LH ∧ cosine finiteness at every level ∧ bounded lags along `b^m`.
- `RHTower/WeilLagProgressionZerosApproachLine` (MUST-1365) — lag progressions at real spacings.
  - Every real spacing `ℓ ≠ 0` detects an attained top (`exists_lag_progression_gt_of_attainedTop`, generalised in `WeilLagFunctionSingleBase`).
  - One bounded progression gives AAL; RH ⟺ ZAL ∧ one bounded progression.
  - With the Baire criterion (MUST-1363), the gap between one good spacing and a non-meagre set of them is exactly ZAL.
- `RHTower/WeilLagCompressedMultiplierCriterion` (MUST-1372): compressed lags `Σ_ρ e^{nh(ρ)}/(ρ(1−ρ))`.
  - A compressing multiplier (finitely many zeros with `Re h > ε`) makes one thin family RH-complete.
  - For the lag multiplier `ℓ(ρ − ½)`, compression ⟺ ZAL.
  - `H(z) = z/log(2 − z²)` compresses unconditionally (`Re H ≤ 3x/log(7/4 + y²)`), so RH ⟺ `sup_n Re R_H(n) < ∞`, with no ZAL premise.
- `RHTower/WeilLagWolffCompressedDetection` (MUST-1372 add. 3): there is a configuration on which every `ℓ`-lag sample vanishes (MUST-1371) and the log-compressed lag is unbounded. The abstract growth law is `exists_re_tsum_mul_exp_ge`. Subexponential slack suffices (add. 2): `riemannHypothesis_iff_logCompressedLag_subexponential`.
- `RHTower/WeilLagCompressedToeplitzPositivity` (MUST-1376): RH ⟺ Toeplitz positivity of the log-compressed lag. This contrasts with MUST-1373, where single-base lag Toeplitz positivity is blind to non-attained tops.
- `RHTower/WeilLagPowerGapSampling` (MUST-1377): arithmetically thick sampling needs no ZAL. If `A` has gaps `O(n^{1−δ})`, then RH ⟺ the lags along `A` are bounded above ⟺ bounded below. In particular this holds for every power set `{j^m}`.
  - Mechanism: the exact slope law makes the transfer error relative to the Chebyshev error, then a Landau–von Koch bootstrap runs `⌈1/δ⌉` rounds.
  - This corrects loop rows 1129 and 1134: `3/4` is not a threshold. Sub-power (log-dense) gaps remain AAL-only.
- `RHTower/WeilLagPersistentOscillation` (MUST-1378): unconditional persistent Ω±. For every `ε, δ > 0`, the lags exceed `a_1 − ε` on whole windows `[n − n^{1−δ}, n]` infinitely often, and lie below a fixed `−η` on whole windows infinitely often. Multiplicative windows would be AAL-type.
- `RHTower/ZerosApproachLineReciprocalZeta` — ZAL ⟹ `|ζ(s)| ≥ c|t|^{−ε}` on `Re s ≥ ½ + κ` at large heights. The three-circles bound is localized in height (`..._of_zeroFree_above`).
  - Also under ZAL: `|ζ'/ζ(s)| ≤ ε log|t|` there (`exists_norm_logDeriv_riemannZeta_le_of_zerosApproachLine`).
- `RHTower/DeBruijnStripThreshold` (MUST-1364) — heat-flow thresholds.
  - Zeros of `H_t` lie in a strip ⟺ `t ≥ 0`.
  - At `t = −τ` zeros reach depth `τ log(height) − C`.
  - Zeros approach the axis ⟺ `t > 0`, or `t = 0` ∧ ZAL.
  - So ZAL is the boundary value of a property that holds for `t > 0` and fails for `t < 0`.
  - Every zero of `F_τ` reappears in `H_{−τ}` along a relatively dense set of heights (`exists_riemannHeat_neg_zero_near_model_dense`).
  - Quantitative Newman: `≫_τ X` distinct non-real zeros with `0 ≤ Re z ≤ X` (`exists_finset_nonreal_riemannHeat_neg_card_ge`, MUST-1364 add. 2).
- `RHTower/ZetaTypicalLocalZeroCount` — local zero counts at the critical scale under typical `ζ'/ζ` box data. Clusters larger than `10κ` at scale `κ/log T` have exponentially small measure; this is a Lean-backed replacement for the Selberg–Fujii cluster input.

## Killed attacks (paper, rows 1057, 1058, 1068, 1071, 1073, 1076)
- Linear arithmetic identities cannot exclude an attained top (`ζ(ρ) = 0` cancels top terms).
- Degree-0 deviation rigidity is false in pure form (Dirichlet-character combinations); only conductor positivity survives.
- Almost periodicity of `ζ` in the strip is only Besicovitch, so it gives no localized recurrence.
- AAL heuristics:
  - the random Euler model gives probability 0 to off-line zeros and does not decide recurrence;
  - Deuring–Heilbronn repulsion is too weak;
  - continuous Beurling systems violate AAL.
- No pointwise symbol certificate for prime-blind positivity (high-pass sign changes; the pole term is indispensable).
- PBAP ∧ FOL ⟹ RH has no mechanism (PBAP is zeta-free).

## Open (recorded)
- AAL unconditionally ("the supremum of `Re ρ − ½` is a limit at infinity"). This is RH-strength in the same way as the arithmetic door.
- Zero-disc weak recurrence unconditionally.
- ~~Lower local counts at the critical scale at typical heights~~ — done. Step 1: `ZetaTypicalLocalZeroCountMultiScale`, MUST-1368. Step 2: `ZetaTypicalLocalZeroCountLower`, MUST-1375. The near/far split uses the two-scale Poisson domination `P(R) ≤ 25(R/R')P(R')`.

## Log
- 2026-10-13 — card created after rows 1053–1077; all listed modules built and audited.
- 2026-10-13 — added `DeBruijnStripThreshold` (row 1083, MUST-1364); `exists_riemannHeat_neg_zero_deep` refactored into `DeBruijnNewmanNonnegative`.
- 2026-10-13 — added `WeilLagProgressionZerosApproachLine` (row 1087, MUST-1365).
- 2026-10-13 — rows 1092, 1098, 1101: model-zero theorem (dense form), threshold sets, quantitative Newman.
- 2026-10-13 — row 1104: ZAL reciprocal-zeta bound (localized three circles).
- 2026-10-13 — row 1112: multi-scale cluster rarity (MUST-1368); row 1111: repaired `WeilLagSingleBaseLowerSide` after the spacing generalization.
- 2026-10-13 — row 1122: compressed-multiplier criterion (MUST-1372). AAL is a coordinate artifact; the price is a resolution factor `w_max/w(γ)` → ∞.
- 2026-10-13 — rows 1124–1128: arithmetic-thickness correction; subexponential slack (MUST-1372 add. 2); abstract growth law and Wolff contrast (add. 3).
- 2026-10-13 — row 1136: lower local counts at typical heights (MUST-1375), so typical counting is two-sided.
- 2026-10-13 — row 1137: compressed Toeplitz positivity (MUST-1376).
- 2026-10-13 — row 1139: power-gap lag sampling (MUST-1377), which corrects rows 1129 and 1134.
- 2026-10-13 — rows 1140–1141: adaptive sampling (MUST-1377 add.) and persistent oscillation (MUST-1378).
