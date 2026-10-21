# Route unification: which frontier-map routes are one route in different languages

- **ID:** `route-unification-dictionaries-2026-10-21`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) programme + report
- **Source:** `docs/reports/review-2110/walls-ledger.md` (the walls dictionary, Wall 1 = five faces of
  one number) extended from obstacles to routes of `docs/reports/rh-current-frontier-map.md`
- **Statement:** the live routes and candidates of the frontier map fall into a small number of
  clusters, each cluster being one receiver read in several languages; every identification is an
  unconditional Lean dictionary theorem (no premises, no axioms, no computation), and the report
  `docs/reports/review-2110/route-unification-ledger.md` records the clusters, the dictionaries,
  the exact differences that survive, and the open arrows.

## Goal
Stop duplicated effort: every certificate pushed on one face of a cluster is a certificate on every
other face, and counts once (the walls ledger's rule, applied to routes). Three graded units carry
the clusters: the zero width (prime side and zero side), the aperture (positivity side) and the
per-zero orientation (zero-indexed candidates). The dictionaries make the merges theorems.

## Gates
- [x] 0 → 1  in-progress: corpus survey done with the search tool (`research`) and `rg`;
  37 width-graded receivers (`xiZeroHalfPlaneBound_iff_*`), 135 per-zero indicators
  (`*_iff_re_eq_half`), the aperture ingredients (Rayleigh GLB, smoothing limit, parity split,
  odd capacity, Doob factorization, dominance chain, Rayleigh bridge) located.
- [x] 1 → 2  fully-proven: every arrow a composition of corpus theorems plus the new aperture
  arguments (mollification into the strict interior; left-continuity of `μ`).
- [x] 2 → 3  formalized: the three dictionary modules compiled with `lake --old env lean`, axioms
  `propext, Classical.choice, Quot.sound` only, oleans built single-threaded, wired into the
  `SquareRootThreshold` umbrella (import block); lint reachable.
- [ ] 3 → 4  not applicable (no stage 4 for non-RH items).

## Deliverables
1. `SquareRootThreshold/TheRoutesMeasureOneAperture.lean` — positivity cluster (RW, ACT, OWU,
   EWU, AIP/APT windows, SRT window and lag): at every aperture `A`, `μ(A) ≥ 0` ⟺ window
   positivity on every smaller aperture ⟺ even ∧ odd window positivity; odd window ⟺ OWU capacity
   inequality; odd window ⟹ ACT pole-free single-shift inequality; `μ(A) ≥ 0` ⟹ EWU blind minimum
   `≥ 0`, ⟹ SRT lag functional `≥ 0` at lag `2(A − w)`; endpoint RH.
2. `SquareRootThreshold/TheRoutesMeasureOneZeroWidth.lean` — width cluster beyond the walls
   dictionary: PBM regularized abscissa, TT Wold energy and directed covariance, HCF Gaussian
   Hankel tail cone, SZ shifted zero-free region, TH thermal projective moments, CCM source
   tomography (RW/HF), cosine shifts of `Ξ` in the Laguerre–Pólya class once the shift passes
   the width (LA/TT/SZ/HCF), packets and splines (WL).
3. `SquareRootThreshold/TheZeroIndexedRoutesMeasureOneSide.lean` — per-zero dictionary for the
   zero-indexed candidates (HJ residual, SEC jet boundedness, CDC confluence, …): all vanish at a
   zero iff it is on the line, and the global forms are RH.
4. `docs/reports/review-2110/route-unification-ledger.md` — the clusters, merges and open arrows.
5. `SquareRootThreshold/TheShiftedGroundStateInequalitiesReadTheOddWindow.lean` — the ACT arrow:
   `Ẑ(m_a u) = 2S_a − D_a + V_a`, so the variation inequality at aperture `A` is the odd window at
   `A` (converse on tests vanishing near the origin, the shift a gauge); the Markov inequality is
   the odd window plus `8(∫u dμ_a)²`, nested between the odd and the polar odd window; endpoints.
6. `SquareRootThreshold/TheBlindMinimumIsTheEvenPolarGroundEnergyBelowTheFirstPrime.lean` — the
   EWU arrow: for `2A < log 2`, `evenBlindMinimum A = μᵉ(A)`; EWU is the blind even window on
   smooth interior tests; the even window is the polar even window plus the unit-cosh-moment slice
   `markovEnergy ≥ −2`; no separation without refuting RH.

## Approach
Glue through the corpus's three zero-set languages (`zetaZeroWidth`, `XiZeroHalfPlaneBound`,
`XiDivisorSupport`) and through the full zero form `Ẑ` on real `C²_c` tests. New mathematics in
the aperture module: window positivity at aperture `A` is the restricted Weil ground energy
`μ(A) ≥ 0` up to the closed/open-aperture distinction (mollification of a `C²` window test into the
strict interior, continuity of the complete Weil energy under mollification, Suzuki's continuity
of `μ`), and the parity split of `Ẑ` turns the all-profile window into the even and odd windows.

## Theorems (all closed, standard axioms)
- `Q:TheRoutesMeasureOneAperture`: `ZetaWindowPositive`, `ZetaEvenWindowPositive`,
  `ZetaOddWindowPositive`, `windowPrimeCutoff`; `zetaWindowPositive_iff_even_and_odd`,
  `zetaOddWindowPositive_iff_sinhCapacity`,
  `shiftedGroundState_markovEnergy_nonneg_of_zetaOddWindowPositive`,
  `ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive`,
  `fullZeroForm_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg`, `smooth_eq_zero_of_radius_lt_abs`,
  `contDiff_top_smooth`, `zetaWindowPositive_of_ccmRestrictedWeilGroundEnergy_nonneg`,
  `ccmRestrictedWeilGroundEnergy_nonneg_iff_forall_lt_zetaWindowPositive`,
  `evenBlindMinimum_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg`,
  `re_W_nonneg_of_zetaWindowPositive`, `zetaWindowPositive_of_re_W_nonneg`,
  `re_lagPrimeWindowRHS_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg`,
  `fullZeroForm_nonneg_of_riemannHypothesis`, `riemannHypothesis_iff_forall_zetaWindowPositive`,
  `riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg`, `theRoutesMeasureOneAperture`.
- `Q:TheRoutesMeasureOneZeroWidth`: `zetaZeroWidth_le_iff_{logZetaRegCoeff,primeRegCoeff,
  vonMangoldtMinusOne}_converges`, `…_forall_packet_upper`, `…_spline_prime_sum_le`,
  `…_exists_dyadicWeightedPrimeWindowPowerUpper`, `…_forall_woldNatResidualSquareEnergy`,
  `…_forall_directedCovariance_bddAbove`, `…_hedenmalmGaussianHankelTailCone`,
  `…_suzukiZetaZeroFreeRightOf`, `…_forall_thermalProjectiveMoment_le`,
  `…_xiProjectiveReflectionRadius_le`, `zetaZeroWidth_eq_xiProjectiveReflectionRadius`,
  `…_criticalMellinDefectAnalyticAbove`, `…_inverseTiltedDyadicSourceAnalyticAbove`,
  `…_xiPoissonTraceVerticalTypeAtMost`, `re_logDeriv_xi_nonneg_of_zetaZeroWidth_le`,
  `zetaZeroWidth_le_iff_forall_exists_zetaDiscStronglyRecurrentOn`,
  `neg_lt_im_xiSpectralPoint_of_zetaZeroWidth_lt`, `laguerrePolya_cosineShiftXi_of_zetaZeroWidth_lt`,
  `theRoutesMeasureOneZeroWidth`.
- `Q:TheZeroIndexedRoutesMeasureOneSide`: `riemannHypothesis_iff_forall_xiDivisorSupport_re_eq_half`,
  `riemannHypothesis_iff_forall_xiDivisorSupport_of_indicator`, the eight
  `re_eq_half_iff_*` readings (HJ residual, seam charge, orientation defect, SEC jet boundedness,
  CDC confluence, BSH mate gain, IRK non-unit, W1C reality), `theZeroIndexedRoutesMeasureOneSide`,
  five global `riemannHypothesis_iff_forall_*` instances.

- `Q:TheSideIsTheDepthAndTheWidthIsItsSupremum` (round two, the unifying object): `criticalDepth`;
  `norm_orbitwiseFirstPrimeSeamCharge_eq_sinh` (`= √2 log 2 sinh(log 2 · depth)`),
  `primeTailSeedTwoReflectionResidual_eq_depth_mul`, `norm_primeTailSeedTwoReflectionResidual_eq`,
  `abs_log_deningerHalfDensityMateGain_eq`, `im_berryKeatingU_eq`, `abs_im_berryKeatingU_eq`,
  `im_weightOneCliffordEnergy_eq`, `abs_im_xiSpectralPoint_eq`,
  `zetaZeroWidth_le_iff_forall_criticalDepth_le`, `zetaZeroWidth_le_iff_forall_norm_seamCharge_le`,
  `zetaZeroWidth_le_iff_forall_abs_log_mateGain_le`, `sSup_norm_seamCharge_eq_sinh_zetaZeroWidth`,
  `theSideIsTheDepth`, `theWidthIsTheSupremumOfTheDepthMeters`.
- `Q:TheContactApertureOfTheGroundEnergyPath` (round two): `groundEnergyNonnegApertures`,
  `windowPositiveApertures`, `zetaContactAperture`; down-set lemmas, `windowPositiveApertures_subset`,
  `Ioo_subset_windowPositiveApertures`, `threeTenths_mem_*`,
  `riemannHypothesis_iff_not_bddAbove_{groundEnergyNonneg,windowPositive}Apertures`,
  `zetaContactAperture_eq_sSup_windowPositiveApertures`, `threeTenths_le_zetaContactAperture`,
  `ccmRestrictedWeilGroundEnergy_{nonneg_of_lt_contact,contact_eq_zero,neg_of_contact_lt}`,
  `zetaWindowPositive_of_lt_contact`, `zetaContactAperture_le_of_near_top_zero`,
  `groundEnergyFloor_feeds_every_width_reading`, `theContactApertureOfTheGroundEnergyPath`.
- Conjecture spun off: `0-backlog/contact-aperture-law-of-the-ground-energy-path-2026-10-21.md`.
- `Q:TheShiftedGroundStateInequalitiesReadTheOddWindow` (round three, the ACT arrow):
  `ShiftVariationWindow`, `ShiftMarkovWindow`, their `OffOrigin` forms,
  `ZetaOddWindowPositiveOffOrigin`, `ZetaPoleFreeOddWindowPositive(OffOrigin)`,
  `ZetaPolarOddWindowPositive`; `fullZeroForm_eq_zeroForm_of_odd`,
  `markovEnergy_eq_fullZeroForm_add_of_odd`, `fullZeroForm_phiDoob_shiftedGroundState`,
  `variationInequality_iff_fullZeroForm_nonneg`,
  `markovEnergy_phiDoob_shiftedGroundState_eq_fullZeroForm_add`,
  `markovEnergy_phiDoob_eq_fullZeroForm_iff`, `shiftVariationWindow_of_zetaOddWindowPositive`,
  `zetaOddWindowPositiveOffOrigin_of_shiftVariationWindow`,
  `shiftVariationWindowOffOrigin_iff_zetaOddWindowPositiveOffOrigin`,
  `shiftVariationWindowOffOrigin_iff_of_pos`, `shiftMarkovWindow_of_zetaOddWindowPositive`,
  `zetaPoleFreeOddWindowPositive_of_zetaOddWindowPositive`,
  `zetaPolarOddWindowPositive_of_zetaPoleFreeOddWindowPositive`,
  `shiftMarkovWindow_of_zetaPoleFreeOddWindowPositive`,
  `zetaPoleFreeOddWindowPositiveOffOrigin_of_shiftMarkovWindow`,
  `shiftMarkovWindowOffOrigin_iff_zetaPoleFreeOddWindowPositiveOffOrigin`,
  `shiftMarkovWindowOffOrigin_iff_of_pos`,
  `variationInequality_of_shiftMarkovWindow_of_profileMoment_eq_zero`,
  `shiftMarkovWindow_iff_fullZeroForm_ge`, `not_riemannHypothesis_of_not_zetaOddWindowPositive`,
  `riemannHypothesis_iff_forall_{shiftVariationWindow,shiftMarkovWindow,zetaOddWindowPositive}`,
  `theShiftedGroundStateInequalitiesReadTheOddWindow`.
- `Q:TheBlindMinimumIsTheEvenPolarGroundEnergyBelowTheFirstPrime` (round three, the EWU arrow):
  `energyProfile_mem_blindProfiles_of_two_mul_lt_log_two`,
  `evenBlindMinimum_eq_evenGroundEnergy_of_two_mul_lt_log_two`,
  `evenBlindMinimum_nonneg_iff_evenGroundEnergy_nonneg_of_two_mul_lt_log_two`,
  `one_twentieth_le_evenGroundEnergy_of_le_primeTwo`, `evenGroundEnergy_nonneg_of_zetaWindowPositive`,
  `re_W_nonneg_of_evenBlindMinimum_nonneg`, `fullZeroForm_nonneg_of_evenBlindMinimum_nonneg`,
  `fullZeroForm_eq_markovEnergy_add_of_even`, `evenPoleMoment_const_mul`,
  `markovEnergy_ofReal_const_mul`, `zetaEvenWindowPositive_iff_polar_and_unitCoshMoment`,
  `not_riemannHypothesis_of_not_zetaEvenWindowPositive`,
  `theBlindMinimumIsTheEvenPolarGroundEnergyBelowTheFirstPrime`.

## Corpus repair made on the way
`RHTower.norm_mobiusMertensPartialSum_eq` was declared in both `R:LiouvilleSummatoryRH` and
`R:CausalMobiusThetaTail` (different statements), both wired into the `RHTower` umbrella; any module
importing both cones fails to elaborate. The Liouville copy is renamed
`norm_mobiusMertensPartialSum_eq_abs_sourcePartialSum_moebiusR` (its only external consumer,
`R:SignedArithmeticAbscissaRH`, updated); both oleans rebuilt single-threaded.

## Log
- 2026-10-21 — card created; survey complete.
- 2026-10-21 — three modules compiled, audited, oleans built, wired; report
  `docs/reports/review-2110/route-unification-ledger.md` written; walls ledger links it as a
  companion. Lint: the three modules reachable; the gate reports four modules of other lanes
  unreachable from their umbrellas (`R:PrimeSpanIsThePolynomialClosure`,
  `R:ZetaOrbitApproachesEveryAnalyticTargetWithTheHurwitzThreshold`,
  `V:ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis`,
  `Q:PositionAndDepthShareOneNyquistAperture`), left to their owners.
- 2026-10-21 — round two (the unifying object): `TheSideIsTheDepthAndTheWidthIsItsSupremum` and
  `TheContactApertureOfTheGroundEnergyPath` compiled with `lake --old env lean`, axioms standard,
  oleans built single-threaded, wired; ledger section "The unifying object: the ground-energy path"
  appended; contact-law conjecture card created in 0-backlog.
- 2026-10-21 — round three (the two open arrows of cluster B):
  `TheShiftedGroundStateInequalitiesReadTheOddWindow` and
  `TheBlindMinimumIsTheEvenPolarGroundEnergyBelowTheFirstPrime` compiled with `lake --old env lean`
  (no warnings), 42 declarations with axioms propext/Classical.choice/Quot.sound only, oleans built
  single-threaded, wired into the umbrella import block; lint: both reachable (the gate reports the
  ChenGuptaLi* and GuthMaynard* modules of other lanes unreachable). Ledger: cluster B bullets, "Not
  the same route" and "Open arrows" updated; both arrows closed, the residuals recorded as the
  unit-cosh-moment slice inequality on `(3/10, ½(log 2 + 1/50)]` (EWU) and the capacity inequality
  on the non-polar tests (ACT).
- 2026-10-21 — the width-to-floor arrow is closed under locally bounded off-line zeros (two-sided
  in the finite case; dichotomy unconditional): see
  `width-to-ground-energy-floor-when-off-line-zeros-do-not-cluster-2026-10-21.md`.
