import GaloisForLFunctions.RHTower.EvenSectorBlindMinimumSmallAperturePositivity
import GaloisForLFunctions.RHTower.MarkovClampedFirstCellAndTailVarianceLocalizationPBAP

/-!
# Pole-Free Euler–Maclaurin Conservation, Clamped Quadrature, and the `27`-Ratio Spectral Gap on `EWU`

This module bridges the Even-Sector Weil Universality (`EWU`) single-source purification and
variational framework (`WeilEvenPolarTestFn`, `SmoothEvenPolarTestFn`, `evenBlindMinimum`) with the
`HF` Euler–Maclaurin + Bochner–Poisson resolvent conservation law and the clamped first-cell /
tail-variance bounds from `MarkovClampedFirstCellAndTailVarianceLocalizationPBAP`:

1. **Automatic Support-Cutoff Existence and Pole-Free Conservation on `EWU` (`Section 1`)**:
   Every `f : WeilTestFn` admits an explicit integer support cutoff `N ≥ 1` such that
   `EF.weilTest f.1 f.1 (± log x) = 0` for all `x ≥ N` (`exists_support_cutoff_weilTest`).
   Because every `g : WeilEvenPolarTestFn` is both even (`cosh`-only) and polar-constrained
   (`paperFT g.1.1 (I / 2) = 0`), its real pole term vanishes identically
   (`re_weilPoleTerm_eq_zero_of_evenPolar g`), so the Euler–Maclaurin conservation law holds with
   **zero `sinhHalfMoment` residual**:
   `primeBlindCounterterm unitStepCountertermWeight g.1 + rightCellQuadratureDefect C_{g.1.1} N + bochnerResolventEnergy k_{g.1.1} = 0`
   (`WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero`).
   On the prime-blind subspace `logVector g.1 = 0`,
   `rightCellQuadratureDefect C_{g.1.1} N + bochnerResolventEnergy k_{g.1.1} = 0`
   (`WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero`).

2. **Cutoff-Free `51/2` and `27` Kinetic Spectral Gaps on `EWU` (`Section 2`)**:
   Combining `exists_support_cutoff_weilTest` with the four-stage degree-16 first-cell coercivity
   theorems eliminates all external support-cutoff parameters `N`, yielding unconditional kinetic
   uncertainty gaps on `WeilEvenPolarTestFn`, `SmoothEvenPolarTestFn`, and real primitive-hyperplane
   tests:
   - `(51 / 2) * ∫ ‖g.1.1 u‖² < spectralSecondMoment g.1.1` when `0 ≤ primeBlindCounterterm unitStepCountertermWeight g.1`,
   - `27 * ∫ ‖g.1.1 u‖² < spectralSecondMoment g.1.1` on the nonnegative log-value cone and on the
     prime-blind subspace `logVector g.1 = 0`
     (`WeilEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logVector_eq_zero`,
     `SmoothEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logVector_eq_zero`).

3. **Pole-Free Clamped All-Ratio Conservation and `S(g)`-Free Tail-Cell (`n ≥ 3`) Localization (`Section 3`)**:
   For every prime-blind `g : WeilEvenPolarTestFn`,
   `(1261 / 1440) * ∫ ‖g.1.1 u‖² + bochnerResolventEnergy k_{g.1.1} ≤ min ((7 / 480) * S, (91 / 50) * L) + (71 / 3600) * √(S(S + 2L))`
   (`WeilEvenPolarTestFn.clamped_all_ratio_conservation_bound_of_logVector_eq_zero`) and
   `∑_{n ∈ [3, N]} ∫_{n-1}^n (C_{g.1.1}(x) - cellSecant(C_{g.1.1}, n, x)) / √x dx ≤ (79 / 100) * ∫ ‖g.1.1 u‖² + (31 / 5) * bochnerResolventEnergy k_{g.1.1}`
   (`WeilEvenPolarTestFn.tail_cell_variance_localization_of_logVector_eq_zero`).

4. **Joint Single-Source Mixture Purification with `evenBlindMinimum` and Clamped Conservation (`Section 4`)**:
   Every nonnegative finite mixture `c : WeilTestFn →₀ ℝ` with vanishing arithmetic trace
   (`linearCombination ℝ logVector c = 0`) is realized by a single `f : SmoothEvenPolarTestFn`
   that simultaneously preserves the exact mixture energy `fullMixtureEnergy c`, is bounded below by
   `evenBlindMinimum a * ‖ccmArchimedeanFormToAperture a u‖²`, satisfies the pole-free
   Euler–Maclaurin conservation law, and obeys the clamped all-ratio and `27`-ratio spectral bounds
   (`exists_single_smooth_blind_purification_with_clamped_conservation`).
-/

open Complex MeasureTheory Set Filter Topology Finsupp Zeta23

noncomputable section

namespace RHTower

open WeilOneSided EvenSector

/-! ## Section 1: Automatic Support-Cutoff Existence and Pole-Free Conservation on `EWU` -/

/-- **Automatic Integer Support-Cutoff Existence for `WeilTestFn`**:
every `f : WeilTestFn` admits an integer cutoff `2 ≤ N` such that `EF.weilTest f.1 f.1 (Real.log x) = 0`
and `EF.weilTest f.1 f.1 (-Real.log x) = 0` at `x = N` and for all `x > N`. -/
theorem exists_support_cutoff_weilTest (f : WeilTestFn) :
    ∃ N : ℕ, 2 ≤ N ∧
      (EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0) ∧
      (∀ x : ℝ, (N : ℝ) < x →
        EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) := by
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  obtain ⟨R, hR⟩ := hkc.isCompact.isBounded.subset_closedBall 0
  let B : ℝ := max R 0 + 1
  have hB_pos : 0 < B := by
    dsimp [B]
    have : 0 ≤ max R 0 := le_max_right R 0
    linarith
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (max (Real.exp B) 2)
  have hN2_real : (2 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right (Real.exp B) 2) hN_gt
  have hN2 : 2 ≤ N := by exact_mod_cast hN2_real.le
  have hN_exp : Real.exp B < (N : ℝ) := lt_of_le_of_lt (le_max_left (Real.exp B) 2) hN_gt
  have hvanish : ∀ x : ℝ, (N : ℝ) ≤ x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0 := by
    intro x hx
    have hx_exp : Real.exp B < x := lt_of_lt_of_le hN_exp hx
    have hx_pos : 0 < x := lt_trans (Real.exp_pos B) hx_exp
    have hlog_gt : B < Real.log x := by
      rw [← Real.log_exp B]
      exact Real.log_lt_log (Real.exp_pos B) hx_exp
    have hR_lt : R < Real.log x := by
      have : R < B := by
        dsimp [B]
        have : R ≤ max R 0 := le_max_left R 0
        linarith
      exact lt_trans this hlog_gt
    have hlog_pos : 0 < Real.log x := lt_trans hB_pos hlog_gt
    constructor
    · refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have hball := hR hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos hlog_pos] at hball
      linarith
    · refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have hball := hR hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hlog_pos] at hball
      linarith
  exact ⟨N, hN2, hvanish N le_rfl, fun x hx => hvanish x hx.le⟩

/-- **Exact Pole-Free Right-Endpoint Euler–Maclaurin Conservation Law on `WeilEvenPolarTestFn`**:
for every `g : WeilEvenPolarTestFn` and support cutoff `1 ≤ N`, the pole contribution vanishes
identically (`re_weilPoleTerm_eq_zero_of_evenPolar g`), so
`primeBlindCounterterm unitStepCountertermWeight g.1 + rightCellQuadratureDefect (weilContinuumLogProfile g.1.1) N + bochnerResolventEnergy (EF.weilTest g.1.1 g.1.1) = 0`. -/
theorem WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
    (g : WeilEvenPolarTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest g.1.1 g.1.1 (Real.log x) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight g.1 +
        rightCellQuadratureDefect (weilContinuumLogProfile g.1.1) N +
        bochnerResolventEnergy (EF.weilTest g.1.1 g.1.1) = 0 := by
  rw [unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    g.1 hN1 hN]
  exact re_weilPoleTerm_eq_zero_of_evenPolar g

/-- **Exact Pole-Free Left-Endpoint Euler–Maclaurin Conservation Law on `WeilEvenPolarTestFn`**. -/
theorem WeilEvenPolarTestFn.unitStep_add_leftCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
    (g : WeilEvenPolarTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest g.1.1 g.1.1 (Real.log x) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight g.1 +
        leftCellQuadratureDefect (weilContinuumLogProfile g.1.1) N +
        bochnerResolventEnergy (EF.weilTest g.1.1 g.1.1) = 0 := by
  rw [unitStep_add_leftCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    g.1 hN1 hN]
  exact re_weilPoleTerm_eq_zero_of_evenPolar g

/-- **Exact Pole-Free Trapezoidal Euler–Maclaurin Conservation Law on `WeilEvenPolarTestFn`**. -/
theorem WeilEvenPolarTestFn.unitStep_add_trapezoidalCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
    (g : WeilEvenPolarTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest g.1.1 g.1.1 (Real.log x) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight g.1 +
        trapezoidalCellQuadratureDefect (weilContinuumLogProfile g.1.1) N +
        bochnerResolventEnergy (EF.weilTest g.1.1 g.1.1) = 0 := by
  rw [unitStep_add_trapezoidalCellQuadratureDefect_add_bochnerResolventEnergy_eq_re_weilPoleTerm
    g.1 hN1 hN]
  exact re_weilPoleTerm_eq_zero_of_evenPolar g

/-- **Two-Term Pole-Free Conservation Law on Prime-Blind `WeilEvenPolarTestFn` (`logVector g.1 = 0`)**:
for every prime-blind `g : WeilEvenPolarTestFn`, the right-endpoint Euler–Maclaurin quadrature
defect and the nonnegative Bochner–Poisson resolvent energy sum to zero:
`rightCellQuadratureDefect (weilContinuumLogProfile g.1.1) N + bochnerResolventEnergy (EF.weilTest g.1.1 g.1.1) = 0`. -/
theorem WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero
    (g : WeilEvenPolarTestFn) (hblind : logVector g.1 = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest g.1.1 g.1.1 (Real.log x) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log x) = 0) :
    rightCellQuadratureDefect (weilContinuumLogProfile g.1.1) N +
        bochnerResolventEnergy (EF.weilTest g.1.1 g.1.1) = 0 := by
  have h :=
    WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
      g hN1 hN
  have hunit : primeBlindCounterterm unitStepCountertermWeight g.1 = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  linarith

/-- **Nonpositivity of the Right-Endpoint Quadrature Defect on Prime-Blind `WeilEvenPolarTestFn`**:
because `bochnerResolventEnergy k_{g.1.1} ≥ 0`, every prime-blind `g : WeilEvenPolarTestFn` satisfies
`rightCellQuadratureDefect (weilContinuumLogProfile g.1.1) N ≤ 0`. -/
theorem WeilEvenPolarTestFn.rightCellQuadratureDefect_nonpos_of_logVector_eq_zero
    (g : WeilEvenPolarTestFn) (hblind : logVector g.1 = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest g.1.1 g.1.1 (Real.log x) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log x) = 0) :
    rightCellQuadratureDefect (weilContinuumLogProfile g.1.1) N ≤ 0 := by
  have h :=
    WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero
      g hblind hN1 hN
  have hres := bochnerResolventEnergy_weilTest_nonneg g.1
  linarith

/-! ## Section 2: Unconditional Cutoff-Free `51/2` and `27` Kinetic Spectral Gaps on `EWU` -/

/-- **Cutoff-Free `51 / 2 = 25.5` Kinetic Spectral Gap on `WeilEvenPolarTestFn`**:
for every `g : WeilEvenPolarTestFn` with `0 ≤ primeBlindCounterterm unitStepCountertermWeight g.1`
and `0 < ∫ u, ‖g.1.1 u‖^2`,
`(51 / 2) * ∫ u, ‖g.1.1 u‖^2 < spectralSecondMoment g.1.1` (without any external cutoff parameter `N`). -/
theorem WeilEvenPolarTestFn.fifty_one_halves_l2_lt_spectralSecondMoment_of_unitStep_nonneg
    (g : WeilEvenPolarTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight g.1)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) :
    (51 / 2) * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) < spectralSecondMoment g.1.1 := by
  by_contra! hle
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest g.1
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
      g hN1 hN
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_fifty_one_halves
      g.1 hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  linarith

/-- **Cutoff-Free `27` Kinetic Spectral Gap on `WeilEvenPolarTestFn` with Nonnegative Log-Values**:
for every `g : WeilEvenPolarTestFn` with `∀ n : ℕ, 2 ≤ n → 0 ≤ logValue g.1.1 n` and
`0 < ∫ u, ‖g.1.1 u‖^2`,
`27 * ∫ u, ‖g.1.1 u‖^2 < spectralSecondMoment g.1.1`. -/
theorem WeilEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logValue_nonneg
    (g : WeilEvenPolarTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos : ∀ n : ℕ, 2 ≤ n → 0 ≤ logValue g.1.1 n)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) :
    27 * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) < spectralSecondMoment g.1.1 := by
  by_contra! hle
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest g.1
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
      g hN1 hN
  have hpos_Icc : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue g.1.1 n :=
    fun n hn => hpos n (Finset.mem_Icc.mp hn).1
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_twenty_seven_of_logValue_nonneg
      g.1 hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos_Icc hle
  have hunit_nonneg : 0 ≤ primeBlindCounterterm unitStepCountertermWeight g.1 := by
    rw [primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight g.1
      (fun n hn => hN n (by exact_mod_cast hn))]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_mem := Finset.mem_Icc.mp hn
    unfold unitStepCountertermWeight
    rw [if_pos hn_mem.1]
    exact mul_nonneg zero_le_one (hpos n hn_mem.1)
  linarith

/-- **Cutoff-Free `27` Kinetic Spectral Gap on Prime-Blind `WeilEvenPolarTestFn` (`logVector g.1 = 0`)**:
every prime-blind `g : WeilEvenPolarTestFn` with `0 < ∫ u, ‖g.1.1 u‖^2` satisfies
`27 * ∫ u, ‖g.1.1 u‖^2 < spectralSecondMoment g.1.1` unconditionally. -/
theorem WeilEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logVector_eq_zero
    (g : WeilEvenPolarTestFn) (hblind : logVector g.1 = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) :
    27 * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) < spectralSecondMoment g.1.1 := by
  by_contra! hle
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest g.1
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero
      g hblind hN1 hN
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_twenty_seven_of_logVector_eq_zero
      g.1 hblind hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  linarith

/-- **Cutoff-Free `27` Kinetic Spectral Gap on Prime-Blind `SmoothEvenPolarTestFn`**:
every prime-blind smooth even polar source `f : SmoothEvenPolarTestFn` (`logVector f.1.1 = 0`)
with `0 < ∫ u, ‖f.1.1.1 u‖^2` satisfies `27 * ∫ u, ‖f.1.1.1 u‖^2 < spectralSecondMoment f.1.1.1`. -/
theorem SmoothEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logVector_eq_zero
    (f : SmoothEvenPolarTestFn) (hblind : logVector f.1.1 = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1.1.1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖f.1.1.1 u‖ ^ 2) :
    27 * (∫ u : ℝ, ‖f.1.1.1 u‖ ^ 2) < spectralSecondMoment f.1.1.1 :=
  WeilEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logVector_eq_zero
    f.1 hblind hint2 hpos_l2

/-- **Cutoff-Free `27` Kinetic Spectral Gap on Prime-Blind Real Primitive-Hyperplane Tests**:
every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, `logVector (realWeilTestFn f hf hfc) = 0`,
and `0 < ∫ u, ‖(realWeilTestFn f hf hfc).1 u‖^2` satisfies
`27 * ∫ u, ‖(realWeilTestFn f hf hfc).1 u‖^2 < spectralSecondMoment (realWeilTestFn f hf hfc).1`
without any external cutoff parameter `N`. -/
theorem twenty_seven_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero_unconditional
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    27 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest (realWeilTestFn f hf hfc)
  exact twenty_seven_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero
    hf hfc hcosh hint2 (by omega) hN0 hN hblind hpos_l2

/-! ## Section 3: Pole-Free Clamped All-Ratio Conservation and `S(g)`-Free Tail-Cell (`n ≥ 3`) Localization on `EWU` -/

/-- **Pole-Free Clamped All-Ratio Conservation Bound on `WeilEvenPolarTestFn`**:
for every `g : WeilEvenPolarTestFn` and support cutoff `1 ≤ N`,
`primeBlindCounterterm unitStepCountertermWeight g.1 + (247 / 300) * ∫ ‖g.1.1 u‖² + bochnerResolventEnergy k_{g.1.1} ≤ min ((7 / 480) * S, (91 / 50) * L) + (71 / 3600) * √(S(S + 2L))`. -/
theorem WeilEvenPolarTestFn.clamped_all_ratio_conservation_bound
    (g : WeilEvenPolarTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest g.1.1 g.1.1 (Real.log N) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest g.1.1 g.1.1 (Real.log x) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log x) = 0) :
    primeBlindCounterterm unitStepCountertermWeight g.1 +
        (247 / 300) * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) +
        bochnerResolventEnergy (EF.weilTest g.1.1 g.1.1) ≤
      min ((7 / 480) * spectralSecondMoment g.1.1)
          ((91 / 50) * ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) +
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment g.1.1 *
              (spectralSecondMoment g.1.1 + 2 * ∫ u : ℝ, ‖g.1.1 u‖ ^ 2)) := by
  have hcons :=
    WeilEvenPolarTestFn.unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero
      g hN1 hN
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      g.1 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_clamped_first_cell_sub_seventy_one_geom_le_secantNumeratorCellDefect
      g.1 hint2 N
  linarith

/-- **Sharp `1261 / 1440` Pole-Free Clamped All-Ratio Conservation Bound on Prime-Blind `WeilEvenPolarTestFn`**:
for every prime-blind `g : WeilEvenPolarTestFn` (`logVector g.1 = 0`) and support cutoff `1 ≤ N`,
`(1261 / 1440) * ∫ ‖g.1.1 u‖² + bochnerResolventEnergy k_{g.1.1} ≤ min ((7 / 480) * S, (91 / 50) * L) + (71 / 3600) * √(S(S + 2L))`. -/
theorem WeilEvenPolarTestFn.clamped_all_ratio_conservation_bound_of_logVector_eq_zero
    (g : WeilEvenPolarTestFn) (hblind : logVector g.1 = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT g.1.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest g.1.1 g.1.1 (Real.log N) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest g.1.1 g.1.1 (Real.log x) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log x) = 0) :
    (1261 / 1440) * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) +
        bochnerResolventEnergy (EF.weilTest g.1.1 g.1.1) ≤
      min ((7 / 480) * spectralSecondMoment g.1.1)
          ((91 / 50) * ∫ u : ℝ, ‖g.1.1 u‖ ^ 2) +
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment g.1.1 *
              (spectralSecondMoment g.1.1 + 2 * ∫ u : ℝ, ‖g.1.1 u‖ ^ 2)) := by
  have hcons :=
    WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero
      g hblind hN1 hN
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      g.1 hblind hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_clamped_first_cell_sub_seventy_one_geom_le_secantNumeratorCellDefect
      g.1 hint2 N
  linarith

/-- **`S(g)`-Free Tail-Cell (`n ≥ 3`) Variance Localization on Prime-Blind `WeilEvenPolarTestFn`**:
for every prime-blind `g : WeilEvenPolarTestFn` (`logVector g.1 = 0`) and support cutoff `2 ≤ N`,
the tail-cell secant numerator sum on `n ∈ [3, N]` is bounded above purely by `(79 / 100) * ∫ ‖g.1.1 u‖²`
and `(31 / 5) * bochnerResolventEnergy k_{g.1.1}`, with **zero `spectralSecondMoment` term** and
**zero pole term**:
`∑_{n ∈ [3, N]} ∫_{n-1}^n (C_{g.1.1}(x) - cellSecant(C_{g.1.1}, n, x)) / √x dx ≤ (79 / 100) * ∫ ‖g.1.1 u‖² + (31 / 5) * bochnerResolventEnergy k_{g.1.1}`. -/
theorem WeilEvenPolarTestFn.tail_cell_variance_localization_of_logVector_eq_zero
    (g : WeilEvenPolarTestFn) (hblind : logVector g.1 = 0)
    {N : ℕ} (hN2 : 2 ≤ N)
    (hN0 : EF.weilTest g.1.1 g.1.1 (Real.log N) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest g.1.1 g.1.1 (Real.log x) = 0 ∧ EF.weilTest g.1.1 g.1.1 (-Real.log x) = 0) :
    (∑ n ∈ Finset.Icc 3 N,
        ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (weilSymmetricLogNumerator g.1.1 x -
              cellSecant (weilSymmetricLogNumerator g.1.1) n x) /
            Real.sqrt x) ≤
      (79 / 100) * (∫ u : ℝ, ‖g.1.1 u‖ ^ 2) +
        (31 / 5) * bochnerResolventEnergy (EF.weilTest g.1.1 g.1.1) := by
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero
      g hblind hN1 hN
  have hcomb_zero : primeBlindCounterterm secantCombinedSecularWeight g.1 = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hdecomp :=
    rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
      g.1 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  rw [hcomb_zero, add_zero] at hdecomp
  unfold secantNumeratorCellDefect at hdecomp
  rw [sum_Icc_two_eq_add_sum_Icc_three _ hN2] at hdecomp
  have hfirst := neg_seventy_nine_hundredths_l2_sub_resolvent_le_origin_add_first_cell g.1
  linarith

/-! ## Section 4: Joint Single-Source Mixture Purification with `evenBlindMinimum`, Clamped Conservation, and the `27`-Ratio Spectral Gap -/

/-- **Joint Single-Source Mixture Purification Theorem (`EWU` + Clamped `HF`)**:
for every nonnegative finite mixture `c : WeilTestFn →₀ ℝ` with vanishing arithmetic trace
(`linearCombination ℝ logVector c = 0`), there exist a single smooth compact even pole-free source
`f : SmoothEvenPolarTestFn`, a supporting aperture `a : SuzukiPositiveAperture`, a form vector
`u : CCMArchimedeanFormDomain a`, and an integer support cutoff `2 ≤ N` such that simultaneously:
1. `f` is prime-blind (`logVector f.1.1 = 0`),
2. `f` realizes the exact mixture energy (`weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) = fullMixtureEnergy c`),
3. `fullMixtureEnergy c` is bounded below by the EWU variational minimum
   `evenBlindMinimum a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2`,
4. `f` obeys the exact pole-free Euler–Maclaurin conservation law
   `rightCellQuadratureDefect (weilContinuumLogProfile f.1.1.1) N + bochnerResolventEnergy (EF.weilTest f.1.1.1 f.1.1.1) = 0`,
5. `f` obeys the `S(f)`-free tail-cell (`n ≥ 3`) variance localization bound, and
6. whenever `0 < ∫ x, ‖f.1.1.1 x‖^2` and `Integrable (fun r => ‖paperFT f.1.1.1 r‖^2 * (2 * r^2))`,
   `f` satisfies the `27`-ratio kinetic spectral gap `27 * ∫ x, ‖f.1.1.1 x‖^2 < spectralSecondMoment f.1.1.1`. -/
theorem exists_single_smooth_blind_purification_with_clamped_conservation
    (c : WeilTestFn →₀ ℝ) (hc : ∀ g, 0 ≤ c g)
    (hblind_c : linearCombination ℝ logVector c = 0) :
    ∃ (f : SmoothEvenPolarTestFn) (a : SuzukiPositiveAperture)
      (u : CCMArchimedeanFormDomain a) (N : ℕ),
      2 ≤ N ∧
      logVector f.1.1 = 0 ∧
      weilArchRe (EF.weilTest f.1.1.1 f.1.1.1) = fullMixtureEnergy c ∧
      evenBlindMinimum a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤ fullMixtureEnergy c ∧
      rightCellQuadratureDefect (weilContinuumLogProfile f.1.1.1) N +
        bochnerResolventEnergy (EF.weilTest f.1.1.1 f.1.1.1) = 0 ∧
      (∑ n ∈ Finset.Icc 3 N,
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator f.1.1.1 x -
                cellSecant (weilSymmetricLogNumerator f.1.1.1) n x) /
              Real.sqrt x) ≤
        (79 / 100) * (∫ x : ℝ, ‖f.1.1.1 x‖ ^ 2) +
          (31 / 5) * bochnerResolventEnergy (EF.weilTest f.1.1.1 f.1.1.1) ∧
      (Integrable (fun r : ℝ => ‖paperFT f.1.1.1 r‖ ^ 2 * (2 * r ^ 2)) →
        0 < (∫ x : ℝ, ‖f.1.1.1 x‖ ^ 2) →
        27 * (∫ x : ℝ, ‖f.1.1.1 x‖ ^ 2) < spectralSecondMoment f.1.1.1) := by
  obtain ⟨f, hft, hfe⟩ := exists_single_smooth_exact_moments c hc
  have hf0 : logVector f.1.1 = 0 := hft.trans hblind_c
  obtain ⟨a, u, hmin⟩ := exists_aperture_evenBlindMinimum_mul_le_smooth_blind f hf0
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest f.1.1
  have hN1 : 1 ≤ N := by omega
  refine ⟨f, a, u, N, hN2, hf0, hfe, hmin.trans_eq hfe,
    WeilEvenPolarTestFn.rightCellQuadratureDefect_add_bochnerResolventEnergy_eq_zero_of_logVector_eq_zero
      f.1 hf0 hN1 hN,
    WeilEvenPolarTestFn.tail_cell_variance_localization_of_logVector_eq_zero
      f.1 hf0 hN2 hN0 hN,
    fun hint2 hpos =>
      SmoothEvenPolarTestFn.twenty_seven_l2_lt_spectralSecondMoment_of_logVector_eq_zero
        f hf0 hint2 hpos⟩

end RHTower

end
