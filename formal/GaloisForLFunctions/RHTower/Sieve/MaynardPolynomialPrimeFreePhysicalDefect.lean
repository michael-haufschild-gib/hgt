import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceLocalization
import GaloisForLFunctions.RHTower.Sieve.MaynardMultiscaleReferenceTelescope
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLimitTool
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinHoheiselPrimeSupply
import GaloisForLFunctions.HTGeometry.WindowRpowIntegral

noncomputable section
namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex
open GaloisForLFunctions.HTGeometry

private theorem tendsto_routeT_polynomialLeakage_envelope_zero
    {theta : ℝ} (htheta : 0 < theta) :
    Tendsto (fun N : ℝ =>
      ((Real.sqrt 2 + 1) / Real.log 2) *
        (Real.log 3 + Real.log N) ^ 2 / N ^ (theta / 2))
      atTop (nhds 0) := by
  have ha : 0 < theta / 2 := by linarith
  have h0 := HTGeometry.tendsto_logPow_div_rpow ha 0
  have h1 := HTGeometry.tendsto_logPow_div_rpow ha 1
  have h2 := HTGeometry.tendsto_logPow_div_rpow ha 2
  have hsum :=
    ((h0.const_mul (Real.log 3 ^ 2)).add
      (h1.const_mul (2 * Real.log 3))).add h2
  have hscaled := hsum.const_mul ((Real.sqrt 2 + 1) / Real.log 2)
  simpa only [pow_zero, pow_one, mul_one, mul_zero, add_zero] using
    hscaled.congr' (Filter.Eventually.of_forall fun N => by ring)

/-- Polynomial target width makes proper-prime-power leakage uniformly negligible. -/
theorem eventually_routeT_primePowerLeakage_le_of_power_width
    {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ,
      N ^ theta ≤ H → H ≤ N →
      (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H ≤
        routeTSmoothWindowCentralMargin / 4 := by
  have hmargin : 0 < routeTSmoothWindowCentralMargin / 4 := by
    positivity [routeTSmoothWindowCentralMargin_pos]
  have hsmall :=
    (tendsto_routeT_polynomialLeakage_envelope_zero htheta).eventually
      (Iio_mem_nhds hmargin)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with N hsmallN hN
  intro H hpower hHN
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have htheta0 : 0 ≤ theta := htheta.le
  have hH1 : 1 ≤ H := by
    exact (Real.one_le_rpow hN htheta0).trans hpower
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hsum1 : 1 ≤ N + 2 * H := by linarith
  have hsumle : N + 2 * H ≤ 3 * N := by linarith
  have hlogle : Real.log (N + 2 * H) ≤ Real.log (3 * N) :=
    Real.log_le_log (by linarith) hsumle
  have hlog3N : Real.log (3 * N) = Real.log 3 + Real.log N := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hN0.ne']
  have hlog0 : 0 ≤ Real.log (N + 2 * H) := Real.log_nonneg hsum1
  have hlog3N0 : 0 ≤ Real.log 3 + Real.log N := by
    rw [← hlog3N]
    exact Real.log_nonneg (by nlinarith)
  have hsqrtTwoH : Real.sqrt (2 * H) = Real.sqrt 2 * Real.sqrt H := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtH1 : 1 ≤ Real.sqrt H := (Real.one_le_sqrt).2 hH1
  have hratio : (Real.sqrt (2 * H) + 1) / H ≤
      (Real.sqrt 2 + 1) / Real.sqrt H := by
    rw [hsqrtTwoH]
    have hsqrtH0 : 0 < Real.sqrt H := Real.sqrt_pos.2 hH0
    rw [div_le_div_iff₀ hH0 hsqrtH0]
    nlinarith [Real.sq_sqrt hH0.le, Real.sqrt_nonneg 2]
  have hsqrtPower : Real.sqrt (N ^ theta) = N ^ (theta / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hsqrtLower : N ^ (theta / 2) ≤ Real.sqrt H := by
    rw [← hsqrtPower]
    exact Real.sqrt_le_sqrt hpower
  have hlogSq : Real.log (N + 2 * H) ^ 2 ≤
      (Real.log 3 + Real.log N) ^ 2 := by
    rw [← hlog3N]
    nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowPos : 0 < N ^ (theta / 2) := Real.rpow_pos_of_pos hN0 _
  calc
    (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H =
        (Real.log (N + 2 * H) ^ 2 / Real.log 2) *
          ((Real.sqrt (2 * H) + 1) / H) := by ring
    _ ≤ ((Real.log 3 + Real.log N) ^ 2 / Real.log 2) *
          ((Real.sqrt 2 + 1) / Real.sqrt H) := by
      gcongr
    _ ≤ ((Real.log 3 + Real.log N) ^ 2 / Real.log 2) *
          ((Real.sqrt 2 + 1) / N ^ (theta / 2)) := by
      gcongr
    _ = ((Real.sqrt 2 + 1) / Real.log 2) *
          (Real.log 3 + Real.log N) ^ 2 / N ^ (theta / 2) := by ring
    _ ≤ routeTSmoothWindowCentralMargin / 4 := hsmallN.le

/-- A fixed quarter-scale reference is eventually PNT-calibrated. -/
theorem eventually_routeT_quarter_reference_smooth_vonMangoldt_mass_lower :
    ∀ᶠ N : ℝ in atTop,
      routeTSmoothWindowCentralMargin * ((N / 4) / 2) ≤
        ∑' n : ℕ, (vonMangoldt n : ℝ) *
          routeTSmoothWindowWeight N (N / 4) n := by
  obtain ⟨c, K, N0, hc, hK, hN0, href⟩ :=
    exists_routeT_reference_smooth_vonMangoldt_mass_lower
  have hgain : Tendsto
      (fun N : ℝ => c * Real.log N ^ ((1 : ℝ) / 10)) atTop atTop :=
    tendsto_logRoot.const_mul_atTop hc
  have hdecay : Tendsto (fun N : ℝ =>
      Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10)))) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hgain
  have hdecayK : Tendsto (fun N : ℝ =>
      K * Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10)))) atTop (nhds 0) := by
    simpa using hdecay.const_mul K
  have hsmall : ∀ᶠ N : ℝ in atTop,
      K * Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10))) < 1 / 4 :=
    hdecayK.eventually
      (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / 4))
  filter_upwards [hsmall, eventually_ge_atTop N0] with N hsmallN hNN0
  have hN3 : 3 ≤ N := hN0.trans hNN0
  have hNpos : 0 < N := by linarith
  have hwidth : K * N *
      Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10))) ≤ N / 4 := by
    calc
      K * N * Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10))) =
          N * (K * Real.exp (-(c * Real.log N ^ ((1 : ℝ) / 10)))) := by ring
      _ ≤ N * (1 / 4) := mul_le_mul_of_nonneg_left hsmallN.le hNpos.le
      _ = N / 4 := by ring
  exact href N (N / 4) hNN0 (by positivity) (by linarith) hwidth

/-- The quantitative Ingham detector supplies a phase-valid reference window for the Maynard
signed-defect producer. -/
theorem eventually_inghamRouteTBuffered_reference_smooth_vonMangoldt_mass_lower :
    ∀ᶠ X : ℕ in atTop,
      routeTSmoothWindowCentralMargin *
          (inghamRouteTMellinBufferedPhysicalWidth X / 2) ≤
        ∑' n : ℕ, (vonMangoldt n : ℝ) *
          routeTSmoothWindowWeight (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X) n := by
  have hmassRe := (Complex.continuous_re.tendsto (1 : ℂ)).comp
    tendsto_inghamRouteTBufferedNormalizedVonMangoldtMass_one
  simp only [Complex.one_re] at hmassRe
  have hmassLower := Filter.Tendsto.eventually_lt
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)))
    hmassRe (by norm_num : (1 / 2 : ℝ) < 1)
  have hmarginOne : routeTSmoothWindowCentralMargin ≤ 1 := by
    rw [routeTSmoothWindowCentralMargin]
    exact (min_le_right _ _).trans (by
      linarith [Real.smoothTransition.pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)])
  filter_upwards [hmassLower, eventually_ge_atTop (1 : ℕ)] with X hmass hX
  have hR : 0 < inghamRouteTMellinBufferedPhysicalWidth X :=
    inghamRouteTMellinBufferedPhysicalWidth_pos hX
  have hmassEq := inghamRouteTBufferedNormalizedVonMangoldtMass_re_eq X
  simp only [Function.comp_apply] at hmass
  rw [hmassEq] at hmass
  rw [inv_mul_eq_div] at hmass
  have hnorm : routeTSmoothWindowCentralMargin / 2 ≤
      (∑' n : ℕ, (vonMangoldt n : ℝ) *
        routeTSmoothWindowWeight (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) n) /
        inghamRouteTMellinBufferedPhysicalWidth X := by
    linarith
  have hmul := (le_div_iff₀ hR).mp hnorm
  rw [show routeTSmoothWindowCentralMargin *
      (inghamRouteTMellinBufferedPhysicalWidth X / 2) =
        routeTSmoothWindowCentralMargin / 2 *
          inghamRouteTMellinBufferedPhysicalWidth X by ring]
  exact hmul

/-- At every late quantitative detector center, a polynomial-width prime-free target below the
buffered physical reference forces a literal adjacent physical-slice defect.  The selected widths
remain between the target and the detector reference, so no near-linear PNT scale is introduced. -/
theorem exists_eventually_inghamRouteTBuffered_primeFree_physicalSlice_defect
    {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ Q : ℕ in atTop,
      ∀ (L X k : ℕ) {T0 t H : ℝ},
        X < (L + 1) ^ k →
        1 < T0 →
        ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤
          inghamRouteTMellinPhysicalCenter Q →
        inghamRouteTMellinPhysicalCenter Q ^ theta ≤ H →
        H ≤ inghamRouteTMellinBufferedPhysicalWidth Q →
        inghamRouteTMellinPhysicalCenter Q +
            2 * inghamRouteTMellinBufferedPhysicalWidth Q ≤ X →
        Chebyshev.theta (inghamRouteTMellinPhysicalCenter Q + 2 * H) -
            Chebyshev.theta (inghamRouteTMellinPhysicalCenter Q) = 0 →
        ∃ J : ℕ, 0 < J ∧
          (((2 ^ (J - 1) : ℕ) : ℝ)) ≤
            inghamRouteTMellinBufferedPhysicalWidth Q / H ∧
          inghamRouteTMellinBufferedPhysicalWidth Q / H <
            (((2 ^ J : ℕ) : ℝ)) ∧
          ∃ j ∈ Finset.range J,
            H ≤ routeTComparableWidthLadder H
                (inghamRouteTMellinBufferedPhysicalWidth Q) (j + 1) ∧
            routeTComparableWidthLadder H
                (inghamRouteTMellinBufferedPhysicalWidth Q) j ≤
              inghamRouteTMellinBufferedPhysicalWidth Q ∧
            routeTComparableWidthLadder H
                  (inghamRouteTMellinBufferedPhysicalWidth Q) (j + 1) ≤
                routeTComparableWidthLadder H
                  (inghamRouteTMellinBufferedPhysicalWidth Q) j ∧
            routeTComparableWidthLadder H
                  (inghamRouteTMellinBufferedPhysicalWidth Q) j ≤
                2 * routeTComparableWidthLadder H
                  (inghamRouteTMellinBufferedPhysicalWidth Q) (j + 1) ∧
            routeTNormalizedSmoothWindowMellin
                  (inghamRouteTMellinPhysicalCenter Q)
                  (routeTComparableWidthLadder H
                    (inghamRouteTMellinBufferedPhysicalWidth Q) j) 1 -
                routeTNormalizedSmoothWindowMellin
                  (inghamRouteTMellinPhysicalCenter Q)
                  (routeTComparableWidthLadder H
                    (inghamRouteTMellinBufferedPhysicalWidth Q) (j + 1)) 1 = 0 ∧
            inghamRouteTMellinPhysicalCenter Q /
                  routeTComparableWidthLadder H
                    (inghamRouteTMellinBufferedPhysicalWidth Q) (j + 1) ≤
                4 * (inghamRouteTMellinPhysicalCenter Q /
                  (2 * routeTComparableWidthLadder H
                    (inghamRouteTMellinBufferedPhysicalWidth Q) j)) ∧
            ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (J : ℝ) ≤
              ‖∫ y : ℝ,
                dirPoly ⌊inghamRouteTMellinPhysicalCenter Q +
                    2 * routeTComparableWidthLadder H
                      (inghamRouteTMellinBufferedPhysicalWidth Q) j⌋₊
                  (routeTVonMangoldtSliceCoeff
                    ⌊inghamRouteTMellinPhysicalCenter Q⌋₊
                    ⌊inghamRouteTMellinPhysicalCenter Q +
                      2 * routeTComparableWidthLadder H
                        (inghamRouteTMellinBufferedPhysicalWidth Q) j⌋₊) (-y) *
                  (routeTNormalizedSmoothWindowMellin
                      (inghamRouteTMellinPhysicalCenter Q)
                      (routeTComparableWidthLadder H
                        (inghamRouteTMellinBufferedPhysicalWidth Q) j)
                      ((1 : ℂ) + (y : ℝ) * Complex.I) -
                    routeTNormalizedSmoothWindowMellin
                      (inghamRouteTMellinPhysicalCenter Q)
                      (routeTComparableWidthLadder H
                        (inghamRouteTMellinBufferedPhysicalWidth Q) (j + 1))
                      ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
  have hcenter : Tendsto inghamRouteTMellinPhysicalCenter atTop atTop := by
    change Tendsto
      ((fun x : ℝ => x ^ inghamRouteTPhysicalScaleExponent) ∘
        (fun Q : ℕ => (Q : ℝ))) atTop atTop
    exact (tendsto_rpow_atTop inghamRouteTPhysicalScaleExponent_pos).comp
      tendsto_natCast_atTop_atTop
  have hleakage := hcenter.eventually
    (eventually_routeT_primePowerLeakage_le_of_power_width htheta)
  have hN2 := hcenter.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hleakage,
    eventually_inghamRouteTBuffered_reference_smooth_vonMangoldt_mass_lower,
    hN2, eventually_ge_atTop (1 : ℕ)] with Q hleakageQ href hN hQ
  intro L X k T0 t H hXL hT0 hscale hpower hHR hsupportR hprimeFree
  have hNpos : 0 < inghamRouteTMellinPhysicalCenter Q := by linarith
  have hN1 : 1 ≤ inghamRouteTMellinPhysicalCenter Q := by linarith
  have hRpos : 0 < inghamRouteTMellinBufferedPhysicalWidth Q :=
    inghamRouteTMellinBufferedPhysicalWidth_pos hQ
  have hRN : inghamRouteTMellinBufferedPhysicalWidth Q ≤
      inghamRouteTMellinPhysicalCenter Q :=
    inghamRouteTMellinBufferedPhysicalWidth_le_center hQ
  have hHN : H ≤ inghamRouteTMellinPhysicalCenter Q := hHR.trans hRN
  have hH1 : 1 ≤ H := by
    exact (Real.one_le_rpow hN1 htheta.le).trans hpower
  have hH : 0 < H := by linarith
  have hwidthH : 1 ≤ 2 * H := by linarith
  have hsupportH : inghamRouteTMellinPhysicalCenter Q + 2 * H ≤ X := by
    linarith
  have hleak := hleakageQ H hpower hHN
  obtain ⟨J, hJ, hbelow, habove, j, hj, hadj, hcomp, hpole,
      htransition, hlarge⟩ :=
    exists_routeTComparableWidthLadder_defect_of_primeFree
      L X k hXL hT0 hscale hN hH hRpos hHR hwidthH hsupportH hsupportR
        (by norm_num : (0 : ℝ) < 1) hprimeFree href hleak
  have hselectedLower : H ≤ routeTComparableWidthLadder H
      (inghamRouteTMellinBufferedPhysicalWidth Q) (j + 1) :=
    le_max_left _ _
  have hselectedUpper : routeTComparableWidthLadder H
      (inghamRouteTMellinBufferedPhysicalWidth Q) j ≤
        inghamRouteTMellinBufferedPhysicalWidth Q := by
    rw [routeTComparableWidthLadder, max_le_iff]
    constructor
    · exact hHR
    · have hpow : (1 : ℝ) ≤ (((2 ^ j : ℕ) : ℝ)) := by
        exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
      have hpowpos : (0 : ℝ) < (((2 ^ j : ℕ) : ℝ)) := by positivity
      exact (div_le_iff₀ hpowpos).2 (by nlinarith)
  have hsupportSelected : inghamRouteTMellinPhysicalCenter Q +
      2 * routeTComparableWidthLadder H
        (inghamRouteTMellinBufferedPhysicalWidth Q) j ≤ X := by
    linarith
  have hselectedInner : 0 < routeTComparableWidthLadder H
      (inghamRouteTMellinBufferedPhysicalWidth Q) (j + 1) :=
    routeTComparableWidthLadder_pos hH (j + 1)
  have hselectedOuter : 0 < routeTComparableWidthLadder H
      (inghamRouteTMellinBufferedPhysicalWidth Q) j :=
    routeTComparableWidthLadder_pos hH j
  have hbridge :=
    integral_windowRelevant_mul_adjacentNormalizedMellin_eq_physicalSlice
      L X k hXL hT0 hscale hNpos hselectedInner hselectedOuter hadj
        hsupportSelected
  refine ⟨J, hJ, hbelow, habove, j, hj, hselectedLower, hselectedUpper,
    hadj, hcomp, hpole, htransition, ?_⟩
  rw [← hbridge]
  simpa using hlarge

/-- Polynomial-width prime-free target windows unconditionally produce a literal physical-slice
signed defect on one adjacent rung of the canonical dyadic ladder. -/
theorem exists_eventually_routeT_polynomial_primeFree_physicalSlice_defect
    {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ N : ℝ in atTop,
      ∀ (L X k : ℕ) {T0 t H : ℝ},
        X < (L + 1) ^ k →
        1 < T0 →
        ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N →
        N ^ theta ≤ H →
        H ≤ N / 4 →
        N + 2 * (N / 4) ≤ X →
        Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0 →
        ∃ J : ℕ, 0 < J ∧
          (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ (N / 4) / H ∧
          (N / 4) / H < (((2 ^ J : ℕ) : ℝ)) ∧
          ∃ j ∈ Finset.range J,
            routeTComparableWidthLadder H (N / 4) (j + 1) ≤
                routeTComparableWidthLadder H (N / 4) j ∧
            routeTComparableWidthLadder H (N / 4) j ≤
                2 * routeTComparableWidthLadder H (N / 4) (j + 1) ∧
            routeTNormalizedSmoothWindowMellin N
                  (routeTComparableWidthLadder H (N / 4) j) 1 -
                routeTNormalizedSmoothWindowMellin N
                  (routeTComparableWidthLadder H (N / 4) (j + 1)) 1 = 0 ∧
            N / routeTComparableWidthLadder H (N / 4) (j + 1) ≤
                4 * (N / (2 * routeTComparableWidthLadder H (N / 4) j)) ∧
            ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (J : ℝ) ≤
              ‖∫ y : ℝ,
                dirPoly ⌊N + 2 * routeTComparableWidthLadder H (N / 4) j⌋₊
                    (routeTVonMangoldtSliceCoeff ⌊N⌋₊
                      ⌊N + 2 * routeTComparableWidthLadder H (N / 4) j⌋₊) (-y) *
                  (routeTNormalizedSmoothWindowMellin N
                        (routeTComparableWidthLadder H (N / 4) j)
                        ((1 : ℂ) + (y : ℝ) * Complex.I) -
                    routeTNormalizedSmoothWindowMellin N
                        (routeTComparableWidthLadder H (N / 4) (j + 1))
                        ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
  filter_upwards [eventually_routeT_primePowerLeakage_le_of_power_width htheta,
    eventually_routeT_quarter_reference_smooth_vonMangoldt_mass_lower,
    eventually_ge_atTop (2 : ℝ)] with N hleakage href hN
  intro L X k T0 t H hXL hT0 hscale hpower hHR hsupportR hprimeFree
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hH1 : 1 ≤ H := by
    exact (Real.one_le_rpow hN1 htheta.le).trans hpower
  have hH : 0 < H := by linarith
  have hR : 0 < N / 4 := by positivity
  have hHN : H ≤ N := by linarith
  have hwidthH : 1 ≤ 2 * H := by linarith
  have hsupportH : N + 2 * H ≤ X := by linarith
  have hleak := hleakage H hpower hHN
  obtain ⟨J, hJ, hbelow, habove, j, hj, hadj, hcomp, hpole,
      htransition, hlarge⟩ :=
    exists_routeTComparableWidthLadder_defect_of_primeFree
      L X k hXL hT0 hscale hN hH hR hHR hwidthH hsupportH hsupportR
        (by norm_num : (0 : ℝ) < 1) hprimeFree href hleak
  have hselectedUpper :
      routeTComparableWidthLadder H (N / 4) j ≤ N / 4 := by
    rw [routeTComparableWidthLadder, max_le_iff]
    constructor
    · exact hHR
    · have hpow : (1 : ℝ) ≤ (((2 ^ j : ℕ) : ℝ)) := by
        exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
      have hpowpos : (0 : ℝ) < (((2 ^ j : ℕ) : ℝ)) := by positivity
      exact (div_le_iff₀ hpowpos).2 (by nlinarith)
  have hsupportSelected :
      N + 2 * routeTComparableWidthLadder H (N / 4) j ≤ X := by
    linarith
  have hselectedInner :
      0 < routeTComparableWidthLadder H (N / 4) (j + 1) :=
    routeTComparableWidthLadder_pos hH (j + 1)
  have hselectedOuter :
      0 < routeTComparableWidthLadder H (N / 4) j :=
    routeTComparableWidthLadder_pos hH j
  have hbridge :=
    integral_windowRelevant_mul_adjacentNormalizedMellin_eq_physicalSlice
      L X k hXL hT0 hscale hNpos hselectedInner hselectedOuter hadj hsupportSelected
  refine ⟨J, hJ, hbelow, habove, j, hj, hadj, hcomp, hpole,
    htransition, ?_⟩
  rw [← hbridge]
  simpa using hlarge

end RHTower.Sieve
