import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinEveryBaseThetaMass
import GaloisForLFunctions.RHTower.Sieve.MaynardPolynomialPrimeFreePhysicalDefect

noncomputable section
namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex
open GaloisForLFunctions.HTGeometry

private theorem tendsto_routeT_polynomialLeakage_envelope_zero_general
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

/-- Polynomial target width makes proper-prime-power leakage smaller than any fixed positive
threshold, uniformly over all larger target widths. -/
theorem eventually_routeT_primePowerLeakage_le_of_power_width_const
    {theta epsilon : ℝ} (htheta : 0 < theta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ,
      N ^ theta ≤ H → H ≤ N →
      (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H ≤
        epsilon := by
  have hsmall :=
    (tendsto_routeT_polynomialLeakage_envelope_zero_general htheta).eventually
      (Iio_mem_nhds hepsilon)
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
    _ ≤ epsilon := hsmallN.le

/-- Any positive reference-density fraction survives after paying half of it to prime-power
leakage. -/
theorem norm_normalized_reference_sub_primeFree_target_vonMangoldt_ge_of_fraction
    {N H R rho : ℝ} (hN : 2 ≤ N) (hH : 0 < H) (hR : 0 < R)
    (hrho : 0 < rho)
    (hwidthH : 1 ≤ 2 * H)
    (hprimeFree : Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0)
    (href : routeTSmoothWindowCentralMargin * (rho * R) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n)
    (hleakage :
      (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H ≤
        routeTSmoothWindowCentralMargin * rho / 2) :
    routeTSmoothWindowCentralMargin * rho / 2 ≤
      ‖(R : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) -
        (H : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))‖ := by
  let MR : ℝ := ∑' n : ℕ,
    (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n
  let MH : ℝ := ∑' n : ℕ,
    (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n
  let E : ℝ := (Real.log (N + 2 * H) / Real.log 2) *
    (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H)
  have htarget : MH ≤ E := by
    dsimp only [MH, E]
    exact routeT_primeFree_smooth_vonMangoldt_mass_le_local_primePower
      hN hH hwidthH hprimeFree
  have hrefNorm : routeTSmoothWindowCentralMargin * rho ≤ MR / R := by
    rw [le_div_iff₀ hR]
    simpa only [mul_assoc] using href
  have htargetNorm : MH / H ≤ routeTSmoothWindowCentralMargin * rho / 2 := by
    calc
      MH / H ≤ E / H := div_le_div_of_nonneg_right htarget hH.le
      _ ≤ routeTSmoothWindowCentralMargin * rho / 2 := by
        simpa only [E] using hleakage
  have hgap : routeTSmoothWindowCentralMargin * rho / 2 ≤
      MR / R - MH / H := by
    linarith
  have hcomplexR :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) = (MR : ℂ) := by
    calc
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) =
          ∑' n : ℕ, (((vonMangoldt n : ℝ) *
            routeTSmoothWindowWeight N R n : ℝ) : ℂ) := by
              apply tsum_congr
              intro n
              rw [Complex.ofReal_mul]
      _ = (MR : ℂ) := by
        dsimp only [MR]
        exact (Complex.ofReal_tsum _).symm
  have hcomplexH :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) = (MH : ℂ) := by
    calc
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ)) =
          ∑' n : ℕ, (((vonMangoldt n : ℝ) *
            routeTSmoothWindowWeight N H n : ℝ) : ℂ) := by
              apply tsum_congr
              intro n
              rw [Complex.ofReal_mul]
      _ = (MH : ℂ) := by
        dsimp only [MH]
        exact (Complex.ofReal_tsum _).symm
  rw [hcomplexR, hcomplexH]
  have hcast : (R : ℂ)⁻¹ * (MR : ℂ) - (H : ℂ)⁻¹ * (MH : ℂ) =
      ((MR / R - MH / H : ℝ) : ℂ) := by
    push_cast
    field_simp [hR.ne', hH.ne']
  have hgap0 : 0 ≤ MR / R - MH / H :=
    (div_nonneg (mul_nonneg routeTSmoothWindowCentralMargin_pos.le hrho.le)
      (by norm_num)).trans hgap
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgap0]
  exact hgap

/-- Fractional reference density produces the corresponding pole-annihilating Perron defect. -/
theorem norm_integral_normalizedKernelDefect_ge_of_primeFree_of_fraction
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H R sigma rho : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 2 ≤ N) (hH : 0 < H) (hR : 0 < R) (hrho : 0 < rho)
    (hwidthH : 1 ≤ 2 * H)
    (hsupportH : N + 2 * H ≤ X) (hsupportR : N + 2 * R ≤ X)
    (hsigma : 0 < sigma)
    (hprimeFree : Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0)
    (href : routeTSmoothWindowCentralMargin * (rho * R) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n)
    (hleakage :
      (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H ≤
        routeTSmoothWindowCentralMargin * rho / 2) :
    (2 * Real.pi) * (routeTSmoothWindowCentralMargin * rho / 2) ≤
      ‖∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((sigma : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N H
              ((sigma : ℂ) + (y : ℝ) * Complex.I))‖ := by
  let Z : ℂ :=
    (R : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N R (n : ℝ) : ℝ) : ℂ)) -
      (H : ℂ)⁻¹ * (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        ((routeTSmoothWindowWeight N H (n : ℝ) : ℝ) : ℂ))
  let J : ℂ := ∫ y : ℝ,
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
        ((sigma : ℂ) + (y : ℝ) * Complex.I) *
      (routeTNormalizedSmoothWindowMellin N R
          ((sigma : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * Complex.I))
  have hgap : routeTSmoothWindowCentralMargin * rho / 2 ≤ ‖Z‖ := by
    dsimp only [Z]
    exact norm_normalized_reference_sub_primeFree_target_vonMangoldt_ge_of_fraction
      hN hH hR hrho hwidthH hprimeFree href hleakage
  have hidentity : (2 * Real.pi : ℝ) • Z = J := by
    dsimp only [Z, J]
    exact smul_normalized_reference_sub_target_vonMangoldt_eq_integral_kernelDefect
      L X k hXL hT0 hscale (by linarith) hH hR
        hsupportH hsupportR hsigma
  calc
    (2 * Real.pi) * (routeTSmoothWindowCentralMargin * rho / 2) ≤
        (2 * Real.pi) * ‖Z‖ :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    _ = ‖(2 * Real.pi : ℝ) • Z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    _ = ‖J‖ := congrArg norm hidentity

/-- Endpoint-only multiscale producer with an arbitrary positive reference-density fraction. -/
theorem exists_routeTComparableWidthLadder_defect_of_primeFree_of_fraction
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H R sigma rho : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 2 ≤ N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hrho : 0 < rho)
    (hwidthH : 1 ≤ 2 * H)
    (hsupportH : N + 2 * H ≤ X) (hsupportR : N + 2 * R ≤ X)
    (hsigma : 0 < sigma)
    (hprimeFree : Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0)
    (href : routeTSmoothWindowCentralMargin * (rho * R) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n)
    (hleakage :
      (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H ≤
        routeTSmoothWindowCentralMargin * rho / 2) :
    ∃ J : ℕ, 0 < J ∧
      (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ R / H ∧
      R / H < (((2 ^ J : ℕ) : ℝ)) ∧
      ∃ j ∈ Finset.range J,
        routeTComparableWidthLadder H R (j + 1) ≤
            routeTComparableWidthLadder H R j ∧
        routeTComparableWidthLadder H R j ≤
            2 * routeTComparableWidthLadder H R (j + 1) ∧
        routeTNormalizedSmoothWindowMellin N
              (routeTComparableWidthLadder H R j) 1 -
            routeTNormalizedSmoothWindowMellin N
              (routeTComparableWidthLadder H R (j + 1)) 1 = 0 ∧
        N / routeTComparableWidthLadder H R (j + 1) ≤
            4 * (N / (2 * routeTComparableWidthLadder H R j)) ∧
        ((2 * Real.pi) * (routeTSmoothWindowCentralMargin * rho / 2)) /
            (J : ℝ) ≤
          ‖∫ y : ℝ,
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
                ((sigma : ℂ) + (y : ℝ) * Complex.I) *
              (routeTNormalizedSmoothWindowMellin N
                    (routeTComparableWidthLadder H R j)
                    ((sigma : ℂ) + (y : ℝ) * Complex.I) -
                routeTNormalizedSmoothWindowMellin N
                    (routeTComparableWidthLadder H R (j + 1))
                    ((sigma : ℂ) + (y : ℝ) * Complex.I))‖ := by
  obtain ⟨J, hJ, hbelow, habove, hW0, hWJ⟩ :=
    exists_routeTComparableWidthLadder_endpoint hH hHR
  let W := routeTComparableWidthLadder H R
  have hW : ∀ j, j ≤ J → 0 < W j := by
    intro j _hj
    exact routeTComparableWidthLadder_pos hH j
  have hwide := norm_integral_normalizedKernelDefect_ge_of_primeFree_of_fraction
    L X k hXL hT0 hscale hN hH hR hrho hwidthH hsupportH hsupportR hsigma
      hprimeFree href hleakage
  have hlarge :
      (2 * Real.pi) * (routeTSmoothWindowCentralMargin * rho / 2) ≤
        ‖∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin N (W 0)
                ((sigma : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin N (W J)
                ((sigma : ℂ) + (y : ℝ) * Complex.I))‖ := by
    dsimp only [W]
    rw [hW0, hWJ]
    exact hwide
  obtain ⟨j, hj, hlargej⟩ :=
    routeT_multiscale_kernelDefect_norm_pigeonhole
      L X k T0 t (by linarith) hsigma W hJ hW hlarge
  have hadj := routeTComparableWidthLadder_adjacent hH hR j
  have hNpos : 0 < N := by linarith
  have hNnonneg : 0 ≤ N := hNpos.le
  have hpole := normalized_reference_sub_target_PerronKernel_one
    (H := routeTComparableWidthLadder H R (j + 1))
    (R := routeTComparableWidthLadder H R j)
    hNpos (routeTComparableWidthLadder_pos (R := R) hH (j + 1))
      (routeTComparableWidthLadder_pos (R := R) hH j)
  have htransition := routeT_adjacentWidth_transition_ratio_le_four
    (H := routeTComparableWidthLadder H R (j + 1))
    (R := routeTComparableWidthLadder H R j)
    hNnonneg (routeTComparableWidthLadder_pos (R := R) hH (j + 1))
      hadj.1 hadj.2
  exact ⟨J, hJ, hbelow, habove, j, hj, hadj.1, hadj.2,
    hpole, htransition, hlargej⟩

/-- At every sufficiently large real base, a polynomial-width prime-free target below the exact
Route-T handoff width forces a phase-valid literal adjacent physical-slice defect. -/
theorem exists_eventually_routeT_handoff_primeFree_physicalSlice_defect
    {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ N : ℝ in atTop,
      ∀ (L X k : ℕ) {T0 t H : ℝ},
        X < (L + 1) ^ k →
        1 < T0 →
        ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N →
        N ^ theta ≤ H →
        H ≤ N ^ routeTPhysicalSliceHandoffTheta →
        N + 2 * N ^ routeTPhysicalSliceHandoffTheta ≤ X →
        Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0 →
        ∃ J : ℕ, 0 < J ∧
          (((2 ^ (J - 1) : ℕ) : ℝ)) ≤
            N ^ routeTPhysicalSliceHandoffTheta / H ∧
          N ^ routeTPhysicalSliceHandoffTheta / H <
            (((2 ^ J : ℕ) : ℝ)) ∧
          ∃ j ∈ Finset.range J,
            H ≤ routeTComparableWidthLadder H
                (N ^ routeTPhysicalSliceHandoffTheta) (j + 1) ∧
            routeTComparableWidthLadder H
                (N ^ routeTPhysicalSliceHandoffTheta) j ≤
              N ^ routeTPhysicalSliceHandoffTheta ∧
            routeTComparableWidthLadder H
                  (N ^ routeTPhysicalSliceHandoffTheta) (j + 1) ≤
                routeTComparableWidthLadder H
                  (N ^ routeTPhysicalSliceHandoffTheta) j ∧
            routeTComparableWidthLadder H
                  (N ^ routeTPhysicalSliceHandoffTheta) j ≤
                2 * routeTComparableWidthLadder H
                  (N ^ routeTPhysicalSliceHandoffTheta) (j + 1) ∧
            routeTNormalizedSmoothWindowMellin N
                  (routeTComparableWidthLadder H
                    (N ^ routeTPhysicalSliceHandoffTheta) j) 1 -
                routeTNormalizedSmoothWindowMellin N
                  (routeTComparableWidthLadder H
                    (N ^ routeTPhysicalSliceHandoffTheta) (j + 1)) 1 = 0 ∧
            N / routeTComparableWidthLadder H
                  (N ^ routeTPhysicalSliceHandoffTheta) (j + 1) ≤
                4 * (N / (2 * routeTComparableWidthLadder H
                  (N ^ routeTPhysicalSliceHandoffTheta) j)) ∧
            ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 32768)) /
                (J : ℝ) ≤
              ‖∫ y : ℝ,
                dirPoly ⌊N + 2 * routeTComparableWidthLadder H
                      (N ^ routeTPhysicalSliceHandoffTheta) j⌋₊
                    (routeTVonMangoldtSliceCoeff ⌊N⌋₊
                      ⌊N + 2 * routeTComparableWidthLadder H
                        (N ^ routeTPhysicalSliceHandoffTheta) j⌋₊) (-y) *
                  (routeTNormalizedSmoothWindowMellin N
                        (routeTComparableWidthLadder H
                          (N ^ routeTPhysicalSliceHandoffTheta) j)
                        ((1 : ℂ) + (y : ℝ) * Complex.I) -
                    routeTNormalizedSmoothWindowMellin N
                        (routeTComparableWidthLadder H
                          (N ^ routeTPhysicalSliceHandoffTheta) (j + 1))
                        ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
  have hepsilon : 0 < routeTSmoothWindowCentralMargin * (1 / 16384 : ℝ) / 2 := by
    positivity [routeTSmoothWindowCentralMargin_pos]
  filter_upwards
      [eventually_routeT_primePowerLeakage_le_of_power_width_const htheta hepsilon,
        eventually_routeT_handoff_reference_smooth_vonMangoldt_mass_lower,
        eventually_ge_atTop (2 : ℝ)] with N hleakage href hN
  intro L X k T0 t H hXL hT0 hscale hpower hHR hsupportR hprimeFree
  let R : ℝ := N ^ routeTPhysicalSliceHandoffTheta
  let rho : ℝ := 1 / 16384
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hRpos : 0 < R := by dsimp only [R]; positivity
  have hrho : 0 < rho := by dsimp only [rho]; norm_num
  have hthetaHandoff1 : routeTPhysicalSliceHandoffTheta ≤ 1 :=
    (routeTPhysicalSliceHandoffTheta_lt_three_fourths.trans (by norm_num)).le
  have hRN : R ≤ N := by
    dsimp only [R]
    have hpow := Real.rpow_le_rpow_of_exponent_le hN1 hthetaHandoff1
    simpa only [Real.rpow_one] using hpow
  have hHN : H ≤ N := hHR.trans hRN
  have hH1 : 1 ≤ H := by
    exact (Real.one_le_rpow hN1 htheta.le).trans hpower
  have hH : 0 < H := by linarith
  have hwidthH : 1 ≤ 2 * H := by linarith
  have hsupportH : N + 2 * H ≤ X := by
    linarith
  have hleak := hleakage H hpower hHN
  have href' : routeTSmoothWindowCentralMargin * (rho * R) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n := by
    calc
      routeTSmoothWindowCentralMargin * (rho * R) =
          routeTSmoothWindowCentralMargin *
            (N ^ routeTPhysicalSliceHandoffTheta / 16384) := by
              dsimp only [rho, R]
              ring
      _ ≤ ∑' n : ℕ, (vonMangoldt n : ℝ) *
          routeTSmoothWindowWeight N R n := by
            simpa only [R] using href.le
  obtain ⟨J, hJ, hbelow, habove, j, hj, hadj, hcomp, hpole,
      htransition, hlarge⟩ :=
    exists_routeTComparableWidthLadder_defect_of_primeFree_of_fraction
      L X k hXL hT0 hscale hN hH hRpos (by simpa only [R] using hHR) hrho
        hwidthH hsupportH (by simpa only [R] using hsupportR)
        (by norm_num : (0 : ℝ) < 1) hprimeFree href'
        (by simpa only [rho] using hleak)
  have hselectedLower : H ≤ routeTComparableWidthLadder H R (j + 1) :=
    le_max_left _ _
  have hselectedUpper : routeTComparableWidthLadder H R j ≤ R := by
    rw [routeTComparableWidthLadder, max_le_iff]
    constructor
    · simpa only [R] using hHR
    · have hpow : (1 : ℝ) ≤ (((2 ^ j : ℕ) : ℝ)) := by
        exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
      have hpowpos : (0 : ℝ) < (((2 ^ j : ℕ) : ℝ)) := by positivity
      exact (div_le_iff₀ hpowpos).2 (by nlinarith)
  have hsupportSelected :
      N + 2 * routeTComparableWidthLadder H R j ≤ X := by
    dsimp only [R] at hsupportR ⊢
    linarith
  have hselectedInner : 0 < routeTComparableWidthLadder H R (j + 1) :=
    routeTComparableWidthLadder_pos hH (j + 1)
  have hselectedOuter : 0 < routeTComparableWidthLadder H R j :=
    routeTComparableWidthLadder_pos hH j
  have hbridge :=
    integral_windowRelevant_mul_adjacentNormalizedMellin_eq_physicalSlice
      L X k hXL hT0 hscale hNpos hselectedInner hselectedOuter hadj
        hsupportSelected
  refine ⟨J, hJ, ?_, ?_, j, hj, ?_, ?_, hadj, hcomp, hpole,
    htransition, ?_⟩
  · simpa only [R] using hbelow
  · simpa only [R] using habove
  · simpa only [R] using hselectedLower
  · simpa only [R] using hselectedUpper
  · rw [← hbridge]
    have hconstant :
        (2 * Real.pi) * (routeTSmoothWindowCentralMargin * rho / 2) =
          (2 * Real.pi) * (routeTSmoothWindowCentralMargin / 32768) := by
      dsimp only [rho]
      ring
    rw [hconstant] at hlarge
    simpa only [R, Complex.ofReal_one] using hlarge

end RHTower.Sieve
