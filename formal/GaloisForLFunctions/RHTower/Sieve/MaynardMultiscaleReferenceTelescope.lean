import GaloisForLFunctions.RHTower.Sieve.MaynardNormalizedReferenceTargetPerron

/-!
# Multiscale pole-annihilating reference telescope

A single PNT-scale reference and a much narrower prime-gap target have incompatible Mellin
bandwidths.  This module replaces that two-scale comparison by an arbitrary finite ladder of
positive widths.  The wide-to-target signed Perron defect telescopes exactly through adjacent
widths, so a large total defect forces one adjacent defect of size at least the average.  Every
adjacent step still annihilates the zeta pole, while comparable consecutive widths leave only a
constant-factor transition between their common low band and target decay scale.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter

/-- Exact finite telescope in a complex normed space. -/
theorem complex_widthLadder_telescope (F : ℕ → ℂ) (J : ℕ) :
    F 0 - F J = ∑ j ∈ Finset.range J, (F j - F (j + 1)) := by
  exact (Finset.sum_range_sub' F J).symm

/-- A large endpoint defect forces an adjacent defect at least as large as its ladder average. -/
theorem complex_widthLadder_norm_pigeonhole
    (F : ℕ → ℂ) {J : ℕ} (hJ : 0 < J) {B : ℝ}
    (hB : B <= ‖F 0 - F J‖) :
    ∃ j ∈ Finset.range J,
      B / (J : ℝ) <= ‖F j - F (j + 1)‖ := by
  have htel := complex_widthLadder_telescope F J
  have hsum : B <= ∑ j ∈ Finset.range J, ‖F j - F (j + 1)‖ := by
    calc
      B <= ‖F 0 - F J‖ := hB
      _ = ‖∑ j ∈ Finset.range J, (F j - F (j + 1))‖ := by rw [htel]
      _ <= ∑ j ∈ Finset.range J, ‖F j - F (j + 1)‖ := norm_sum_le _ _
  have hconst :
      ∑ _j ∈ Finset.range J, B / (J : ℝ) = B := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
    field_simp
  have hsum' :
      ∑ j ∈ Finset.range J, B / (J : ℝ) <=
        ∑ j ∈ Finset.range J, ‖F j - F (j + 1)‖ := by
    rwa [hconst]
  exact Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr hJ.ne') hsum'

/-- Full-line Perron integral at one physical width. -/
def routeTNormalizedWidthPerronIntegral
    (L X k : ℕ) (T0 t N sigma H : ℝ) : ℂ :=
  ∫ y : ℝ,
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
        ((sigma : ℂ) + (y : ℝ) * I) *
      routeTNormalizedSmoothWindowMellin N H
        ((sigma : ℂ) + (y : ℝ) * I)

/-- Difference of two one-width Perron integrals is exactly the signed kernel-defect integral. -/
theorem routeTNormalizedWidthPerronIntegral_sub_eq_kernelDefect
    (L X k : ℕ) (T0 t : ℝ) {N sigma H R : ℝ}
    (hN : 0 < N) (hsigma : 0 < sigma) (hH : 0 < H) (hR : 0 < R) :
    routeTNormalizedWidthPerronIntegral L X k T0 t N sigma R -
        routeTNormalizedWidthPerronIntegral L X k T0 t N sigma H =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((sigma : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((sigma : ℂ) + (y : ℝ) * I)) := by
  have hIntR :=
    integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hR hsigma
  have hIntH :=
    integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hH hsigma
  rw [routeTNormalizedWidthPerronIntegral,
    routeTNormalizedWidthPerronIntegral, ← integral_sub hIntR hIntH]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- Exact telescope of the wide-to-target signed Perron defect through arbitrary positive
intermediate widths. -/
theorem routeT_multiscale_kernelDefect_integral_telescope
    (L X k : ℕ) (T0 t : ℝ) {N sigma : ℝ}
    (hN : 0 < N) (hsigma : 0 < sigma)
    (W : ℕ → ℝ) (J : ℕ) (hW : ∀ j, j <= J → 0 < W j) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N (W 0)
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N (W J)
            ((sigma : ℂ) + (y : ℝ) * I))) =
      ∑ j ∈ Finset.range J,
        ∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            (routeTNormalizedSmoothWindowMellin N (W j)
                ((sigma : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N (W (j + 1))
                ((sigma : ℂ) + (y : ℝ) * I)) := by
  let P : ℕ → ℂ := fun j =>
    routeTNormalizedWidthPerronIntegral L X k T0 t N sigma (W j)
  have hfull := routeTNormalizedWidthPerronIntegral_sub_eq_kernelDefect
    L X k T0 t hN hsigma (hW J le_rfl) (hW 0 (Nat.zero_le J))
  have hstep : ∀ j ∈ Finset.range J,
      P j - P (j + 1) =
        ∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            (routeTNormalizedSmoothWindowMellin N (W j)
                ((sigma : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N (W (j + 1))
                ((sigma : ℂ) + (y : ℝ) * I)) := by
    intro j hj
    have hjlt : j < J := Finset.mem_range.mp hj
    dsimp only [P]
    exact routeTNormalizedWidthPerronIntegral_sub_eq_kernelDefect
      L X k T0 t hN hsigma (hW (j + 1) (by omega)) (hW j (by omega))
  rw [← hfull]
  calc
    P 0 - P J = ∑ j ∈ Finset.range J, (P j - P (j + 1)) :=
      complex_widthLadder_telescope P J
    _ = _ := Finset.sum_congr rfl hstep

/-- **Multiscale signed large-error producer.**  A large wide-to-target Perron defect forces one
adjacent-scale pole-annihilating defect of average size.  No PNT estimate at intermediate widths
is assumed. -/
theorem routeT_multiscale_kernelDefect_norm_pigeonhole
    (L X k : ℕ) (T0 t : ℝ) {N sigma B : ℝ}
    (hN : 0 < N) (hsigma : 0 < sigma)
    (W : ℕ → ℝ) {J : ℕ} (hJ : 0 < J)
    (hW : ∀ j, j <= J → 0 < W j)
    (hlarge : B <= ‖∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N (W 0)
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N (W J)
            ((sigma : ℂ) + (y : ℝ) * I))‖) :
    ∃ j ∈ Finset.range J,
      B / (J : ℝ) <= ‖∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N (W j)
              ((sigma : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N (W (j + 1))
              ((sigma : ℂ) + (y : ℝ) * I))‖ := by
  let P : ℕ → ℂ := fun j =>
    routeTNormalizedWidthPerronIntegral L X k T0 t N sigma (W j)
  have hfull := routeTNormalizedWidthPerronIntegral_sub_eq_kernelDefect
    L X k T0 t hN hsigma (hW J le_rfl) (hW 0 (Nat.zero_le J))
  have hlargeP : B <= ‖P 0 - P J‖ := by
    rw [hfull]
    exact hlarge
  obtain ⟨j, hj, hjlarge⟩ :=
    complex_widthLadder_norm_pigeonhole P hJ hlargeP
  refine ⟨j, hj, ?_⟩
  have hjlt : j < J := Finset.mem_range.mp hj
  have hstep := routeTNormalizedWidthPerronIntegral_sub_eq_kernelDefect
    L X k T0 t hN hsigma (hW (j + 1) (by omega)) (hW j (by omega))
  dsimp only [P] at hjlarge
  rw [hstep] at hjlarge
  exact hjlarge

/-- Comparable adjacent widths leave only a constant-factor transition between common low band
and target decay scale. -/
theorem routeT_adjacentWidth_transition_ratio_le_four
    {N H R : ℝ} (hN : 0 <= N) (hH : 0 < H)
    (hHR : H <= R) (hRH : R <= 2 * H) :
    N / H <= 4 * (N / (2 * R)) := by
  have hR : 0 < R := hH.trans_le hHR
  rw [div_le_iff₀ hH, div_eq_mul_inv]
  field_simp [hR.ne']
  nlinarith

/-- Dyadic physical-width ladder, stopped once it reaches the target width. -/
def routeTComparableWidthLadder (H R : ℝ) (j : ℕ) : ℝ :=
  max H (R / (((2 ^ j : ℕ) : ℝ)))

/-- A wide and a target width admit a genuinely logarithmic dyadic stopping index.  The explicit
power bracket prevents the finite telescope from concealing a linear-in-`R / H` loss. -/
theorem exists_routeTComparableWidthLadder_endpoint
    {H R : ℝ} (hH : 0 < H) (hHR : H ≤ R) :
    ∃ J : ℕ, 0 < J ∧
      (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ R / H ∧
      R / H < (((2 ^ J : ℕ) : ℝ)) ∧
      routeTComparableWidthLadder H R 0 = R ∧
      routeTComparableWidthLadder H R J = H := by
  have hratio : 1 ≤ R / H := by
    apply (le_div_iff₀ hH).2
    simpa using hHR
  obtain ⟨j, hbelowRaw, haboveRaw⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  let J := j + 1
  have hJpos : 0 < J := by omega
  have hbelow : (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ R / H := by
    simpa [J, Nat.cast_pow] using hbelowRaw
  have habove : R / H < (((2 ^ J : ℕ) : ℝ)) := by
    simpa [J, Nat.cast_pow] using haboveRaw
  refine ⟨J, hJpos, hbelow, habove, ?_, ?_⟩
  · simp [routeTComparableWidthLadder, max_eq_right hHR]
  · rw [routeTComparableWidthLadder, max_eq_left_iff]
    have hpowpos : (0 : ℝ) < ((2 ^ J : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hpowpos]
    simpa [mul_comm] using (div_le_iff₀ hH).mp habove.le

/-- Every rung of the stopped dyadic ladder remains positive. -/
theorem routeTComparableWidthLadder_pos
    {H R : ℝ} (hH : 0 < H) (j : ℕ) :
    0 < routeTComparableWidthLadder H R j :=
  hH.trans_le (le_max_left _ _)

/-- Consecutive stopped dyadic widths are decreasing and differ by at most a factor of two. -/
theorem routeTComparableWidthLadder_adjacent
    {H R : ℝ} (hH : 0 < H) (hR : 0 < R) (j : ℕ) :
    routeTComparableWidthLadder H R (j + 1) ≤
        routeTComparableWidthLadder H R j ∧
      routeTComparableWidthLadder H R j ≤
        2 * routeTComparableWidthLadder H R (j + 1) := by
  let q : ℕ → ℝ := fun n => ((2 ^ n : ℕ) : ℝ)
  have hqj : 0 < q j := by dsimp [q]; positivity
  have hqnext : q (j + 1) = 2 * q j := by
    simp [q, pow_succ, mul_comm]
  have hdivnext : R / q (j + 1) = (R / q j) / 2 := by
    rw [hqnext]
    field_simp
  constructor
  · unfold routeTComparableWidthLadder
    apply max_le_max_left
    rw [hdivnext]
    nlinarith [div_pos hR hqj]
  · unfold routeTComparableWidthLadder
    rw [hdivnext]
    apply max_le
    · have hfloor := le_max_left H (R / q j / 2)
      nlinarith
    · have hhalf := le_max_right H (R / q j / 2)
      nlinarith

/-- **Prime-free multiscale producer.**  Existing wide-reference calibration and target
prime-freeness force one adjacent-scale signed defect of average size.  Intermediate widths need
no prime-number theorem input: they enter only through the exact telescope. -/
theorem norm_adjacent_multiscale_kernelDefect_ge_of_primeFree
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H R sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 2 ≤ N) (hH : 0 < H) (hR : 0 < R)
    (hwidthH : 1 ≤ 2 * H)
    (hsupportH : N + 2 * H ≤ X) (hsupportR : N + 2 * R ≤ X)
    (hsigma : 0 < sigma)
    (hprimeFree : Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0)
    (href : routeTSmoothWindowCentralMargin * (R / 2) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n)
    (hleakage :
      (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H ≤
        routeTSmoothWindowCentralMargin / 4)
    (W : ℕ → ℝ) {J : ℕ} (hJ : 0 < J)
    (hW : ∀ j, j <= J → 0 < W j)
    (hW0 : W 0 = R) (hWJ : W J = H) :
    ∃ j ∈ Finset.range J,
      ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (J : ℝ) <=
        ‖∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
              ((sigma : ℂ) + (y : ℝ) * I) *
            (routeTNormalizedSmoothWindowMellin N (W j)
                ((sigma : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N (W (j + 1))
                ((sigma : ℂ) + (y : ℝ) * I))‖ := by
  have hwide := norm_integral_normalizedKernelDefect_ge_of_primeFree
    L X k hXL hT0 hscale hN hH hR hwidthH hsupportH hsupportR hsigma
      hprimeFree href hleakage
  have hlarge : (2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4) <=
      ‖∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((sigma : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N (W 0)
              ((sigma : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N (W J)
              ((sigma : ℂ) + (y : ℝ) * I))‖ := by
    rw [hW0, hWJ]
    exact hwide
  exact routeT_multiscale_kernelDefect_norm_pigeonhole
    L X k T0 t (by linarith) hsigma W hJ hW hlarge

/-- **Endpoint-only prime-free multiscale producer.**  The arbitrary ladder from
`norm_adjacent_multiscale_kernelDefect_ge_of_primeFree` is discharged by the canonical dyadic
ladder.  The selected adjacent defect simultaneously has logarithmic averaging loss, exact pole
cancellation, and no more than a factor-four Mellin transition gap. -/
theorem exists_routeTComparableWidthLadder_defect_of_primeFree
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H R sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 2 ≤ N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hwidthH : 1 ≤ 2 * H)
    (hsupportH : N + 2 * H ≤ X) (hsupportR : N + 2 * R ≤ X)
    (hsigma : 0 < sigma)
    (hprimeFree : Chebyshev.theta (N + 2 * H) - Chebyshev.theta N = 0)
    (href : routeTSmoothWindowCentralMargin * (R / 2) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N R n)
    (hleakage :
      (Real.log (N + 2 * H) / Real.log 2) *
          (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) / H ≤
        routeTSmoothWindowCentralMargin / 4) :
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
        ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) / (J : ℝ) ≤
          ‖∫ y : ℝ,
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
                ((sigma : ℂ) + (y : ℝ) * I) *
              (routeTNormalizedSmoothWindowMellin N
                    (routeTComparableWidthLadder H R j)
                    ((sigma : ℂ) + (y : ℝ) * I) -
                routeTNormalizedSmoothWindowMellin N
                    (routeTComparableWidthLadder H R (j + 1))
                    ((sigma : ℂ) + (y : ℝ) * I))‖ := by
  obtain ⟨J, hJ, hbelow, habove, hW0, hWJ⟩ :=
    exists_routeTComparableWidthLadder_endpoint hH hHR
  let W := routeTComparableWidthLadder H R
  have hW : ∀ j, j ≤ J → 0 < W j := by
    intro j _hj
    exact routeTComparableWidthLadder_pos hH j
  obtain ⟨j, hj, hlarge⟩ :=
    norm_adjacent_multiscale_kernelDefect_ge_of_primeFree
      L X k hXL hT0 hscale hN hH hR hwidthH hsupportH hsupportR hsigma
        hprimeFree href hleakage W hJ hW hW0 hWJ
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
    hNnonneg (routeTComparableWidthLadder_pos (R := R) hH (j + 1)) hadj.1 hadj.2
  refine ⟨J, hJ, hbelow, habove, j, hj, hadj.1, hadj.2,
    hpole, htransition, ?_⟩
  exact hlarge

end RHTower.Sieve
