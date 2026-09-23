import GaloisForLFunctions.RHTower.XiHeatCassiniWoldLowerHalfShiftGapSummability
import GaloisForLFunctions.RHTower.XiMassCriticalIntegerFace

/-!
# Prime-gap quadrature form of the Route-T logarithmic mesh

The logarithmic main current left by the centered Wold decomposition is exactly the
right-endpoint Stieltjes quadrature of the continuous critical growing Fourier profile on the
ordered prime-log partition.  Its cell error is the integral of one derivative against the
linear Peano kernel.  This exposes the precise arithmetic cost: the square of each prime-log
gap, multiplied by the critical half-density at the right endpoint.

No prime-gap estimate is assumed in this module.  Every result is an unconditional identity or
pointwise analytic bound.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Right-endpoint quadrature on the ordered prime-log partition, including the initial
`[0, log 2]` endpoint atom. -/
def xiHeatCassiniOrderedLogMeshGapSampleSum
    (a : ℝ) (τ : ℂ) (N : ℕ) : ℂ :=
  (xiMassNthPrimeLogHeight 0 : ℂ) *
      xiHeatCassiniOrderedPrimeHalfDensityProfile a τ 0 +
    ∑ n ∈ Finset.range N,
      (xiHeatCassiniOrderedPrimeLogGap n : ℂ) *
        xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (n + 1)

/-- Finite Abel transport turns the logarithmic terminal-plus-connection current into literal
right-endpoint prime-log quadrature. -/
theorem xiHeatCassiniOrderedLogMeshFlux_eq_gapSampleSum
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    xiHeatCassiniOrderedLogMeshTerminalFlux a τ N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedLogMeshConnectionAtom a τ n =
      xiHeatCassiniOrderedLogMeshGapSampleSum a τ N := by
  induction N with
  | zero =>
      simp [xiHeatCassiniOrderedLogMeshTerminalFlux,
        xiHeatCassiniOrderedLogMeshGapSampleSum]
      ring
  | succ N ih =>
      simp only [Finset.sum_range_succ] at ih ⊢
      simp only [xiHeatCassiniOrderedLogMeshGapSampleSum] at ih ⊢
      simp only [Finset.sum_range_succ] at ih ⊢
      rw [xiHeatCassiniOrderedLogMeshTerminalFlux,
        xiHeatCassiniOrderedLogMeshConnectionAtom]
      simp only [xiHeatCassiniOrderedPrimeLogGap]
      push_cast at ih ⊢
      calc
        xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (N + 1) *
              xiMassNthPrimeLogHeight (N + 1) +
            ((∑ n ∈ Finset.range N,
                xiHeatCassiniOrderedLogMeshConnectionAtom a τ n) +
              (xiMassNthPrimeLogHeight N : ℂ) *
                (xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N -
                  xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (N + 1))) =
            (xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N *
                xiMassNthPrimeLogHeight N +
              ∑ n ∈ Finset.range N,
                xiHeatCassiniOrderedLogMeshConnectionAtom a τ n) +
              ((xiMassNthPrimeLogHeight (N + 1) : ℂ) -
                  xiMassNthPrimeLogHeight N) *
                xiHeatCassiniOrderedPrimeHalfDensityProfile a τ (N + 1) := by ring
        _ = _ := by
          rw [show xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N *
              (xiMassNthPrimeLogHeight N : ℂ) =
                xiHeatCassiniOrderedLogMeshTerminalFlux a τ N by rfl, ih]
          simp only [xiHeatCassiniOrderedPrimeLogGap]
          push_cast
          ring

/-- Restored prime half-density is the continuous growing profile sampled at prime-log height. -/
theorem xiHeatCassiniOrderedPrimeHalfDensityProfile_eq_growingFourierProfile
    (a sigma u : ℝ) (N : ℕ) :
    xiHeatCassiniOrderedPrimeHalfDensityProfile
        a ((sigma : ℂ) + u * I) N =
      xiMassCriticalGrowingFourierProfile
        a sigma u (xiMassNthPrimeLogHeight N) := by
  unfold xiHeatCassiniOrderedPrimeHalfDensityProfile
    xiHeatCassiniPrimeMassFourierProfile
    xiMassCriticalGrowingFourierProfile
    xiMassNthPrimeLogHeight
  congr 1
  have hp : 0 < (nthPrimeSubtype N : ℝ) := nthPrimeSubtype_pos N
  rw [← Real.log_sqrt hp.le, Real.exp_log (Real.sqrt_pos.mpr hp)]

/-- The complete finite logarithmic main current is sampled continuum growing-profile
quadrature. -/
theorem xiHeatCassiniOrderedLogMeshFlux_eq_growingPrimeGapQuadrature
    (a sigma u : ℝ) (N : ℕ) :
    xiHeatCassiniOrderedLogMeshTerminalFlux
          a ((sigma : ℂ) + u * I) N +
        ∑ n ∈ Finset.range N,
          xiHeatCassiniOrderedLogMeshConnectionAtom
            a ((sigma : ℂ) + u * I) n =
      (xiMassNthPrimeLogHeight 0 : ℂ) *
          xiMassCriticalGrowingFourierProfile
            a sigma u (xiMassNthPrimeLogHeight 0) +
        ∑ n ∈ Finset.range N,
          (xiHeatCassiniOrderedPrimeLogGap n : ℂ) *
            xiMassCriticalGrowingFourierProfile
              a sigma u (xiMassNthPrimeLogHeight (n + 1)) := by
  rw [xiHeatCassiniOrderedLogMeshFlux_eq_gapSampleSum,
    xiHeatCassiniOrderedLogMeshGapSampleSum,
    xiHeatCassiniOrderedPrimeHalfDensityProfile_eq_growingFourierProfile]
  apply congrArg (fun z : ℂ =>
    (xiMassNthPrimeLogHeight 0 : ℂ) *
      xiMassCriticalGrowingFourierProfile
        a sigma u (xiMassNthPrimeLogHeight 0) + z)
  apply Finset.sum_congr rfl
  intro n hn
  rw [xiHeatCassiniOrderedPrimeHalfDensityProfile_eq_growingFourierProfile]

/-- Named derivative of the critical growing Fourier profile. -/
def xiMassCriticalGrowingFourierDerivative
    (a sigma u h : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) *
    ((1 / 2 : ℂ) *
        stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) +
      xiMassFourierDerivative a sigma u h)

theorem hasDerivAt_xiMassCriticalGrowingFourierProfile_named
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u h : ℝ) :
    HasDerivAt (xiMassCriticalGrowingFourierProfile a sigma u)
      (xiMassCriticalGrowingFourierDerivative a sigma u h) h := by
  simpa [xiMassCriticalGrowingFourierDerivative] using
    hasDerivAt_xiMassCriticalGrowingFourierProfile ha hsigma u h

theorem continuous_xiMassCriticalGrowingFourierDerivative
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ) :
    Continuous (xiMassCriticalGrowingFourierDerivative a sigma u) := by
  unfold xiMassCriticalGrowingFourierDerivative
  have hwcont : Continuous (fun h : ℝ => (Real.exp (h / 2) : ℂ)) := by fun_prop
  have hFcont : Continuous (fun h : ℝ =>
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro h
    exact (hasDerivAt_xiMassRealFourierProfile ha hsigma u h).continuousAt
  exact hwcont.mul ((hFcont.const_mul _).add
    (continuous_xiMassFourierDerivative ha hsigma u))

/-- Uniform vertical-line derivative bound.  All height growth is the explicit critical factor
`exp(h/2)`; the remaining constant is independent of spectral frequency `u`. -/
theorem norm_xiMassCriticalGrowingFourierDerivative_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u h : ℝ) :
    ‖xiMassCriticalGrowingFourierDerivative a sigma u h‖ ≤
      Real.exp (h / 2) * xiMassCriticalOutgoingZeroShiftBound sigma := by
  have hF := norm_stripFourier_xiMassAnalyticTest_vertical_le ha hsigma u h
  have hD := norm_xiMassFourierDerivative_deepShift_le
    (a := a) (σ := sigma) (d := 0) (by norm_num) ha hsigma u h
  have hD0 : ‖xiMassFourierDerivative a sigma u h‖ ≤
      ∫ x : ℝ, |x| * Real.exp (-(sigma * |x|)) := by
    simpa using hD
  rw [xiMassCriticalGrowingFourierDerivative, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (h / 2) *
        ‖(1 / 2 : ℂ) *
            stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) +
          xiMassFourierDerivative a sigma u h‖ ≤
      Real.exp (h / 2) *
        ((1 / 2 : ℝ) *
            ‖stripFourier
              (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ +
          ‖xiMassFourierDerivative a sigma u h‖) := by
        gcongr
        calc
          ‖(1 / 2 : ℂ) *
                stripFourier
                  (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) +
              xiMassFourierDerivative a sigma u h‖ ≤
            ‖(1 / 2 : ℂ) *
                stripFourier
                  (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ +
              ‖xiMassFourierDerivative a sigma u h‖ := norm_add_le _ _
          _ = (1 / 2 : ℝ) *
                ‖stripFourier
                  (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ +
              ‖xiMassFourierDerivative a sigma u h‖ := by norm_num
    _ ≤ Real.exp (h / 2) *
        ((1 / 2 : ℝ) * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
          ∫ x : ℝ, |x| * Real.exp (-(sigma * |x|))) := by gcongr
    _ = Real.exp (h / 2) * xiMassCriticalOutgoingZeroShiftBound sigma := by
      rw [xiMassCriticalOutgoingZeroShiftBound]

/-- Exact Peano-kernel identity for one right-endpoint quadrature cell. -/
theorem xiMassCriticalGrowingFourierProfile_rightCellError_eq
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (u r s : ℝ) :
    ((s - r : ℝ) : ℂ) * xiMassCriticalGrowingFourierProfile a sigma u s -
        ∫ h in r..s, xiMassCriticalGrowingFourierProfile a sigma u h =
      ∫ h in r..s, ((h - r : ℝ) : ℂ) *
        xiMassCriticalGrowingFourierDerivative a sigma u h := by
  let G : ℝ → ℂ := xiMassCriticalGrowingFourierProfile a sigma u
  let D : ℝ → ℂ := xiMassCriticalGrowingFourierDerivative a sigma u
  have hu : ∀ h ∈ Set.uIcc r s,
      HasDerivAt (fun y : ℝ => ((y - r : ℝ) : ℂ)) 1 h := by
    intro h hh
    simpa using ((hasDerivAt_id h).sub_const r).ofReal_comp
  have hv : ∀ h ∈ Set.uIcc r s, HasDerivAt G (D h) h := by
    intro h hh
    exact hasDerivAt_xiMassCriticalGrowingFourierProfile_named ha hsigma u h
  have huInt : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume r s :=
    intervalIntegrable_const
  have hvInt : IntervalIntegrable D volume r s :=
    (continuous_xiMassCriticalGrowingFourierDerivative ha hsigma u).intervalIntegrable _ _
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv huInt hvInt
  change ((s - r : ℝ) : ℂ) * G s - (∫ h in r..s, G h) =
    ∫ h in r..s, ((h - r : ℝ) : ℂ) * D h
  calc
    ((s - r : ℝ) : ℂ) * G s - (∫ h in r..s, G h) =
        ((s - r : ℝ) : ℂ) * G s - ((0 : ℝ) : ℂ) * G r -
          ∫ h in r..s, (1 : ℂ) * G h := by simp
    _ = ∫ h in r..s, ((h - r : ℝ) : ℂ) * D h := by
      simpa using hip.symm

/-- One right-endpoint cell costs at most squared mesh width times the critical half-density at
the right endpoint. -/
theorem norm_xiMassCriticalGrowingFourierProfile_rightCellError_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (u : ℝ) {r s : ℝ} (hrs : r ≤ s) :
    ‖((s - r : ℝ) : ℂ) * xiMassCriticalGrowingFourierProfile a sigma u s -
        ∫ h in r..s, xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤
      (s - r) ^ (2 : ℕ) * Real.exp (s / 2) *
        xiMassCriticalOutgoingZeroShiftBound sigma := by
  rw [xiMassCriticalGrowingFourierProfile_rightCellError_eq ha hsigma]
  let J : ℝ := xiMassCriticalOutgoingZeroShiftBound sigma
  let C : ℝ := (s - r) * Real.exp (s / 2) * J
  have hpoint : ∀ h ∈ Set.uIoc r s,
      ‖((h - r : ℝ) : ℂ) *
          xiMassCriticalGrowingFourierDerivative a sigma u h‖ ≤ C := by
    intro h hh
    rw [uIoc_of_le hrs] at hh
    have hhr : 0 ≤ h - r := sub_nonneg.mpr hh.1.le
    have hhs : h ≤ s := hh.2
    have hD := norm_xiMassCriticalGrowingFourierDerivative_le ha hsigma u h
    have hexp : Real.exp (h / 2) ≤ Real.exp (s / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hJ : 0 ≤ J := by
      exact xiMassCriticalOutgoingZeroShiftBound_nonneg sigma
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hhr]
    calc
      (h - r) * ‖xiMassCriticalGrowingFourierDerivative a sigma u h‖ ≤
          (h - r) * (Real.exp (h / 2) * J) :=
        mul_le_mul_of_nonneg_left hD hhr
      _ ≤ (s - r) * (Real.exp (s / 2) * J) := by
        exact mul_le_mul
          (sub_le_sub_right hhs r)
          (mul_le_mul_of_nonneg_right hexp hJ)
          (mul_nonneg (Real.exp_nonneg _) hJ) (sub_nonneg.mpr hrs)
      _ = C := by dsimp only [C]; ring
  calc
    ‖∫ h in r..s, ((h - r : ℝ) : ℂ) *
        xiMassCriticalGrowingFourierDerivative a sigma u h‖ ≤
        C * |s - r| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (s - r) ^ (2 : ℕ) * Real.exp (s / 2) *
        xiMassCriticalOutgoingZeroShiftBound sigma := by
      rw [abs_of_nonneg (sub_nonneg.mpr hrs)]
      dsimp only [C, J]
      ring

/-- Prime-log specialization of the cell bound. -/
theorem norm_xiMassCriticalGrowingFourierProfile_primeLogCellError_le
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (u : ℝ) (N : ℕ) :
    ‖(xiHeatCassiniOrderedPrimeLogGap N : ℂ) *
          xiMassCriticalGrowingFourierProfile
            a sigma u (xiMassNthPrimeLogHeight (N + 1)) -
        ∫ h in xiMassNthPrimeLogHeight N..xiMassNthPrimeLogHeight (N + 1),
          xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤
      xiHeatCassiniOrderedPrimeLogGap N ^ (2 : ℕ) *
        Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) *
          xiMassCriticalOutgoingZeroShiftBound sigma := by
  simpa [xiHeatCassiniOrderedPrimeLogGap, xiMassNthPrimeLogHeight] using
    norm_xiMassCriticalGrowingFourierProfile_rightCellError_le
      ha hsigma u
        (nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N))

/-- Additive gap between two consecutive ordered primes, viewed as a real number. -/
def xiHeatCassiniOrderedPrimeGap (N : ℕ) : ℝ :=
  (nthPrimeSubtype (N + 1) : ℝ) - (nthPrimeSubtype N : ℝ)

theorem xiHeatCassiniOrderedPrimeGap_nonneg (N : ℕ) :
    0 ≤ xiHeatCassiniOrderedPrimeGap N := by
  unfold xiHeatCassiniOrderedPrimeGap
  exact sub_nonneg.mpr (by
    exact_mod_cast nthPrimeSubtype_strictMono.monotone (Nat.le_succ N))

/-- The logarithmic mesh gap is bounded by relative additive prime gap. -/
theorem xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime (N : ℕ) :
    xiHeatCassiniOrderedPrimeLogGap N ≤
      xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ) := by
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hq : 0 < q := nthPrimeSubtype_pos (N + 1)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
  change Real.log q - Real.log p ≤ (q - p) / p
  calc
    Real.log q - Real.log p = Real.log (q / p) := by
      rw [Real.log_div hq.ne' hp.ne']
    _ ≤ q / p - 1 := hlog
    _ = (q - p) / p := by field_simp [hp.ne']

/-- Critical prime-log cell weight is dominated by normalized additive prime-gap square.
Bertrand is used only to replace the right-endpoint square root by twice the left-endpoint one. -/
theorem primeLogGap_sq_mul_criticalHalfDensity_le_primeGapSq (N : ℕ) :
    xiHeatCassiniOrderedPrimeLogGap N ^ (2 : ℕ) *
        Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) ≤
      2 * (xiHeatCassiniOrderedPrimeGap N /
          (nthPrimeSubtype N : ℝ)) ^ (2 : ℕ) *
        Real.sqrt (nthPrimeSubtype N : ℝ) := by
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let gap : ℝ := xiHeatCassiniOrderedPrimeGap N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hq : 0 < q := nthPrimeSubtype_pos (N + 1)
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hgap : 0 ≤ gap := xiHeatCassiniOrderedPrimeGap_nonneg N
  have hratio : 0 ≤ gap / p := div_nonneg hgap hp.le
  have hdle : delta ≤ gap / p :=
    xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime N
  have hsq : delta ^ (2 : ℕ) ≤ (gap / p) ^ (2 : ℕ) :=
    (sq_le_sq₀ hdelta hratio).mpr hdle
  have hq2p : q ≤ 2 * p := by
    dsimp only [p, q]
    exact_mod_cast nthPrimeSubtype_succ_le_two_mul N
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrtNonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hsqrt : Real.sqrt q ≤ 2 * Real.sqrt p := by
    calc
      Real.sqrt q ≤ Real.sqrt (2 * p) := Real.sqrt_le_sqrt hq2p
      _ = Real.sqrt 2 * Real.sqrt p := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * Real.sqrt p :=
        mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg p)
  have hexp : Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) =
      Real.sqrt q := by
    dsimp only [xiMassNthPrimeLogHeight, q]
    rw [← Real.log_sqrt hq.le, Real.exp_log (Real.sqrt_pos.mpr hq)]
  change delta ^ (2 : ℕ) *
      Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2) ≤
    2 * (gap / p) ^ (2 : ℕ) * Real.sqrt p
  rw [hexp]
  calc
    delta ^ (2 : ℕ) * Real.sqrt q ≤
        (gap / p) ^ (2 : ℕ) * (2 * Real.sqrt p) :=
      mul_le_mul hsq hsqrt (Real.sqrt_nonneg q) (sq_nonneg (gap / p))
    _ = 2 * (gap / p) ^ (2 : ℕ) * Real.sqrt p := by ring

/-- Exact Route-T cell error now has a purely additive-prime-gap majorant. -/
theorem norm_xiMassCriticalGrowingFourierProfile_primeLogCellError_le_primeGapSq
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (u : ℝ) (N : ℕ) :
    ‖(xiHeatCassiniOrderedPrimeLogGap N : ℂ) *
          xiMassCriticalGrowingFourierProfile
            a sigma u (xiMassNthPrimeLogHeight (N + 1)) -
        ∫ h in xiMassNthPrimeLogHeight N..xiMassNthPrimeLogHeight (N + 1),
          xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤
      (2 * (xiHeatCassiniOrderedPrimeGap N /
          (nthPrimeSubtype N : ℝ)) ^ (2 : ℕ) *
        Real.sqrt (nthPrimeSubtype N : ℝ)) *
          xiMassCriticalOutgoingZeroShiftBound sigma := by
  calc
    ‖(xiHeatCassiniOrderedPrimeLogGap N : ℂ) *
          xiMassCriticalGrowingFourierProfile
            a sigma u (xiMassNthPrimeLogHeight (N + 1)) -
        ∫ h in xiMassNthPrimeLogHeight N..xiMassNthPrimeLogHeight (N + 1),
          xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤
      (xiHeatCassiniOrderedPrimeLogGap N ^ (2 : ℕ) *
        Real.exp (xiMassNthPrimeLogHeight (N + 1) / 2)) *
          xiMassCriticalOutgoingZeroShiftBound sigma := by
        simpa [mul_assoc] using
          norm_xiMassCriticalGrowingFourierProfile_primeLogCellError_le
            ha hsigma u N
    _ ≤ (2 * (xiHeatCassiniOrderedPrimeGap N /
          (nthPrimeSubtype N : ℝ)) ^ (2 : ℕ) *
        Real.sqrt (nthPrimeSubtype N : ℝ)) *
          xiMassCriticalOutgoingZeroShiftBound sigma :=
      mul_le_mul_of_nonneg_right
        (primeLogGap_sq_mul_criticalHalfDensity_le_primeGapSq N)
        (xiMassCriticalOutgoingZeroShiftBound_nonneg sigma)

end

end RHTower
