import GaloisForLFunctions.RHTower.XiMassStationaryPrimeConeNoncancellation
import GaloisForLFunctions.RHTower.XiMassTwoRapidityCorrelationGeometry

/-!
# Complete stationary prime-cone covariance is pointwise large

At any fixed pair of timelike stationary frequencies, the *complete*
uncentered von Mangoldt rapidity kernels each have square-root-cutoff size.
Their literal two-rapidity covariance therefore has cutoff-sized modulus.
This is a pointwise result; the RH-equivalent bound concerns the signed
rapidity integral and does not follow from it.
-/

namespace RHTower

private theorem exp_half_log_eq_inv_sqrt (n : ℕ) (hn : 0 < n) :
    Real.exp (-Real.log (n : ℝ) / 2) = 1 / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnR]
  rw [one_div, ← Real.exp_neg]
  congr 1
  ring

private theorem prime_cone_term_factor
    (a sigma u t X : ℝ) (n : ℕ) (hn : 0 < n) :
    (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      ((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) * (a : ℂ)) *
      xiMassRapidityPhaseKernel a sigma u (Real.log n) t =
    ((a * Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I *
        ((a * (u * Real.cosh t + Real.log X * Real.sinh t) : ℝ) : ℂ))) *
      ((((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)) *
        Complex.exp (((a * Real.sinh t * (Real.log X - Real.log n) : ℝ) : ℂ) *
          Complex.I)) := by
  rw [exp_half_log_eq_inv_sqrt n hn]
  rw [xiMassRapidityPhaseKernel]
  have he :
      -(Complex.I * ((a * (u * Real.cosh t + Real.log X * Real.sinh t) : ℝ) : ℂ)) +
          ((a * Real.sinh t * (Real.log X - Real.log n) : ℝ) : ℂ) * Complex.I =
        -(Complex.I * ((a * (u * Real.cosh t + Real.log n * Real.sinh t) : ℝ) : ℂ)) := by
    push_cast
    ring
  have heq :
      Complex.exp (-(Complex.I *
        ((a * (u * Real.cosh t + Real.log X * Real.sinh t) : ℝ) : ℂ))) *
        Complex.exp (((a * Real.sinh t * (Real.log X - Real.log n) : ℝ) : ℂ) *
          Complex.I) =
      Complex.exp (-(Complex.I *
        ((a * (u * Real.cosh t + Real.log n * Real.sinh t) : ℝ) : ℂ))) := by
    rw [← Complex.exp_add, he]
  calc
    _ = ((a * Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t) : ℝ) : ℂ) *
          ((((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ))) *
          Complex.exp (-(Complex.I *
            ((a * (u * Real.cosh t + Real.log n * Real.sinh t) : ℝ) : ℂ))) := by
            push_cast
            ring
    _ = _ := by rw [← heq]; ring

private theorem prime_cone_kernel_factor
    (a sigma d u t : ℝ)
    (hX : 2 ≤ Real.exp (d * u / (d - 1 / 2))) :
    xiMassCriticalPrimeConeRapidityKernel a sigma d u t =
      ((a * Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I *
          ((a * (u * Real.cosh t +
            Real.log (Real.exp (d * u / (d - 1 / 2))) * Real.sinh t) : ℝ) : ℂ))) *
          apexAlignedPrimeMass (Real.exp (d * u / (d - 1 / 2)))
            (a * Real.sinh t) := by
  rw [apexAlignedPrimeMass_eq_shifted hX]
  unfold xiMassCriticalPrimeConeRapidityKernel
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hn : 0 < k + 2 := by omega
  have hcast : ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
  simp only [xiMassCriticalPrimeConeRapidityWeight, hcast]
  simpa only [mul_assoc] using
    prime_cone_term_factor a sigma u t
      (Real.exp (d * u / (d - 1 / 2))) (k + 2) hn

private theorem prime_cone_kernel_norm_factor
    (a sigma d u t : ℝ)
    (hX : 2 ≤ Real.exp (d * u / (d - 1 / 2))) :
    ‖xiMassCriticalPrimeConeRapidityKernel a sigma d u t‖ =
      |a * Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t)| *
        ‖apexAlignedPrimeMass (Real.exp (d * u / (d - 1 / 2)))
          (a * Real.sinh t)‖ := by
  rw [prime_cone_kernel_factor a sigma d u t hX, norm_mul, norm_mul]
  have hphase :
      ‖Complex.exp (-(Complex.I *
          ((a * (u * Real.cosh t +
            Real.log (Real.exp (d * u / (d - 1 / 2))) * Real.sinh t) : ℝ) : ℂ)))‖ = 1 := by
    have he :
        -(Complex.I *
          ((a * (u * Real.cosh t +
            Real.log (Real.exp (d * u / (d - 1 / 2))) * Real.sinh t) : ℝ) : ℂ)) =
          ((-(a * (u * Real.cosh t +
            Real.log (Real.exp (d * u / (d - 1 / 2))) * Real.sinh t)) : ℝ) : ℂ) *
            Complex.I := by push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  rw [hphase, mul_one, Complex.norm_real, Real.norm_eq_abs]

private theorem stationary_rapidity_tendsto_zero (h : ℝ) :
    Filter.Tendsto (fun u : ℝ => -timelikeRapidity u h)
      Filter.atTop (nhds 0) := by
  have hsinh : Filter.Tendsto
      (fun u : ℝ => Real.sinh (-timelikeRapidity u h))
      Filter.atTop (nhds 0) := by
    simpa only [one_mul] using tendsto_stationary_prime_frequency_zero 1 h
  have harsinh := (Real.continuous_arsinh.tendsto 0).comp hsinh
  simpa only [Function.comp_def, Real.arsinh_sinh, Real.arsinh_zero] using harsinh

private theorem stationary_prime_amplitude_tendsto
    (a sigma h : ℝ) :
    Filter.Tendsto
      (fun u : ℝ => a * Real.cosh (-timelikeRapidity u h) *
        Real.exp (-(a * sigma) * Real.cosh (-timelikeRapidity u h)))
      Filter.atTop (nhds (a * Real.exp (-(a * sigma)))) := by
  have hc : Continuous (fun t : ℝ =>
      a * Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t)) := by fun_prop
  have hlim := (hc.tendsto 0).comp (stationary_rapidity_tendsto_zero h)
  simpa only [Function.comp_def, Real.cosh_zero, mul_one] using hlim

private theorem eventually_stationary_kernel_norm_lower
    {a d : ℝ} (ha : 0 < a) (hd : (1 : ℝ) / 2 < d)
    (sigma h : ℝ) :
    ∀ᶠ u : ℝ in Filter.atTop,
      (a * Real.exp (-(a * sigma)) / 8) *
          Real.sqrt (Real.exp (d * u / (d - 1 / 2))) ≤
        ‖xiMassCriticalPrimeConeRapidityKernel a sigma d u
          (-timelikeRapidity u h)‖ := by
  let c : ℝ := a * Real.exp (-(a * sigma))
  have hcpos : 0 < c := mul_pos ha (Real.exp_pos _)
  have hAmp : ∀ᶠ u : ℝ in Filter.atTop,
      c / 2 < a * Real.cosh (-timelikeRapidity u h) *
        Real.exp (-(a * sigma) * Real.cosh (-timelikeRapidity u h)) := by
    exact (stationary_prime_amplitude_tendsto a sigma h).eventually
      (eventually_gt_nhds (by dsimp [c]; linarith))
  have hcoef : 0 < d / (d - 1 / 2) := by
    apply div_pos <;> linarith
  have harg : Filter.Tendsto (fun u : ℝ => d * u / (d - 1 / 2))
      Filter.atTop Filter.atTop := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, id_eq] using
      Filter.tendsto_id.const_mul_atTop hcoef
  have hX : Filter.Tendsto
      (fun u : ℝ => Real.exp (d * u / (d - 1 / 2)))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp harg
  filter_upwards
    [hAmp, eventually_apexAlignedPrimeMass_stationary_re_ge_quarter_sqrt hd a h,
      hX.eventually (Filter.eventually_ge_atTop (1000000 : ℝ))]
    with u hamp hmass hXu
  let X := Real.exp (d * u / (d - 1 / 2))
  let t := -timelikeRapidity u h
  have hamp0 : 0 ≤ a * Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t) := by
    dsimp only [t] at hamp ⊢
    linarith
  have hA : Real.sqrt X / 4 ≤ ‖apexAlignedPrimeMass X (a * Real.sinh t)‖ := by
    calc
      Real.sqrt X / 4 = (1 / 4 : ℝ) * Real.sqrt X := by ring
      _ ≤ (apexAlignedPrimeMass X (a * Real.sinh t)).re := hmass
      _ ≤ ‖apexAlignedPrimeMass X (a * Real.sinh t)‖ := Complex.re_le_norm _
  have hnorm := prime_cone_kernel_norm_factor a sigma d u t (by linarith)
  rw [abs_of_nonneg hamp0] at hnorm
  change ‖xiMassCriticalPrimeConeRapidityKernel a sigma d u t‖ =
    (a * Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t)) *
      ‖apexAlignedPrimeMass X (a * Real.sinh t)‖ at hnorm
  change (c / 8) * Real.sqrt X ≤ ‖xiMassCriticalPrimeConeRapidityKernel a sigma d u t‖
  calc
    (c / 8) * Real.sqrt X = (c / 2) * (Real.sqrt X / 4) := by ring
    _ ≤ (a * Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t)) *
          (Real.sqrt X / 4) :=
        mul_le_mul_of_nonneg_right hamp.le (by positivity)
    _ ≤ (a * Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t)) *
          ‖apexAlignedPrimeMass X (a * Real.sinh t)‖ :=
        mul_le_mul_of_nonneg_left hA hamp0
    _ = _ := hnorm.symm

/-- The full uncentered two-rapidity covariance has at least linear-cutoff
modulus at every fixed pair of timelike stationary frequencies, cofinally. -/
theorem eventually_stationary_covariance_norm_lower
    {a d : ℝ} (ha : 0 < a) (hd : (1 : ℝ) / 2 < d)
    (sigma h k : ℝ) :
    ∀ᶠ u : ℝ in Filter.atTop,
      ((a * Real.exp (-(a * sigma))) ^ (2 : ℕ) / 64) *
          Real.exp (d * u / (d - 1 / 2)) ≤
        ‖xiMassCriticalPrimeConeTwoRapidityCovariance a sigma d u
          (-timelikeRapidity u h) (-timelikeRapidity u k)‖ := by
  let c : ℝ := a * Real.exp (-(a * sigma))
  filter_upwards
    [eventually_stationary_kernel_norm_lower ha hd sigma h,
      eventually_stationary_kernel_norm_lower ha hd sigma k]
    with u hh hk
  let X := Real.exp (d * u / (d - 1 / 2))
  let th := -timelikeRapidity u h
  let tk := -timelikeRapidity u k
  let Kh := xiMassCriticalPrimeConeRapidityKernel a sigma d u th
  let Kk := xiMassCriticalPrimeConeRapidityKernel a sigma d u tk
  have hh' : c / 8 * Real.sqrt X ≤ ‖Kh‖ := hh
  have hk' : c / 8 * Real.sqrt X ≤ ‖Kk‖ := hk
  have hA0 : 0 ≤ c / 8 * Real.sqrt X := by
    dsimp [c, X]
    positivity
  have hnorm :
      ‖xiMassCriticalPrimeConeTwoRapidityCovariance a sigma d u th tk‖ =
        ‖Kh‖ * ‖Kk‖ := by
    rw [← xiMassCriticalPrimeConeRapidityKernel_mul_star_eq_twoRapidityCovariance]
    change ‖Kh * star Kk‖ = ‖Kh‖ * ‖Kk‖
    rw [norm_mul, norm_star]
  have hsq : Real.sqrt X ^ (2 : ℕ) = X := Real.sq_sqrt (Real.exp_pos _).le
  change c ^ (2 : ℕ) / 64 * X ≤
    ‖xiMassCriticalPrimeConeTwoRapidityCovariance a sigma d u th tk‖
  calc
    c ^ (2 : ℕ) / 64 * X =
        (c / 8 * Real.sqrt X) * (c / 8 * Real.sqrt X) := by
          calc
            c ^ (2 : ℕ) / 64 * X =
                c ^ (2 : ℕ) / 64 * (Real.sqrt X) ^ (2 : ℕ) := by rw [hsq]
            _ = _ := by ring
    _ ≤ ‖Kh‖ * (c / 8 * Real.sqrt X) :=
      mul_le_mul_of_nonneg_right hh' hA0
    _ ≤ ‖Kh‖ * ‖Kk‖ :=
      mul_le_mul_of_nonneg_left hk' (norm_nonneg _)
    _ = _ := hnorm.symm

end RHTower
