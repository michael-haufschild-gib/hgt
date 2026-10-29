import GaloisForLFunctions.ArithmeticCompensationTheory.ThePrimePolarCutoffHasUniformFrequencyBounds
import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeEstimateHoldsOnCompleteProfiles

/-!
# The prime–polar cutoff represents the original complete source

Finite Fourier inversion and an absolutely integrable polar kernel identify
the cutoff multiplier with the full prime sum minus both pole moments. The
edge equals one on the correlation support, so it changes no source term.
-/

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform SchwartzMap
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open GaloisForLFunctions.RHTower ArithmeticCompensationTheory
open ArithmeticCastelnuovoSeveri.LogCells SpacingScaleHarmonicAnalysis

private theorem integrable_primePolar_fourier_kernel (U : SchwartzMap ℝ ℂ)
    {S : ℝ} (hS : 0 < S) :
    Integrable (fun z : ℝ × ℝ => primePolarDensity S z.1 *
      (‖𝓕 (U : ℝ → ℂ) z.2‖ ^ 2 * Real.cos (2 * Real.pi * (z.2 * z.1))))
        ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hc : Continuous (fun z : ℝ × ℝ => primePolarDensity S z.1 *
      (‖𝓕 (U : ℝ → ℂ) z.2‖ ^ 2 * Real.cos (2 * Real.pi * (z.2 * z.1)))) :=
    ((continuous_primePolarDensity S).comp continuous_fst).mul
      (((_root_.RHTower.continuous_spectralDensity U).comp continuous_snd).mul (by fun_prop))
  apply ((integrableOn_primePolarDensity hS).mul_prod
    (_root_.RHTower.integrable_spectralDensity U)).mono' hc.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (primePolarDensity_nonneg S z.1),
    abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _))
      (primePolarDensity_nonneg S z.1)

private theorem primePolarCutoffSymbol_mul (S t a : ℝ) :
    primePolarCutoffSymbol S t * a =
      2 * ((∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1),
        (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2) *
          primePolarCutoff S (Real.log n)) * (a * Real.cos (t * Real.log n))) -
        ∫ s in Ioi (0 : ℝ), primePolarDensity S s * (a * Real.cos (t * s))) := by
  calc
    _ = 2 * (((∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1),
        ArithmeticFunction.vonMangoldt n * primePolarLagWeight S t (Real.log n)) * a) -
        (∫ s in Ioi (0 : ℝ), (Real.exp s + 1) * primePolarLagWeight S t s) * a) := by
      rw [primePolarCutoffSymbol]
      ring
    _ = _ := by
      rw [Finset.sum_mul, ← integral_mul_const]
      congr 1
      congr 1
      · apply Finset.sum_congr rfl
        intro n _
        dsimp only [primePolarLagWeight]
        ring
      · apply integral_congr_ae
        filter_upwards [] with s
        dsimp only [primePolarLagWeight, primePolarDensity]
        ring

private theorem integrable_primePolar_prime_density (U : SchwartzMap ℝ ℂ) (S : ℝ) :
    Integrable (fun ξ : ℝ => ∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1),
      (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2) *
        primePolarCutoff S (Real.log n)) *
          (‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 * Real.cos (2 * Real.pi * (ξ * Real.log n)))) :=
  integrable_finsetSum _ fun n _ =>
    (integrable_spectralDensity_mul_cos U (Real.log n)).const_mul _

theorem integrable_primePolarCutoffSymbol_density (U : SchwartzMap ℝ ℂ)
    {S : ℝ} (hS : 0 < S) :
    Integrable (fun ξ : ℝ => primePolarCutoffSymbol S (2 * Real.pi * ξ) *
      ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2) := by
  have hi := ((integrable_primePolar_prime_density U S).sub
    (integrable_primePolar_fourier_kernel U hS).integral_prod_right).const_mul 2
  apply hi.congr
  filter_upwards [] with ξ
  rw [primePolarCutoffSymbol_mul]
  simp only [Pi.sub_apply, mul_assoc]

/-- Fourier inversion retains every cutoff prime atom and the entire paired polar density. -/
theorem integral_primePolarCutoffSymbol_density {a S : ℝ}
    (u : SuzukiRestrictedWeilCore a) (hS : 0 < S) :
    (∫ ξ : ℝ, primePolarCutoffSymbol S (2 * Real.pi * ξ) *
      ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2) =
    2 * ((∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1),
      (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2) *
        primePolarCutoff S (Real.log n)) * suzukiCoreAutocorrelation u (Real.log n)) -
      ∫ s in Ioi (0 : ℝ), primePolarDensity S s * suzukiCoreAutocorrelation u s) := by
  have he (ξ : ℝ) : primePolarCutoffSymbol S (2 * Real.pi * ξ) *
      ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 =
      2 * ((∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1),
        (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2) *
          primePolarCutoff S (Real.log n)) *
            (‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 *
              Real.cos (2 * Real.pi * (ξ * Real.log n)))) -
        ∫ s in Ioi (0 : ℝ), primePolarDensity S s *
          (‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 *
            Real.cos (2 * Real.pi * (ξ * s)))) := by
    rw [primePolarCutoffSymbol_mul]
    simp only [mul_assoc]
  simp_rw [he]
  rw [integral_const_mul, integral_sub
    (integrable_primePolar_prime_density _ S)
    (integrable_primePolar_fourier_kernel _ hS).integral_prod_right,
    integral_finsetSum (Finset.range (⌈Real.exp S⌉₊ + 1))
      (fun n _ => (integrable_spectralDensity_mul_cos
        (suzukiRestrictedWeilCoreSchwartz u) (Real.log n)).const_mul
          (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2) *
            primePolarCutoff S (Real.log n))),
    ← integral_integral_swap (integrable_primePolar_fourier_kernel _ hS)]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    rw [integral_const_mul, ← suzukiCoreAutocorrelation_eq_integral_fourier_cos]
  · apply integral_congr_ae
    filter_upwards [] with s
    rw [integral_const_mul, ← suzukiCoreAutocorrelation_eq_integral_fourier_cos]

private theorem coreCorrelation_eq_integral {a : ℝ} (u : SuzukiRestrictedWeilCore a) (s : ℝ) :
    suzukiCoreAutocorrelation u s = ∫ x, u x * u (x + s) := by
  simp only [suzukiCoreAutocorrelation, screwCrossCorr, add_comm]

private theorem coreCorrelation_eq_autocorr {a : ℝ} (u : SuzukiRestrictedWeilCore a) (s : ℝ) :
    suzukiCoreAutocorrelation u s = _root_.RHTower.ArchimedeanAnomaly.autocorr u s := by
  rw [coreCorrelation_eq_integral]
  rfl

private theorem coreCorrelation_cutoff {a S : ℝ} (u : SuzukiRestrictedWeilCore a)
    (hS : 2 * u.supportRadius + 1 ≤ S) (s : ℝ) :
    primePolarCutoff S s * suzukiCoreAutocorrelation u s = suzukiCoreAutocorrelation u s := by
  by_cases hs : s ≤ S - 1
  · rw [primePolarCutoff_eq_one hs, one_mul]
  · have hz : suzukiCoreAutocorrelation u s = 0 :=
      screwCrossCorr_eq_zero_of_support_radius_pos u.support_subset u.support_subset
        (by linarith only [hS, lt_of_not_ge hs])
    rw [hz, mul_zero]

private theorem vonMangoldtAtom_eq_half_density (n : ℕ) :
    vonMangoldtAtom n = ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2) := by
  by_cases hn : 2 ≤ n
  · rw [vonMangoldtAtom, if_pos hn, ArithmeticIncidencePositivity.exp_neg_half_log
      (show (0 : ℝ) < n by exact_mod_cast (by omega : 0 < n)), div_eq_mul_inv]
  · have hsmall : n ≤ 1 := by omega
    interval_cases n <;> simp [vonMangoldtAtom]

/-- The smooth edge leaves the literal complete prime sum unchanged. -/
theorem primeSum_eq_primePolarCutoff_core {a S : ℝ} (u : SuzukiRestrictedWeilCore a)
    (hS : 2 * u.supportRadius + 1 ≤ S) :
    primeSum u = 2 * ∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1),
      (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2) *
        primePolarCutoff S (Real.log n)) * suzukiCoreAutocorrelation u (Real.log n) := by
  have hu : SupportedIn (S / 2) u := by
    intro x hx
    by_contra hn
    have hh := abs_le.mpr (u.support_subset hn)
    linarith only [hS, hx, hh]
  rw [primeSum_eq_sum_of_supportedIn hu]
  have hr : lagRange (S / 2) = ⌈Real.exp S⌉₊ + 1 := by
    rw [lagRange, show 2 * (S / 2) = S by ring]
  rw [hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hm : (∫ x, u x * u (x - Real.log n)) =
      suzukiCoreAutocorrelation u (-Real.log n) := by
    rw [coreCorrelation_eq_integral]
    simp only [sub_eq_add_neg]
  rw [hm, ← coreCorrelation_eq_integral, suzukiCoreAutocorrelation_neg,
    vonMangoldtAtom_eq_half_density]
  calc _ = 2 * (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        suzukiCoreAutocorrelation u (Real.log n) := by ring
    _ = 2 * (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        (primePolarCutoff S (Real.log n) * suzukiCoreAutocorrelation u (Real.log n)) := by
      rw [coreCorrelation_cutoff u hS (Real.log n)]
    _ = _ := by ring

private theorem core_polar_eq_integral {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    2 * coshHalfMoment u ^ 2 - 2 * sinhHalfMoment u ^ 2 =
      4 * ∫ s in Ioi (0 : ℝ), Real.cosh (s / 2) * suzukiCoreAutocorrelation u s := by
  have hu : ContDiff ℝ 2 (u : ℝ → ℝ) :=
    u.smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have he := integral_comp_abs
    (f := fun s => _root_.RHTower.ArchimedeanAnomaly.autocorr u s * Real.cosh (s / 2))
  have hid (s : ℝ) : _root_.RHTower.ArchimedeanAnomaly.autocorr u |s| *
      Real.cosh (|s| / 2) =
        _root_.RHTower.ArchimedeanAnomaly.autocorr u s * Real.cosh (s / 2) := by
    rcases abs_choice s with hs | hs
    · rw [hs]
    · rw [hs, _root_.RHTower.ArchimedeanExactForm.autocorr_neg,
        show -s / 2 = -(s / 2) by ring, Real.cosh_neg]
  simp_rw [hid] at he
  rw [_root_.RHTower.ArchimedeanExactForm.integral_autocorr_mul_cosh hu u.hasCompactSupport] at he
  have hp : Integrable (fun x => Real.exp (x / 2) * u x) :=
    ((by fun_prop : Continuous (fun x : ℝ => Real.exp (x / 2))).mul
      u.continuous).integrable_of_hasCompactSupport u.hasCompactSupport.mul_left
  have hm : Integrable (fun x => Real.exp (-(x / 2)) * u x) :=
    ((by fun_prop : Continuous (fun x : ℝ => Real.exp (-(x / 2)))).mul
      u.continuous).integrable_of_hasCompactSupport u.hasCompactSupport.mul_left
  rw [(halfMoments_eq_exp hp hm).1, (halfMoments_eq_exp hp hm).2]
  have hi : (∫ s in Ioi (0 : ℝ), Real.cosh (s / 2) * suzukiCoreAutocorrelation u s) =
      ∫ s in Ioi (0 : ℝ), _root_.RHTower.ArchimedeanAnomaly.autocorr u s *
        Real.cosh (s / 2) := by
    apply integral_congr_ae
    filter_upwards [] with s
    rw [coreCorrelation_eq_autocorr, mul_comm]
  rw [hi]
  simp only [mul_comm, neg_div] at he ⊢
  nlinarith only [he]

/-- The original prime sum minus both pole moments is the cutoff multiplier pairing. -/
theorem primeSum_sub_poles_eq_primePolarCutoff_integral {a S : ℝ}
    (u : SuzukiRestrictedWeilCore a) (hS : 2 * u.supportRadius + 1 ≤ S) :
    primeSum u - (2 * coshHalfMoment u ^ 2 - 2 * sinhHalfMoment u ^ 2) =
      ∫ ξ : ℝ, primePolarCutoffSymbol S (2 * Real.pi * ξ) *
        ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 := by
  have hSpos : 0 < S := by linarith only [hS, u.supportRadius_nonneg]
  rw [integral_primePolarCutoffSymbol_density u hSpos, primeSum_eq_primePolarCutoff_core u hS,
    core_polar_eq_integral]
  have he (s : ℝ) : primePolarDensity S s * suzukiCoreAutocorrelation u s =
      2 * (Real.cosh (s / 2) * suzukiCoreAutocorrelation u s) := by
    rw [primePolarDensity]
    calc _ = ((Real.exp s + 1) * Real.exp (-s / 2)) *
        (primePolarCutoff S s * suzukiCoreAutocorrelation u s) := by ring
      _ = ((Real.exp s + 1) * (2 * Real.exp (-s / 2))) *
          suzukiCoreAutocorrelation u s / 2 := by rw [coreCorrelation_cutoff u hS s]; ring
      _ = _ := by rw [ArithmeticIncidencePositivity.polarDensity_mul_half_weight]; ring
  simp_rw [he]
  rw [integral_const_mul]
  ring

end GaloisForLFunctions.ArithmeticIndexDescent
