import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeBoundaryHasItsMeanPole
import GaloisForLFunctions.RHTower.ConstrainedWeilFourierMultiplier
import GaloisForLFunctions.RHTower.VonMangoldtLineSeriesSwap
import GaloisForLFunctions.ArithmeticElectrostatics.TheExternalFieldIsAPrimeSum

/-!
# The literal square-prime source and its Fourier boundary

Absolute Dirichlet summation gives the damped arithmetic identity. Compact
correlation support removes damping on the literal source. The regular
boundary converges in its original Schwartz pairing, while its pole leaves
exactly half the squared mean.
-/

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform SchwartzMap Complex
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticFunction ArithmeticElectrostatics
open GaloisForLFunctions.RHTower

/-- The damped literal even-power source, in its exact prime-log correlation coordinates. -/
def dampedSquarePrimeSource (u : SchwartzMap ℝ ℂ) (σ : ℝ) : ℝ :=
  2 * ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-σ) *
    (autocorrelationSchwartz u (2 * Real.log n)).re

/-- Fourier inversion and absolutely convergent Dirichlet summation identify the damped source. -/
theorem dampedSquarePrimeSource_eq_integral (u : SchwartzMap ℝ ℂ)
    {σ : ℝ} (hσ : 1 < σ) :
    dampedSquarePrimeSource u σ =
      ∫ ξ : ℝ, 2 * (LSeries (fun n => (vonMangoldt n : ℂ))
        ((σ : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I)).re *
          ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2 := by
  let w : ℕ → ℝ := fun n => vonMangoldt n * (n : ℝ) ^ (-σ)
  let ρ : ℝ → ℝ := fun ξ => ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2
  let f : ℕ → ℝ → ℝ := fun n ξ => w n *
    (ρ ξ * Real.cos (2 * Real.pi * (ξ * (2 * Real.log n))))
  have hw (n : ℕ) : 0 ≤ w n := mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hρ : Integrable ρ := integrable_spectralDensity u
  have hf (n : ℕ) : Integrable (f n) :=
    (integrable_spectralDensity_mul_cos u (2 * Real.log n)).const_mul (w n)
  have hbound (n : ℕ) (ξ : ℝ) : ‖f n ξ‖ ≤ w n * ρ ξ := by
    rw [f, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n), abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)) (hw n)
  have hsum : Summable (fun n : ℕ => ∫ ξ : ℝ, ‖f n ξ‖) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ξ => norm_nonneg _))
      (fun n => ?_) ((summable_vonMangoldt_mul_rpow hσ).mul_right (∫ ξ : ℝ, ρ ξ))
    calc
      _ ≤ ∫ ξ : ℝ, w n * ρ ξ := integral_mono (hf n).norm (hρ.const_mul _) (hbound n)
      _ = _ := integral_const_mul _ _
  have hswap := integral_tsum_of_summable_integral_norm hf hsum
  have hsingle (n : ℕ) : (∫ ξ : ℝ, f n ξ) =
      w n * (autocorrelationSchwartz u (2 * Real.log n)).re := by
    rw [autocorrelationSchwartz_re_eq_integral_cos, ← integral_const_mul]
    rfl
  have hpoint (ξ : ℝ) : (∑' n : ℕ, f n ξ) =
      (LSeries (fun n => (vonMangoldt n : ℂ))
        ((σ : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I)).re * ρ ξ := by
    rw [re_LSeries_vonMangoldt_eq (by simpa using hσ)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]
    rw [← tsum_mul_right]
    apply tsum_congr
    intro n
    have ha : 2 * Real.pi * (ξ * (2 * Real.log n)) =
        (4 * Real.pi * ξ) * Real.log n := by ring
    dsimp only [f, w]
    rw [ha]
    ring
  have he : (∑' n : ℕ, w n * (autocorrelationSchwartz u (2 * Real.log n)).re) =
      ∫ ξ : ℝ, (LSeries (fun n => (vonMangoldt n : ℂ))
        ((σ : ℂ) + ((4 * Real.pi * ξ : ℝ) : ℂ) * I)).re * ρ ξ := by
    rw [← tsum_congr hsingle, hswap]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [dampedSquarePrimeSource]
  change 2 * (∑' n : ℕ, w n * (autocorrelationSchwartz u (2 * Real.log n)).re) = _
  rw [he, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  dsimp only [ρ]
  ring

/-- Squaring the integer lag gives exactly the original critical even-power coefficient. -/
theorem square_prime_coefficient (n : ℕ) :
    2 * vonMangoldt (n ^ 2) / Real.sqrt ((n ^ 2 : ℕ) : ℝ) =
      2 * vonMangoldt n / (n : ℝ) := by
  rw [vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0), Nat.cast_pow,
    Real.sqrt_sq (Nat.cast_nonneg n)]

private theorem core_schwartz_autocorrelation_re {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) (h : ℝ) :
    (autocorrelationSchwartz (suzukiRestrictedWeilCoreSchwartz u) h).re =
      suzukiCoreAutocorrelation u h := by
  have he : (suzukiCoreAutocorrelation u h : ℂ) =
      autocorrelationSchwartz (suzukiRestrictedWeilCoreSchwartz u) h := by
    rw [← suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_ofReal]
    rfl
  simpa only [Complex.ofReal_re] using (congrArg Complex.re he).symm

/-- Compact support cuts off the actual square-prime correlations before any damping is imposed. -/
theorem exists_squarePrime_correlation_cutoff {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → suzukiCoreAutocorrelation u (2 * Real.log n) = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp u.supportRadius)
  refine ⟨N, ?_⟩
  intro n hn
  have he : Real.exp u.supportRadius < (n : ℝ) := hN.trans_le (Nat.cast_le.mpr hn)
  have hnpos : (0 : ℝ) < n := (Real.exp_pos _).trans he
  have hl : u.supportRadius < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr he
  exact screwCrossCorr_eq_zero_of_support_radius_pos u.support_subset u.support_subset
    (by linarith only [hl])

/-- The literal critical even-power prime source includes every part of the original profile. -/
def squarePrimeSource (f : ℝ → ℝ) : ℝ :=
  2 * ∑' n : ℕ, (vonMangoldt n / (n : ℝ)) *
    screwCrossCorr f f (2 * Real.log n)

theorem dampedSquarePrimeSource_one {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    dampedSquarePrimeSource (suzukiRestrictedWeilCoreSchwartz u) 1 = squarePrimeSource u := by
  unfold dampedSquarePrimeSource squarePrimeSource
  congr 1
  apply tsum_congr
  intro n
  rw [core_schwartz_autocorrelation_re, Real.rpow_neg_one, div_eq_mul_inv]

/-- Damping removal on the literal source is a finite sum limit with its original coefficients. -/
theorem continuous_dampedSquarePrimeSource_core {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Continuous (dampedSquarePrimeSource (suzukiRestrictedWeilCoreSchwartz u)) := by
  obtain ⟨N, hN⟩ := exists_squarePrime_correlation_cutoff u
  have he (σ : ℝ) : dampedSquarePrimeSource (suzukiRestrictedWeilCoreSchwartz u) σ =
      2 * ∑ n ∈ Finset.range N, vonMangoldt n * (n : ℝ) ^ (-σ) *
        suzukiCoreAutocorrelation u (2 * Real.log n) := by
    unfold dampedSquarePrimeSource
    simp_rw [core_schwartz_autocorrelation_re]
    congr 1
    apply tsum_eq_sum
    intro n hn
    rw [hN n (by simpa only [Finset.mem_range, not_lt] using hn), mul_zero]
  simp_rw [he]
  apply Continuous.const_mul
  apply continuous_finset_sum
  intro n _
  by_cases hn : n = 0
  · subst n
    simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp_rw [Real.rpow_def_of_pos hnpos]
    fun_prop


/-- The damped literal source splits into its original pole and regular boundary. -/
theorem dampedSquarePrimeSource_eq_pole_add_regular (u : SchwartzMap ℝ ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    dampedSquarePrimeSource u (1 + 4 * Real.pi * ε) =
      (∫ ξ : ℝ, squarePrimePoleMultiplier ε ξ * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2) +
        ∫ ξ : ℝ, regularSquareDampedSpectralDensity u ε ξ := by
  have hσ : 1 < 1 + 4 * Real.pi * ε := by positivity
  rw [dampedSquarePrimeSource_eq_integral u hσ,
    ← integral_add (integrable_squarePrimePole_spectralDensity u hε)
      (integrable_regularSquareDampedSpectralDensity u hε.le)]
  apply integral_congr_ae
  filter_upwards with ξ
  let s : ℂ := ((1 + 4 * Real.pi * ε : ℝ) : ℂ) +
    ((4 * Real.pi * ξ : ℝ) : ℂ) * I
  have hs : 1 < s.re := by simpa [s] using hσ
  have hs1 : s ≠ 1 := fun he => by simpa [he] using hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hp := congrArg Complex.re (RHTower.Sieve.neg_logDeriv_riemannZeta_eq_of_ne_zero hs1 hz)
  have he : s - 1 = ((4 * Real.pi * ε : ℝ) : ℂ) +
      ((4 * Real.pi * ξ : ℝ) : ℂ) * I := by dsimp [s]; push_cast; ring
  rw [Complex.neg_re, Complex.add_re, he] at hp
  change 2 * (LSeries (fun n => (vonMangoldt n : ℂ)) s).re * _ = _
  rw [re_LSeries_vonMangoldt_eq_neg hs]
  unfold squarePrimePoleMultiplier regularSquareDampedSpectralDensity
  dsimp only [s] at hp
  linarith only [congrArg (fun x : ℝ => 2 * x * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2) hp]

/-- The literal critical square-prime source equals its regular Fourier boundary plus half its mean square. -/
theorem squarePrimeSource_eq_regular_add_mean {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    squarePrimeSource u =
      (∫ ξ : ℝ, regularSquareDampedSpectralDensity (suzukiRestrictedWeilCoreSchwartz u) 0 ξ) +
        (1 / 2 : ℝ) * ‖∫ x : ℝ, suzukiRestrictedWeilCoreSchwartz u x‖ ^ 2 := by
  let U := suzukiRestrictedWeilCoreSchwartz u
  have hpath : Tendsto (fun ε : ℝ => 1 + 4 * Real.pi * ε)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 1) := by
    have h : ContinuousAt (fun ε : ℝ => 1 + 4 * Real.pi * ε) 0 := by fun_prop
    simpa using h.mono_left nhdsWithin_le_nhds
  have hleft := (continuous_dampedSquarePrimeSource_core u).continuousAt.tendsto.comp hpath
  rw [dampedSquarePrimeSource_one] at hleft
  have hright := (tendsto_squarePrime_pole_meanSquare U).add
    (tendsto_integral_regularSquareDampedSpectralDensity U)
  have he : (fun ε : ℝ => dampedSquarePrimeSource U (1 + 4 * Real.pi * ε)) =ᶠ[
      nhdsWithin 0 (Ioi (0 : ℝ))]
      (fun ε => (∫ ξ : ℝ, squarePrimePoleMultiplier ε ξ * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2) +
        ∫ ξ : ℝ, regularSquareDampedSpectralDensity U ε ξ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact dampedSquarePrimeSource_eq_pole_add_regular U hε
  have hlim := tendsto_nhds_unique hleft (hright.congr' he.symm)
  simpa only [U, add_comm] using hlim


end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.dampedSquarePrimeSource_eq_integral
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.continuous_dampedSquarePrimeSource_core

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.squarePrimeSource_eq_regular_add_mean
