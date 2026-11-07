import GaloisForLFunctions.SelbergClass.Primon.KestenMcKay
import GaloisForLFunctions.HTGeometry.PoissonKernelBound
import GaloisForLFunctions.RHTower.BourgainUnitIntervalTorus
import GaloisForLFunctions.RHTower.RandomEulerObservableFactor

/-!
# Exact logarithmic averaging of the charged local factor

The Kesten–McKay average in Hartnoll–Yang, arXiv:2502.02661v2, (91), follows
from Poisson reproduction of a zero-free affine factor. Phase reflection
replaces the original factor by its even part. Every analytic input follows
from the explicit disk coordinate; no spectral equidistribution is assumed.
-/

open MeasureTheory Set Metric
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Logarithmic denominator of the charged local factor at phase `πt`. -/
def phaseLogDenominator (s t : ℝ) : ℝ :=
  Real.log (1 - 2 * cavityDiskCoordinate s * Real.cos (Real.pi * t) +
    cavityDiskCoordinate s ^ 2)

/-- Logarithmic denominator after pairing opposite charges and phases. -/
def evenPhaseLogDenominator (s t : ℝ) : ℝ :=
  Real.log (1 - 2 * cavityDiskCoordinate s ^ 2 * Real.cos (2 * Real.pi * t) +
    (cavityDiskCoordinate s ^ 2) ^ 2)

private theorem disk_square_lt_one (s : ℝ) : cavityDiskCoordinate s ^ 2 < 1 := by
  have h := pow_lt_one₀ (abs_nonneg (cavityDiskCoordinate s))
    (abs_cavityDiskCoordinate_lt_one s) (by omega : (2 : ℕ) ≠ 0)
  simpa only [sq_abs] using h

private theorem character_eq (t : ℝ) :
    RHTower.bourgainUnitCharacter t =
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  unfold RHTower.bourgainUnitCharacter
  congr 1
  push_cast
  ring

/-- The angular and geometric Poisson kernels agree also at negative real radii. -/
theorem poissonKer_character (q t : ℝ) :
    poissonKer q (2 * Real.pi * t) =
      poissonKernel 0 (q : ℂ) (RHTower.bourgainUnitCharacter t) := by
  rw [character_eq, poissonKernel_def, poissonKer, poissonKer_denom_eq]
  simp only [sub_zero, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, one_pow]

/-- The even denominator is the squared modulus of the existing random Euler factor. -/
theorem evenPhaseLogDenominator_eq_log_norm (s t : ℝ) :
    evenPhaseLogDenominator s t =
      2 * Real.log ‖1 - (cavityDiskCoordinate s : ℂ) ^ 2 *
        RHTower.bourgainUnitCharacter t‖ := by
  have hn := GaloisForLFunctions.RHTower.normSq_one_sub_randomEulerLogArg
    (cavityDiskCoordinate s ^ 2) t
  rw [Complex.ofReal_pow, ← character_eq] at hn
  rw [evenPhaseLogDenominator, ← hn, Real.log_pow]
  norm_num

/-- Poisson averaging of the even local logarithm evaluates it at the disk point. -/
theorem integral_poisson_evenPhaseLog (s u : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, poissonKer (cavityDiskCoordinate u) (2 * Real.pi * t) *
      evenPhaseLogDenominator s t) =
      2 * Real.log (1 - cavityDiskCoordinate s ^ 2 * cavityDiskCoordinate u) := by
  let r := cavityDiskCoordinate s
  let q := cavityDiskCoordinate u
  let f : ℂ → ℂ := fun z => 1 - (r : ℂ) ^ 2 * z
  have hr : r ^ 2 < 1 := disk_square_lt_one s
  have hdiff : Differentiable ℂ f := by dsimp [f]; fun_prop
  have ha : AnalyticOnNhd ℂ f (closedBall 0 1) := by
    intro z _
    exact hdiff.differentiableOn.analyticAt Filter.univ_mem
  have hzero : ∀ z ∈ closedBall (0 : ℂ) 1, f z ≠ 0 := by
    intro z hz he
    have hz1 : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hz
    have hn : ‖(r : ℂ) ^ 2 * z‖ < 1 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact (mul_le_mul_of_nonneg_left hz1 (sq_nonneg r)).trans_lt (by simpa using hr)
    have heq := congrArg norm (sub_eq_zero.mp he)
    rw [norm_one] at heq
    linarith
  have hw : (q : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball, dist_eq_norm, Complex.norm_real, Real.norm_eq_abs, q] using
      abs_cavityDiskCoordinate_lt_one u
  have hrep := circleAverage_poissonKernel_log_norm ha hzero hw
  rw [RHTower.circleAverage_zero_one_eq_unitInterval,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hrep
  simp only [smul_eq_mul, Pi.mul_apply] at hrep
  have hpos : 0 < 1 - r ^ 2 * q := by
    have hq : q ≤ 1 := (le_abs_self q).trans (abs_cavityDiskCoordinate_lt_one u).le
    have hm := mul_le_mul_of_nonneg_left hq (sq_nonneg r)
    nlinarith only [hr, hm]
  have hcast : f (q : ℂ) = ((1 - r ^ 2 * q : ℝ) : ℂ) := by
    dsimp [f]
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hrep
  have he : (fun t => poissonKer q (2 * Real.pi * t) * evenPhaseLogDenominator s t) =
      fun t => 2 * (poissonKernel 0 (q : ℂ) (RHTower.bourgainUnitCharacter t) *
        Real.log ‖f (RHTower.bourgainUnitCharacter t)‖) := by
    funext t
    rw [poissonKer_character, evenPhaseLogDenominator_eq_log_norm]
    dsimp [f, r]
    ring
  change (∫ t in Ioo (0 : ℝ) 1, poissonKer q (2 * Real.pi * t) *
    evenPhaseLogDenominator s t) = _
  rw [he, integral_const_mul, hrep]

/-- The even logarithmic local factor has zero uniform angular mean. -/
theorem integral_evenPhaseLogDenominator (s : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, evenPhaseLogDenominator s t) = 0 := by
  simpa [cavityDiskCoordinate, poissonKer] using integral_poisson_evenPhaseLog s 0

theorem continuous_phaseLogDenominator (s : ℝ) : Continuous (phaseLogDenominator s) := by
  unfold phaseLogDenominator
  apply Continuous.log (by fun_prop)
  intro t
  exact (poissonKer_denom_pos (abs_cavityDiskCoordinate_lt_one s) (Real.pi * t)).ne'

theorem continuous_evenPhaseLogDenominator (s : ℝ) :
    Continuous (evenPhaseLogDenominator s) := by
  unfold evenPhaseLogDenominator
  apply Continuous.log (by fun_prop)
  intro t
  exact (poissonKer_denom_pos (by
    rw [abs_of_nonneg (sq_nonneg _)]; exact disk_square_lt_one s) (2 * Real.pi * t)).ne'

/-- Pairing reflected phases turns a degree-two factor into its even local factor. -/
theorem phaseLogDenominator_reflection_sum (s t : ℝ) :
    phaseLogDenominator s t + phaseLogDenominator s (1 - t) =
      evenPhaseLogDenominator s t := by
  let r := cavityDiskCoordinate s
  have hc : Real.cos (Real.pi * (1 - t)) = -Real.cos (Real.pi * t) := by
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring,
      Real.cos_sub, Real.cos_pi, Real.sin_pi]
    ring
  have he : (1 - 2 * r * Real.cos (Real.pi * t) + r ^ 2) *
      (1 - 2 * r * Real.cos (Real.pi * (1 - t)) + r ^ 2) =
      1 - 2 * r ^ 2 * Real.cos (2 * Real.pi * t) + (r ^ 2) ^ 2 := by
    rw [hc, show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.cos_two_mul]
    ring
  have h1 := poissonKer_denom_pos (abs_cavityDiskCoordinate_lt_one s) (Real.pi * t)
  have h2 := poissonKer_denom_pos (abs_cavityDiskCoordinate_lt_one s) (Real.pi * (1 - t))
  unfold phaseLogDenominator evenPhaseLogDenominator
  rw [← he, Real.log_mul h1.ne' h2.ne']

/-- The prime Poisson radius is an explicit cavity disk coordinate. -/
theorem cavityDiskCoordinate_prime_inverse (p : Nat.Primes) :
    cavityDiskCoordinate ((p : ℝ) - 1)⁻¹ = (p : ℝ)⁻¹ := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hs : 0 < (p : ℝ) - 1 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
  rw [cavityDiskCoordinate, abs_of_pos (inv_pos.mpr hs)]
  field_simp [hs.ne', hp0]
  ring

/-- Exact Kesten–McKay averaging of the even logarithmic factor. -/
theorem integral_kesten_evenPhaseLog (p : Nat.Primes) (s : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * evenPhaseLogDenominator s t) =
      -((p : ℝ) - 1) * Real.log (1 - cavityDiskCoordinate s ^ 2 / (p : ℝ)) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hr0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hr1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hp
  have hE : IntegrableOn (evenPhaseLogDenominator s) (Ioo (0 : ℝ) 1) :=
    (continuous_evenPhaseLogDenominator s).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hP : Continuous (fun t : ℝ => poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t)) :=
    (poissonKer_continuous (by rwa [abs_of_nonneg hr0])).comp (by fun_prop)
  have hPE : IntegrableOn (fun t => poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t) *
      evenPhaseLogDenominator s t) (Ioo (0 : ℝ) 1) :=
    (hP.mul (continuous_evenPhaseLogDenominator s)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have he : (fun t => kestenMcKayDensity p t * evenPhaseLogDenominator s t) =
      fun t => ((p : ℝ) + 1) / 2 * evenPhaseLogDenominator s t -
        ((p : ℝ) - 1) / 2 *
          (poissonKer (p : ℝ)⁻¹ (2 * Real.pi * t) * evenPhaseLogDenominator s t) := by
    funext t
    rw [kestenMcKayDensity_eq_poisson]
    ring
  have hrep := integral_poisson_evenPhaseLog s ((p : ℝ) - 1)⁻¹
  rw [cavityDiskCoordinate_prime_inverse] at hrep
  rw [he, integral_sub (hE.const_mul _) (hPE.const_mul _), integral_const_mul,
    integral_const_mul, integral_evenPhaseLogDenominator, hrep]
  simp only [div_eq_mul_inv]
  ring

/-- Every observable has the same Kesten–McKay mean after phase reflection. -/
theorem integral_kesten_reflection (p : Nat.Primes) (f : ℝ → ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * f (1 - t)) =
      ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * f t := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
    (fun t => kestenMcKayDensity p t * f t) 1
  simpa only [sub_self, sub_zero, kestenMcKayDensity_reflection,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] using h

/-- The full logarithmic average of the charged local factor is the fermionic
logarithm with exponent `(p-1)/2`, including the exceptional prime two. -/
theorem integral_kesten_log_local_factor (p : Nat.Primes) (s : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * (-phaseLogDenominator s t)) =
      ((p : ℝ) - 1) / 2 * Real.log (1 - cavityDiskCoordinate s ^ 2 / (p : ℝ)) := by
  have hi : IntegrableOn (fun t => kestenMcKayDensity p t * phaseLogDenominator s t)
      (Ioo (0 : ℝ) 1) :=
    ((continuous_kestenMcKayDensity p).mul (continuous_phaseLogDenominator s)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hj : IntegrableOn (fun t => kestenMcKayDensity p t * phaseLogDenominator s (1 - t))
      (Ioo (0 : ℝ) 1) :=
    ((continuous_kestenMcKayDensity p).mul
      ((continuous_phaseLogDenominator s).comp (by fun_prop))).continuousOn.integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
  have hsum : (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * evenPhaseLogDenominator s t) =
      2 * (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * phaseLogDenominator s t) := by
    have he : (fun t => kestenMcKayDensity p t * evenPhaseLogDenominator s t) =
        fun t => kestenMcKayDensity p t * phaseLogDenominator s t +
          kestenMcKayDensity p t * phaseLogDenominator s (1 - t) := by
      funext t
      rw [← phaseLogDenominator_reflection_sum]
      ring
    rw [he, integral_add hi hj, integral_kesten_reflection]
    ring
  rw [integral_kesten_evenPhaseLog] at hsum
  simp_rw [mul_neg]
  rw [integral_neg]
  linarith only [hsum]

end
end GaloisForLFunctions.SelbergClass.Primon
