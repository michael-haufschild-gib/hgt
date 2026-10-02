import GaloisForLFunctions.RHTower.MobiusDivisorCriticalContinuousLogMoments
import GaloisForLFunctions.RHTower.CriticalAbelRoutePAsymptoticBridge
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Absolute boundary moments of the literal critical Abel source

In logarithmic coordinates the normalized Abel source is the positive-time
convolution of the actual Chebyshev defect with an exponential kernel. The
exact quadratic moment identity gives the absolute boundary domination needed
to differentiate the retained old-cutoff prime term.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private def criticalAbelLogSource (t : ℝ) : ℝ :=
  Real.exp (-t) * psiDefect ⌊Real.exp t⌋₊

private def criticalAbelLogKernel (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp (-(3 * t / 2))

private theorem exp_integrable_iff (f : ℝ → ℝ) :
    IntegrableOn f (Ioi (1 : ℝ)) ↔
      IntegrableOn (fun t : ℝ => Real.exp t * f (Real.exp t)) (Ioi (0 : ℝ)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun a _ b _ hab => Real.exp_injective hab) f
  simpa only [Real.image_exp_Ioi, Real.exp_zero, abs_of_pos (Real.exp_pos _),
    smul_eq_mul] using h

private theorem criticalAbelLogSource_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * criticalAbelLogSource t) (Ioi (0 : ℝ)) := by
  have hi := (exp_integrable_iff
    (fun x : ℝ => |psiDefect ⌊x⌋₊| * Real.log x ^ k / x ^ (2 : ℕ))).mp
      (integrableOn_psiDefect_floor_log_moment k)
  have hm : Measurable (fun t : ℝ => t ^ k * criticalAbelLogSource t) := by
    have hp : Measurable (fun t : ℝ => psiDefect ⌊Real.exp t⌋₊) :=
      (measurable_of_countable psiDefect).comp Real.measurable_exp.nat_floor
    exact (measurable_id.pow_const k).mul
      ((Real.measurable_exp.comp measurable_id.neg).mul hp)
  apply hi.mono' hm.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  rw [Real.norm_eq_abs, criticalAbelLogSource, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg ht.le k), abs_of_pos (Real.exp_pos _), Real.log_exp,
    Real.exp_neg]
  exact le_of_eq (by field_simp [Real.exp_ne_zero t])

private theorem criticalAbelLogKernel_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * criticalAbelLogKernel t) (Ioi (0 : ℝ)) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (k : ℝ)) (b := (3 / 2 : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num) (by norm_num)
  apply IntegrableOn.congr_fun (hi.const_mul (1 / 2 : ℝ)) _ measurableSet_Ioi
  intro t _
  simp only [Real.rpow_natCast, Real.rpow_one, criticalAbelLogKernel]
  rw [show -(3 / 2 : ℝ) * t = -(3 * t / 2) by ring]
  ring

private def criticalAbelMomentConvolution (i j : ℕ) : ℝ → ℝ :=
  posConvolution (fun t => t ^ i * criticalAbelLogSource t)
    (fun t => t ^ j * criticalAbelLogKernel t) (ContinuousLinearMap.mul ℝ ℝ)

private theorem criticalAbelMomentConvolution_integrable (i j : ℕ) :
    Integrable (criticalAbelMomentConvolution i j) :=
  integrable_posConvolution (criticalAbelLogSource_moment_integrable i)
    (criticalAbelLogKernel_moment_integrable j) (ContinuousLinearMap.mul ℝ ℝ)

private theorem criticalAbelMomentConvolution_eq {T : ℝ} (hT : 0 < T) (i j : ℕ) :
    criticalAbelMomentConvolution i j T =
      ∫ t in (0 : ℝ)..T, (t ^ i * criticalAbelLogSource t) *
        ((T - t) ^ j * criticalAbelLogKernel (T - t)) := by
  simp [criticalAbelMomentConvolution, posConvolution, hT]

private theorem criticalAbelMomentConvolution_intervalIntegrable
    {T : ℝ} (hT : 0 < T) (i j : ℕ) :
    IntervalIntegrable (fun t : ℝ => (t ^ i * criticalAbelLogSource t) *
      ((T - t) ^ j * criticalAbelLogKernel (T - t))) volume 0 T := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ i * criticalAbelLogSource t)
      volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    exact (criticalAbelLogSource_moment_integrable i).mono_set Ioc_subset_Ioi_self
  apply hi.mul_continuousOn
  have hc : Continuous (fun t : ℝ => (T - t) ^ j * criticalAbelLogKernel (T - t)) := by
    dsimp [criticalAbelLogKernel]
    fun_prop
  exact hc.continuousOn

private theorem criticalAbelMomentConvolution_sq {T : ℝ} (hT : 0 < T) :
    T ^ (2 : ℕ) * criticalAbelMomentConvolution 0 0 T =
      criticalAbelMomentConvolution 2 0 T +
        2 * criticalAbelMomentConvolution 1 1 T +
          criticalAbelMomentConvolution 0 2 T := by
  have h20 := criticalAbelMomentConvolution_intervalIntegrable hT 2 0
  have h11 := criticalAbelMomentConvolution_intervalIntegrable hT 1 1
  have h02 := criticalAbelMomentConvolution_intervalIntegrable hT 0 2
  rw [criticalAbelMomentConvolution_eq hT 0 0,
    criticalAbelMomentConvolution_eq hT 2 0,
    criticalAbelMomentConvolution_eq hT 1 1,
    criticalAbelMomentConvolution_eq hT 0 2]
  simp only [pow_zero, pow_one, one_mul] at h20 h11 h02 ⊢
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add h20 (h11.const_mul 2),
    ← intervalIntegral.integral_add (h20.add (h11.const_mul 2)) h02]
  apply intervalIntegral.integral_congr
  intro t _
  ring

private theorem criticalAbelMomentConvolution_zero_eq {T : ℝ} (hT : 0 < T) :
    criticalAbelMomentConvolution 0 0 T =
      Real.exp (-(3 * T / 2)) * criticalContinuousAbel (Real.exp T) := by
  rw [criticalAbelMomentConvolution_eq hT 0 0]
  simp only [pow_zero, one_mul]
  calc
    (∫ t in (0 : ℝ)..T, criticalAbelLogSource t * criticalAbelLogKernel (T - t)) =
        ∫ t in (0 : ℝ)..T, ((1 / 2 : ℝ) * Real.exp (-(3 * T / 2))) *
          (Real.exp (t / 2) * psiDefect ⌊Real.exp t⌋₊) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [criticalAbelLogSource, criticalAbelLogKernel]
      calc
        _ = (1 / 2 : ℝ) *
            (Real.exp (-t) * Real.exp (-(3 * (T - t) / 2))) *
              psiDefect ⌊Real.exp t⌋₊ := by ring
        _ = _ := by
          rw [← Real.exp_add,
            show -t + -(3 * (T - t) / 2) = -(3 * T / 2) + t / 2 by ring,
            Real.exp_add]
          ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        ← criticalContinuousAbel_exp_eq_log_integral hT.le]
      ring

private theorem criticalAbelMomentConvolution_sq_integrable :
    IntegrableOn (fun T : ℝ => T ^ (2 : ℕ) * criticalAbelMomentConvolution 0 0 T)
      (Ioi (0 : ℝ)) := by
  have hi := ((criticalAbelMomentConvolution_integrable 2 0).add
    ((criticalAbelMomentConvolution_integrable 1 1).const_mul 2)).add
      (criticalAbelMomentConvolution_integrable 0 2)
  exact hi.integrableOn.congr_fun
    (fun T hT => (criticalAbelMomentConvolution_sq hT).symm) measurableSet_Ioi

/-- The literal Abel source has an absolutely integrable quadratic logarithmic
moment at the boundary, including the unweighted term. This dominates the
derivative of the omitted old-cutoff prime contribution. -/
theorem integrableOn_criticalContinuousAbel_boundary_log_sq :
    IntegrableOn (fun x : ℝ => |criticalContinuousAbel x| *
      (1 + Real.log x ^ (2 : ℕ)) / x ^ (5 / 2 : ℝ)) (Ioi (1 : ℝ)) := by
  apply (exp_integrable_iff _).mpr
  have hi := (criticalAbelMomentConvolution_integrable 0 0).norm.integrableOn.add
    criticalAbelMomentConvolution_sq_integrable.norm
  apply hi.congr_fun _ measurableSet_Ioi
  intro T hT
  change 0 < T at hT
  have hw : Real.exp T / (Real.exp T) ^ (5 / 2 : ℝ) =
      Real.exp (-(3 * T / 2)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos T), Real.log_exp, ← Real.exp_sub]
    congr 1
    ring
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg T), criticalAbelMomentConvolution_zero_eq hT,
    abs_mul, abs_of_pos (Real.exp_pos _), Real.log_exp]
  calc
    Real.exp (-(3 * T / 2)) * |criticalContinuousAbel (Real.exp T)| +
        T ^ (2 : ℕ) * (Real.exp (-(3 * T / 2)) *
          |criticalContinuousAbel (Real.exp T)|) =
      (Real.exp T / (Real.exp T) ^ (5 / 2 : ℝ)) *
        |criticalContinuousAbel (Real.exp T)| * (1 + T ^ (2 : ℕ)) := by rw [hw]; ring
    _ = _ := by ring

end RHTower
