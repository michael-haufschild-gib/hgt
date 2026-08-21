import GaloisForLFunctions.RHTower.Sieve.MaynardMellinWaveletCalibration

/-!
# Exact physical-scale covariance of the Route-T Mellin window

The physical base, target width, and integration coordinate must be dilated together.  The
resulting normalized Mellin kernel is one fixed relative-shape coefficient times the exact Mellin
character of the physical scale.  This is the coherence needed before applying spatial `L²`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex
open GaloisForLFunctions.HTGeometry

/-- A common positive dilation leaves the smooth cutoff's relative profile unchanged. -/
theorem smoothWeight_mul_scale
    (lambda N H x : ℝ) (hlambda : 0 < lambda) :
    smoothWeight (lambda * N) (lambda * H) (lambda * x) = smoothWeight N H x := by
  rw [smoothWeight, smoothWeight]
  congr 2
  field_simp [hlambda.ne']

/-- A common positive dilation leaves the adjacent Route-T window's relative profile unchanged. -/
theorem routeTSmoothWindowWeight_mul_scale
    (lambda N H x : ℝ) (hlambda : 0 < lambda) :
    routeTSmoothWindowWeight (lambda * N) (lambda * H) (lambda * x) =
      routeTSmoothWindowWeight N H x := by
  rw [routeTSmoothWindowWeight, routeTSmoothWindowWeight]
  rw [show lambda * N + lambda * H = lambda * (N + H) by ring]
  rw [smoothWeight_mul_scale lambda (N + H) H x hlambda,
    smoothWeight_mul_scale lambda N H x hlambda]

/-- The scaled adjacent window is the fixed relative window evaluated at inverse scale. -/
theorem routeTSmoothWindowWeight_mul_scale_argument
    (lambda N H x : ℝ) (hlambda : 0 < lambda) :
    routeTSmoothWindowWeight (lambda * N) (lambda * H) x =
      routeTSmoothWindowWeight N H (lambda⁻¹ * x) := by
  have h := routeTSmoothWindowWeight_mul_scale lambda N H (lambda⁻¹ * x) hlambda
  convert h using 1
  field_simp [hlambda.ne']

/-- Raw adjacent-window Mellin transforms carry the exact physical-scale character `lambda^s`. -/
theorem mellin_routeTSmoothWindowWeight_mul_scale
    (lambda N H : ℝ) (s : ℂ) (hlambda : 0 < lambda) :
    mellin (fun x : ℝ =>
        ((routeTSmoothWindowWeight (lambda * N) (lambda * H) x : ℝ) : ℂ)) s =
      (lambda : ℂ) ^ s *
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s := by
  let f : ℝ → ℂ := fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)
  have hfun : (fun x : ℝ =>
      ((routeTSmoothWindowWeight (lambda * N) (lambda * H) x : ℝ) : ℂ)) =
      fun x : ℝ => f (lambda⁻¹ * x) := by
    funext x
    simpa only [f] using congrArg (fun r : ℝ => (r : ℂ))
      (routeTSmoothWindowWeight_mul_scale_argument lambda N H x hlambda)
  rw [hfun, mellin_comp_mul_left f s (inv_pos.mpr hlambda)]
  change (((lambda⁻¹ : ℝ) : ℂ) ^ (-s)) * mellin f s =
    (lambda : ℂ) ^ s * mellin f s
  have harg : (lambda : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hlambda.le]
    exact ne_of_lt Real.pi_pos
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  congr 2
  ring

/-- Width normalization lowers the physical Mellin character by exactly one degree. -/
theorem routeTNormalizedSmoothWindowMellin_mul_scale
    (lambda N H : ℝ) (s : ℂ) (hlambda : 0 < lambda) (hH : 0 < H) :
    routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H) s =
      (lambda : ℂ) ^ (s - 1) * routeTNormalizedSmoothWindowMellin N H s := by
  rw [routeTNormalizedSmoothWindowMellin, routeTNormalizedSmoothWindowMellin,
    mellin_routeTSmoothWindowWeight_mul_scale lambda N H s hlambda]
  rw [show s - 1 = s + (-1) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hlambda.ne'),
    Complex.cpow_neg_one, Complex.ofReal_mul]
  field_simp [hlambda.ne', hH.ne']

/-- Target-reference subtraction preserves one fixed relative defect under physical dilation. -/
theorem routeTNormalizedSmoothWindowMellin_defect_mul_scale
    (lambda N R H : ℝ) (s : ℂ) (hlambda : 0 < lambda)
    (hR : 0 < R) (hH : 0 < H) :
    routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R) s -
        routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H) s =
      (lambda : ℂ) ^ (s - 1) *
        (routeTNormalizedSmoothWindowMellin N R s -
          routeTNormalizedSmoothWindowMellin N H s) := by
  rw [routeTNormalizedSmoothWindowMellin_mul_scale lambda N R s hlambda hR,
    routeTNormalizedSmoothWindowMellin_mul_scale lambda N H s hlambda hH]
  ring

end RHTower.Sieve
