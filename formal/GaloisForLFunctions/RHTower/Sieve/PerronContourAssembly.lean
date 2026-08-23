import GaloisForLFunctions.RHTower.Sieve.PerronHorizontalSide
import GaloisForLFunctions.RHTower.Sieve.ContourShiftIdentity
import GaloisForLFunctions.RHTower.Sieve.PerronRectangleResidueUnderRH

/-!
# Assembling the shifted contour

The shift identity, divided by `2πi`, says that the normalised vertical integral at the Perron
abscissa is the residue plus the normalised integrals over the other three sides.  Under the Riemann
hypothesis the residue is `x`, so the whole discrepancy is the three side integrals.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

theorem norm_two_pi_I_inv : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I))‖ = 1 / (2 * Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  norm_num

/-- **The shifted contour, assembled.**  Under the Riemann hypothesis the normalised vertical
integral at the Perron abscissa differs from `x` by the three remaining sides. -/
theorem norm_vIntegral'_perron_sub_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    {σ₁ σ₀ T : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT : 0 < T) :
    ‖VIntegral' (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
          σ₀ (-T) T - (x : ℂ)‖
      ≤ (1 / (2 * Real.pi))
        * (‖VIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
              * ((x : ℂ) ^ s / s)) σ₁ (-T) T‖
          + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
              * ((x : ℂ) ^ s / s)) σ₁ σ₀ T‖
          + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
              * ((x : ℂ) ^ s / s)) σ₁ σ₀ (-T)‖) := by
  set f : ℂ → ℂ := fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s) with hf
  have hshift := vIntegral_shift f σ₁ σ₀ T
  have hres := rectangleIntegral_perron_eq hRH hx hσ₁ hσ₁1 hσ₀ hT
  have hexp : VIntegral' f σ₀ (-T) T - (x : ℂ)
      = (1 / (2 * (Real.pi : ℂ) * Complex.I))
        • (VIntegral f σ₁ (-T) T + HIntegral f σ₁ σ₀ T - HIntegral f σ₁ σ₀ (-T)) := by
    rw [VIntegral', hshift, ← hres, RectangleIntegral', ← hf, ← smul_sub]
    congr 1
    ring
  rw [hexp, norm_smul, norm_two_pi_I_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sub_le _ _) ?_
  refine add_le_add (le_trans (norm_add_le _ _) (by linarith)) le_rfl

end

end RHTower.Sieve
