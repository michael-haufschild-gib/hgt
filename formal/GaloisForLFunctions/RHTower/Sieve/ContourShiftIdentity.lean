import GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles

/-!
# The finite-height contour shift

Moving a truncated vertical integral from one abscissa to another is an identity, not an estimate:
the rectangle integral is by definition the difference of the two vertical sides minus the two
horizontal ones.  Isolating the right-hand vertical side expresses it as the rectangle integral —
which residue calculus evaluates — plus the shifted vertical side and the two horizontal segments.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **The finite-height contour shift**, as an identity. -/
theorem vIntegral_shift (f : ℂ → ℂ) (σ₁ σ₀ T : ℝ) :
    VIntegral f σ₀ (-T) T
      = RectangleIntegral f ((σ₁ : ℂ) - Complex.I * (T : ℂ)) ((σ₀ : ℂ) + Complex.I * (T : ℂ))
        + VIntegral f σ₁ (-T) T
        + HIntegral f σ₁ σ₀ T - HIntegral f σ₁ σ₀ (-T) := by
  have hzre : ((σ₁ : ℂ) - Complex.I * (T : ℂ)).re = σ₁ := by simp
  have hzim : ((σ₁ : ℂ) - Complex.I * (T : ℂ)).im = -T := by simp
  have hwre : ((σ₀ : ℂ) + Complex.I * (T : ℂ)).re = σ₀ := by simp
  have hwim : ((σ₀ : ℂ) + Complex.I * (T : ℂ)).im = T := by simp
  rw [RectangleIntegral, hzre, hzim, hwre, hwim]
  ring

end

end RHTower.Sieve
