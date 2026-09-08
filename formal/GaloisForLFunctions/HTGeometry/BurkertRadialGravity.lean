import GaloisForLFunctions.HTGeometry.BurkertMassNormalization

/-!
# Corrected Burkert mass as a radial gravitational source

The corrected mass normalization is the actual radial density integral.
The resulting lapse satisfies equation (13) of arXiv:2608.23600v1, at every
positive radius, with arbitrary positive central density and halo scale.
All derivatives and scale cancellations are proved directly from the primitive.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem burkertEnclosedMass_integral (d t : ℝ) :
    burkertEnclosedMass d (Real.exp t) =
      ∫ r in (0 : ℝ)..Real.exp t, (4 * Real.pi * Real.exp d) * (r ^ 2 * burkertDensity r) := by
  rw [intervalIntegral.integral_const_mul, integral_burkert_radial_mass]
  unfold burkertEnclosedMass
  ring

def burkertMetric (d r : ℝ) : ℝ := 1 - 2 * burkertEnclosedMass d r / r

theorem burkertMetric_derivative (d t : ℝ) :
    HasDerivAt (burkertMetric d)
      (2 * burkertEnclosedMass d (Real.exp t) / (Real.exp t) ^ 2 -
        8 * Real.pi * Real.exp d * Real.exp t * burkertDensity (Real.exp t)) (Real.exp t) := by
  have h := (((burkertEnclosedMass_derivative d t).const_mul 2).div
    (hasDerivAt_id (Real.exp t)) (Real.exp_ne_zero t)).const_sub 1
  apply h.congr_deriv
  dsimp
  field_simp
  ring

theorem burkertMetric_radial_Einstein_law (d t : ℝ) :
    1 - burkertMetric d (Real.exp t) - Real.exp t * deriv (burkertMetric d) (Real.exp t) =
      8 * Real.pi * Real.exp d * (Real.exp t) ^ 2 * burkertDensity (Real.exp t) := by
  rw [(burkertMetric_derivative d t).deriv]
  unfold burkertMetric
  field_simp
  ring

def scaledBurkertMass (d ell r : ℝ) : ℝ :=
  Real.exp ell ^ 3 * burkertEnclosedMass d (r / Real.exp ell)

theorem scaledBurkertMass_derivative (d ell t : ℝ) :
    HasDerivAt (scaledBurkertMass d ell)
      (4 * Real.pi * Real.exp d * (Real.exp t) ^ 2 * burkertDensity (Real.exp t / Real.exp ell))
      (Real.exp t) := by
  have hm := burkertEnclosedMass_derivative d (t - ell)
  rw [Real.exp_sub] at hm
  have h := (hm.comp (Real.exp t) ((hasDerivAt_id (Real.exp t)).div_const (Real.exp ell))).const_mul
    ((Real.exp ell) ^ 3)
  apply h.congr_deriv
  field_simp

def scaledBurkertMetric (d ell r : ℝ) : ℝ := 1 - 2 * scaledBurkertMass d ell r / r

theorem scaledBurkertMetric_derivative (d ell t : ℝ) :
    HasDerivAt (scaledBurkertMetric d ell)
      (2 * scaledBurkertMass d ell (Real.exp t) / (Real.exp t) ^ 2 -
        8 * Real.pi * Real.exp d * Real.exp t * burkertDensity (Real.exp t / Real.exp ell))
      (Real.exp t) := by
  have h := (((scaledBurkertMass_derivative d ell t).const_mul 2).div
    (hasDerivAt_id (Real.exp t)) (Real.exp_ne_zero t)).const_sub 1
  apply h.congr_deriv
  dsimp
  field_simp
  ring

theorem scaledBurkertMetric_radial_Einstein_law (d ell t : ℝ) :
    1 - scaledBurkertMetric d ell (Real.exp t) -
      Real.exp t * deriv (scaledBurkertMetric d ell) (Real.exp t) =
        8 * Real.pi * Real.exp d * (Real.exp t) ^ 2 * burkertDensity (Real.exp t / Real.exp ell) := by
  rw [(scaledBurkertMetric_derivative d ell t).deriv]
  unfold scaledBurkertMetric
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
