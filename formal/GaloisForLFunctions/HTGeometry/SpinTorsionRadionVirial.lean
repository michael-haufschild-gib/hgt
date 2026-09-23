import GaloisForLFunctions.HTGeometry.TwoModulusLogHessian

/-!
# Radial virial identities for the two-modulus spin-torsion potential

Grouping the potential by curvature, flux, and torsion reveals an exact off-shell virial law.  A
common logarithmic-radius displacement has weights `-8`, `-10`, and `-6`; consequently the
potential corrected by one eighth of its radial force equals one quarter of torsion minus flux.
For positive physical coefficients this corrected energy is strictly negative everywhere.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Curvature-attraction part of the logarithmic two-modulus potential. -/
def twoModulusLogCurvaturePotential (A x y : ℝ) : ℝ :=
  logMonomial (-2 * A) 4 4 x y + logMonomial (-24 * A) 2 6 x y

/-- Quantized-flux part of the logarithmic two-modulus potential. -/
def twoModulusLogFluxPotential (B q m n x y : ℝ) : ℝ :=
  logMonomial (B * m ^ (2 : ℕ) / 2) 6 4 x y +
    logMonomial (B * q * n ^ (2 : ℕ)) 2 8 x y

/-- Spin-torsion binding part of the logarithmic two-modulus potential. -/
def twoModulusLogTorsionPotential (C family x y : ℝ) : ℝ :=
  logMonomial (-C * family ^ (2 : ℕ)) 2 4 x y

/-- Exact curvature-flux-torsion decomposition. -/
theorem twoModulusLogPotential_decomposition (A B C q m n family x y : ℝ) :
    twoModulusLogPotential A B C q m n family x y =
      twoModulusLogCurvaturePotential A x y +
      twoModulusLogFluxPotential B q m n x y +
      twoModulusLogTorsionPotential C family x y := by
  unfold twoModulusLogPotential twoModulusLogCurvaturePotential
    twoModulusLogFluxPotential twoModulusLogTorsionPotential
  ring

/-- A common log-radius shift exposes the three exact homogeneity weights. -/
theorem twoModulusLogPotential_diagonalShift
    (A B C q m n family x y shift : ℝ) :
    twoModulusLogPotential A B C q m n family (x + shift) (y + shift) =
      Real.exp (-8 * shift) * twoModulusLogCurvaturePotential A x y +
      Real.exp (-10 * shift) * twoModulusLogFluxPotential B q m n x y +
      Real.exp (-6 * shift) * twoModulusLogTorsionPotential C family x y := by
  have hshift (coefficient p q : ℝ) :
      logMonomial coefficient p q (x + shift) (y + shift) =
        Real.exp (-(p + q) * shift) * logMonomial coefficient p q x y := by
    unfold logMonomial
    rw [show -p * (x + shift) - q * (y + shift) =
        (-(p + q) * shift) + (-p * x - q * y) by ring, Real.exp_add]
    ring
  unfold twoModulusLogPotential twoModulusLogCurvaturePotential
    twoModulusLogFluxPotential twoModulusLogTorsionPotential
  rw [hshift, hshift, hshift, hshift, hshift]
  norm_num
  ring

/-- Exact off-shell radial virial identity. -/
theorem twoModulusLogPotential_radialVirial (A B C q m n family x y : ℝ) :
    8 * twoModulusLogPotential A B C q m n family x y +
        twoModulusLogForceX A B C q m n family x y +
        twoModulusLogForceY A B C q m n family x y =
      2 * (twoModulusLogTorsionPotential C family x y -
        twoModulusLogFluxPotential B q m n x y) := by
  unfold twoModulusLogPotential twoModulusLogForceX twoModulusLogForceY
    twoModulusLogFluxPotential twoModulusLogTorsionPotential logMonomialDx logMonomialDy
  ring

/-- Potential after subtracting the radial dilation response. -/
def twoModulusRadialVirialEnergy (A B C q m n family x y : ℝ) : ℝ :=
  twoModulusLogPotential A B C q m n family x y +
    (twoModulusLogForceX A B C q m n family x y +
      twoModulusLogForceY A B C q m n family x y) / 8

/-- Curvature cancels completely from the radial virial energy. -/
theorem twoModulusRadialVirialEnergy_eq (A B C q m n family x y : ℝ) :
    twoModulusRadialVirialEnergy A B C q m n family x y =
      (twoModulusLogTorsionPotential C family x y -
        twoModulusLogFluxPotential B q m n x y) / 4 := by
  unfold twoModulusRadialVirialEnergy
  have h := twoModulusLogPotential_radialVirial A B C q m n family x y
  linarith

/-- Positive flux and torsion scales force the radial virial energy to be strictly negative. -/
theorem twoModulusRadialVirialEnergy_exp_neg
    (logA logB logC logQ logM logN logFamily x y : ℝ) :
    twoModulusRadialVirialEnergy (Real.exp logA) (Real.exp logB) (Real.exp logC)
        (Real.exp logQ) (Real.exp logM) (Real.exp logN) (Real.exp logFamily) x y < 0 := by
  rw [twoModulusRadialVirialEnergy_eq]
  have hFlux : 0 < twoModulusLogFluxPotential (Real.exp logB) (Real.exp logQ)
      (Real.exp logM) (Real.exp logN) x y := by
    unfold twoModulusLogFluxPotential logMonomial
    positivity
  have hTorsion : twoModulusLogTorsionPotential (Real.exp logC)
      (Real.exp logFamily) x y < 0 := by
    unfold twoModulusLogTorsionPotential logMonomial
    have h : 0 < Real.exp logC * Real.exp logFamily ^ (2 : ℕ) *
        Real.exp (-2 * x - 4 * y) := by positivity
    nlinarith
  linarith

/-- Difference of radion forces isolates the anisotropic exponent imbalance. -/
theorem twoModulusLogForce_anisotropy (A B C q m n family x y : ℝ) :
    twoModulusLogForceX A B C q m n family x y -
        twoModulusLogForceY A B C q m n family x y =
      4 * logMonomial (-24 * A) 2 6 x y -
      2 * logMonomial (B * m ^ (2 : ℕ) / 2) 6 4 x y +
      6 * logMonomial (B * q * n ^ (2 : ℕ)) 2 8 x y +
      2 * logMonomial (-C * family ^ (2 : ℕ)) 2 4 x y := by
  unfold twoModulusLogForceX twoModulusLogForceY logMonomialDx logMonomialDy
  ring

end GaloisForLFunctions.HTGeometry
