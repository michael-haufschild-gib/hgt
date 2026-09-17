import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCovectorModular

/-!
# Hyperbolic energy of the literal full angular covector

The HB-B2 cyclic cap needs global control of actual base derivatives, not an
invalid Euclidean-coordinate covariance claim.  This file extracts the exact
quantity preserved by the literal modular covector law: height squared times
the two-component covector norm-square.  It is an input to the remaining
cusp-tail/base-jet problem; it makes no cap, QNM, or action assertion.
-/

open UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups

namespace RHTower.D4BMFullCovectorHyperbolicEnergy

open D4BMHorizon D4BMGlobalAngularResponse D4BMModularCore

noncomputable section
set_option autoImplicit false

/-- Squared Euclidean norm of a covector's two actual chart components. -/
def covectorNormSq (V : Covector) (z : ℍ) : ℝ :=
  Complex.normSq (V 0 (coordinates z)) + Complex.normSq (V 1 (coordinates z))

/-- The modularly intrinsic first-order covector energy in the upper-half-plane chart. -/
def hyperbolicCovectorEnergy (V : Covector) (z : ℍ) : ℝ :=
  z.im ^ 2 * covectorNormSq V z

private theorem covector_rotation_scale_normSq (d u₀ u₁ : ℂ) :
    Complex.normSq (d.re * u₀ + d.im * u₁) +
      Complex.normSq ((-d.im) * u₀ + d.re * u₁) =
      Complex.normSq d * (Complex.normSq u₀ + Complex.normSq u₁) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.neg_im]
  ring

/-- A covector transported by the literal modular Jacobian has the exact
rotation--scale norm law. -/
theorem covectorNormSq_transport (V : Covector) (A : SL(2, ℤ)) (z : ℍ)
    (hV : ∀ v : ℂ, covectorAction V (coordinates (A • z))
      ((1 / denom A z ^ 2) * v) = covectorAction V (coordinates z) v) :
    covectorNormSq V z = Complex.normSq (1 / denom A z ^ 2) * covectorNormSq V (A • z) := by
  let d : ℂ := 1 / denom A z ^ 2
  have h0 : covectorAction V (coordinates (A • z)) (d * 1) =
      covectorAction V (coordinates z) 1 := by
    simpa only [d] using hV 1
  have h1 : covectorAction V (coordinates (A • z)) (d * Complex.I) =
      covectorAction V (coordinates z) Complex.I := by
    simpa only [d] using hV Complex.I
  have h0' : (d.re : ℂ) * V 0 (coordinates (A • z)) +
      (d.im : ℂ) * V 1 (coordinates (A • z)) = V 0 (coordinates z) := by
    simpa [covectorAction] using h0
  have h1' : (-d.im : ℂ) * V 0 (coordinates (A • z)) +
      (d.re : ℂ) * V 1 (coordinates (A • z)) = V 1 (coordinates z) := by
    simpa [covectorAction] using h1
  change Complex.normSq (V 0 (coordinates z)) + Complex.normSq (V 1 (coordinates z)) =
    Complex.normSq d * (Complex.normSq (V 0 (coordinates (A • z))) +
      Complex.normSq (V 1 (coordinates (A • z))))
  rw [← h0', ← h1']
  exact covector_rotation_scale_normSq d _ _

/-- Height-square times the covector norm-square is invariant under the literal
modular pullback law. -/
theorem hyperbolicCovectorEnergy_modular (V : Covector) (A : SL(2, ℤ)) (z : ℍ)
    (hV : ∀ v : ℂ, covectorAction V (coordinates (A • z))
      ((1 / denom A z ^ 2) * v) = covectorAction V (coordinates z) v) :
    hyperbolicCovectorEnergy V (A • z) = hyperbolicCovectorEnergy V z := by
  have hden : Complex.normSq (denom A z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (UpperHalfPlane.denom_ne_zero A z))
  unfold hyperbolicCovectorEnergy
  rw [ModularGroup.im_smul_eq_div_normSq, covectorNormSq_transport V A z hV]
  simp only [show Complex.normSq (1 / denom A z ^ 2) =
      1 / Complex.normSq (denom A z) ^ 2 by simp [one_div]]
  field_simp

/-- The actual full angular covector has invariant hyperbolic energy. -/
theorem fullAngularCovector_hyperbolicEnergy_modular (q : XiZeroCopy) (branch : Bool)
    (A : SL(2, ℤ)) (z : ℍ) :
    hyperbolicCovectorEnergy (fullAngularCovector q branch) (A • z) =
      hyperbolicCovectorEnergy (fullAngularCovector q branch) z :=
  hyperbolicCovectorEnergy_modular _ A z (fullAngularCovector_modular q branch A z)

/-- The literal quadratic-source covector has invariant hyperbolic energy. -/
theorem fullSquareCovector_hyperbolicEnergy_modular (q : XiZeroCopy) (A : SL(2, ℤ))
    (z : ℍ) :
    hyperbolicCovectorEnergy (fullSquareCovector q) (A • z) =
      hyperbolicCovectorEnergy (fullSquareCovector q) z :=
  hyperbolicCovectorEnergy_modular _ A z (fullSquareCovector_modular q A z)

/-- The retained gradient-source covector has invariant hyperbolic energy. -/
theorem fullGradientCovector_hyperbolicEnergy_modular (q : XiZeroCopy) (branch : Bool)
    (A : SL(2, ℤ)) (z : ℍ) :
    hyperbolicCovectorEnergy (fullGradientCovector q branch) (A • z) =
      hyperbolicCovectorEnergy (fullGradientCovector q branch) z :=
  hyperbolicCovectorEnergy_modular _ A z (fullGradientCovector_modular q branch A z)

end

end RHTower.D4BMFullCovectorHyperbolicEnergy
