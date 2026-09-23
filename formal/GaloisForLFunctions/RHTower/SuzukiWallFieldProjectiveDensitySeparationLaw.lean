import GaloisForLFunctions.RHTower.SuzukiCriticalWallFieldSquareRootWeld
import GaloisForLFunctions.RHTower.SuzukiProjectiveAffineSecantTensor

/-!
# Suzuki wall-field projective density separation law

Suzuki's normalized response is projective, so common source scaling cancels after characteristic
division.  The correct carrier before division is the marked affine-secant tensor together with
its denominator.  Both are homogeneous of degree two in one source vector.

This file proves that critical Gamma wall field is their exact common density.  Its bilinear square
is already the von-Mangoldt far-hinge numerator, so universal far source survives precisely in the
division-free determinant line while normalized quotient remains scale-blind.  No RH premise,
positivity assumption, estimate, numerical computation, or endpoint regularity is used.
-/

namespace RHTower

noncomputable section

/-! ## Homogeneous marked projective density -/

/-- Marked affine-secant tensor is homogeneous of degree two under common source scaling. -/
theorem suzukiProjectiveAffineSecantTensor_commonScale
    {F : Type*} [CommRing F]
    (alpha beta omega x X y Y c : F) :
    suzukiProjectiveAffineSecantTensor alpha beta
        (omega * x) (omega * X) (omega * y) (omega * Y) (omega * c) =
      omega ^ (2 : ℕ) * suzukiProjectiveAffineSecantTensor alpha beta x X y Y c := by
  simp only [suzukiProjectiveAffineSecantTensor]
  ring

/-- Projective affine-secant denominator has same degree-two source density. -/
theorem suzukiProjectiveAffineSecantDenominator_commonScale
    {F : Type*} [CommRing F]
    (alpha beta omega y Y : F) :
    suzukiProjectiveAffineSecantDenominator alpha beta
        (omega * y) (omega * Y) =
      omega ^ (2 : ℕ) * suzukiProjectiveAffineSecantDenominator alpha beta y Y := by
  simp only [suzukiProjectiveAffineSecantDenominator]
  ring

/-- Division-free affine cross numerator carries same quadratic source density. -/
theorem suzukiProjectiveAffineSecant_cross_commonScale
    {F : Type*} [CommRing F]
    (alpha beta omega x X y Y c : F) :
    beta * (omega * (X - beta * x + c)) * (omega * (Y - alpha * y)) -
        alpha * (omega * (X - alpha * x + c)) * (omega * (Y - beta * y)) =
      (beta - alpha) * omega ^ (2 : ℕ) *
        suzukiProjectiveAffineSecantTensor alpha beta x X y Y c := by
  simp only [suzukiProjectiveAffineSecantTensor]
  ring

/-- Common nonzero source scaling cancels exactly from normalized affine-secant quotient. -/
theorem suzukiProjectiveAffineSecant_quotient_commonScale
    {F : Type*} [Field F]
    {alpha beta omega x X y Y c : F}
    (homega : omega ≠ 0)
    (hden : suzukiProjectiveAffineSecantDenominator alpha beta y Y ≠ 0) :
    suzukiProjectiveAffineSecantTensor alpha beta
          (omega * x) (omega * X) (omega * y) (omega * Y) (omega * c) /
        suzukiProjectiveAffineSecantDenominator alpha beta (omega * y) (omega * Y) =
      suzukiProjectiveAffineSecantTensor alpha beta x X y Y c /
        suzukiProjectiveAffineSecantDenominator alpha beta y Y := by
  rw [suzukiProjectiveAffineSecantTensor_commonScale,
    suzukiProjectiveAffineSecantDenominator_commonScale]
  field_simp [homega, hden]

/-! ## Source-linear realization -/

/-- If all marked coordinates are observations of same scaled source vector, complex linearity
forces exactly common quadratic density, including homogeneous coordinate `K(e)`. -/
theorem suzukiProjectiveAffineSecantTensor_linearMap_smul
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : V →ₗ[ℂ] V) (B D K : V →ₗ[ℂ] ℂ)
    (alpha beta omega : ℂ) (v e : V) :
    suzukiProjectiveAffineSecantTensor alpha beta
        (B (omega • v)) (B (A (omega • v)))
        (D (omega • v)) (D (A (omega • v))) (K (omega • e)) =
      omega ^ (2 : ℕ) *
        suzukiProjectiveAffineSecantTensor alpha beta
          (B v) (B (A v)) (D v) (D (A v)) (K e) := by
  simpa only [map_smul, smul_eq_mul] using
    suzukiProjectiveAffineSecantTensor_commonScale alpha beta omega
      (B v) (B (A v)) (D v) (D (A v)) (K e)

/-! ## Critical wall field as exact determinant-line density -/

/-- Critical wall field never vanishes at real height and prime-power depth. -/
private theorem suzukiCriticalWallField_ne_zero
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallField t p e ≠ 0 := by
  have hbare : suzukiCriticalEntryWallBareAmplitude p e ≠ 0 := by
    unfold suzukiCriticalEntryWallBareAmplitude
    apply ne_of_gt
    rw [Real.sqrt_pos]
    have hn : 0 < (xiGammaEulerValuationNat (p, e) : ℝ) := by
      exact_mod_cast (pow_pos p.property.pos (e + 1))
    exact mul_pos
      (div_pos (Real.log_pos (by exact_mod_cast p.property.one_lt)) hn)
      (Real.exp_pos _)
  rw [suzukiCriticalWallField_eq_bareAmplitude_mul_kernel]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hbare)
    (by simp [suzukiOscillatoryKernel])

/-- **Projective density weld.**  Scaling marked tensor by critical wall field multiplies it by
exact von-Mangoldt far-hinge numerator. -/
theorem suzukiProjectiveAffineSecantTensor_criticalWallField_eq_farHingeDensity
    (alpha beta x X y Y c : ℂ) (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiProjectiveAffineSecantTensor alpha beta
        (suzukiCriticalWallField t p e * x)
        (suzukiCriticalWallField t p e * X)
        (suzukiCriticalWallField t p e * y)
        (suzukiCriticalWallField t p e * Y)
        (suzukiCriticalWallField t p e * c) =
      ((ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
        suzukiOscillatoryKernel (t : ℂ)
          (Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) *
        suzukiProjectiveAffineSecantTensor alpha beta x X y Y c := by
  rw [suzukiProjectiveAffineSecantTensor_commonScale,
    sq_suzukiCriticalWallField_eq_farHingeNumerator]

/-- Critical wall field gives same exact far-hinge density to projective denominator. -/
theorem suzukiProjectiveAffineSecantDenominator_criticalWallField_eq_farHingeDensity
    (alpha beta y Y : ℂ) (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiProjectiveAffineSecantDenominator alpha beta
        (suzukiCriticalWallField t p e * y)
        (suzukiCriticalWallField t p e * Y) =
      ((ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
        suzukiOscillatoryKernel (t : ℂ)
          (Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) *
        suzukiProjectiveAffineSecantDenominator alpha beta y Y := by
  rw [suzukiProjectiveAffineSecantDenominator_commonScale,
    sq_suzukiCriticalWallField_eq_farHingeNumerator]

/-- Wall field cancels from normalized quotient, while preceding division-free theorems retain its
far-hinge density. -/
theorem suzukiProjectiveAffineSecant_quotient_criticalWallField
    {alpha beta x X y Y c : ℂ}
    (t : ℝ) (p : Nat.Primes) (e : ℕ)
    (hden : suzukiProjectiveAffineSecantDenominator alpha beta y Y ≠ 0) :
    suzukiProjectiveAffineSecantTensor alpha beta
          (suzukiCriticalWallField t p e * x)
          (suzukiCriticalWallField t p e * X)
          (suzukiCriticalWallField t p e * y)
          (suzukiCriticalWallField t p e * Y)
          (suzukiCriticalWallField t p e * c) /
        suzukiProjectiveAffineSecantDenominator alpha beta
          (suzukiCriticalWallField t p e * y)
          (suzukiCriticalWallField t p e * Y) =
      suzukiProjectiveAffineSecantTensor alpha beta x X y Y c /
        suzukiProjectiveAffineSecantDenominator alpha beta y Y := by
  exact suzukiProjectiveAffineSecant_quotient_commonScale
    (suzukiCriticalWallField_ne_zero t p e) hden

/-- Division-free Suzuki affine cross numerator carries exact far-prime projective density. -/
theorem suzukiProjectiveAffineSecant_cross_criticalWallField_eq_farHingeDensity
    (alpha beta x X y Y c : ℂ) (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    beta * (suzukiCriticalWallField t p e * (X - beta * x + c)) *
          (suzukiCriticalWallField t p e * (Y - alpha * y)) -
        alpha * (suzukiCriticalWallField t p e * (X - alpha * x + c)) *
          (suzukiCriticalWallField t p e * (Y - beta * y)) =
      (beta - alpha) *
        ((ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
            Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
          suzukiOscillatoryKernel (t : ℂ)
            (Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) *
        suzukiProjectiveAffineSecantTensor alpha beta x X y Y c := by
  rw [suzukiProjectiveAffineSecant_cross_commonScale,
    sq_suzukiCriticalWallField_eq_farHingeNumerator]

end

end RHTower
