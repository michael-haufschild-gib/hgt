import GaloisForLFunctions.RHTower.PrimeDepthBVWoldSourcePointedNormalJet
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldPositiveStokesPolarization
import GaloisForLFunctions.RHTower.XiSelectedBilateralPositiveSourceReceiver
import GaloisForLFunctions.RHTower.PurityCurvatureExponentialTransgression

/-!
# Arithmetic modular-Hodge energy law

Four independently constructed defects carry one scalar field.  Deninger's
local-Hodge commutator coefficient is `-a`; the intrinsic BV--Wold
normal-extension cocycle is `c ↦ a c`; fixed-source Stokes excess is its
squared norm in the explicit edge/clock gauge; and the logarithm of the
Meyer/Gamma Radon--Nikodym weight is `-log(p) a`.

The identities below are coefficientwise and retain divisor, prime, source-cell,
splitting, and conormal labels.  They prove a quantitative common-field law,
not merely equality of zero loci.  They do not prove that the common field
vanishes; that remains the source-side arithmetic selection problem.
-/

namespace RHTower

noncomputable section

/-- Weight-one purity curvature, the coefficient of Deninger's local-Hodge
commutator, is exactly the negative BV--Wold centered normal field. -/
theorem weightOnePurityCurvature_eq_neg_primeDepthBVWoldXiCenteredRate
    (q : XiZeroCopy) :
    weightOnePurityCurvature (q.1 : ℂ) =
      -(primeDepthBVWoldXiCenteredRate q.1 : ℂ) := by
  rw [weightOnePurityCurvature, primeDepthBVWoldXiCenteredRate]
  apply Complex.ext
  · simp
    ring
  · simp

/-- The intrinsic BV--Wold normal extension is multiplication by the negative
Deninger local-Hodge commutator coefficient. -/
theorem primeDepthBVWoldXiNormalExtensionCocycle_eq_neg_hodgeCurvature
    (q : XiZeroCopy) (i : PrimeDepthBVWoldCell)
    (s : ℂ →ₗ[ℂ] (ℂ × ℂ))
    (hs : primeDepthBVWoldVerticalQuotient.comp s = LinearMap.id)
    (c : ℂ) :
    primeDepthBVWoldSourceNormalExtensionCocycle
        (primeDepthBVWoldXiCenteredRate q.1) i s c =
      -weightOnePurityCurvature (q.1 : ℂ) * c := by
  rw [primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
      (primeDepthBVWoldXiCenteredRate q.1) i s hs c,
    weightOnePurityCurvature_eq_neg_primeDepthBVWoldXiCenteredRate]
  ring

/-- Fixed-source Stokes excess is the squared norm of the intrinsic normal
extension cocycle, up to only the explicit edge/clock gauge. -/
theorem primeDepthBVWoldSourcePolarizationStokesExcess_eq_normalExtensionEnergy
    (a : ℝ) (i j : PrimeDepthBVWoldCell)
    (s : ℂ →ₗ[ℂ] (ℂ × ℂ))
    (hs : primeDepthBVWoldVerticalQuotient.comp s = LinearMap.id)
    (c : ℂ) :
    primeDepthBVWoldSourcePolarizationStokesExcess a i j c =
      (primeDepthBVWoldConnection i j /
          (xiGammaEulerPrimitivePrimeDepthLogClock i *
            xiGammaEulerPrimitivePrimeDepthLogClock j)) ^ (2 : ℕ) *
        Complex.normSq
          (primeDepthBVWoldSourceNormalExtensionCocycle a j s c) := by
  rw [primeDepthBVWoldSourcePolarizationStokesExcess_eq,
    primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse a j s hs c,
    Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- The logarithm of the genuine Meyer/Gamma modular correction recovers the
same centered normal field, with the retained prime logarithm as clock. -/
theorem log_deningerMeyerXiPrimeGammaModularWeight
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    Real.log (deningerMeyerXiPrimeGammaModularWeight rho p) =
      -Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho := by
  rw [deningerMeyerXiPrimeGammaModularWeight,
    norm_deningerMeyerXiPrimeGammaCharacter_eq_halfGammaClock]
  rw [show
      Real.exp (-(Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) / 2) ^ (2 : ℕ) =
        Real.exp (-Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  rw [Real.log_exp]

/-- Prime-clocked intrinsic normal energy is exactly logarithmic
Radon--Nikodym energy.  No source edge or polarization is needed. -/
theorem primeDepthBVWoldXiNormalExtensionEnergy_eq_modularLogEnergy
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (i : PrimeDepthBVWoldCell)
    (s : ℂ →ₗ[ℂ] (ℂ × ℂ))
    (hs : primeDepthBVWoldVerticalQuotient.comp s = LinearMap.id)
    (c : ℂ) :
    Real.log (p : ℝ) ^ (2 : ℕ) *
        Complex.normSq
          (primeDepthBVWoldSourceNormalExtensionCocycle
            (primeDepthBVWoldXiCenteredRate rho) i s c) =
      Real.log (deningerMeyerXiPrimeGammaModularWeight rho p) ^ (2 : ℕ) *
        Complex.normSq c := by
  rw [primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
      (primeDepthBVWoldXiCenteredRate rho) i s hs c,
    Complex.normSq_mul, Complex.normSq_ofReal,
    log_deningerMeyerXiPrimeGammaModularWeight]
  ring

/-- On every multiplicity copy, intrinsic normal energy is exactly four times
the squared transverse spectral displacement, coefficient by coefficient. -/
theorem primeDepthBVWoldXiNormalExtensionEnergy_eq_spectralEnergy
    (q : XiZeroCopy) (i : PrimeDepthBVWoldCell)
    (s : ℂ →ₗ[ℂ] (ℂ × ℂ))
    (hs : primeDepthBVWoldVerticalQuotient.comp s = LinearMap.id)
    (c : ℂ) :
    Complex.normSq
        (primeDepthBVWoldSourceNormalExtensionCocycle
          (primeDepthBVWoldXiCenteredRate q.1) i s c) =
      4 * (xiSpectralPoint q).im ^ (2 : ℕ) * Complex.normSq c := by
  rw [primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
    (primeDepthBVWoldXiCenteredRate q.1) i s hs c]
  have hrate :
      primeDepthBVWoldXiCenteredRate q.1 = -2 * (xiSpectralPoint q).im := by
    rw [primeDepthBVWoldXiCenteredRate, xiSpectralPoint]
    norm_num [Complex.mul_im]
    ring
  rw [hrate, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- Prime-clocked fixed-source Stokes energy is the same logarithmic modular
energy in the explicit edge/clock gauge. -/
theorem primeDepthBVWoldXiStokesEnergy_eq_modularLogEnergy
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (i j : PrimeDepthBVWoldCell) (c : ℂ) :
    Real.log (p : ℝ) ^ (2 : ℕ) *
        primeDepthBVWoldSourcePolarizationStokesExcess
          (primeDepthBVWoldXiCenteredRate rho) i j c =
      (primeDepthBVWoldConnection i j /
          (xiGammaEulerPrimitivePrimeDepthLogClock i *
            xiGammaEulerPrimitivePrimeDepthLogClock j)) ^ (2 : ℕ) *
        Real.log (deningerMeyerXiPrimeGammaModularWeight rho p) ^ (2 : ℕ) *
          Complex.normSq c := by
  rw [primeDepthBVWoldSourcePolarizationStokesExcess_eq,
    log_deningerMeyerXiPrimeGammaModularWeight]
  ring

end


end RHTower
