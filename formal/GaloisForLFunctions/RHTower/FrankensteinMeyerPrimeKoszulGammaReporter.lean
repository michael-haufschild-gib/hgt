import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerInvariantEvaluationGaugeFrontier
import GaloisForLFunctions.RHTower.FrankensteinBigWittSingularGammaReporterDescent
import GaloisForLFunctions.RHTower.PrimeTranslationKoszulOffLine

/-!
# Meyer--Koszul--Gamma source reporter

This module constructs, for every actual Xi divisor support point, one literal nonzero reporter on
Meyer's algebraic source cohomology.  At prime time `-log p`, its centered-flow character is exactly
the critical prime-translation Koszul multiplier `deltaS p rho`; the squared norm of that same
character is exactly the coefficient-faithful inverse-Gamma ghost.

Thus the Koszul multiplier and the Gamma ghost are not parallel fitted parameters.  They are the
linear character and its Hermitian square coming from one Xi-selected source reporter.  No
boundedness, completion, shared scalar, or RH hypothesis is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- Zeroth multiplicity jet of an actual Xi divisor, as a reporter on literal Meyer cohomology. -/
def deningerMeyerXiPrimeGammaSourceReporter
    (rho : XiDivisorSupport) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  deningerMeyerXiSupportJetEvaluationLM rho
    (⟨0, xiSupportMultiplicity_pos rho⟩ : DeningerArithmeticJetIndex rho)

/-- The source reporter is genuine: divisor multiplicity makes its zeroth jet available and the
Meyer spectral-inclusion theorem makes it nonzero. -/
theorem deningerMeyerXiPrimeGammaSourceReporter_ne_zero
    (rho : XiDivisorSupport) :
    deningerMeyerXiPrimeGammaSourceReporter rho ≠ 0 :=
  deningerMeyerXiSupportEvaluationLM_ne_zero rho

/-- Exact centered prime-time character of the Xi-selected reporter. -/
def deningerMeyerXiPrimeGammaCharacter
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℂ :=
  Complex.exp
    (((-Real.log (p.1 : ℝ) : ℝ) : ℂ) * ((rho : ℂ) - 1 / 2))

/-- The source character is exactly the multiplier used by the normalized prime-translation
Koszul complex, including its complex phase. -/
theorem deningerMeyerXiPrimeGammaCharacter_eq_deltaS
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    deningerMeyerXiPrimeGammaCharacter rho p = deltaS p rho := by
  have hpC : (p.1 : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hlog : Complex.log (p.1 : ℂ) = (Real.log (p.1 : ℝ) : ℂ) :=
    (Complex.natCast_log (n := p.1)).symm
  rw [deningerMeyerXiPrimeGammaCharacter, deltaS,
    Complex.cpow_def_of_ne_zero hpC, hlog]
  congr 1
  push_cast
  ring

/-- Hermitian square of the Meyer/Koszul character is the literal inverse-oriented Gamma ghost. -/
theorem norm_sq_deningerMeyerXiPrimeGammaCharacter
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ‖deningerMeyerXiPrimeGammaCharacter rho p‖ ^ 2 =
      primeGammaLocalInverseOrientedGhost
        (primeDepthBVWoldXiCenteredRate rho) p := by
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hlog : Complex.log (p.1 : ℂ) = (Real.log (p.1 : ℝ) : ℂ) :=
    (Complex.natCast_log (n := p.1)).symm
  rw [deningerMeyerXiPrimeGammaCharacter, Complex.norm_exp, pow_two,
    ← Real.exp_add, primeGammaLocalInverseOrientedGhost,
    Real.rpow_def_of_pos hp]
  congr 1
  norm_num [Complex.mul_re, Complex.sub_re, Complex.div_re,
    Complex.normSq, primeDepthBVWoldXiCenteredRate]
  rw [hlog, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Prime-time centered flow acts on the actual source reporter by the exact Koszul character. -/
theorem deningerMeyerXiPrimeGammaSourceReporter_primeFlow
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerXiPrimeGammaSourceReporter rho
        (deningerMeyerStrongLogCenteredCohomologyFlow
          (-Real.log (p.1 : ℝ)) u) =
      deningerMeyerXiPrimeGammaCharacter rho p *
        deningerMeyerXiPrimeGammaSourceReporter rho u := by
  simpa only [deningerMeyerXiPrimeGammaSourceReporter,
    deningerMeyerXiPrimeGammaCharacter] using
      deningerMeyerXiSupportEvaluationLM_centeredFlow rho
        (-Real.log (p.1 : ℝ)) u

/-- Prime Koszul coordinate on literal Meyer cohomology selected by one actual Xi divisor. -/
def deningerMeyerXiPrimeKoszulCoordinate
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerStrongLogCohomology :=
  deningerMeyerStrongLogCenteredCohomologyFlow (-Real.log (p.1 : ℝ)) -
    deningerMeyerXiPrimeGammaCharacter rho p • LinearMap.id

/-- The genuine Xi source reporter is a cocycle for every normalized prime Koszul coordinate. -/
theorem deningerMeyerXiPrimeGammaSourceReporter_koszulCoordinate
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerXiPrimeGammaSourceReporter rho
        (deningerMeyerXiPrimeKoszulCoordinate rho p u) = 0 := by
  rw [deningerMeyerXiPrimeKoszulCoordinate, LinearMap.sub_apply, map_sub,
    deningerMeyerXiPrimeGammaSourceReporter_primeFlow,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  ring

/-- Every actual Xi divisor supplies a nonzero Koszul cohomology reporter.  Consequently its
selected Meyer prime coordinate is not algebraically surjective. -/
theorem not_surjective_deningerMeyerXiPrimeKoszulCoordinate
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    ¬ Function.Surjective (deningerMeyerXiPrimeKoszulCoordinate rho p) := by
  intro hsurj
  apply deningerMeyerXiPrimeGammaSourceReporter_ne_zero rho
  apply LinearMap.ext
  intro u
  obtain ⟨v, hv⟩ := hsurj u
  rw [← hv]
  simpa using
    deningerMeyerXiPrimeGammaSourceReporter_koszulCoordinate rho p v

/-- Packaged unconditional producer: one nonzero coefficient-faithful source reporter exists for
every retained Xi divisor and simultaneously realizes the Koszul and Gamma coefficients. -/
structure DeningerMeyerXiPrimeKoszulGammaReporter
    (rho : XiDivisorSupport) where
  reporter : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ
  reporter_ne_zero : reporter ≠ 0
  character : Nat.Primes → ℂ
  prime_flow : ∀ (p : Nat.Primes) (u : DeningerMeyerStrongLogCohomology),
    reporter
        (deningerMeyerStrongLogCenteredCohomologyFlow
          (-Real.log (p.1 : ℝ)) u) =
      character p * reporter u
  character_eq_koszul : ∀ p, character p = deltaS p rho
  character_norm_sq_eq_gamma : ∀ p,
    ‖character p‖ ^ 2 =
      primeGammaLocalInverseOrientedGhost
        (primeDepthBVWoldXiCenteredRate rho) p

/-- Explicit construction for every actual divisor; no existence premise remains. -/
def deningerMeyerXiPrimeKoszulGammaReporter
    (rho : XiDivisorSupport) :
    DeningerMeyerXiPrimeKoszulGammaReporter rho where
  reporter := deningerMeyerXiPrimeGammaSourceReporter rho
  reporter_ne_zero := deningerMeyerXiPrimeGammaSourceReporter_ne_zero rho
  character := deningerMeyerXiPrimeGammaCharacter rho
  prime_flow := deningerMeyerXiPrimeGammaSourceReporter_primeFlow rho
  character_eq_koszul := deningerMeyerXiPrimeGammaCharacter_eq_deltaS rho
  character_norm_sq_eq_gamma :=
    norm_sq_deningerMeyerXiPrimeGammaCharacter rho

end

end RHTower
