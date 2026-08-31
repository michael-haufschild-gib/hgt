import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedIntegrableCocycleDescent
import GaloisForLFunctions.RHTower.HedenmalmThetaSourcePrimeModularCompactRecurrenceDescent

open Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- `L¹` gauge-potential descent of the prime modular character through the compact prime circle. -/
def PrimeModularIntegrablePotential (t : ℝ) : Prop :=
  IntegrableTranslationPotential primeCircleHom (primeModularLogCharacter t)

/-- Prime modular `L¹` descent is possible exactly for neutral modular rate. -/
theorem primeModularIntegrablePotential_iff (t : ℝ) :
    PrimeModularIntegrablePotential t ↔ t = 0 := by
  rw [PrimeModularIntegrablePotential, integrableTranslationPotential_iff,
    primeModularLogCharacter_eq_zero_iff]

end

end GaloisForLFunctions.RHTower

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions
open GaloisForLFunctions.RHTower

noncomputable section

/-- Integrable-cocycle descent of the theta-source modular rate on one Xi divisor copy. -/
def ThetaXiPrimeModularIntegrablePotential (q : RHTower.XiZeroCopy) : Prop :=
  GaloisForLFunctions.RHTower.PrimeModularIntegrablePotential
    (RHTower.primeDepthBVWoldXiCenteredRate q.1)

/-- Pointwise `L¹` cocycle selection is exactly critical-line placement. -/
theorem thetaXiPrimeModularIntegrablePotential_iff (q : RHTower.XiZeroCopy) :
    ThetaXiPrimeModularIntegrablePotential q ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [ThetaXiPrimeModularIntegrablePotential,
    GaloisForLFunctions.RHTower.primeModularIntegrablePotential_iff,
    RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Functional-equation reflection negates the potential gauge and preserves `L¹` descent. -/
theorem thetaXiPrimeModularIntegrablePotential_lineConj_iff
    (q : RHTower.XiZeroCopy) :
    ThetaXiPrimeModularIntegrablePotential
        (RHTower.xiZeroCopyLineConjEquiv q) ↔
      ThetaXiPrimeModularIntegrablePotential q := by
  rw [thetaXiPrimeModularIntegrablePotential_iff,
    thetaXiPrimeModularIntegrablePotential_iff]
  change (1 - star (q.1 : ℂ)).re = 1 / 2 ↔ (q.1 : ℂ).re = 1 / 2
  simp
  constructor <;> intro h <;> linarith

/-- Global integrable prime-circle potential existence is equivalent to RH. -/
theorem forall_thetaXiPrimeModularIntegrablePotential_iff_riemannHypothesis :
    (∀ q : RHTower.XiZeroCopy, ThetaXiPrimeModularIntegrablePotential q) ↔
      RiemannHypothesis := by
  constructor
  · intro hpotential
    have hline : ∀ q : RHTower.XiZeroCopy, (q.1 : ℂ).re = 1 / 2 :=
      fun q => (thetaXiPrimeModularIntegrablePotential_iff q).mp (hpotential q)
    apply RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [RHTower.xiSpectralPoint]
    · simp [RHTower.xiSpectralPoint, hline q]
  · intro hRH q
    apply (thetaXiPrimeModularIntegrablePotential_iff q).2
    exact RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end RHTower.HedenmalmThetaSource
