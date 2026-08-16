import GaloisForLFunctions.RHTower.FrankensteinThetaTerminalGammaSharedGhost
import GaloisForLFunctions.RHTower.RouteRReciprocalLogFisherEntranceWall

/-!
# Terminal theta multiplicity jets at the Fisher entrance wall

The normalized terminal jet of the literal theta reflection defect retains the complete complex
Xi divisor coefficient.  Sampling its cut covariance at `log p` gives exactly `p^(rho-1/2)`;
reversing the same jet ratio gives `p^(1/2-rho)`.  Multiplication by the source-derived
Euler--Fisher reciprocal-log potential therefore puts the two same-fibre orientations on the
sharp Route-R entrance wall.

The forward field is in `ell^2` exactly for `Re rho <= 1/2`, while the inverse field is in `ell^2`
exactly for `Re rho >= 1/2`.  Bilateral admission is consequently equivalent to the critical line
for each retained divisor, and constructs the coefficient-faithful source-natural Gamma reporter.
This is a coefficient-preserving cross-corpus reduction; no bilateral-admission premise is
asserted.
-/

open Complex

namespace RHTower

noncomputable section

/-- Prime-log cut transport of the first surviving theta-source multiplicity jet. -/
def xiThetaTerminalMultiplicityPrimeTransport
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℂ :=
  xiThetaTerminalMultiplicityCutJet rho (Real.log (p : ℝ)) /
    xiThetaTerminalMultiplicityCutJet rho 0

/-- The literal normalized terminal jet is the full complex prime character, not only its real
grade or an integer-valued shadow. -/
theorem xiThetaTerminalMultiplicityPrimeTransport_eq_cpow
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiThetaTerminalMultiplicityPrimeTransport rho p =
      (((p : ℕ) : ℝ) : ℂ) ^ ((rho : ℂ) - 1 / 2) := by
  rw [xiThetaTerminalMultiplicityPrimeTransport,
    xiThetaTerminalMultiplicityCutJet_eq_exp_mul_zero]
  rw [mul_div_cancel_right₀]
  · have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    have hp0 : ((((p : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast ne_of_gt hp
    rw [Complex.cpow_def_of_ne_zero hp0, Complex.ofReal_log hp.le]
    congr 1
    rw [xiSpectralPointSupport]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · exact xiThetaTerminalMultiplicityCutJet_ne_zero rho 0

/-- Forward terminal-jet character with the critical Euler--Fisher potential. -/
def xiThetaTerminalMultiplicityFisherField
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℂ :=
  xiThetaTerminalMultiplicityPrimeTransport rho p *
    (routeRFisherLogPotential p : ℂ)

theorem xiThetaTerminalMultiplicityFisherField_eq_routeR
    (rho : XiDivisorSupport) :
    xiThetaTerminalMultiplicityFisherField rho =
      fun p : Nat.Primes =>
        (1 : ℂ) * (((p : ℕ) : ℝ) : ℂ) ^ ((rho : ℂ) - 1 / 2) *
          (routeRFisherLogPotential p : ℂ) := by
  funext p
  rw [xiThetaTerminalMultiplicityFisherField,
    xiThetaTerminalMultiplicityPrimeTransport_eq_cpow]
  ring

/-- The forward literal theta field detects the closed left half of the critical strip. -/
theorem memℓp_two_xiThetaTerminalMultiplicityFisherField_iff
    (rho : XiDivisorSupport) :
    Memℓp (xiThetaTerminalMultiplicityFisherField rho) 2 ↔
      (rho : ℂ).re ≤ 1 / 2 := by
  rw [xiThetaTerminalMultiplicityFisherField_eq_routeR]
  exact memℓp_two_xiDivisor_coefficient_iff (1 : ℂ) one_ne_zero rho

/-- Reciprocal transport of the same terminal jet, without replacing the divisor by an abstract
opposite-grade parameter. -/
def xiThetaTerminalMultiplicityPrimeInverseTransport
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℂ :=
  xiThetaTerminalMultiplicityCutJet rho 0 /
    xiThetaTerminalMultiplicityCutJet rho (Real.log (p : ℝ))

/-- The reciprocal same-fibre jet ratio is the opposite full complex prime character. -/
theorem xiThetaTerminalMultiplicityPrimeInverseTransport_eq_cpow
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiThetaTerminalMultiplicityPrimeInverseTransport rho p =
      (((p : ℕ) : ℝ) : ℂ) ^ (1 / 2 - (rho : ℂ)) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hp0 : ((((p : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hp
  have hjet : xiThetaTerminalMultiplicityPrimeInverseTransport rho p =
      Complex.exp
        (-(Complex.I * xiSpectralPointSupport rho * (Real.log (p : ℝ) : ℂ))) := by
    rw [xiThetaTerminalMultiplicityPrimeInverseTransport,
      show xiThetaTerminalMultiplicityCutJet rho (Real.log (p : ℝ)) =
        Complex.exp (Complex.I * xiSpectralPointSupport rho *
          (Real.log (p : ℝ) : ℂ)) * xiThetaTerminalMultiplicityCutJet rho 0 from
        xiThetaTerminalMultiplicityCutJet_eq_exp_mul_zero rho _]
    apply (div_eq_iff (mul_ne_zero (Complex.exp_ne_zero _)
      (xiThetaTerminalMultiplicityCutJet_ne_zero rho 0))).2
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  rw [hjet, Complex.cpow_def_of_ne_zero hp0, Complex.ofReal_log hp.le]
  congr 1
  rw [xiSpectralPointSupport]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Inverse terminal-jet character with the same critical Euler--Fisher potential. -/
def xiThetaTerminalMultiplicityInverseFisherField
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℂ :=
  xiThetaTerminalMultiplicityPrimeInverseTransport rho p *
    (routeRFisherLogPotential p : ℂ)

/-- Same-fibre inverse transport agrees exactly with the Route-R field of the functional-equation
reflection. -/
theorem xiThetaTerminalMultiplicityInverseFisherField_eq_routeR_reflect
    (rho : XiDivisorSupport) :
    xiThetaTerminalMultiplicityInverseFisherField rho =
      fun p : Nat.Primes =>
        (1 : ℂ) * (((p : ℕ) : ℝ) : ℂ) ^
          ((xiZeroReflectEquiv rho : ℂ) - 1 / 2) *
            (routeRFisherLogPotential p : ℂ) := by
  funext p
  rw [xiThetaTerminalMultiplicityInverseFisherField,
    xiThetaTerminalMultiplicityPrimeInverseTransport_eq_cpow,
    xiZeroReflectEquiv_apply]
  congr 2
  ring

/-- The inverse literal theta field detects the closed right half of the critical strip. -/
theorem memℓp_two_xiThetaTerminalMultiplicityInverseFisherField_iff
    (rho : XiDivisorSupport) :
    Memℓp (xiThetaTerminalMultiplicityInverseFisherField rho) 2 ↔
      1 / 2 ≤ (rho : ℂ).re := by
  rw [xiThetaTerminalMultiplicityInverseFisherField_eq_routeR_reflect,
    memℓp_two_xiDivisor_coefficient_iff (1 : ℂ) one_ne_zero]
  rw [xiZeroReflectEquiv_apply]
  simp only [Complex.sub_re, Complex.one_re]
  constructor <;> intro h <;> linarith

/-- Bilateral admission of the two orientations of one literal terminal jet is pointwise critical
line placement. -/
theorem memℓp_two_both_xiThetaTerminalMultiplicityFisherFields_iff
    (rho : XiDivisorSupport) :
    (Memℓp (xiThetaTerminalMultiplicityFisherField rho) 2 ∧
      Memℓp (xiThetaTerminalMultiplicityInverseFisherField rho) 2) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [memℓp_two_xiThetaTerminalMultiplicityFisherField_iff,
    memℓp_two_xiThetaTerminalMultiplicityInverseFisherField_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact le_antisymm hlo hhi
  · intro h
    exact ⟨h.le, h.ge⟩

def XiThetaTerminalMultiplicityBilateralFisherAdmitted
    (rho : XiDivisorSupport) : Prop :=
  Memℓp (xiThetaTerminalMultiplicityFisherField rho) 2 ∧
    Memℓp (xiThetaTerminalMultiplicityInverseFisherField rho) 2

theorem xiThetaTerminalMultiplicityBilateralFisherAdmitted_iff
    (rho : XiDivisorSupport) :
    XiThetaTerminalMultiplicityBilateralFisherAdmitted rho ↔
      (rho : ℂ).re = 1 / 2 :=
  memℓp_two_both_xiThetaTerminalMultiplicityFisherFields_iff rho

/-- Bilateral terminal-jet admission constructs the requested coefficient-faithful natural Gamma
reporter for this retained divisor. -/
theorem xiThetaTerminalMultiplicityBilateralFisherAdmitted_constructs_naturalReporter
    (rho : XiDivisorSupport)
    (h : XiThetaTerminalMultiplicityBilateralFisherAdmitted rho) :
    Nonempty
      (PrimeGammaTwoThreeSourceNaturalReporter
        (primeDepthBVWoldXiCenteredRate rho)) := by
  apply xiThetaTerminalMultiplicityTwoThreeSharedGhost_constructs_naturalReporter rho
  exact (xiThetaTerminalMultiplicityTwoThreeSharedGhost_iff_line rho).2
    ((xiThetaTerminalMultiplicityBilateralFisherAdmitted_iff rho).1 h)

/-- Global bilateral admission of these literal source fields is exactly RH. -/
theorem riemannHypothesis_iff_forall_xiThetaTerminalMultiplicityBilateralFisherAdmitted :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        XiThetaTerminalMultiplicityBilateralFisherAdmitted rho := by
  constructor
  · intro hRH rho
    apply (xiThetaTerminalMultiplicityBilateralFisherAdmitted_iff rho).2
    exact xi_divisor_support_re_eq_half_of_rh hRH rho
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (xiThetaTerminalMultiplicityBilateralFisherAdmitted_iff rho).1 (h rho)

end

end RHTower
