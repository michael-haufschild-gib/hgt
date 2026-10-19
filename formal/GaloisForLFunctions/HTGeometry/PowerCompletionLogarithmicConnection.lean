import GaloisForLFunctions.HTGeometry.ArithmeticPowerDilation
import GaloisForLFunctions.HTGeometry.DirichletMaurerCartanMellinOrbitLaw

/-!
The logarithmic derivative of weighted power completion is an exact convolution
connection. Its potential is the dilated von Mangoldt function, including the
power-clock factor. Möbius inversion conjugates every iterated logarithmic
derivative to an iterate of this connection, coefficientwise and without an
analytic convergence premise.
This connects the power-completion mechanism of paper2, Section 5, to the
existing arithmetic logarithmic derivation and von Mangoldt current.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open _root_.RHTower

/-- The algebraic chain rule applies to arbitrary arithmetic coefficients. -/
theorem arithmeticLogDerivation_powerTwistedDilation
    (m : ℕ) (w : ℕ →* ℂ) (f : ArithmeticFunction ℂ) :
    arithmeticLogDerivation (powerTwistedDilation m w f) =
      ((m + 1 : ℕ) : ℂ) • powerTwistedDilation m w (arithmeticLogDerivation f) := by
  ext n
  by_cases hn : ∃ k, k ^ (m + 1) = n
  · obtain ⟨k, rfl⟩ := hn
    change (Real.log (k ^ (m + 1) : ℕ) : ℂ) *
        powerTwistedDilation m w f (k ^ (m + 1)) =
      ((m + 1 : ℕ) : ℂ) *
        powerTwistedDilation m w (arithmeticLogDerivation f) (k ^ (m + 1))
    simp only [powerTwistedDilation_apply_pow, arithmeticLogDerivation_apply,
      Nat.cast_pow, Real.log_pow,
      Complex.ofReal_mul, Complex.ofReal_natCast]
    ring
  · have hz (g : ArithmeticFunction ℂ) : powerTwistedDilation m w g n = 0 :=
      mPart_apply_of_forall_pow_ne _ _ (fun k hk => hn ⟨k, hk⟩)
    change (Real.log n : ℂ) * powerTwistedDilation m w f n =
      ((m + 1 : ℕ) : ℂ) * powerTwistedDilation m w (arithmeticLogDerivation f) n
    simp [hz]

/-- The source term created by differentiating the completed factor. -/
def powerCompletionPotential (m : ℕ) (w : ℕ →* ℂ) : ArithmeticFunction ℂ :=
  ((m + 1 : ℕ) : ℂ) • powerTwistedDilation m w complexVonMangoldt

theorem powerCompletionPotential_apply_pow
    (m : ℕ) (w : ℕ →* ℂ) (n : ℕ) :
    powerCompletionPotential m w (n ^ (m + 1)) =
      ((m + 1 : ℕ) : ℂ) * (w n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
  simp [powerCompletionPotential,
    powerTwistedDilation_apply_pow, complexVonMangoldt, smul_eq_mul]

/-- The completed logarithmic derivative retains the exact von Mangoldt source. -/
theorem powerCompletion_logarithmicDerivative
    (m : ℕ) (w : ℕ →* ℂ) :
    powerTwistedDilation m w (moebius : ArithmeticFunction ℂ) *
        arithmeticLogDerivation (powerTwistedDilation m w (zeta : ArithmeticFunction ℂ)) =
      powerCompletionPotential m w := by
  rw [arithmeticLogDerivation_powerTwistedDilation, mul_smul_comm,
    ← map_mul, arithmeticLogDerivation_zeta, complex_moebius_mul_log_eq_vonMangoldt]
  rfl

theorem arithmeticLogDerivation_completedZeta
    (m : ℕ) (w : ℕ →* ℂ) :
    arithmeticLogDerivation (powerTwistedDilation m w (zeta : ArithmeticFunction ℂ)) =
      powerTwistedDilation m w (zeta : ArithmeticFunction ℂ) *
        powerCompletionPotential m w := by
  rw [← powerCompletion_logarithmicDerivative]
  rw [← mul_assoc, mul_comm (powerTwistedDilation m w (zeta : ArithmeticFunction ℂ)),
    ← map_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta, map_one, one_mul]

/-- Logarithmic differentiation after completion, pulled back to the original coefficients. -/
def powerCompletionConnection (m : ℕ) (w : ℕ →* ℂ)
    (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  arithmeticLogDerivation f + powerCompletionPotential m w * f

private theorem logDerivation_mul (f g : ArithmeticFunction ℂ) :
    arithmeticLogDerivation (f * g) =
      arithmeticLogDerivation f * g + f * arithmeticLogDerivation g := by
  have h := arithmeticLogDerivation.leibniz f g
  change arithmeticLogDerivation (f * g) =
    f * arithmeticLogDerivation g + g * arithmeticLogDerivation f at h
  rw [h]
  ring

theorem arithmeticLogDerivation_powerCompletion
    (m : ℕ) (w : ℕ →* ℂ) (f : ArithmeticFunction ℂ) :
    arithmeticLogDerivation (powerTwistedDilation m w (zeta : ArithmeticFunction ℂ) * f) =
      powerTwistedDilation m w (zeta : ArithmeticFunction ℂ) *
        powerCompletionConnection m w f := by
  rw [logDerivation_mul, arithmeticLogDerivation_completedZeta,
    powerCompletionConnection]
  ring

/-- Every logarithmic moment of the completed sum has the same exact conjugation law. -/
theorem iterate_arithmeticLogDerivation_powerCompletion
    (m : ℕ) (w : ℕ →* ℂ) (k : ℕ) (f : ArithmeticFunction ℂ) :
    (arithmeticLogDerivation^[k])
        (powerTwistedDilation m w (zeta : ArithmeticFunction ℂ) * f) =
      powerTwistedDilation m w (zeta : ArithmeticFunction ℂ) *
        ((powerCompletionConnection m w)^[k]) f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      arithmeticLogDerivation_powerCompletion]

theorem moebius_reconstructs_completed_logarithmic_moments
    (m : ℕ) (w : ℕ →* ℂ) (k : ℕ) (f : ArithmeticFunction ℂ) :
    powerTwistedDilation m w (moebius : ArithmeticFunction ℂ) *
        (arithmeticLogDerivation^[k])
          (powerTwistedDilation m w (zeta : ArithmeticFunction ℂ) * f) =
      ((powerCompletionConnection m w)^[k]) f := by
  rw [iterate_arithmeticLogDerivation_powerCompletion,
    powerTwistedDilation_moebius_zeta_cancel]

/-- The completed Möbius inverse is an exact horizontal section. -/
theorem powerCompletionConnection_moebius
    (m : ℕ) (w : ℕ →* ℂ) :
    powerCompletionConnection m w
      (powerTwistedDilation m w (moebius : ArithmeticFunction ℂ)) = 0 := by
  have h := moebius_reconstructs_completed_logarithmic_moments m w 1
    (powerTwistedDilation m w (moebius : ArithmeticFunction ℂ))
  rw [Function.iterate_one, Function.iterate_one, mul_comm
      (powerTwistedDilation m w (zeta : ArithmeticFunction ℂ)),
    ← map_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta, map_one,
    Derivation.map_one_eq_zero, mul_zero] at h
  exact h.symm

/-- The second moment contains both the differentiated source and its convolution square. -/
theorem powerCompletionConnection_second
    (m : ℕ) (w : ℕ →* ℂ) (f : ArithmeticFunction ℂ) :
    powerCompletionConnection m w (powerCompletionConnection m w f) =
      arithmeticLogDerivation (arithmeticLogDerivation f) +
        2 * powerCompletionPotential m w * arithmeticLogDerivation f +
        (arithmeticLogDerivation (powerCompletionPotential m w) +
          powerCompletionPotential m w ^ 2) * f := by
  simp only [powerCompletionConnection, map_add, logDerivation_mul]
  ring

end GaloisForLFunctions.HTGeometry
