import GaloisForLFunctions.HTGeometry.PaperFormalCoefficientDerivation
import GaloisForLFunctions.HTGeometry.PaperPrimeFlowCoefficients
import GaloisForLFunctions.HTGeometry.FinitePrimeCoefficientDifferentialField

/-!
# Exact logarithmic covariance of the coefficient-mixing prime flow

The native prime/logarithmic Euler commutator propagates through every
prime derivative and through the complete formal exponential. The correction
is the formal-time Euler operator, with coefficient i log p. No convergence
or zero-location premise enters this identity on the full arithmetic algebra.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The native Euler commutator at every derivative order, for arbitrary arithmetic input. -/
theorem paperPrimeArithmetic_log_iterate (p : Nat.Primes) (f : ArithmeticFunction ℂ)
    (m : ℕ) :
    (primeArithmeticDerivation (p : ℕ) p.property :
        ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m]
        (rotatedLogArithmeticDerivationComplex f) =
      rotatedLogArithmeticDerivationComplex
        ((primeArithmeticDerivation (p : ℕ) p.property :
          ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] f) +
        ((m : ℂ) * (Complex.I * (Real.log (p : ℕ) : ℂ))) •
          ((primeArithmeticDerivation (p : ℕ) p.property :
            ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] f) := by
  let D := primeArithmeticDerivation (p : ℕ) p.property
  let L := rotatedLogArithmeticDerivationComplex
  let w : ℂ := Complex.I * (Real.log (p : ℕ) : ℂ)
  have hcomm (g : ArithmeticFunction ℂ) : D (L g) = L (D g) + w • D g := by
    have h := primeDeriv_rotatedLogArithmetic_commutator p g
    change D (L g) - L (D g) = w • D g at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  change (D : ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] (L f) =
    L ((D : ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] f) +
      ((m : ℂ) * w) • ((D : ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] f)
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Function.iterate_succ_apply', ih, map_add, Derivation.map_smul, hcomm]
      push_cast
      module

/-- Each formal-time coefficient carries exactly its order times the prime logarithmic weight. -/
theorem paperArithmeticPrimeFormalFlow_log_coeff (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) (m : ℕ) :
    PowerSeries.coeff m
        (paperArithmeticPrimeFormalFlow p (rotatedLogArithmeticDerivationComplex f)) =
      rotatedLogArithmeticDerivationComplex
        (PowerSeries.coeff m (paperArithmeticPrimeFormalFlow p f)) +
      ((m : ℂ) * (Complex.I * (Real.log (p : ℕ) : ℂ))) •
        PowerSeries.coeff m (paperArithmeticPrimeFormalFlow p f) := by
  simp only [paperArithmeticPrimeFormalFlow, paperFormalExponential_coeff]
  rw [paperPrimeArithmetic_log_iterate, smul_add, Derivation.map_smul]
  module

/-- The full prime transport intertwines the logarithmic clock with a formal-time Euler correction. -/
theorem paperArithmeticPrimeFormalFlow_log_covariance (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) :
    paperArithmeticPrimeFormalFlow p (rotatedLogArithmeticDerivationComplex f) =
      paperFormalCoefficientDerivation rotatedLogArithmeticDerivationComplex
        (paperArithmeticPrimeFormalFlow p f) +
      (Complex.I * (Real.log (p : ℕ) : ℂ)) •
        (PowerSeries.X * PowerSeries.derivative (ArithmeticFunction ℂ)
          (paperArithmeticPrimeFormalFlow p f)) := by
  apply PowerSeries.ext
  intro m
  rw [paperArithmeticPrimeFormalFlow_log_coeff, map_add,
    paperFormalCoefficientDerivation_coeff, PowerSeries.coeff_smul, paperFormalTimeEuler_coeff]
  module

/-- The native logarithmic clock preserves every complete prime-terminating algebra. -/
theorem paperPrimeTerminatingCore_log_mem (p : Nat.Primes)
    (f : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
    rotatedLogArithmeticDerivationComplex (f : ArithmeticFunction ℂ) ∈
      paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property) := by
  obtain ⟨m, hm⟩ := (paperTerminatingCore_mem_iff _ _).mp f.property
  apply (paperTerminatingCore_mem_iff _ _).mpr
  refine ⟨m, ?_⟩
  rw [paperPrimeArithmetic_log_iterate, hm]
  simp

end

end GaloisForLFunctions.HTGeometry
