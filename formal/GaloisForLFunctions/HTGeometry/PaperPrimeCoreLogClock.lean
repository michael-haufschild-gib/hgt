import GaloisForLFunctions.HTGeometry.PaperPrimeLogFormalCovariance
import GaloisForLFunctions.HTGeometry.PaperPrimeTerminatingSlice

/-!
# Two interacting clocks on the entire prime-terminating algebra

The logarithmic clock restricts to the maximal prime core and retains the
native Euler commutator with its locally nilpotent prime clock. Its own
polynomial formal orbits are only scalar constants, so this restriction is
not locally nilpotent despite preservation of the whole prime core.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

/-- The actual logarithmic derivation restricted to the complete prime core. -/
def paperPrimeCoreLogClock (p : Nat.Primes) :
    Derivation ℂ
      (paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
      (paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) where
  toFun f := ⟨rotatedLogArithmeticDerivationComplex f, paperPrimeTerminatingCore_log_mem p f⟩
  map_add' f g := Subtype.ext (by simp)
  map_smul' c f := Subtype.ext (by simp)
  map_one_eq_zero' := Subtype.ext (by simp)
  leibniz' f g := Subtype.ext (by simp)

@[simp] theorem paperPrimeCoreLogClock_coe (p : Nat.Primes)
    (f : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
    (paperPrimeCoreLogClock p f : ArithmeticFunction ℂ) =
      rotatedLogArithmeticDerivationComplex (f : ArithmeticFunction ℂ) := rfl

/-- Every restricted logarithmic iterate agrees with its ambient arithmetic iterate. -/
theorem paperPrimeCoreLogClock_iterate_coe (p : Nat.Primes)
    (f : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) (m : ℕ) :
    ((paperPrimeCoreLogClock p)^[m] f : ArithmeticFunction ℂ) =
      (rotatedLogArithmeticDerivationComplex :
        ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] (f : ArithmeticFunction ℂ) := by
  have h := derivation_iterate_naturality (paperPrimeCoreLogClock p)
    rotatedLogArithmeticDerivationComplex
    (paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)).val
    (fun _ => rfl) m f
  exact h.symm

/-- The full prime core supports the same noncommuting prime/logarithmic clock pair. -/
theorem paperPrimeCoreLogClock_commutator (p : Nat.Primes)
    (f : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
    paperTerminatingClock (primeArithmeticDerivation (p : ℕ) p.property)
        (paperPrimeCoreLogClock p f) -
      paperPrimeCoreLogClock p
        (paperTerminatingClock (primeArithmeticDerivation (p : ℕ) p.property) f) =
      (Complex.I * (Real.log (p : ℕ) : ℂ)) •
        paperTerminatingClock (primeArithmeticDerivation (p : ℕ) p.property) f := by
  apply Subtype.ext
  exact primeDeriv_rotatedLogArithmetic_commutator p (f : ArithmeticFunction ℂ)

/-- Inside the prime core, the logarithmic formal flow is polynomial only on scalar inputs. -/
theorem paperPrimeCoreLogClock_polynomial_iff (p : Nat.Primes)
    (f : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
    (∃ P : Polynomial (paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)),
      paperFormalExponential (paperPrimeCoreLogClock p) f =
        (P : PowerSeries (paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)))) ↔
      (f : ArithmeticFunction ℂ) = (f : ArithmeticFunction ℂ) 1 •
        (1 : ArithmeticFunction ℂ) := by
  have hpoly := paperFormalExponential_polynomial_iff (k := ℂ)
    (A := paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
    (paperPrimeCoreLogClock p) f
  have hiter : (∃ m : ℕ, (paperPrimeCoreLogClock p)^[m] f = 0) ↔
      ∃ m : ℕ, (rotatedLogArithmeticDerivationComplex :
        ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] (f : ArithmeticFunction ℂ) = 0 := by
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, (paperPrimeCoreLogClock_iterate_coe p f m).symm.trans
        (congrArg Subtype.val hm)⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, Subtype.ext ((paperPrimeCoreLogClock_iterate_coe p f m).trans hm)⟩
  exact hpoly.trans (hiter.trans (paperArithmeticLog_terminates_iff (f : ArithmeticFunction ℂ)))

/-- Preservation of the prime core does not make the logarithmic clock locally nilpotent. -/
theorem paperPrimeCoreLogClock_not_locallyNilpotent (p : Nat.Primes) :
    ¬ IsLocallyNilpotent (k := ℂ)
      (A := paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
      (paperPrimeCoreLogClock p) := by
  intro h
  obtain ⟨m, hm⟩ := h (paperPrimeTerminatingGenerator p)
  have he := paperPrimeCoreLogClock_iterate_coe p (paperPrimeTerminatingGenerator p) m
  rw [hm] at he
  have hs := (paperArithmeticLog_terminates_iff (paperPrimeCoordinate p)).mp ⟨m, he.symm⟩
  have hv := congrArg (fun f : ArithmeticFunction ℂ => f (p : ℕ)) hs
  simp [ArithmeticFunction.smul_map, p.property.ne_one] at hv

end

end GaloisForLFunctions.HTGeometry
