import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeRestriction
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerCoefficients

/-!+# Exact relations created by a finite Euler modification

Deleting the modifying prime from the quadratic Euler modification of zeta recovers the same
partial zeta stream. Consequently the two full coefficient streams satisfy an exact relation
whose coefficients use only that prime. The local coefficient at one is one on both sides,
so both coefficients are units in the formal Dirichlet algebra.
-/

noncomputable section

namespace GaloisForLFunctions.SelbergClass.PositiveFiniteEuler

open ArithmeticFunction DirichletSeries
open scoped Classical

/-- Removing the modifying prime erases the entire quadratic Euler modification. -/
theorem primeRestrict_compl_singleton (p : Nat.Primes) (A : ℝ) :
    primeRestrict ({(p : ℕ)}ᶜ) (arithmeticCoeffs p A) =
      primeRestrict ({(p : ℕ)}ᶜ) (zeta : ArithmeticFunction ℂ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  by_cases hs : (↑n.primeFactors : Set ℕ) ⊆ {(p : ℕ)}ᶜ
  · have hpn : ¬ (p : ℕ) ∣ n := by
      intro hd
      have hp := hs (Nat.mem_primeFactors.mpr ⟨p.2, hd, hn⟩)
      exact hp rfl
    have hp2n : ¬ (p : ℕ) ^ 2 ∣ n := fun h =>
      hpn (dvd_trans (dvd_pow_self (p : ℕ) (by omega)) h)
    simp [primeRestrict_apply, hs, arithmeticCoeffs_apply, coeff, hn, hpn, hp2n,
      ArithmeticFunction.zeta_apply]
  · simp [primeRestrict_apply, hs]

/-- The explicit dependence relation uses only coefficients supported at the modifying prime. -/
theorem finite_euler_cross_relation (p : Nat.Primes) (A : ℝ) :
    primeRestrict {(p : ℕ)} (zeta : ArithmeticFunction ℂ) * arithmeticCoeffs p A =
      primeRestrict {(p : ℕ)} (arithmeticCoeffs p A) * (zeta : ArithmeticFunction ℂ) :=
  euler_cross_relation {(p : ℕ)} _ _ (arithmeticCoeffs_isMultiplicative p.2 A)
    isMultiplicative_zeta.natCast (primeRestrict_compl_singleton p A)

/-- Both coefficients in the dependence relation are units; neither coefficient vanishes. -/
theorem finite_euler_relation_coefficients_are_units (p : Nat.Primes) (A : ℝ) :
    IsUnit (primeRestrict {(p : ℕ)} (zeta : ArithmeticFunction ℂ)) ∧
      IsUnit (primeRestrict {(p : ℕ)} (arithmeticCoeffs p A)) := by
  simp only [isUnit_primeRestrict_iff, ArithmeticFunction.isUnit_iff_isUnit_apply_one,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    arithmeticCoeffs_apply, coeff_one p.2, Complex.ofReal_one]
  simp

end GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
