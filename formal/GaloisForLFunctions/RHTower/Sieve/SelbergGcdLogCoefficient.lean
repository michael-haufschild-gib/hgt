import GaloisForLFunctions.RHTower.Sieve.BivariateDerivation
import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionCoefficient
import GaloisForLFunctions.RHTower.Sieve.SelbergPrincipalOriginalCoefficients

/-!
# The gcd-logarithmic Selberg coefficient is a derivation

`c(m,n)·log (m,n)` is the `s`-derivative at `s = 1` of `c_s(m,n) = μ(m)μ(n)(m,n)^s/(mn)`.  It is
therefore not multiplicative, but it *is* a Leibniz derivation of the original Selberg coefficient:
pair-coprime arguments split the gcd, hence split its logarithm additively.

This is the first of the two derivation instances the gcd-logarithmic asymptotic needs; the other is
the convolution `corr ∗ 𝒫^{log} + corr^{log} ∗ 𝒫`, supplied by
`BivariateDerivation.convolution`.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- The gcd-logarithmic weight of the original Selberg coefficient. -/
def selbergOriginalGcdLogCoeff (m n : ℕ) : ℝ :=
  selbergOriginalCoeff m n * Real.log ((Nat.gcd m n : ℕ) : ℝ)

@[simp] theorem selbergOriginalGcdLogCoeff_one :
    selbergOriginalGcdLogCoeff 1 1 = 0 := by
  simp [selbergOriginalGcdLogCoeff]

/-- **`c·log(m,n)` is a Leibniz derivation of the original Selberg coefficient.** -/
theorem bivariateDerivation_selbergOriginalGcdLogCoeff :
    BivariateDerivation selbergOriginalCoeff selbergOriginalGcdLogCoeff := by
  constructor
  · exact selbergOriginalGcdLogCoeff_one
  · intro a b c d h
    by_cases hab0 : a * b = 0
    · have hcd1 : c * d = 1 := by
        have hcop : Nat.Coprime 0 (c * d) := by rw [← hab0]; exact h
        simpa using hcop
      have hc1 : c = 1 := Nat.dvd_one.mp ⟨d, hcd1.symm⟩
      have hd1 : d = 1 := Nat.dvd_one.mp ⟨c, by rw [Nat.mul_comm]; exact hcd1.symm⟩
      subst hc1
      subst hd1
      simp [selbergOriginalGcdLogCoeff_one, selbergOriginalCoeff_one]
    by_cases hcd0 : c * d = 0
    · have hab1 : a * b = 1 := by
        have hcop : Nat.Coprime (a * b) 0 := by rw [← hcd0]; exact h
        simpa using hcop
      have ha1 : a = 1 := Nat.dvd_one.mp ⟨b, hab1.symm⟩
      have hb1 : b = 1 := Nat.dvd_one.mp ⟨a, by rw [Nat.mul_comm]; exact hab1.symm⟩
      subst ha1
      subst hb1
      simp [selbergOriginalGcdLogCoeff_one, selbergOriginalCoeff_one]
    have ha : 0 < a := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hb : 0 < b := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hc : 0 < c := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    have hd : 0 < d := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    have hgab : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
    have hgcd : 0 < Nat.gcd c d := Nat.gcd_pos_of_pos_left d hc
    have hgabR : ((Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hgab.ne'
    have hgcdR : ((Nat.gcd c d : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hgcd.ne'
    have hgsplit : Nat.gcd (a * c) (b * d) = Nat.gcd a b * Nat.gcd c d :=
      gcd_pair_mul_of_pair_coprime h
    have hlog : Real.log ((Nat.gcd (a * c) (b * d) : ℕ) : ℝ) =
        Real.log ((Nat.gcd a b : ℕ) : ℝ) + Real.log ((Nat.gcd c d : ℕ) : ℝ) := by
      rw [hgsplit]
      push_cast
      exact Real.log_mul hgabR hgcdR
    rw [selbergOriginalGcdLogCoeff, selbergOriginalGcdLogCoeff,
      selbergOriginalGcdLogCoeff, hlog,
      bivariateMultiplicative_selbergOriginalCoeff.map_mul_of_pair_coprime h]
    ring

/-- The gcd-logarithmic Selberg log-monomial: the object whose asymptotic the corrected
Levinson route needs. -/
def selbergOriginalGcdLogMonomial (i j N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    selbergOriginalGcdLogCoeff m n *
      (Real.log ((N : ℝ) / (m : ℝ)) ^ i * Real.log ((N : ℝ) / (n : ℝ)) ^ j)

end

end RHTower.Sieve
