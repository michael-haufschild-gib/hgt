import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicVerticalFirstJets
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.EulerOperatorsLowerMultiplicity
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!+# Higher logarithmic-flow jets

The weighted Euler operator gives every scalar derivative of a polynomial
along the prime-logarithmic flow. Leibniz transports point multiplicity to
scalar vanishing order for every finite coordinate family.
-/

open MvPolynomial
noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Euler differentiation in the logarithmic-flow direction. -/
def primeLogEuler {n : ℕ} (p : Fin n → ℕ) (F : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ :=
  ∑ i, C (Real.log (p i) : ℂ) * X i * pderiv i F

theorem hasDerivAt_primeLogTrace_at {n : ℕ} (p : Fin n → ℕ)
    (F : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (s : ℂ) :
    HasDerivAt (primeLogTrace p F x) (primeLogTrace p (primeLogEuler p F) x s) s := by
  have hg (i : Fin n) :
      HasDerivAt (fun z : ℂ => x i * Complex.exp (z * (Real.log (p i) : ℂ)))
        (x i * Complex.exp (s * (Real.log (p i) : ℂ)) * (Real.log (p i) : ℂ)) s := by
    convert (((hasDerivAt_id s).mul_const (Real.log (p i) : ℂ)).cexp.const_mul (x i))
      using 1 <;> ring
  have h := HTGeometry.hasDerivAt_mvPolynomial_eval_curve_complex F
    (fun i z => x i * Complex.exp (z * (Real.log (p i) : ℂ)))
    (fun i => x i * Complex.exp (s * (Real.log (p i) : ℂ)) * (Real.log (p i) : ℂ)) s hg
  convert h using 1
  · rfl
  · simp only [primeLogTrace, primeLogEuler, map_sum, eval_mul, eval_C, eval_X]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem deriv_primeLogTrace_eq {n : ℕ} (p : Fin n → ℕ)
    (F : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    deriv (primeLogTrace p F x) = primeLogTrace p (primeLogEuler p F) x := by
  funext s
  exact (hasDerivAt_primeLogTrace_at p F x s).deriv

/-- All scalar jets are exact iterates of the logarithmic Euler operator. -/
theorem iteratedDeriv_primeLogTrace {n : ℕ} (p : Fin n → ℕ)
    (F : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (k : ℕ) :
    iteratedDeriv k (primeLogTrace p F x) =
      primeLogTrace p ((primeLogEuler p)^[k] F) x := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, deriv_primeLogTrace_eq, Function.iterate_succ_apply']

theorem primeLogEuler_mem_ideal_pow {n : ℕ} (p : Fin n → ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (m : ℕ) {F : MvPolynomial (Fin n) ℂ}
    (hF : F ∈ I ^ (m + 1)) : primeLogEuler p F ∈ I ^ m := by
  apply (I ^ m).sum_mem
  intro i _
  exact (I ^ m).mul_mem_left _ (derivation_mem_ideal_pow (pderiv i) I m hF)

/-- A scalar jet of order `k` loses at most `k` factors of any ideal. -/
theorem iterate_primeLogEuler_mem_ideal_pow {n : ℕ} (p : Fin n → ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (m k : ℕ) {F : MvPolynomial (Fin n) ℂ}
    (hF : F ∈ I ^ (m + k)) : (primeLogEuler p)^[k] F ∈ I ^ m := by
  induction k generalizing m with
  | zero => simpa only [Nat.add_zero, Function.iterate_zero, id_eq] using hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    apply primeLogEuler_mem_ideal_pow p I m
    apply ih (m + 1)
    simpa only [Nat.add_assoc, Nat.add_comm 1] using hF

/-- Point multiplicity forces every lower scalar logarithmic jet to vanish. -/
theorem iteratedDeriv_primeLogTrace_eq_zero_of_mem_pointIdeal_pow {n : ℕ}
    (p : Fin n → ℕ) (F : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) {r k : ℕ}
    (hF : F ∈ vanishingIdeal ℂ {x} ^ r) (hk : k < r) :
    iteratedDeriv k (primeLogTrace p F x) 0 = 0 := by
  rw [iteratedDeriv_primeLogTrace, primeLogTrace_zero]
  have hpow : (primeLogEuler p)^[k] F ∈ vanishingIdeal ℂ {x} ^ (r - k) := by
    apply iterate_primeLogEuler_mem_ideal_pow p _ (r - k) k
    simpa only [Nat.sub_add_cancel hk.le] using hF
  have hmem := Ideal.pow_le_pow_right (by omega : 1 ≤ r - k) hpow
  simpa only [pow_one, mem_vanishingIdeal_singleton_iff, aeval_eq_eval] using hmem

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iteratedDeriv_primeLogTrace
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iteratedDeriv_primeLogTrace_eq_zero_of_mem_pointIdeal_pow
