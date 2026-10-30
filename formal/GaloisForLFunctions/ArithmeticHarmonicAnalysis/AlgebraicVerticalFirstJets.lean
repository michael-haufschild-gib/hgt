import GaloisForLFunctions.RHTower.LadderNesting
import GaloisForLFunctions.HTGeometry.MvPolynomialSmoothEvaluation

/-!
# Algebraic coefficients make the first logarithmic jet faithful

Along the prime-logarithmic flow, the chain rule expresses the first
scalar derivative as a linear form in prime logarithms. At an algebraic
torus point its coefficients are algebraic, so Baker independence detects
every coordinate partial derivative.
-/

open MvPolynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Restrict a prime-coordinate polynomial to the logarithmic flow through a point. -/
def primeLogTrace {n : ℕ} (p : Fin n → ℕ) (F : MvPolynomial (Fin n) ℂ)
    (x : Fin n → ℂ) (s : ℂ) : ℂ :=
  eval (fun i => x i * Complex.exp (s * (Real.log (p i) : ℂ))) F

theorem primeLogTrace_zero {n : ℕ} (p : Fin n → ℕ)
    (F : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    primeLogTrace p F x 0 = eval x F := by
  simp only [primeLogTrace, zero_mul, Complex.exp_zero, mul_one]

/-- The logarithmic-flow derivative is the prime-log weighted Euler gradient. -/
theorem hasDerivAt_primeLogTrace {n : ℕ} (p : Fin n → ℕ)
    (F : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    HasDerivAt (primeLogTrace p F x)
      (∑ i, (x i * eval x (pderiv i F)) * (Real.log (p i) : ℂ)) 0 := by
  have hg (i : Fin n) :
      HasDerivAt (fun s : ℂ => x i * Complex.exp (s * (Real.log (p i) : ℂ)))
        (x i * (Real.log (p i) : ℂ)) 0 := by
    simpa only [id_eq, zero_mul, Complex.exp_zero, one_mul] using
      (((hasDerivAt_id (0 : ℂ)).mul_const (Real.log (p i) : ℂ)).cexp.const_mul (x i))
  have h := HTGeometry.hasDerivAt_mvPolynomial_eval_curve_complex F
    (fun i s => x i * Complex.exp (s * (Real.log (p i) : ℂ)))
    (fun i => x i * (Real.log (p i) : ℂ)) 0 hg
  simp only [zero_mul, Complex.exp_zero, mul_one] at h
  convert h using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem deriv_primeLogTrace {n : ℕ} (p : Fin n → ℕ)
    (F : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    deriv (primeLogTrace p F x) 0 =
      ∑ i, (x i * eval x (pderiv i F)) * (Real.log (p i) : ℂ) :=
  (hasDerivAt_primeLogTrace p F x).deriv

/-- At an algebraic torus point, one logarithmic derivative detects every partial derivative. -/
theorem algebraic_primeLogTrace_derivative_zero_iff {n : ℕ}
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (F : MvPolynomial (Fin n) (algebraicClosure ℚ ℂ))
    (x : Fin n → algebraicClosure ℚ ℂ) (hx : ∀ i, x i ≠ 0) :
    deriv (primeLogTrace p (map (algebraicClosure ℚ ℂ).subtype F)
      (fun i => (x i : ℂ))) 0 = 0 ↔ ∀ i, eval x (pderiv i F) = 0 := by
  rw [deriv_primeLogTrace]
  have heval (i : Fin n) :
      eval (fun j => (x j : ℂ)) (pderiv i (map (algebraicClosure ℚ ℂ).subtype F)) =
        ((eval x (pderiv i F) : algebraicClosure ℚ ℂ) : ℂ) := by
    rw [pderiv_map, eval_map]
    exact (eval₂_comp (algebraicClosure ℚ ℂ).subtype x (pderiv i F)).symm
  simp only [heval]
  constructor
  · intro h
    have hcoeff := (Fintype.linearIndependent_iff.mp
      (RHTower.primeLogs_algClosure_linearIndependent p hp hpinj))
        (fun i => x i * eval x (pderiv i F))
        (by simpa only [IntermediateField.smul_def, smul_eq_mul,
          IntermediateField.coe_mul] using h)
    intro i
    exact (mul_eq_zero.mp (hcoeff i)).resolve_left (hx i)
  · intro h
    simp only [h, ZeroMemClass.coe_zero, mul_zero, zero_mul, Finset.sum_const_zero]

/-- Value and first logarithmic jet recover all first-order vanishing data over algebraic numbers. -/
theorem algebraic_primeLogTrace_firstJets_vanish_iff {n : ℕ}
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (F : MvPolynomial (Fin n) (algebraicClosure ℚ ℂ))
    (x : Fin n → algebraicClosure ℚ ℂ) (hx : ∀ i, x i ≠ 0) :
    (primeLogTrace p (map (algebraicClosure ℚ ℂ).subtype F)
        (fun i => (x i : ℂ)) 0 = 0 ∧
      deriv (primeLogTrace p (map (algebraicClosure ℚ ℂ).subtype F)
        (fun i => (x i : ℂ))) 0 = 0) ↔
      eval x F = 0 ∧ ∀ i, eval x (pderiv i F) = 0 := by
  rw [algebraic_primeLogTrace_derivative_zero_iff p hp hpinj F x hx,
    primeLogTrace_zero, eval_map]
  have heval : eval₂ (algebraicClosure ℚ ℂ).subtype (fun i => (x i : ℂ)) F =
      ((eval x F : algebraicClosure ℚ ℂ) : ℂ) :=
    (eval₂_comp (algebraicClosure ℚ ℂ).subtype x F).symm
  rw [heval]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨Subtype.ext h, h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨by rw [h]; rfl, h'⟩

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
