import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberTranslation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationCurrent
import Mathlib.Algebra.Polynomial.Div

/-!
# Radial orientation of the finite translation edge

The exact finite cosine translation edge vanishes through degree `2*d+1`.  Hence it contains a
forced factor `X^(2*d+2)`.  On the upper half-plane this factor contributes an explicit negative
radial current.  The only possible positive current is the current of the residual polynomial.
-/

open Complex Polynomial
namespace RHTower
noncomputable section

lemma normSq_pow_xiCTaylorThetaTailFiniteTranslationRadialEdge (z : ℂ) (m : ℕ) :
    Complex.normSq (z ^ m) = Complex.normSq z ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Complex.normSq_mul, ih, pow_succ]

theorem orientedPolynomialCurrent_X (z : ℂ) :
    orientedPolynomialCurrent (X : Polynomial ℂ) z = -z.im := by
  unfold orientedPolynomialCurrent
  simp

lemma orientedPolynomialCurrent_X_pow_succ (m : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (X ^ (m + 1) : Polynomial ℂ) z =
      -((m + 1 : ℕ) : ℝ) * z.im * Complex.normSq z ^ m := by
  induction m with
  | zero => simpa using orientedPolynomialCurrent_X z
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ,
        orientedPolynomialCurrent_mul, ih, eval_pow, eval_X, normSq_pow_xiCTaylorThetaTailFiniteTranslationRadialEdge,
        orientedPolynomialCurrent_X]
      push_cast
      rw [pow_succ]
      ring

theorem orientedPolynomialCurrent_X_pow (m : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (X ^ m : Polynomial ℂ) z =
      -(m : ℝ) * z.im * Complex.normSq z ^ (m - 1) := by
  cases m with
  | zero => simp [orientedPolynomialCurrent]
  | succ m => simpa using orientedPolynomialCurrent_X_pow_succ m z

/-- Exact current law for a polynomial with a prescribed radial zero at the origin. -/
theorem orientedPolynomialCurrent_X_pow_mul
    (m : ℕ) (P : Polynomial ℂ) (z : ℂ) :
    orientedPolynomialCurrent (X ^ m * P) z =
      Complex.normSq z ^ m * orientedPolynomialCurrent P z -
        (m : ℝ) * z.im * Complex.normSq z ^ (m - 1) *
          Complex.normSq (P.eval z) := by
  rw [orientedPolynomialCurrent_mul, orientedPolynomialCurrent_X_pow,
    eval_pow, eval_X, normSq_pow_xiCTaylorThetaTailFiniteTranslationRadialEdge]
  ring

/-- The full common-cutoff loss has a zero of order at least `2*d+2` at the spectral origin. -/
theorem finiteCosineTranslationTopEdge_X_pow_dvd
    (d : ℕ) (x a : ℝ) :
    (X : Polynomial ℂ) ^ (2 * d + 2) ∣
      finiteCosineTranslationTopEdge d x a := by
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  exact finiteCosineTranslationTopEdge_coeff_eq_zero_of_le d x a (by omega)

theorem exists_finiteCosineTranslationTopEdge_radialFactor
    (d : ℕ) (x a : ℝ) :
    ∃ R : Polynomial ℂ,
      finiteCosineTranslationTopEdge d x a = X ^ (2 * d + 2) * R := by
  obtain ⟨R, hR⟩ := finiteCosineTranslationTopEdge_X_pow_dvd d x a
  exact ⟨R, hR⟩

/-- The exact orientation split for any residual factor of the finite translation edge.  The
second term is nonpositive whenever `Im z >= 0`; it is the degree-sized radial gain that must
absorb the residual off-diagonal current. -/
theorem finiteCosineTranslationTopEdge_radial_current
    (d : ℕ) (x a : ℝ) (R : Polynomial ℂ)
    (hR : finiteCosineTranslationTopEdge d x a = X ^ (2 * d + 2) * R)
    (z : ℂ) :
    orientedPolynomialCurrent (finiteCosineTranslationTopEdge d x a) z =
      Complex.normSq z ^ (2 * d + 2) * orientedPolynomialCurrent R z -
        ((2 * d + 2 : ℕ) : ℝ) * z.im * Complex.normSq z ^ (2 * d + 1) *
          Complex.normSq (R.eval z) := by
  rw [hR, orientedPolynomialCurrent_X_pow_mul,
    show 2 * d + 2 - 1 = 2 * d + 1 by omega]

end
end RHTower
