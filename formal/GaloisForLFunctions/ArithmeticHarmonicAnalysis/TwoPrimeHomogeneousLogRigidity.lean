import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.HTGeometry.TranscendentalPowerIndependence
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Homogeneous logarithmic forms for two primes

At each fixed degree, monomials in two distinct prime logarithms are
linearly independent over the algebraic numbers. Dividing by a power of
one logarithm reduces this to the transcendence of their ratio.
Relations mixing degrees are outside this statement.
-/

open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- A homogeneous binary family is independent when its coordinate ratio is transcendental. -/
theorem homogeneousPower_linearIndependent {K A : Type*} [Field K] [Field A]
    [Algebra K A] {x y : A} (hy : y ≠ 0) (hxy : Transcendental K (x / y)) (T : ℕ) :
    LinearIndependent K (fun j : Fin (T + 1) => x ^ j.val * y ^ (T - j.val)) := by
  have hscale (j : Fin (T + 1)) :
      y ^ T * (x / y) ^ j.val = x ^ j.val * y ^ (T - j.val) := by
    rw [div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero j.val hy)]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)]
    exact mul_comm _ _
  have hpow : LinearIndependent K (fun j : Fin (T + 1) => (x / y) ^ j.val) :=
    transcendental_pow_comp_linearIndependent hxy Fin.val_injective
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  apply (Fintype.linearIndependent_iff.mp hpow) c ?_ j
  apply (mul_eq_zero.mp (show y ^ T * (∑ i, c i • (x / y) ^ i.val) = 0 from ?_)).resolve_left
    (pow_ne_zero T hy)
  calc
    y ^ T * (∑ i, c i • (x / y) ^ i.val) =
        ∑ i, c i • (x ^ i.val * y ^ (T - i.val)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_smul_comm, hscale]
    _ = 0 := hc

/-- Every fixed-degree homogeneous family in two prime logs is rationally independent. -/
theorem twoPrimeLog_homogeneous_linearIndependent {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (T : ℕ) :
    LinearIndependent ℚ (fun j : Fin (T + 1) =>
      Real.log p ^ j.val * Real.log q ^ (T - j.val)) :=
  homogeneousPower_linearIndependent
    (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
    (RHTower.log_ratio_transcendental hq hp hpq.symm) T

/-- Homogeneous two-prime log forms admit no nonzero algebraic-coefficient relation. -/
theorem twoPrimeLog_homogeneous_algClosure_linearIndependent {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (T : ℕ) :
    LinearIndependent (algebraicClosure ℚ ℂ) (fun j : Fin (T + 1) =>
      (Real.log p : ℂ) ^ j.val * (Real.log q : ℂ) ^ (T - j.val)) := by
  have hratioQ : Transcendental ℚ ((Real.log p : ℂ) / (Real.log q : ℂ)) := by
    rw [← Complex.ofReal_div]
    intro h
    exact RHTower.log_ratio_transcendental hq hp hpq.symm
      ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℚ ℝ ℂ)
        Complex.ofReal_injective).mp h)
  letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  exact homogeneousPower_linearIndependent
    (Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hq.one_lt)).ne')
    (hratioQ.extendScalars (algebraicClosure ℚ ℂ)) T

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
