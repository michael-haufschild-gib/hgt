import GaloisForLFunctions.HTGeometry.MixedEvenTrigMoments
import GaloisForLFunctions.HTGeometry.HardySpace

/-!
# Exact Bernstein-row diagonalization

The squared weighted Bernstein row is exactly the diagonal central-binomial kernel after the
characteristic change of variables `B = a + b`, `D = a - b`.  Parseval supplies the row norm;
circle squaring and the mixed Wallis moment identify its diagonal form.
-/

open MeasureTheory Complex
open scoped BigOperators Nat Real Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A continuous `2 pi`-periodic integral is unchanged by angle doubling. -/
lemma integral_comp_two_eq_of_two_pi_periodic
    {f : ℝ → ℝ} (hf : Continuous f)
    (hperiod : Function.Periodic f (2 * Real.pi)) :
    (∫ x in (0 : ℝ)..2 * Real.pi, f (2 * x)) =
      ∫ x in (0 : ℝ)..2 * Real.pi, f x := by
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    fun a b => hf.intervalIntegrable a b
  have hdouble := hperiod.intervalIntegral_add_zsmul_eq (2 : ℤ) (0 : ℝ) hint
  have hdouble' : (∫ x in (0 : ℝ)..4 * Real.pi, f x) =
      2 * ∫ x in (0 : ℝ)..2 * Real.pi, f x := by
    convert hdouble using 1 <;> norm_num
    all_goals ring
  rw [intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [mul_zero]
  rw [show (2 : ℝ) * (2 * Real.pi) = 4 * Real.pi by ring, hdouble']
  simp

/-- Squared Euclidean norm of a weighted Bernstein row. -/
def bernsteinRowSquare (a b : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) ^ (2 : ℕ) * a ^ (2 * k) * b ^ (2 * (n - k))

/-- Parseval representation of the squared weighted Bernstein row. -/
theorem bernsteinRowSquare_eq_normalizedIntegral (a b : ℝ) (n : ℕ) :
    bernsteinRowSquare a b n =
      (2 * Real.pi)⁻¹ *
        (∫ x in (0 : ℝ)..2 * Real.pi,
          ‖((a : ℂ) * circleMap 0 1 x + (b : ℂ)) ^ n‖ ^ (2 : ℕ)) := by
  let c : ℕ → ℂ := fun k =>
    (((Nat.choose n k : ℝ) * a ^ k * b ^ (n - k) : ℝ) : ℂ)
  have hparseval := circleAverage_normSq_poly (1 : ℝ) (n + 1) c
  have hpoly (x : ℝ) :
      (∑ k ∈ Finset.range (n + 1), c k * (circleMap 0 1 x) ^ k) =
        ((a : ℂ) * circleMap 0 1 x + (b : ℂ)) ^ n := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [c]
    push_cast
    rw [mul_pow]
    ring
  have hfun : (fun x : ℝ =>
      ‖∑ k ∈ Finset.range (n + 1), c k * (circleMap 0 1 x) ^ k‖ ^ (2 : ℕ)) =
      fun x : ℝ => ‖((a : ℂ) * circleMap 0 1 x + (b : ℂ)) ^ n‖ ^ (2 : ℕ) := by
    funext x
    rw [hpoly]
  rw [hfun] at hparseval
  rw [hparseval, bernsteinRowSquare]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [c]
  simp only [one_pow, mul_one]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
  ring

/-- Pointwise characteristic-coordinate identity on the doubled unit circle. -/
lemma norm_pow_circleMap_two_eq_diagonalTrigKernel
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    ‖((a : ℂ) * circleMap 0 1 (2 * x) + (b : ℂ)) ^ n‖ ^ (2 : ℕ) =
      diagonalTrigKernel (a + b) (a - b) n x := by
  have hbase :
      Complex.normSq ((a : ℂ) * circleMap 0 1 (2 * x) + (b : ℂ)) =
        (a - b) ^ (2 : ℕ) * Real.sin x ^ (2 : ℕ) + (a + b) ^ (2 : ℕ) * Real.cos x ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, circleMap_zero_re, circleMap_zero_im,
      one_mul, zero_mul, sub_zero, add_zero]
    rw [Real.cos_two_mul, Real.sin_two_mul]
    have htrig := Real.sin_sq_add_cos_sq x
    linear_combination
      (a ^ (2 : ℕ) * (4 * Real.cos x ^ (2 : ℕ) - 1) + 2 * a * b - b ^ (2 : ℕ)) * htrig
  rw [norm_pow, ← pow_mul, show n * 2 = 2 * n by omega, pow_mul,
    ← Complex.normSq_eq_norm_sq, hbase]
  rfl

/-- **Exact Bernstein-row diagonalization.** -/
theorem bernsteinRowSquare_eq_centralBinomialDiagonalKernelCoefficient
    (a b : ℝ) (n : ℕ) :
    bernsteinRowSquare a b n =
      centralBinomialDiagonalKernelCoefficient (a + b) (a - b) n := by
  let f : ℝ → ℝ := fun x =>
    ‖((a : ℂ) * circleMap 0 1 x + (b : ℂ)) ^ n‖ ^ (2 : ℕ)
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hperiod : Function.Periodic f (2 * Real.pi) := by
    intro x
    dsimp only [f]
    rw [periodic_circleMap]
  rw [bernsteinRowSquare_eq_normalizedIntegral]
  have hdouble := integral_comp_two_eq_of_two_pi_periodic hf hperiod
  have hpoint : (fun x : ℝ => f (2 * x)) =
      diagonalTrigKernel (a + b) (a - b) n := by
    funext x
    exact norm_pow_circleMap_two_eq_diagonalTrigKernel a b n x
  change (2 * Real.pi)⁻¹ * (∫ x in (0 : ℝ)..2 * Real.pi, f x) = _
  rw [← hdouble, hpoint]
  exact normalizedIntegral_diagonalTrigKernel_eq_coefficient (a + b) (a - b) n

end


end GaloisForLFunctions.HTGeometry
