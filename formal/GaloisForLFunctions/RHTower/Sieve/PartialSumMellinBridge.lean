import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# The Mertens function as the Mellin datum of `1/ζ`

For `Re s > 1`,

`1/ζ(s) = s ∫_1^∞ M(⌊t⌋) t^(-(s+1)) dt`,   `M(m) = ∑_{k ≤ m} μ(k)`.

The integral representation of a Dirichlet series through the partial sums of its coefficients is
mathlib's `LSeries_eq_mul_integral'`, and its zeta instance is `RHTower.riemannZeta_eq_mul_integral_floor`;
what is recorded here is the Möbius instance, obtained from `‖μ‖ ≤ 1` and `L(μ, s) = 1/ζ(s)`.

The kernel attached to the vertical line is `1/s`, decaying like `1/|t|`, in contrast with the smoothed
cutoffs used elsewhere in the corpus, whose kernels are Mellin transforms of a smoothing profile. This
is the identity underlying every Mertens-type criterion: a bound `M(x) = O(x^θ)` makes the right-hand
side converge for `Re s > θ`.
-/

open Complex Filter MeasureTheory Set Asymptotics Topology

noncomputable section

namespace RHTower.Sieve

/-- **The Mertens instance of the integral representation.** -/
theorem inv_riemannZeta_eq_mul_integral_mertens {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹
      = s * ∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.moebius k : ℤ) : ℂ))
            * ((t : ℝ) : ℂ) ^ (-(s + 1)) := by
  have hbdd : ∀ n : ℕ, ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    intro n
    have habs : |ArithmeticFunction.moebius n| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
    have hR : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast habs
    rw [show ((ArithmeticFunction.moebius n : ℤ) : ℂ)
        = ((((ArithmeticFunction.moebius n : ℤ) : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact hR
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖((ArithmeticFunction.moebius k : ℤ) : ℂ)‖)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    have hle : ∑ k ∈ Finset.Icc 1 n, ‖((ArithmeticFunction.moebius k : ℤ) : ℂ)‖ ≤ (n : ℝ) := by
      refine le_trans (Finset.sum_le_sum fun k _ => hbdd k) ?_
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      simp
    have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, ‖((ArithmeticFunction.moebius k : ℤ) : ℂ)‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    rw [Real.rpow_one, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hnn, abs_of_nonneg (Nat.cast_nonneg n)]
    exact hle
  have hmain := LSeries_eq_mul_integral' (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
    (r := 1) zero_le_one hs hO
  rw [RHTower.LSeries_moebius_eq_inv_riemannZeta hs] at hmain
  exact hmain

end RHTower.Sieve

end
