import GaloisForLFunctions.RHTower.DirichletLMixedAdditiveEvenIndexLaw

/-!
# Radial upper bound from the even-index Hermitian Abel series

The order-two parity projection writes the sum of the Hermitian radial squares at `r` and `-r` as
twice the even-index Abel series.  Discarding the nonnegative `-r` square yields a one-sided radial
upper bound: the squared Hermitian modulus at `r` is dominated by twice the even-index Abel series of
the real parts of the mixed additive convolution powers
(`norm_pow_sq_le_two_mul_tsum_evenIndex_re`).  Since each real part is at most its positive part, this
strengthens the paper's inequality `(5)` (which uses positive parts).  It is the coefficient-side
input for the pole-frontier recurrence: a radially unbounded left-hand side forces the even-index real
parts to be positive at cofinally many indices.
-/

open Complex Filter
open scoped BigOperators Topology

namespace RHTower

/-- The even-index subseries of an absolutely convergent mixed additive Cauchy power is summable. -/
theorem summable_evenIndex_mixedAdditive (a : ℕ → ℂ) {r : ℝ}
    (ha : Summable (fun N : ℕ => ‖a N * (r : ℂ) ^ N‖)) (k : ℕ) :
    Summable (fun q : ℕ => mixedAdditiveConvolutionPower a k (2 * q) * (r : ℂ) ^ (2 * q)) := by
  have hc : Summable (fun N : ℕ => mixedAdditiveConvolutionPower a k N * (r : ℂ) ^ N) :=
    (summable_norm_mixedAdditiveConvolutionPower_mul_pow a (r : ℂ) ha k).of_norm
  exact hc.comp_injective (i := fun x : ℕ => 2 * x)
    (fun x y h => Nat.mul_left_cancel (by norm_num) h)

/-- **Radial Hermitian upper bound.**  The squared Hermitian modulus of the `k`-th Cauchy power at
radius `r` is at most twice the even-index Abel series of the real parts of the mixed additive
convolution powers.  This is sharper than the positive-part inequality `(5)` of the parity law. -/
theorem norm_pow_sq_le_two_mul_tsum_evenIndex_re (a : ℕ → ℂ) {r : ℝ}
    (ha : Summable (fun N : ℕ => ‖a N * (r : ℂ) ^ N‖)) (k : ℕ) :
    ‖(∑' N : ℕ, a N * (r : ℂ) ^ N) ^ k‖ ^ 2 ≤
      2 * ∑' q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q)).re * r ^ (2 * q) := by
  have hsum := summable_evenIndex_mixedAdditive a ha k
  have hterm : ∀ q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q) * (r : ℂ) ^ (2 * q)).re
      = (mixedAdditiveConvolutionPower a k (2 * q)).re * r ^ (2 * q) := by
    intro q
    rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hTre : (∑' q : ℕ, mixedAdditiveConvolutionPower a k (2 * q) * (r : ℂ) ^ (2 * q)).re
      = ∑' q : ℕ, (mixedAdditiveConvolutionPower a k (2 * q)).re * r ^ (2 * q) := by
    rw [re_tsum hsum]; exact tsum_congr hterm
  have hofRealSq : ∀ b : ℝ, ((b : ℂ) ^ 2).re = b ^ 2 := by
    intro b; rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
  have hpar := add_pos_neg_hermitianAbel_eq_two_mul_tsum_evenIndex a r ha k
  rw [Complex.mul_conj', Complex.mul_conj'] at hpar
  have hre := congrArg Complex.re hpar
  rw [Complex.add_re, hofRealSq, hofRealSq,
    show ((2 : ℂ) * ∑' q : ℕ, mixedAdditiveConvolutionPower a k (2 * q) * (r : ℂ) ^ (2 * q)).re
      = 2 * (∑' q : ℕ, mixedAdditiveConvolutionPower a k (2 * q) * (r : ℂ) ^ (2 * q)).re from by
      simp [Complex.mul_re], hTre] at hre
  have hneg : (0 : ℝ) ≤ ‖(∑' N : ℕ, a N * (-(r : ℂ)) ^ N) ^ k‖ ^ 2 := sq_nonneg _
  linarith [hre]

end RHTower
