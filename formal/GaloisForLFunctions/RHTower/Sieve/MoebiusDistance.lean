import GaloisForLFunctions.RHTower.Sieve.HalaszUniqueClose
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# The distance from the Möbius function to a character

Halász's dichotomy is only useful once the distance `δ` is known to be large, and for the Möbius
function that distance has an explicit trigonometric form: since `μ(p) = −1`,

`D(μ, χ_t; P)² = ∑_{p ∈ P} (1 + cos(t log p))/p`.

At `t = 0` this is `2∑_{p ∈ P} 1/p`, which Mertens' second theorem bounds below by
`2(log log z − c)`: the Möbius function is quantitatively far from the trivial character, with no
analytic input.  For `t ≠ 0` the same identity reduces the question to the size of
`∑_p cos(t log p)/p`, which is the zero-free-region input the corpus does not have.
-/

namespace RHTower.Sieve

open Finset

/-- **The distance from a function taking the value `−1` on primes.** -/
theorem mulDistSqPair_neg_one_charFn {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, f p = -1)
    (t : ℝ) :
    mulDistSqPair f (charFn t) P
      = ∑ p ∈ P, (1 + Real.cos (t * Real.log (p : ℝ))) / (p : ℝ) := by
  rw [mulDistSqPair]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hf p hp, conj_charFn]
  have hre : (Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)).re
      = Real.cos (-(t * Real.log (p : ℝ))) := Complex.exp_ofReal_mul_I_re _
  have hmul : ((-1 : ℂ) * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)).re
      = -(Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)).re := by
    simp
  rw [hmul, hre, Real.cos_neg]
  ring_nf

/-- **At the trivial character the distance is twice Mertens' sum.** -/
theorem mulDistSqPair_neg_one_zero {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, f p = -1) :
    mulDistSqPair f (charFn 0) P = 2 * ∑ p ∈ P, 1 / (p : ℝ) := by
  rw [mulDistSqPair_neg_one_charFn hf 0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [zero_mul, Real.cos_zero]
  ring

/-- **The Möbius function is far from the trivial character.**  Unconditional, from Mertens' second
theorem: the squared distance grows like `2 log log z`. -/
theorem two_mul_logLog_sub_le_mulDistSqPair {f : ℕ → ℂ} {z : ℕ} (hz : 2 ≤ z)
    (hf : ∀ p ∈ Nat.primesLE z, f p = -1) :
    2 * (logLog z - mertensSecondLowerConst)
      ≤ mulDistSqPair f (charFn 0) (Nat.primesLE z) := by
  rw [mulDistSqPair_neg_one_zero hf]
  have hm : logLog z - mertensSecondLowerConst ≤ mertensS z := le_mertensS hz
  have hval : mertensS z = ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) := rfl
  rw [hval] at hm
  linarith

/-- The Mertens three-four-one weight is a square. -/
theorem three_add_four_cos_add_cos_two (x : ℝ) :
    3 + 4 * Real.cos x + Real.cos (2 * x) = 2 * (1 + Real.cos x) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

/-- **The three-four-one inequality for the Möbius distance.**  The Möbius function cannot be close
to both `χ_t` and `χ_{2t}`: the two squared distances satisfy

`2 ∑_p 1/p ≤ 4 D(μ, χ_t)² + D(μ, χ_{2t})²`.

This is Mertens' classical device, and it is entirely elementary — no zero-free region. -/
theorem two_mul_sum_inv_le_four_mul_dist_add_dist {f : ℕ → ℂ} {P : Finset ℕ}
    (hf : ∀ p ∈ P, f p = -1) (hP : ∀ p ∈ P, 0 < p) (t : ℝ) :
    2 * ∑ p ∈ P, 1 / (p : ℝ)
      ≤ 4 * mulDistSqPair f (charFn t) P + mulDistSqPair f (charFn (2 * t)) P := by
  classical
  rw [mulDistSqPair_neg_one_charFn hf t, mulDistSqPair_neg_one_charFn hf (2 * t)]
  have hkey : ∀ p ∈ P,
      2 * (1 / (p : ℝ))
        ≤ 4 * ((1 + Real.cos (t * Real.log (p : ℝ))) / (p : ℝ))
          + (1 + Real.cos (2 * t * Real.log (p : ℝ))) / (p : ℝ) := by
    intro p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
    have hrw : 2 * t * Real.log (p : ℝ) = 2 * (t * Real.log (p : ℝ)) := by ring
    rw [hrw]
    have hsq := three_add_four_cos_add_cos_two (t * Real.log (p : ℝ))
    have hnn : 0 ≤ 2 * (1 + Real.cos (t * Real.log (p : ℝ))) ^ 2 := by positivity
    have hnum : (2 : ℝ)
        ≤ 4 * (1 + Real.cos (t * Real.log (p : ℝ)))
          + (1 + Real.cos (2 * (t * Real.log (p : ℝ)))) := by linarith
    have hcomb : 4 * ((1 + Real.cos (t * Real.log (p : ℝ))) / (p : ℝ))
        + (1 + Real.cos (2 * (t * Real.log (p : ℝ)))) / (p : ℝ)
        = (4 * (1 + Real.cos (t * Real.log (p : ℝ)))
            + (1 + Real.cos (2 * (t * Real.log (p : ℝ))))) / (p : ℝ) := by ring
    have hleft : 2 * (1 / (p : ℝ)) = 2 / (p : ℝ) := by ring
    rw [hcomb, hleft]
    exact div_le_div_of_nonneg_right hnum hppos.le
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hkey

/-- **An elementary exceptional-frequency bound.**  At one of `t`, `2t` the Möbius distance is at
least `(2/5) ∑_p 1/p`, hence of order `log log z`. -/
theorem two_mul_sum_inv_div_five_le_max {f : ℕ → ℂ} {P : Finset ℕ}
    (hf : ∀ p ∈ P, f p = -1) (hP : ∀ p ∈ P, 0 < p) (t : ℝ) :
    2 * (∑ p ∈ P, 1 / (p : ℝ)) / 5
      ≤ max (mulDistSqPair f (charFn t) P) (mulDistSqPair f (charFn (2 * t)) P) := by
  have hkey := two_mul_sum_inv_le_four_mul_dist_add_dist hf hP t
  have h1 : mulDistSqPair f (charFn t) P
      ≤ max (mulDistSqPair f (charFn t) P) (mulDistSqPair f (charFn (2 * t)) P) :=
    le_max_left _ _
  have h2 : mulDistSqPair f (charFn (2 * t)) P
      ≤ max (mulDistSqPair f (charFn t) P) (mulDistSqPair f (charFn (2 * t)) P) :=
    le_max_right _ _
  linarith

/-- **Unconditional decay of the Möbius smooth sum at the trivial frequency.**  The Euler-product
bound and the doubled distance give `exp(∑1/p² − ∑1/p)`, which tends to zero. -/
theorem norm_smoothMulSum_zero_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hneg : ∀ p ∈ P, f p = -1) :
    ‖smoothMulSum f P 0‖
      ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ) ^ 2) - ∑ p ∈ P, 1 / (p : ℝ)) := by
  rw [smoothMulSum]
  refine le_trans (norm_sum_smooth_le_exp hf hmul h1 0 hP) (Real.exp_le_exp.mpr ?_)
  have hdist : mulDistSq f 0 P = 2 * ∑ p ∈ P, 1 / (p : ℝ) := by
    rw [mulDistSq_eq_pair]
    exact mulDistSqPair_neg_one_zero hneg
  rw [hdist]
  linarith

end RHTower.Sieve
