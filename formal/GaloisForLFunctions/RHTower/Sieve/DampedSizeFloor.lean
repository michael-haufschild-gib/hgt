import GaloisForLFunctions.RHTower.Sieve.GhsPerronDamped
import GaloisForLFunctions.RHTower.Sieve.MoebiusDistance

/-!
# The damping factor cannot exceed the prime mass

The damped Cesàro and Halász chains escape the coefficient-free cap of `CoefficientFreeCap.lean`: their
right-hand side is parametrised by a distance level `δ`, and the admissible `δ` depends on the sequence,
so instantiating at the constant sequence forces `δ = 0` and yields nothing.  What stops them instead is
quantitative, and it is available unconditionally.

The distance to a character is at most twice the prime mass — `1 − Re(f(p)·conj(g(p))) ≤ 2` for bounded
`f`, `g` — so any `δ` legitimately used satisfies `δ² ≤ 2∑_{p ∈ P}1/p`, and

`dampedSize σ δ z L ≥ (1 + 1/(σ−1))·exp(7/2 + 2(σ−1)(log z + log 4) − 2∑_{p ≤ z}1/p)`.

With `∑_{p ≤ z}1/p = logLog z + O(1)` the exponential is `≍ (log z)^{-2}`, so writing
`A = (σ−1)log L` and `z = L` the two parts of `dampedSize` are `≳ (e^{2A}/A)(log L)^{-1}` and
`(log L/A)e^{-A}`; their sum is minimised at `A ≍ (2/3)logLog L`, where both are `≍ (log L)^{1/3}/A`.
So `dampedSize ≳ (log L)^{1/3}/logLog L` for every admissible `σ` and `δ`: the damped analytic term is
never `o(1)`, whatever zero-free region supplies the distance.  The chain therefore cannot reach `o(N)`
either — not because it is blind to the coefficients, but because the damping it can buy is bounded by
the total prime mass while the truncation tail charges the abscissa back.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- **The distance to a character is at most twice the prime mass.** -/
theorem mulDistSqPair_le_two_mul_sum_inv {f g : ℕ → ℂ} {P : Finset ℕ}
    (hf : ∀ p ∈ P, ‖f p‖ ≤ 1) (hg : ∀ p ∈ P, ‖g p‖ ≤ 1) (hP : ∀ p ∈ P, 0 < p) :
    mulDistSqPair f g P ≤ 2 * ∑ p ∈ P, 1 / (p : ℝ) := by
  rw [mulDistSqPair, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
  have hnorm : ‖f p * (starRingEnd ℂ) (g p)‖ ≤ 1 := by
    rw [norm_mul, RCLike.norm_conj]
    calc ‖f p‖ * ‖g p‖ ≤ 1 * 1 :=
          mul_le_mul (hf p hp) (hg p hp) (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hre : -(1 : ℝ) ≤ (f p * (starRingEnd ℂ) (g p)).re := by
    have h := Complex.abs_re_le_norm (f p * (starRingEnd ℂ) (g p))
    have h2 := abs_le.1 h
    linarith [h2.1, hnorm]
  have hnum : 1 - (f p * (starRingEnd ℂ) (g p)).re ≤ 2 := by linarith
  calc (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ) ≤ 2 / (p : ℝ) :=
        div_le_div_of_nonneg_right hnum hp0.le
    _ = 2 * (1 / (p : ℝ)) := by rw [mul_one_div]

/-- **The damped size, floored by the distance bound.**  Substituting an upper bound for `δ²`. -/
theorem dampedSize_ge_of_sq_le {σ δ D : ℝ} (hσ : 1 < σ) (z L : ℕ) (hδ : δ ^ (2 : ℕ) ≤ D) :
    (1 + 1 / (σ - 1)) * Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - D)
      ≤ dampedSize σ δ z L := by
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  have hcoef : (0 : ℝ) ≤ 1 + 1 / (σ - 1) := by positivity
  have htail : (0 : ℝ) ≤ ((L : ℝ)) ^ (1 - σ) / (σ - 1) := by
    have hL0 : (0 : ℝ) ≤ ((L : ℕ) : ℝ) := Nat.cast_nonneg L
    positivity
  have hexp : Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - D)
      ≤ Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ (2 : ℕ)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [dampedSize]
  have hmul := mul_le_mul_of_nonneg_left hexp hcoef
  linarith

/-- **The damping is bounded by the prime mass.**  Any distance level legitimately available at a
bounded multiplicative `f` obeys `δ² ≤ 2∑_{p ∈ P}1/p`, so the damped size has the stated floor. -/
theorem dampedSize_ge_of_dist {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hP : ∀ p ∈ P, 0 < p) {σ δ t : ℝ} (hσ : 1 < σ) (hδ : 0 ≤ δ) (z L : ℕ)
    (hdist : δ ≤ Real.sqrt (mulDistSqPair f (charFn t) P)) :
    (1 + 1 / (σ - 1))
        * Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4)
            - 2 * ∑ p ∈ P, 1 / (p : ℝ))
      ≤ dampedSize σ δ z L := by
  refine dampedSize_ge_of_sq_le hσ z L ?_
  have hnn : 0 ≤ mulDistSqPair f (charFn t) P :=
    mulDistSqPair_nonneg_disc hf (fun p _ => (norm_charFn t p).le) hP
  have hsq : δ ^ (2 : ℕ) ≤ mulDistSqPair f (charFn t) P := by
    have h := pow_le_pow_left₀ hδ hdist 2
    rwa [Real.sq_sqrt hnn] at h
  exact le_trans hsq
    (mulDistSqPair_le_two_mul_sum_inv hf (fun p _ => (norm_charFn t p).le) hP)

end RHTower.Sieve
end
