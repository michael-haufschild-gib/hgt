import GaloisForLFunctions.RHTower.EstermannProgressionOrthogonality

/-!
# The smoothed divisor sum in a progression to a prime modulus

Additive orthogonality writes `q · ∑_{N ≡ b (q)} d(N) e^{-Nx}` as a character average of the
smoothed twisted divisor sums.  For a prime modulus every nonzero twist is a unit, so the average
splits into the untwisted term `a = 0` and a weighted sum over the units.  Since the main term of
the twisted sum does not depend on the twist, the unit part contributes
`(∑_a w(a)) · (γ − log x − 2 log q)/(qx)` up to `O(x^{-1/2})`, and for a nonzero residue `b` the
weight sum is the Ramanujan sum `c_q(b) = −1`.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Weighted twist expansion, main term retained.**  Because the main term is independent of the
twist, an arbitrary weight on the units reproduces it with the factor `∑_a w(a)`. -/
theorem exists_bound_norm_estermann_weighted (q : ℕ) [NeZero q] (w : (ZMod q)ˣ → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(∑ a : (ZMod q)ˣ, w a * estermannSmoothedSum q (a : ZMod q) x)
          - (∑ a : (ZMod q)ˣ, w a) * estermannSmoothedMain q x‖
        ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  classical
  choose C hC hbound using
    fun a : (ZMod q)ˣ => exists_bound_norm_estermannSmoothedSum_sub_main q a
  refine ⟨∑ a : (ZMod q)ˣ, ‖w a‖ * C a, ?_, fun x hx => ?_⟩
  · exact Finset.sum_nonneg (fun a _ => mul_nonneg (norm_nonneg _) (hC a))
  · have hsplit : (∑ a : (ZMod q)ˣ, w a * estermannSmoothedSum q (a : ZMod q) x)
        - (∑ a : (ZMod q)ˣ, w a) * estermannSmoothedMain q x
        = ∑ a : (ZMod q)ˣ, w a *
            (estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x) := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hsplit]
    have hterm : ∀ a : (ZMod q)ˣ,
        ‖w a * (estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x)‖
          ≤ (‖w a‖ * C a) * x ^ (-(1 / 2 : ℝ)) := by
      intro a
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hbound a x hx) (norm_nonneg _)
    calc ‖∑ a : (ZMod q)ˣ, w a *
            (estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x)‖
        ≤ ∑ a : (ZMod q)ˣ, ‖w a *
            (estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ a : (ZMod q)ˣ, (‖w a‖ * C a) * x ^ (-(1 / 2 : ℝ)) :=
          Finset.sum_le_sum (fun a _ => hterm a)
      _ = (∑ a : (ZMod q)ˣ, ‖w a‖ * C a) * x ^ (-(1 / 2 : ℝ)) := by
          rw [← Finset.sum_mul]

/-- The untwisted smoothed divisor sum is the zero twist. -/
theorem estermannSmoothedSum_zero (q : ℕ) [NeZero q] (x : ℝ) :
    estermannSmoothedSum q (0 : ZMod q) x
      = ∑' N : ℕ, ((N.divisors.card : ℂ)) * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)) := by
  rw [estermannSmoothedSum]
  refine tsum_congr (fun N => ?_)
  have h0 : ((ZMod.stdAddChar (0 : ZMod q)) : ℂ) = 1 := by simp
  rw [estermannCoeff, zero_mul, h0, mul_one]

end

end RHTower
