import GaloisForLFunctions.RHTower.EstermannSmoothedSum

/-!
# Mean-zero twists annihilate the main term of the smoothed divisor sum

The smoothed twisted divisor sum `∑_N d(N) e(aN/q) e^{-Nx}` has main term
`(γ − log x − 2 log q)/(qx)`, and that main term **does not depend on the twist `a`** — this is the
content of the character-sum collapse `∑_{c mod q} expZeta(c/q, s) = q^{1−s} ζ(s)` behind
`estermann_smoothed_sum`.  Consequently any weight on the unit twists that sums to zero removes the
main term entirely, leaving only the `O(x^{-1/2})` critical-line integral:

`‖∑_{a ∈ (ZMod q)ˣ} w(a) ∑_N d(N) e(aN/q) e^{-Nx}‖ ≤ C_w · x^{-1/2}`.

For a non-principal Dirichlet character `χ` mod `q` the weight `w = χ` is mean zero on the units, so
the character-twisted smoothed divisor sum has no main term at all.  Character orthogonality turns
this into the divisor sum over an arithmetic progression.
-/

open Complex

namespace RHTower

noncomputable section

/-- The smoothed twisted divisor sum `∑_N d(N) e(aN/q) e^{-Nx}`. -/
def estermannSmoothedSum (q : ℕ) [NeZero q] (a : ZMod q) (x : ℝ) : ℂ :=
  ∑' N : ℕ, estermannCoeff q a N * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ))

/-- The twist-independent main term `(γ − log x − 2 log q)/(qx)`. -/
def estermannSmoothedMain (q : ℕ) (x : ℝ) : ℂ :=
  ((q : ℂ) * (x : ℂ))⁻¹ *
    ((Real.eulerMascheroniConstant : ℂ) - (Real.log x : ℂ) - 2 * Complex.log (q : ℂ))

theorem estermannSmoothedSum_sub_main (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {x : ℝ} (hx : 0 < x) :
    estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x
      = (1 / (2 * Real.pi) : ℝ) • ∫ v : ℝ,
          estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I) := by
  rw [estermannSmoothedSum, estermannSmoothedMain, estermann_smoothed_sum q a hx]
  ring

theorem exists_bound_norm_estermannSmoothedSum_sub_main (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x‖
        ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_norm_estermann_smoothed_error q a
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [estermannSmoothedSum_sub_main q a hx]
  exact hbound x hx

/-- **Mean-zero twists have no main term.**  Because the main term is independent of the twist, a
weight summing to zero over the units leaves only the critical-line error, of size `x^{-1/2}`. -/
theorem exists_bound_norm_estermann_meanZero (q : ℕ) [NeZero q] (w : (ZMod q)ˣ → ℂ)
    (hw : ∑ a : (ZMod q)ˣ, w a = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖∑ a : (ZMod q)ˣ, w a * estermannSmoothedSum q (a : ZMod q) x‖
        ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  classical
  choose C hC hbound using
    fun a : (ZMod q)ˣ => exists_bound_norm_estermannSmoothedSum_sub_main q a
  refine ⟨∑ a : (ZMod q)ˣ, ‖w a‖ * C a, ?_, fun x hx => ?_⟩
  · exact Finset.sum_nonneg (fun a _ => mul_nonneg (norm_nonneg _) (hC a))
  · have hsplit : (∑ a : (ZMod q)ˣ, w a * estermannSmoothedSum q (a : ZMod q) x)
        = ∑ a : (ZMod q)ˣ, w a *
            (estermannSmoothedSum q (a : ZMod q) x - estermannSmoothedMain q x) := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw, zero_mul, sub_zero]
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

/-- **Non-principal character twists have no main term.**  A non-principal Dirichlet character is
mean zero on the units, so its smoothed twisted divisor sum is `O(x^{-1/2})`. -/
theorem exists_bound_norm_estermann_character (q : ℕ) [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (hχ : ∑ a : (ZMod q)ˣ, χ ((a : ZMod q)) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖∑ a : (ZMod q)ˣ, χ ((a : ZMod q)) * estermannSmoothedSum q (a : ZMod q) x‖
        ≤ C * x ^ (-(1 / 2 : ℝ)) :=
  exists_bound_norm_estermann_meanZero q (fun a => χ ((a : ZMod q))) hχ

end

end RHTower
