import GaloisForLFunctions.RHTower.PoleMinusPrimeMainIsLaplace
import GaloisForLFunctions.RHTower.ArchimedeanSingleIntegral

/-!
# Finite-interval Laplace substitution and scalar cancellation

Substituting `t = 2u` rewrites the displayed finite-interval archimedean mode
as twice a Laplace integral. The scalar identity
`2 * Lhalf + (A0 - 2 * Lhalf) = A0` then removes a shared term from any
decomposition supplied as a hypothesis. The constant Laplace integral and
monotonicity of the mode denominators are also proved.

This module supplies no source-level identification of the full Weil form,
no bound on the prime-counting error, and no summability theorem for the
archimedean tail. The individual reciprocal mode bounds alone are not
summable. Applying the scalar cancellation to arithmetic sources requires
separate identifications and estimates. Actual pole-source leading
cancellation is established in `CCMPoleLeadingCancellation`.
-/

open Real intervalIntegral

noncomputable section

namespace RHTower

/-- **The substitution.**  The archimedean integrand at mode `n`, rewritten by `t = 2u`, is the
Laplace transform of `A` at `2n + 1/2`, doubled. -/
theorem arch_mode_is_laplace (A : ℝ → ℝ) (n X : ℝ) :
    ∫ t in (0:ℝ)..(2 * X), Real.exp (-(n + 3 / 4) * t) * A (t / 2) * Real.exp (t / 2)
      = 2 * ∫ u in (0:ℝ)..X, A u * Real.exp (-(2 * n + 1 / 2) * u) := by
  have h := smul_integral_comp_mul_left (a := (0:ℝ)) (b := X)
    (fun t : ℝ => Real.exp (-(n + 3 / 4) * t) * A (t / 2) * Real.exp (t / 2)) 2
  simp only [smul_eq_mul, mul_zero] at h
  rw [← h]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  simp only []
  rw [show (2:ℝ) * u / 2 = u by ring,
    mul_comm (Real.exp (-(n + 3 / 4) * (2 * u))) (A u), mul_assoc, ← Real.exp_add,
    show -(n + 3 / 4) * (2 * u) + u = -(2 * n + 1 / 2) * u by ring]

/-- **The three-way cancellation.**  The pole-minus-prime-main residue `2·𝓛A(1/2)` plus the first
archimedean mode `A(0) - 2·𝓛A(1/2)` is `A(0)`: the Laplace transforms at `1/2` cancel exactly. -/
theorem three_way_cancellation (A0 Lhalf : ℝ) :
    2 * Lhalf + (A0 - 2 * Lhalf) = A0 := by ring

/-- The cancellation is width-independent: it holds for every value of the residue, so widening the
window changes nothing in the combined term. -/
theorem cancellation_width_independent (A0 L₁ L₂ : ℝ) :
    (2 * L₁ + (A0 - 2 * L₁)) = (2 * L₂ + (A0 - 2 * L₂)) := by ring

/-- Rewrite a supplied scalar upper bound in division notation. No integral estimate is
established by this lemma. -/
theorem laplace_mode_bound {A0 s I : ℝ} (_hs : 0 < s) (hI : I ≤ A0 * (1 / s)) :
    I ≤ A0 / s := by
  rwa [mul_one_div] at hI

/-- The exact Laplace transform of a constant on `[0, X]`, the extremal case of the bound. -/
theorem laplace_const {s X : ℝ} (hs : s ≠ 0) :
    ∫ u in (0:ℝ)..X, Real.exp (-s * u) = (1 - Real.exp (-s * X)) / s := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) X,
      HasDerivAt (fun u : ℝ => -(Real.exp (-s * u)) / s) (Real.exp (-s * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => -s * u) (-s) x := by
      simpa using (hasDerivAt_id x).const_mul (-s)
    have h2 := h1.exp
    have h3 := (h2.neg).div_const s
    simpa [hs] using h3
  have hint : IntervalIntegrable (fun u : ℝ => Real.exp (-s * u))
      MeasureTheory.volume 0 X :=
    (Real.continuous_exp.comp (continuous_id.const_mul (-s))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  rw [show -s * (0:ℝ) = 0 by ring, Real.exp_zero]
  ring

/-- **The modes decay.**  `2n + 1/2` increases without bound, so the bound `A(0)/(2n+1/2)` on the
`n`-th surviving mode tends to zero: no single mode carries exponential weight. -/
theorem mode_denominators_increase {m n : ℕ} (h : m ≤ n) :
    2 * (m : ℝ) + 1 / 2 ≤ 2 * (n : ℝ) + 1 / 2 := by
  have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h
  linarith

/-- Cancel the shared scalar term in a supplied decomposition. The dependence of `Tail` and
`Err` on a source or width remains unrestricted. -/
theorem no_exponential_content {A0 Lhalf Tail Err W : ℝ}
    (hW : W = 2 * Lhalf + (A0 - 2 * Lhalf) - Tail - Err) :
    W = A0 - Tail - Err := by rw [hW]; ring

end RHTower
