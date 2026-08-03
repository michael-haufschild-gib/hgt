import GaloisForLFunctions.RHTower.Sieve.AmGmDirichlet

/-!
# A large-values estimate for Dirichlet polynomials

For `F(t) = ∑_{n < N} a_n n^{it}` and points `t_0 < … < t_R` in `[δ/2, T - δ/2]` with consecutive
gaps at least `δ`,

`∑_{r ≤ R} |F(t_r)|² ≤ (T + 4N(1 + log N))(δ^{-1} + 2 log N) ∑_{n < N} |a_n|²`.

Gallagher's reduction trades the discrete sum for the two integrals over `[0,T]`, the mixed one is
split with the balancing parameter `log N`, and both are then bounded by the mean value theorem.
This is the estimate a large-values or zero-density argument consumes.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **A large-values estimate for Dirichlet polynomials.** -/
theorem largeValues_dirPoly (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T) :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N)
          * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hcont1 : Continuous (fun t : ℝ => ‖dirPoly N a t‖ ^ 2) :=
    ((continuous_dirPoly N a).norm).pow 2
  have hcont2 : Continuous (fun t : ℝ =>
      2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖) :=
    (continuous_const.mul (continuous_dirPoly N a).norm).mul
      (continuous_dirPoly N (dirDerivCoeff N a)).norm
  have hA : (0 : ℝ) ≤ lam 0 - δ / 2 := by linarith
  have hmono : lam 0 ≤ lam R := by
    have h := le_of_gap hgap 0 R (Nat.zero_le R)
    simp only [Nat.cast_zero, sub_zero] at h
    have hR : (0 : ℝ) ≤ (R : ℝ) * δ := by positivity
    linarith
  have hright : (0 : ℝ) ≤ lam R + δ / 2 := by linarith
  have hbase := gallagher_dirPoly_sum N a hδ hgap hA R
  -- extend both integrals to `[0, T]`
  have hext1 : (∫ t in (0 : ℝ)..(lam R + δ / 2), ‖dirPoly N a t‖ ^ 2)
      ≤ ∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hright hhigh
      (Filter.Eventually.of_forall (fun t => sq_nonneg _)) (hcont1.intervalIntegrable _ _)
  have hext2 : (∫ t in (0 : ℝ)..(lam R + δ / 2),
        2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖)
      ≤ ∫ t in (0 : ℝ)..T, 2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖ :=
    intervalIntegral.integral_mono_interval le_rfl hright hhigh
      (Filter.Eventually.of_forall (fun t => by positivity))
      (hcont2.intervalIntegrable _ _)
  -- split the mixed term with the balancing parameter `log N`
  have hmix := integral_mixed_dirPoly_le N a (A := (0 : ℝ)) (B := T) hT hlogpos
  -- bound the two energies
  have hI1 := integral_normSq_dirPoly_le N a T
  have hI2 := integral_normSq_dirPoly_deriv_le N a hT
  set W : ℝ := T + 4 * (N : ℝ) * (1 + Real.log N) with hW
  set S : ℝ := ∑ m : Fin N, ‖a m‖ ^ 2 with hS
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have hlognn : (0 : ℝ) ≤ Real.log N := le_of_lt hlogpos
  have hlinv : (0 : ℝ) ≤ 1 / Real.log N := by positivity
  have hstep0 := mul_le_mul_of_nonneg_left hext1 hδinv
  have hstep1 := mul_le_mul_of_nonneg_left hI1 hδinv
  have hstep2 := mul_le_mul_of_nonneg_left hI1 hlognn
  have hstep3 := mul_le_mul_of_nonneg_left hI2 hlinv
  have hcollapse : (1 / Real.log N) * (W * ((Real.log N) ^ 2 * S)) = W * Real.log N * S := by
    field_simp
  rw [hcollapse] at hstep3
  have hfinal : W * (1 / δ + 2 * Real.log N) * S
      = (1 / δ) * (W * S) + (Real.log N * (W * S) + W * Real.log N * S) := by
    ring
  rw [hfinal]
  linarith [hbase, hstep0, hext2, hmix, hstep1, hstep2, hstep3]

end RHTower.Sieve
