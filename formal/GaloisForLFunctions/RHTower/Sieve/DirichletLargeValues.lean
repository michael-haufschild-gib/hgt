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

/-- **The large-values estimate with the two energies as parameters.**  Gallagher's reduction and the
AM–GM split use nothing about the energies beyond their values, so any mean-square bound feeds the
estimate. -/
theorem largeValues_dirPoly_of_energy (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {lam : ℕ → ℝ}
    {δ T E E' : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T)
    (hI1 : (∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2) ≤ E)
    (hI2 : (∫ t in (0 : ℝ)..T, ‖dirPoly N (dirDerivCoeff N a) t‖ ^ 2) ≤ E') :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2
      ≤ (1 / δ) * E + Real.log N * E + (1 / Real.log N) * E' := by
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
  have hmix := integral_mixed_dirPoly_le N a (A := (0 : ℝ)) (B := T) hT hlogpos
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have hlognn : (0 : ℝ) ≤ Real.log N := le_of_lt hlogpos
  have hlinv : (0 : ℝ) ≤ 1 / Real.log N := by positivity
  have hstep0 := mul_le_mul_of_nonneg_left hext1 hδinv
  have hstep1 := mul_le_mul_of_nonneg_left hI1 hδinv
  have hstep2 := mul_le_mul_of_nonneg_left hI1 hlognn
  have hstep3 := mul_le_mul_of_nonneg_left hI2 hlinv
  linarith [hbase, hstep0, hext2, hmix, hstep1, hstep2, hstep3]

/-- **A large-values estimate for Dirichlet polynomials.**  The instance at the mean value theorem's
energies. -/
theorem largeValues_dirPoly (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T) :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N)
          * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hbase := largeValues_dirPoly_of_energy N hN a hδ hT hgap hlow R hhigh
    (integral_normSq_dirPoly_le N a T) (integral_normSq_dirPoly_deriv_le N a hT)
  refine le_trans hbase (le_of_eq ?_)
  field_simp
  ring

end RHTower.Sieve
