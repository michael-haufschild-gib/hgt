import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import GaloisForLFunctions.Bottcher.ConnectedPolyClassification

open Complex Polynomial Filter Metric Topology

namespace Bottcher

/-- **Entire functions of polynomial growth are polynomials.**  If `f : ℂ → ℂ` is entire and satisfies
`‖f z‖ ≤ C · (max 1 ‖z‖)^n` for all `z`, then `f` agrees with a polynomial (of degree `≤ n`).  Proof:
by the Cauchy estimate on spheres of radius `R`, `‖f^{(k)}(0)‖ ≤ k! · C · R^{n-k} → 0` as `R → ∞` for
`k > n`, so all Taylor coefficients beyond `n` vanish; the entire function equals its (now finite)
Taylor series, i.e. a polynomial.  This is the Liouville-type growth theorem underlying the
connected-case natural-boundary argument (task02, step T02f). -/
theorem exists_polynomial_of_entire_polyGrowth {f : ℂ → ℂ} {C : ℝ} {n : ℕ}
    (hf : Differentiable ℂ f)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ n) :
    ∃ Q : ℂ[X], ∀ z, f z = Q.eval z := by
  -- high derivatives vanish
  have hvanish : ∀ k, n < k → iteratedDeriv k f 0 = 0 := by
    intro k hk
    have hbound : ∀ R : ℝ, 1 ≤ R →
        ‖iteratedDeriv k f 0‖ ≤ ((k.factorial : ℝ) * C) * (R ^ (k - n))⁻¹ := by
      intro R hR1
      have hR0 : 0 < R := by linarith
      have hdc : DiffContOnCl ℂ f (ball (0 : ℂ) R) :=
        ⟨hf.differentiableOn, hf.continuous.continuousOn⟩
      have hsphere : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C * R ^ n := by
        intro z hz
        rw [mem_sphere_iff_norm, sub_zero] at hz
        have hgz := hgrowth z
        rwa [hz, max_eq_right hR1] at hgz
      have hcauchy := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR0 hdc hsphere
      calc ‖iteratedDeriv k f 0‖ ≤ (k.factorial : ℝ) * (C * R ^ n) / R ^ k := hcauchy
        _ = ((k.factorial : ℝ) * C) * (R ^ (k - n))⁻¹ := by
            have hRk : R ^ k = R ^ n * R ^ (k - n) := by rw [← pow_add]; congr 1; omega
            have hRn0 : R ^ n ≠ 0 := (pow_pos hR0 n).ne'
            have hRkn0 : R ^ (k - n) ≠ 0 := (pow_pos hR0 (k - n)).ne'
            rw [hRk]; field_simp
    have htend : Tendsto (fun R : ℝ => ((k.factorial : ℝ) * C) * (R ^ (k - n))⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => R ^ (k - n)) atTop atTop :=
        tendsto_pow_atTop (by omega)
      simpa using h1.inv_tendsto_atTop.const_mul ((k.factorial : ℝ) * C)
    have hle : ‖iteratedDeriv k f 0‖ ≤ 0 := by
      refine ge_of_tendsto htend ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      exact hbound R hR
    exact norm_le_zero_iff.mp hle
  -- assemble the Taylor polynomial
  refine ⟨∑ k ∈ Finset.range (n + 1),
      Polynomial.C ((k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0) * X ^ k, fun z => ?_⟩
  have htaylor := taylorSeries_eq_of_entire' 0 z hf
  simp only [sub_zero] at htaylor
  rw [← htaylor,
      tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
        rw [Finset.mem_range] at hk
        rw [hvanish k (by omega), mul_zero, zero_mul]),
      Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- **Entire-level classification (task02, T02f ∘ T02g).**  If `P : ℂ → ℂ` is entire, has polynomial
growth `‖P z‖ ≤ C·(max 1 ‖z‖)^n`, satisfies the functional equation `P(s²) = P(s)² + c·s` as functions,
and `P(0) = 1`, then `c = 0` or `c = -2`.  Combines `exists_polynomial_of_entire_polyGrowth` (the entire
function is a genuine polynomial `Q`) with the polynomial classification
`c_mem_of_poly_functional_eq`.  This bridges the analytic side of the connected-case natural-boundary
argument to its proven algebraic core. -/
theorem c_mem_of_entire_functional_eq {P : ℂ → ℂ} {C : ℝ} {n : ℕ} {c : ℂ}
    (hP : Differentiable ℂ P)
    (hgrowth : ∀ z, ‖P z‖ ≤ C * (max 1 ‖z‖) ^ n)
    (hfe : ∀ s : ℂ, P (s ^ 2) = (P s) ^ 2 + c * s)
    (h0 : P 0 = 1) :
    c = 0 ∨ c = -2 := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_of_entire_polyGrowth hP hgrowth
  have hpoly : Q.comp (X ^ 2) = Q ^ 2 + Polynomial.C c * X := by
    apply Polynomial.funext
    intro s
    simp only [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, ← hQ]
    exact hfe s
  have hc0 : Q.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← hQ]; exact h0
  exact c_mem_of_poly_functional_eq hpoly hc0

end Bottcher
