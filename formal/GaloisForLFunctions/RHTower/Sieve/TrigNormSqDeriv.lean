import GaloisForLFunctions.RHTower.Sieve.TrigDerivative

/-!
# The derivative of the squared modulus

Gallagher's bound is applied to `f(t) = |S(t)|²`, so it needs that function's derivative.  Writing
the squared modulus as the real inner product `⟪S, S⟫` makes the derivative immediate,

`(|S|²)' = ⟪S, S'⟫ + ⟪S', S⟫`,

and Cauchy–Schwarz bounds it by `2‖S‖‖S'‖`.  Both integrals of the Sobolev bound are then in terms
of `|S|` and `|S'|`, which `TrigParseval.lean` and `TrigDerivative.lean` evaluate.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- A trigonometric polynomial is continuous. -/
theorem continuous_expSum (N : ℕ) (c : Fin N → ℂ) : Continuous (expSum N c) := by
  have hfun : expSum N c = fun s : ℝ => ∑ n : Fin N, c n * circleFreq (((n : ℕ) : ℝ) * s) := by
    funext s
    exact expSum_eq_sum N c s
  rw [hfun]
  refine continuous_finsetSum _ fun n _ => ?_
  unfold circleFreq
  fun_prop

/-- **The derivative of the squared modulus.** -/
theorem hasDerivAt_normSq_expSum (N : ℕ) (c : Fin N → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖expSum N c s‖ ^ (2 : ℕ))
      ((inner ℝ (expSum N c t) (expSum N (derivCoeff N c) t) : ℝ)
        + (inner ℝ (expSum N (derivCoeff N c) t) (expSum N c t) : ℝ)) t := by
  have hd := hasDerivAt_expSum N c t
  have h := HasDerivAt.inner ℝ hd hd
  have hfun : (fun s : ℝ => (inner ℝ (expSum N c s) (expSum N c s) : ℝ))
      = fun s : ℝ => ‖expSum N c s‖ ^ (2 : ℕ) := by
    funext s
    exact real_inner_self_eq_norm_sq _
  rw [hfun] at h
  exact h

/-- **Cauchy–Schwarz for the derivative of the squared modulus.** -/
theorem abs_deriv_normSq_le (N : ℕ) (c : Fin N → ℂ) (t : ℝ) :
    |(inner ℝ (expSum N c t) (expSum N (derivCoeff N c) t) : ℝ)
      + (inner ℝ (expSum N (derivCoeff N c) t) (expSum N c t) : ℝ)|
      ≤ 2 * ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖ := by
  refine le_trans (abs_add_le _ _) ?_
  have h1 := abs_real_inner_le_norm (expSum N c t) (expSum N (derivCoeff N c) t)
  have h2 := abs_real_inner_le_norm (expSum N (derivCoeff N c) t) (expSum N c t)
  have hc : ‖expSum N (derivCoeff N c) t‖ * ‖expSum N c t‖
      = ‖expSum N c t‖ * ‖expSum N (derivCoeff N c) t‖ := mul_comm _ _
  linarith

end RHTower.Sieve
