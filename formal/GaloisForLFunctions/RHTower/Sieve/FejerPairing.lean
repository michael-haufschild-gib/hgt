import GaloisForLFunctions.RHTower.Sieve.FejerBounds

/-!
# Pairing a Dirichlet polynomial with the Fejér weight

`∫_0^T F(t)(1 - t/T) dt = ∑_{n < N} a_n ∫_0^T n^{it}(1 - t/T) dt`,

and each inner integral is evaluated by `FejerHalf.lean`: for `n ≥ 1` it is
`i/L_n - (e^{iTL_n} - 1)/(TL_n²)` at the frequency `L_n = log n`, and for `n = 1` — the term whose
frequency vanishes — it is `T/2`.

So the Fejér-weighted average of a Dirichlet polynomial is the coefficient sum weighted by an
explicit, nonnegative, rapidly decaying kernel.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The Fejér weight is continuous. -/
theorem continuous_fejerWeight (T : ℝ) :
    Continuous (fun t : ℝ => ((1 - t / T : ℝ) : ℂ)) := by
  fun_prop

/-- **Pairing a Dirichlet polynomial with the Fejér weight.** -/
theorem integral_fejerHalf_dirPoly (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, dirPoly N a t * ((1 - t / T : ℝ) : ℂ))
      = ∑ n : Fin N, a n
          * (∫ t in (0 : ℝ)..T,
              Complex.exp (((t * Real.log (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
                * ((1 - t / T : ℝ) : ℂ)) :=
  integral_dirPoly_mul N a (continuous_fejerWeight T) 0 T

/-- The inner integrals in the order the closed form uses. -/
theorem integral_fejer_comm (L : ℝ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
        Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * ((1 - t / T : ℝ) : ℂ))
      = ∫ t in (0 : ℝ)..T,
          ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) :=
  intervalIntegral.integral_congr (fun _ _ => mul_comm _ _)

/-- **The Fejér weight at the trivial frequency integrates to half the interval.** -/
theorem integral_fejer_zero {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ)
        * Complex.exp (((t * (0 : ℝ) : ℝ) : ℂ) * Complex.I)) = ((T / 2 : ℝ) : ℂ) := by
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hT
  have hone : ∀ t : ℝ, ((1 - t / T : ℝ) : ℂ)
      * Complex.exp (((t * (0 : ℝ) : ℝ) : ℂ) * Complex.I) = ((1 - t / T : ℝ) : ℂ) := by
    intro t
    norm_num
  rw [intervalIntegral.integral_congr (fun t _ => hone t)]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s - s ^ (2 : ℕ) / (2 * T)) (1 - t / T) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ) / (2 * T)) (2 * t / (2 * T)) t := by
      have h := (hasDerivAt_pow 2 t).div_const (2 * T)
      simpa using h
    have hd := h1.sub h2
    have hval : (1 : ℝ) - 2 * t / (2 * T) = 1 - t / T := by
      field_simp
    rw [hval] at hd
    exact hd
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((continuous_const.sub (continuous_id.div_const T)).intervalIntegrable _ _)]
  field_simp
  ring

end RHTower.Sieve
