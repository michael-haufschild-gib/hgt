import GaloisForLFunctions.RHTower.Sieve.SymmetricPhaseIntegral

/-!
# The Dirichlet kernel against a Dirichlet polynomial

Pairing with the constant kernel over a symmetric interval,

`∫_{-T}^{T} F(t) dt = ∑_{n < N} a_n ∫_{-T}^{T} n^{it} dt`,

and each inner integral is the Dirichlet kernel `2 sin(T log n)/log n`, of modulus at most
`min(2T, 2/|log n|)`.

The two bounds are what make the pairing selective: near the trivial frequency the kernel is of size
`2T`, and it decays like the reciprocal of the frequency elsewhere.  After a twist by `x^{-it}` the
frequencies become `log(n/x)`, so the pairing localises the coefficient sum to `n ≈ x`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The Dirichlet kernel decays in the frequency. -/
theorem norm_integral_exp_phase_symm_le_inv (L : ℝ) (hL : L ≠ 0) (T : ℝ) :
    ‖∫ t in (-T)..T, Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / |L| := by
  rw [integral_exp_phase_symm L hL T, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hnum : ‖2 * ((Real.sin (T * L) : ℝ) : ℂ)‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs : |Real.sin (T * L)| ≤ 1 := Real.abs_sin_le_one _
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    linarith
  have hpos : (0 : ℝ) < |L| := abs_pos.mpr hL
  gcongr

/-- The Dirichlet kernel is bounded by the length of the interval. -/
theorem norm_integral_exp_phase_symm_le_len (L : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * T := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
    (a := -T) (b := T) (C := 1)
    (fun x _ => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  have hlen : |T - -T| = 2 * T := by
    rw [show T - -T = 2 * T by ring, abs_of_nonneg (by linarith)]
  rw [hlen, one_mul] at hbound
  exact hbound

/-- **Pairing a Dirichlet polynomial with the Dirichlet kernel.** -/
theorem integral_dirPoly_symm (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, dirPoly N a t)
      = ∑ n : Fin N, a n
          * (∫ t in (-T)..T,
              Complex.exp (((t * Real.log (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) := by
  have h := integral_dirPoly_mul N a (K := fun _ : ℝ => (1 : ℂ)) continuous_const (-T) T
  simpa using h

end RHTower.Sieve
