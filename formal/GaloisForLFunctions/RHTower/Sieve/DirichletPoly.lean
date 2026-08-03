import GaloisForLFunctions.RHTower.Sieve.SieveBoundSharp

/-!
# Dirichlet polynomials and their derivatives

The Dirichlet polynomial `F(t) = ∑_{n < N} a_n n^{it}`, written with the phase form `n^{it} =
exp(it log n)` used throughout this folder.  Differentiating term by term multiplies each coefficient
by `i log n`, so the derivative is again a Dirichlet polynomial and the squared modulus differentiates
through the real inner product exactly as in `TrigNormSqDeriv.lean`.

These are the inputs Gallagher's Sobolev bound needs in order to control `F` at separated points by
integrals over an interval — the first step of every large-values argument for Dirichlet polynomials.
Unlike the trigonometric case there is no Parseval available on a finite interval, so the integrals
are not evaluated here; the reduction to them is what this layer supplies.
-/

namespace RHTower.Sieve

open Finset

/-- The Dirichlet polynomial with coefficients `a`. -/
noncomputable def dirPoly (N : ℕ) (a : Fin N → ℂ) (t : ℝ) : ℂ :=
  ∑ n : Fin N, a n * Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)

/-- The coefficients of the derivative. -/
noncomputable def dirDerivCoeff (N : ℕ) (a : Fin N → ℂ) : Fin N → ℂ :=
  fun n => ((Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I * a n

/-- The derivative of a single phase. -/
theorem hasDerivAt_exp_phase (L t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (((s * L : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * ((L : ℂ) * Complex.I)) t := by
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) ((1 : ℝ) : ℂ) t := (hasDerivAt_id t).ofReal_comp
  have hg := (hid.const_mul ((L : ℂ) * Complex.I)).cexp
  have hfun : ∀ s : ℝ, Complex.exp (((L : ℂ) * Complex.I) * (s : ℂ))
      = Complex.exp (((s * L : ℝ) : ℂ) * Complex.I) := by
    intro s
    congr 1
    push_cast
    ring
  simp only [hfun] at hg
  have hval : Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * (((L : ℂ) * Complex.I) * ((1 : ℝ) : ℂ))
      = Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * ((L : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hval] at hg
  exact hg

/-- A Dirichlet polynomial is continuous. -/
theorem continuous_dirPoly (N : ℕ) (a : Fin N → ℂ) : Continuous (dirPoly N a) := by
  have hfun : dirPoly N a = fun t : ℝ => ∑ n : Fin N,
      a n * Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := rfl
  rw [hfun]
  refine continuous_finsetSum _ fun n _ => ?_
  fun_prop

/-- **The derivative of a Dirichlet polynomial is a Dirichlet polynomial.** -/
theorem hasDerivAt_dirPoly (N : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    HasDerivAt (dirPoly N a) (dirPoly N (dirDerivCoeff N a) t) t := by
  have hd : HasDerivAt (fun s : ℝ => ∑ n : Fin N,
        a n * Complex.exp (((s * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
      (∑ n : Fin N, a n * (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
        * (((Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I))) t := by
    have hsum := HasDerivAt.sum
      (fun (n : Fin N) (_ : n ∈ (Finset.univ : Finset (Fin N))) =>
        (hasDerivAt_exp_phase (Real.log ((n : ℕ) + 1)) t).const_mul (a n))
    have heq : (∑ n ∈ (Finset.univ : Finset (Fin N)),
        fun s : ℝ => a n * Complex.exp (((s * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
        = fun s : ℝ => ∑ n : Fin N,
          a n * Complex.exp (((s * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
      funext s
      simp [Finset.sum_apply]
    rw [heq] at hsum
    exact hsum
  have hval : (∑ n : Fin N, a n * (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
      * (((Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)))
      = dirPoly N (dirDerivCoeff N a) t := by
    rw [dirPoly]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [dirDerivCoeff]
    ring
  rw [← hval]
  exact hd

/-- **The derivative of the squared modulus.** -/
theorem hasDerivAt_normSq_dirPoly (N : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖dirPoly N a s‖ ^ 2)
      ((inner ℝ (dirPoly N a t) (dirPoly N (dirDerivCoeff N a) t) : ℝ)
        + (inner ℝ (dirPoly N (dirDerivCoeff N a) t) (dirPoly N a t) : ℝ)) t := by
  have hd := hasDerivAt_dirPoly N a t
  have h := HasDerivAt.inner ℝ hd hd
  have hfun : (fun s : ℝ => (inner ℝ (dirPoly N a s) (dirPoly N a s) : ℝ))
      = fun s : ℝ => ‖dirPoly N a s‖ ^ 2 := by
    funext s
    exact real_inner_self_eq_norm_sq _
  rw [hfun] at h
  exact h

/-- **Cauchy–Schwarz for the derivative of the squared modulus.** -/
theorem abs_deriv_normSq_dirPoly_le (N : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    |(inner ℝ (dirPoly N a t) (dirPoly N (dirDerivCoeff N a) t) : ℝ)
      + (inner ℝ (dirPoly N (dirDerivCoeff N a) t) (dirPoly N a t) : ℝ)|
      ≤ 2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖ := by
  refine le_trans (abs_add_le _ _) ?_
  have h1 := abs_real_inner_le_norm (dirPoly N a t) (dirPoly N (dirDerivCoeff N a) t)
  have h2 := abs_real_inner_le_norm (dirPoly N (dirDerivCoeff N a) t) (dirPoly N a t)
  have hc : ‖dirPoly N (dirDerivCoeff N a) t‖ * ‖dirPoly N a t‖
      = ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖ := mul_comm _ _
  linarith

end RHTower.Sieve
