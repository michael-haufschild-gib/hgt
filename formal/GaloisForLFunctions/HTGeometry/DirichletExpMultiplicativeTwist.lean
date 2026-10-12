import GaloisForLFunctions.HTGeometry.DirichletConvolutionExponential

/-!
# Completely multiplicative twists of a Dirichlet exponential

Let `g : ℕ →*₀ ℂ` be completely multiplicative.  Twisting by `g` is a ring homomorphism for
Dirichlet convolution, `(u ⋆ v)·g = (u·g) ⋆ (v·g)`, so it commutes with the Dirichlet exponential:

`exp⋆(ℓ·g) = (exp⋆ ℓ)·g`   (`dirichletExp_mul_twist`).

**Theorem** (`tsum_dirichletExp_twist_ne_zero`).  If `ℓ(0) = ℓ(1) = 0` and `Σ_n |ℓ(n) g(n)| < ∞`,
then `Σ_{n ≥ 1} (exp⋆ ℓ)(n) g(n) = exp(Σ_{n ≥ 1} ℓ(n) g(n))`, which is not zero.

With `g(n) = z^{Ω(n)}`-type prime twists this is the statement that the Bohr lift of
`exp(Σ ℓ(n) n^{−s})` has no zero on any polydisc where the logarithm converges absolutely.
-/

open LSeries Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Twisting by a completely multiplicative function commutes with Dirichlet convolution powers. -/
theorem dirichletConvPow_mul_twist (ℓ : ℕ → ℂ) (g : ℕ →*₀ ℂ) (k n : ℕ) :
    dirichletConvPow (fun m => ℓ m * g m) k n = dirichletConvPow ℓ k n * g n := by
  induction k generalizing n with
  | zero =>
    rw [dirichletConvPow_zero_apply, dirichletConvPow_zero_apply]
    split_ifs with h
    · rw [h, map_one, one_mul]
    · rw [zero_mul]
  | succ k ih =>
    rw [dirichletConvPow_succ, dirichletConvPow_succ, LSeries.convolution_def,
      LSeries.convolution_def]
    simp only
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpn : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
    rw [ih, ← hpn, map_mul]
    ring

/-- **Twisting commutes with the Dirichlet exponential.** -/
theorem dirichletExp_mul_twist (ℓ : ℕ → ℂ) (g : ℕ →*₀ ℂ) (n : ℕ) :
    dirichletExp (fun m => ℓ m * g m) n = dirichletExp ℓ n * g n := by
  unfold dirichletExp
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dirichletConvPow_mul_twist]
  ring

/-- **The twisted sum of a Dirichlet exponential.**  `Σ_{n≥1} (exp⋆ ℓ)(n) g(n)` is the exponential
of `Σ_{n≥1} ℓ(n) g(n)`, so it does not vanish. -/
theorem LSeries_dirichletExp_twist {ℓ : ℕ → ℂ} (h0 : ℓ 0 = 0) (h1 : ℓ 1 = 0) (g : ℕ →*₀ ℂ)
    (hs : LSeriesSummable (fun n => ℓ n * g n) 0) :
    LSeriesSummable (fun n => dirichletExp ℓ n * g n) 0 ∧
      LSeries (fun n => dirichletExp ℓ n * g n) 0 = Complex.exp (LSeries (fun n => ℓ n * g n) 0) := by
  have h0' : (fun n => ℓ n * g n) 0 = 0 := by simp [h0]
  have h1' : (fun n => ℓ n * g n) 1 = 0 := by simp [h1]
  have h := LSeries_dirichletExp h0' h1' hs
  have he : dirichletExp (fun n => ℓ n * g n) = fun n => dirichletExp ℓ n * g n :=
    funext (dirichletExp_mul_twist ℓ g)
  rwa [he] at h

theorem tsum_dirichletExp_twist_ne_zero {ℓ : ℕ → ℂ} (h0 : ℓ 0 = 0) (h1 : ℓ 1 = 0) (g : ℕ →*₀ ℂ)
    (hs : LSeriesSummable (fun n => ℓ n * g n) 0) :
    LSeries (fun n => dirichletExp ℓ n * g n) 0 ≠ 0 := by
  rw [(LSeries_dirichletExp_twist h0 h1 g hs).2]
  exact Complex.exp_ne_zero _

end

end GaloisForLFunctions.HTGeometry
