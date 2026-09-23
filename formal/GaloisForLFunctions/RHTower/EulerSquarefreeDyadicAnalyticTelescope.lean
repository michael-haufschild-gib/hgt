import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization

/-!
# The scalar analytic shadow of the dyadic squarefree channel

`dyadic-squarefree-euler-fock-source-factorization`, §6, equations `(27)`–`(29)`.

With `Z_sq(s) = ζ(s)/ζ(2s)` (the Dirichlet series of the squarefree indicator, by
`LSeries_squarefree_eq_riemannZeta_div`), `A(s) = -ζ'(s)/ζ(s)` and `J_sq(s) = -Z_sq'(s)/Z_sq(s)`:

```text
ζ(s) = ∏_{r<R} Z_sq(2^r s) · ζ(2^R s),                 (27)
A(s) = ∑_{r<R} 2^r J_sq(2^r s) + 2^R A(2^R s).         (29)
```

Both hold for every `R` on the absolutely convergent half plane `Re s > 1`.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- `Z_sq(s) = ζ(s)/ζ(2s)`, the squarefree Dirichlet series on `Re s > 1`. -/
def squarefreeZeta (s : ℂ) : ℂ := riemannZeta s / riemannZeta (2 * s)

/-- The Euler logarithmic morphism `A(s) = -ζ'(s)/ζ(s)`. -/
def eulerLogMorphism (s : ℂ) : ℂ := -logDeriv riemannZeta s

/-- The squarefree logarithmic morphism `J_sq(s) = -Z_sq'(s)/Z_sq(s)`. -/
def squarefreeLogMorphism (s : ℂ) : ℂ := -logDeriv squarefreeZeta s

theorem two_mul_re_lt {s : ℂ} (hs : 1 < s.re) : 1 < (2 * s).re := by
  have : (2 * s).re = 2 * s.re := by simp
  rw [this]; linarith

theorem riemannZeta_ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro h
  rw [h] at hs
  simp at hs

/-- `Z_sq` is the Dirichlet series of the squarefree indicator. -/
theorem squarefreeZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    squarefreeZeta s
      = LSeries (fun n => ((ArithmeticFunction.pmul (ArithmeticFunction.moebius)
          (ArithmeticFunction.moebius) n : ℤ) : ℂ)) s := by
  rw [squarefreeZeta]
  exact (LSeries_squarefree_eq_riemannZeta_div hs).symm

theorem squarefreeZeta_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    squarefreeZeta s * riemannZeta (2 * s) = riemannZeta s := by
  rw [squarefreeZeta, div_mul_cancel₀ _ (riemannZeta_ne_zero_of_one_lt_re (two_mul_re_lt hs))]

theorem squarefreeZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : squarefreeZeta s ≠ 0 := by
  intro h
  have := squarefreeZeta_mul_riemannZeta hs
  rw [h, zero_mul] at this
  exact riemannZeta_ne_zero_of_one_lt_re hs this.symm

/-! ## The analytic telescope `(27)` -/

/-- **Equation (27).**  The exact finite dyadic telescope of the Euler product. -/
theorem riemannZeta_dyadic_telescope : ∀ (R : ℕ) {s : ℂ}, 1 < s.re →
    riemannZeta s
      = (∏ r ∈ Finset.range R, squarefreeZeta (2 ^ r * s)) * riemannZeta (2 ^ R * s)
  | 0, s, _ => by simp
  | (R + 1), s, hs => by
      have hs2 := two_mul_re_lt hs
      have hIH := riemannZeta_dyadic_telescope R hs2
      have hbase := squarefreeZeta_mul_riemannZeta hs
      rw [← hbase, hIH, Finset.prod_range_succ']
      have hrw : ∀ r : ℕ, (2 : ℂ) ^ r * (2 * s) = 2 ^ (r + 1) * s := by
        intro r; rw [pow_succ]; ring
      have hpow : (2 : ℂ) ^ R * (2 * s) = 2 ^ (R + 1) * s := by rw [pow_succ]; ring
      rw [Finset.prod_congr rfl (fun r _ => by rw [hrw r]), hpow, pow_zero, one_mul]
      ring

/-! ## Differentiability on the absolutely convergent half plane -/

theorem differentiableAt_riemannZeta_two_mul {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s := by
  have h2 := riemannZeta_ne_one_of_one_lt_re (two_mul_re_lt hs)
  exact (differentiableAt_riemannZeta h2).comp s
    ((differentiableAt_id).const_mul 2)

theorem differentiableAt_squarefreeZeta {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ squarefreeZeta s := by
  have h1 := differentiableAt_riemannZeta (riemannZeta_ne_one_of_one_lt_re hs)
  have h2 := differentiableAt_riemannZeta_two_mul hs
  exact h1.div h2 (riemannZeta_ne_zero_of_one_lt_re (two_mul_re_lt hs))

theorem deriv_riemannZeta_two_mul {s : ℂ} (hs : 1 < s.re) :
    deriv (fun z : ℂ => riemannZeta (2 * z)) s = deriv riemannZeta (2 * s) * 2 := by
  have h2 := riemannZeta_ne_one_of_one_lt_re (two_mul_re_lt hs)
  have hz : HasDerivAt riemannZeta (deriv riemannZeta (2 * s)) (2 * s) :=
    (differentiableAt_riemannZeta h2).hasDerivAt
  have hin : HasDerivAt (fun z : ℂ => 2 * z) 2 s := by
    simpa using ((hasDerivAt_id s).const_mul (2 : ℂ))
  exact (hz.comp s hin).deriv

theorem logDeriv_riemannZeta_two_mul_eulerSquarefreeDyadicAnalyticTelescope {s : ℂ} (hs : 1 < s.re) :
    logDeriv (fun z : ℂ => riemannZeta (2 * z)) s = 2 * logDeriv riemannZeta (2 * s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_two_mul hs]
  ring

/-! ## The morphism reconstruction `(29)` -/

theorem eulerLogMorphism_step {s : ℂ} (hs : 1 < s.re) :
    eulerLogMorphism s = squarefreeLogMorphism s + 2 * eulerLogMorphism (2 * s) := by
  have hs2 := two_mul_re_lt hs
  have hopen : {z : ℂ | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have heq : (riemannZeta : ℂ → ℂ)
      =ᶠ[nhds s] fun z : ℂ => squarefreeZeta z * riemannZeta (2 * z) := by
    filter_upwards [hopen] with z hz
    exact (squarefreeZeta_mul_riemannZeta hz).symm
  have hval : riemannZeta s = squarefreeZeta s * riemannZeta (2 * s) :=
    (squarefreeZeta_mul_riemannZeta hs).symm
  have hlog : logDeriv riemannZeta s
      = logDeriv (fun z : ℂ => squarefreeZeta z * riemannZeta (2 * z)) s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, hval]
  have hmul : logDeriv (fun z : ℂ => squarefreeZeta z * riemannZeta (2 * z)) s
      = logDeriv squarefreeZeta s + logDeriv (fun z : ℂ => riemannZeta (2 * z)) s :=
    logDeriv_mul s (squarefreeZeta_ne_zero hs) (riemannZeta_ne_zero_of_one_lt_re hs2)
      (differentiableAt_squarefreeZeta hs) (differentiableAt_riemannZeta_two_mul hs)
  rw [eulerLogMorphism, squarefreeLogMorphism, eulerLogMorphism, hlog, hmul,
    logDeriv_riemannZeta_two_mul_eulerSquarefreeDyadicAnalyticTelescope hs]
  ring

/-- **Equation (29).**  The exact finite dyadic reconstruction of the Euler logarithmic
morphism from the squarefree layers and the strict-right residual. -/
theorem eulerLogMorphism_dyadic_reconstruction : ∀ (R : ℕ) {s : ℂ}, 1 < s.re →
    eulerLogMorphism s
      = (∑ r ∈ Finset.range R, 2 ^ r * squarefreeLogMorphism (2 ^ r * s))
        + 2 ^ R * eulerLogMorphism (2 ^ R * s)
  | 0, s, _ => by simp
  | (R + 1), s, hs => by
      have hs2 := two_mul_re_lt hs
      have hIH := eulerLogMorphism_dyadic_reconstruction R hs2
      have hstep := eulerLogMorphism_step hs
      have hrw : ∀ r : ℕ, (2 : ℂ) ^ r * (2 * s) = 2 ^ (r + 1) * s := by
        intro r; rw [pow_succ]; ring
      have hpow : (2 : ℂ) ^ R * (2 * s) = 2 ^ (R + 1) * s := by rw [pow_succ]; ring
      have hsum : (2 : ℂ)
            * (∑ r ∈ Finset.range R, 2 ^ r * squarefreeLogMorphism (2 ^ r * (2 * s)))
          = ∑ k ∈ Finset.range R, 2 ^ (k + 1) * squarefreeLogMorphism (2 ^ (k + 1) * s) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hrw r, pow_succ]
        ring
      rw [hstep, hIH, Finset.sum_range_succ', hpow, ← hsum, pow_zero, one_mul]
      ring

end RHTower
