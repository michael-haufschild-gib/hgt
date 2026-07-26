import GaloisForLFunctions.RHTower.MobiusBinaryExcursion

/-!
# The character-twisted Möbius--Laplace source

The conductor-one development uses the Mellin--Dirichlet identity
`mellin A s = Γ(s) / ζ(s)` on `Re s > 1`.  The same identity holds for the source twisted by a
Dirichlet character, with `ζ` replaced by `L(s, χ)`, because mathlib supplies both the Mellin
interchange (`hasSum_mellin`) and the inverse relation `L(χ) · L(χ·μ) = 1`.

This is the analytic input `(R9)` of the order law at arbitrary conductor.
-/

open Complex Filter Set
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {N : ℕ}

/-- The character-twisted Möbius--Laplace source `∑ χ(n) μ(n) e^{-n x}`. -/
noncomputable def twistedMobiusLaplaceTransform (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑' n : ℕ, (↗χ * ↗μ) n * Complex.exp (-((n : ℝ) * x : ℝ))

theorem norm_twistedMobiusCoeff_le_one (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖(↗χ * ↗μ) n‖ ≤ 1 := by
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one n
  have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  simpa [norm_mul] using mul_le_one₀ hχ (norm_nonneg _) hμ

theorem summable_twistedMobiusLaplaceTerm (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => (↗χ * ↗μ) n * Complex.exp (-((n : ℝ) * x : ℝ)) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_pow_mul_exp_neg 0 hx)
  rw [norm_mul, Complex.norm_exp]
  have hexp : 0 ≤ Real.exp (-((n : ℝ) * x)) := (Real.exp_pos _).le
  simpa using mul_le_mul_of_nonneg_right (norm_twistedMobiusCoeff_le_one χ n) hexp

theorem twistedMobiusLaplaceTerm_hasSum (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (↗χ * ↗μ) n * Complex.exp (-((n : ℝ) * x : ℝ)))
      (twistedMobiusLaplaceTransform χ x) :=
  (summable_twistedMobiusLaplaceTerm χ hx).hasSum

/-- The weighted twisted coefficients are summable on `Re s > 1`. -/
theorem twistedMobiusMellin_weight_summable (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖(↗χ * ↗μ) n‖ / (n : ℝ) ^ s.re := by
  have h := (DirichletCharacter.LSeriesSummable_mul χ
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)).norm
  refine h.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn]

/-- **Mellin--Dirichlet identity, twisted form.**  On the half-plane of absolute convergence the
Mellin transform of the twisted source is `Γ(s)` times the twisted Möbius L-series. -/
theorem mellin_twistedMobiusLaplaceTransform_eq_gamma_mul_LSeries
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    mellin (twistedMobiusLaplaceTransform χ) s = Complex.Gamma s * L (↗χ * ↗μ) s := by
  have hp : ∀ n : ℕ, (↗χ * ↗μ) n = 0 ∨ 0 < (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · left
      subst n
      simp
    · right
      exact_mod_cast Nat.pos_of_ne_zero hn
  have hs0 : 0 < s.re := by linarith
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n : ℕ => (↗χ * ↗μ) n * Real.exp (-(n : ℝ) * t))
        (twistedMobiusLaplaceTransform χ t) := by
    intro t ht
    convert twistedMobiusLaplaceTerm_hasSum χ ht using 2 with n
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  have hmellin : HasSum (fun n : ℕ => Complex.Gamma s * (↗χ * ↗μ) n / (n : ℂ) ^ s)
      (mellin (twistedMobiusLaplaceTransform χ) s) :=
    hasSum_mellin hp hs0 hF (twistedMobiusMellin_weight_summable χ hs)
  rw [← hmellin.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def₀ (by simp) s n, div_eq_mul_inv, Complex.cpow_neg]
  ring

/-- The twisted source has Mellin transform `Γ(s)/L(s,χ)` on `Re s > 1`. -/
theorem mellin_twistedMobiusLaplaceTransform_eq_gamma_div_LSeries
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    mellin (twistedMobiusLaplaceTransform χ) s = Complex.Gamma s * (L ↗χ s)⁻¹ := by
  rw [mellin_twistedMobiusLaplaceTransform_eq_gamma_mul_LSeries χ hs]
  congr 1
  have hone := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hne : L ↗χ s ≠ 0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
  field_simp
  linear_combination hone

end RHTower
