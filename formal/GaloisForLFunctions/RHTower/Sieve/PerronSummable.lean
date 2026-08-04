import GaloisForLFunctions.RHTower.Sieve.PerronGeneralTerm

/-!
# The smoothed Perron formula under a summability hypothesis

The unit bound on the coefficients is stronger than the identity needs.  What the proof actually
uses is that the Dirichlet series converges absolutely on the line, and that is the natural
hypothesis: the smoothed sum is finite, but the identity equates it with an integral of the *full*
series.

Replacing `‖a n‖ ≤ 1` by `Summable (fun n => ‖a n‖ · n^{-σ})` costs nothing in the proof and admits
every Dirichlet series whose abscissa of convergence lies below `σ` — in particular `Λ`, whose
coefficients grow like `log n`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set Filter GaloisForLFunctions.HTGeometry

/-- **The smoothed Perron formula, under absolute convergence on the line.** -/
theorem tsum_mul_smoothWeight_eq_integral_summable {a : ℕ → ℂ} (ha0 : a 0 = 0) {N H : ℝ}
    (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (hsummable : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-σ)) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (∑' n : ℕ, a n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I))) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * Complex.I) := by
  classical
  have hσ0 : (0 : ℝ) < σ := by linarith
  set W : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
      ((σ : ℂ) + (y : ℝ) * Complex.I) with hWdef
  set F : ℕ → ℝ → ℂ := fun n y =>
    a n * ((n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I)) * W y) with hF
  have hWint : Integrable W := verticalIntegrable_mellin_smoothWeight hN hH hσ0
  have hint : ∀ n, Integrable (F n) := fun n =>
    integrable_perron_term_general ha0 hN hH hσ0 n
  set V : ℝ := ∫ y : ℝ, ‖W y‖ with hV
  have hV0 : 0 ≤ V := integral_nonneg fun y => norm_nonneg _
  have hnormle : ∀ n : ℕ, (∫ y : ℝ, ‖F n y‖) ≤ (‖a n‖ * (n : ℝ) ^ (-σ)) * V := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, ha0, Real.zero_rpow (by linarith : -σ ≠ 0)]
    have heq : ∀ y : ℝ, ‖F n y‖ = ‖a n‖ * (n : ℝ) ^ (-σ) * ‖W y‖ := by
      intro y
      rw [hF]
      simp only
      rw [norm_mul, norm_mul, norm_natCast_cpow_neg_line hn]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul]
  have hsum : Summable fun n : ℕ => ∫ y : ℝ, ‖F n y‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) hnormle ?_
    exact hsummable.mul_right V
  have hHS := hasSum_integral_of_summable_integral_norm hint hsum
  have hpoint : ∀ y : ℝ, (∑' n : ℕ, F n y)
      = (∑' n : ℕ, a n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I))) * W y := by
    intro y
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [hF]
    ring
  have hterm : ∀ n : ℕ, (∫ y : ℝ, F n y)
      = (2 * Real.pi : ℝ) • (a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, ha0]
    rw [hF]
    simp only
    rw [integral_perron_term hN hH hσ0 hn]
    exact mul_smul_comm _ _ _
  have hfin : Summable fun n : ℕ => a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
    refine summable_of_ne_finset_zero (s := Finset.range (⌈N + H⌉₊ + 1)) fun n hn => ?_
    rw [Finset.mem_range] at hn
    have hge : N + H ≤ (n : ℝ) := by
      have h1 : (N + H : ℝ) ≤ (⌈N + H⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈N + H⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.le_of_not_lt hn
      push_cast at h2
      linarith
    rw [smoothWeight_eq_zero hH hge]
    simp
  have hHS2 : HasSum (fun n : ℕ => (2 * Real.pi : ℝ) •
      (a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)))
      ((2 * Real.pi : ℝ) • ∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) :=
    hfin.hasSum.const_smul _
  have hHS3 : HasSum (fun n : ℕ => ∫ y : ℝ, F n y)
      ((2 * Real.pi : ℝ) • ∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) := by
    have hfun : (fun n : ℕ => ∫ y : ℝ, F n y)
        = fun n : ℕ => (2 * Real.pi : ℝ) • (a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) :=
      funext hterm
    rw [hfun]
    exact hHS2
  rw [hHS3.unique hHS]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

end RHTower.Sieve
