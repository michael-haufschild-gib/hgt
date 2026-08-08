import GaloisForLFunctions.RHTower.VanDerCorput

/-!
# Integration by parts for an oscillatory integral

The first-derivative van der Corput tests bound `∫ A·exp(iφ)` under a monotonicity assumption on
the phase derivative.  The mechanism behind them is a single integration by parts, and that step
needs no monotonicity at all: writing the integrand as `B·(exp∘iφ)'` for `B = A/(iφ')` turns the
integral into boundary terms plus the total variation of `B`.

The statement here takes the antiderivative datum `B` and its derivative as given, related to the
amplitude by `B·(iφ') = A`.  This makes it usable when `φ'` is not monotone but `1/φ'` still has
controlled variation, which is the situation of an oscillatory integral whose amplitude and
frequency are both slowly varying.
-/

noncomputable section

open MeasureTheory intervalIntegral Complex Set

namespace RHTower

/-- **Integration by parts for an oscillatory integral.**  If `B·(iφ') = A` on the interval, then
`∫ A·exp(iφ)` is bounded by the boundary values of `B` plus the integrated size of `B'`.  No
monotonicity or lower bound on the phase derivative is used. -/
theorem norm_integral_cexp_le_of_antiderivative
    {a b : ℝ} (hab : a ≤ b) {φ φ' : ℝ → ℝ} {A B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ Set.uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ Set.uIcc a b, HasDerivAt B (B' x) x)
    (hB'c : ContinuousOn B' (Set.uIcc a b))
    (hAc : ContinuousOn A (Set.uIcc a b))
    (hrel : ∀ x ∈ Set.uIcc a b, B x * (Complex.I * (φ' x : ℂ)) = A x) :
    ‖∫ t in a..b, A t * Complex.exp (Complex.I * φ t)‖ ≤
      ‖B b‖ + ‖B a‖ + ∫ t in a..b, ‖B' t‖ := by
  have hφc : ContinuousOn φ (Set.uIcc a b) := fun x hx =>
    (hφ x hx).continuousAt.continuousWithinAt
  have hVc : ContinuousOn (fun t : ℝ => Complex.exp (Complex.I * φ t)) (Set.uIcc a b) := by
    refine Complex.continuous_exp.comp_continuousOn ?_
    exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφc)
  have hVd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * φ t))
        (Complex.exp (Complex.I * φ x) * (Complex.I * (φ' x : ℂ))) x := by
    intro x hx
    exact (((hφ x hx).ofReal_comp).const_mul Complex.I).cexp
  have hprod : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => B t * Complex.exp (Complex.I * φ t))
        (B' x * Complex.exp (Complex.I * φ x) + A x * Complex.exp (Complex.I * φ x)) x := by
    intro x hx
    have h := (hB x hx).mul (hVd x hx)
    have hr := hrel x hx
    have hcalc : B' x * Complex.exp (Complex.I * φ x)
        + B x * (Complex.exp (Complex.I * φ x) * (Complex.I * (φ' x : ℂ)))
        = B' x * Complex.exp (Complex.I * φ x) + A x * Complex.exp (Complex.I * φ x) := by
      rw [← hr]; ring
    exact hcalc ▸ h
  have hi1 : IntervalIntegrable (fun t : ℝ => B' t * Complex.exp (Complex.I * φ t)) volume a b :=
    (hB'c.mul hVc).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ => A t * Complex.exp (Complex.I * φ t)) volume a b :=
    (hAc.mul hVc).intervalIntegrable
  have hftc : (∫ t in a..b, (B' t * Complex.exp (Complex.I * φ t)
      + A t * Complex.exp (Complex.I * φ t)))
      = B b * Complex.exp (Complex.I * φ b) - B a * Complex.exp (Complex.I * φ a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hprod (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hftc
  have hsplit : (∫ t in a..b, A t * Complex.exp (Complex.I * φ t))
      = B b * Complex.exp (Complex.I * φ b) - B a * Complex.exp (Complex.I * φ a)
        - ∫ t in a..b, B' t * Complex.exp (Complex.I * φ t) := by
    linear_combination hftc
  have hnormB' : (∫ t in a..b, ‖B' t * Complex.exp (Complex.I * φ t)‖)
      = ∫ t in a..b, ‖B' t‖ := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    simp only [norm_mul, norm_phase, mul_one]
  have hbound : ‖∫ t in a..b, B' t * Complex.exp (Complex.I * φ t)‖ ≤ ∫ t in a..b, ‖B' t‖ := by
    rw [← hnormB']
    exact intervalIntegral.norm_integral_le_integral_norm hab
  calc ‖∫ t in a..b, A t * Complex.exp (Complex.I * φ t)‖
      = ‖B b * Complex.exp (Complex.I * φ b) - B a * Complex.exp (Complex.I * φ a)
          - ∫ t in a..b, B' t * Complex.exp (Complex.I * φ t)‖ := by rw [hsplit]
    _ ≤ ‖B b * Complex.exp (Complex.I * φ b) - B a * Complex.exp (Complex.I * φ a)‖
          + ‖∫ t in a..b, B' t * Complex.exp (Complex.I * φ t)‖ := norm_sub_le _ _
    _ ≤ (‖B b * Complex.exp (Complex.I * φ b)‖ + ‖B a * Complex.exp (Complex.I * φ a)‖)
          + ∫ t in a..b, ‖B' t‖ := by
        exact add_le_add (norm_sub_le _ _) hbound
    _ = ‖B b‖ + ‖B a‖ + ∫ t in a..b, ‖B' t‖ := by
        rw [norm_mul, norm_mul, norm_phase, norm_phase, mul_one, mul_one]

/-- The boundary terms of the integration by parts are controlled by the amplitude divided by the
frequency lower bound. -/
theorem norm_antiderivative_le {x lam M : ℝ} {φ' : ℝ → ℝ} {A B : ℝ → ℂ}
    (hlam : 0 < lam) (hφ' : lam ≤ |φ' x|) (hM : ‖A x‖ ≤ M)
    (hrel : B x * (Complex.I * (φ' x : ℂ)) = A x) :
    ‖B x‖ ≤ M / lam := by
  have hnorm : ‖B x‖ * |φ' x| = ‖A x‖ := by
    rw [← hrel]
    simp [Complex.norm_I]
  have hstep : ‖B x‖ * lam ≤ M := by
    calc ‖B x‖ * lam ≤ ‖B x‖ * |φ' x| := by
          exact mul_le_mul_of_nonneg_left hφ' (norm_nonneg _)
      _ = ‖A x‖ := hnorm
      _ ≤ M := hM
  exact (le_div_iff₀ hlam).mpr hstep

/-- **Oscillatory bound with a bounded-variation antiderivative datum.**  With a frequency lower
bound `|φ'| ≥ λ > 0` and a bounded amplitude, the oscillatory integral is at most `2M/λ` plus the
integrated size of `B'`.  Unlike the monotone-phase first-derivative tests, the phase derivative is
allowed to vary arbitrarily; the variation is paid for by `B'`. -/
theorem norm_integral_cexp_le_of_frequency_lower_bound
    {a b lam M : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {φ φ' : ℝ → ℝ} {A B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ Set.uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ Set.uIcc a b, HasDerivAt B (B' x) x)
    (hB'c : ContinuousOn B' (Set.uIcc a b))
    (hAc : ContinuousOn A (Set.uIcc a b))
    (hrel : ∀ x ∈ Set.uIcc a b, B x * (Complex.I * (φ' x : ℂ)) = A x)
    (hφ'lb : ∀ x ∈ Set.uIcc a b, lam ≤ |φ' x|)
    (hM : ∀ x ∈ Set.uIcc a b, ‖A x‖ ≤ M) :
    ‖∫ t in a..b, A t * Complex.exp (Complex.I * φ t)‖ ≤
      2 * M / lam + ∫ t in a..b, ‖B' t‖ := by
  have hb := norm_antiderivative_le hlam (hφ'lb b Set.right_mem_uIcc) (hM b Set.right_mem_uIcc)
    (hrel b Set.right_mem_uIcc)
  have ha := norm_antiderivative_le hlam (hφ'lb a Set.left_mem_uIcc) (hM a Set.left_mem_uIcc)
    (hrel a Set.left_mem_uIcc)
  have hmain := norm_integral_cexp_le_of_antiderivative hab hφ hB hB'c hAc hrel
  have h2 : ‖B b‖ + ‖B a‖ ≤ 2 * M / lam := by
    have : M / lam + M / lam = 2 * M / lam := by ring
    linarith
  linarith


end RHTower
