import GaloisForLFunctions.HTGeometry.PolynomialVanishingOrderBound

/-!
# A rational function vanishing to order `N` is `O(‖u‖^N)` near the origin

`exists_norm_polyEval_div_pow_le_of_dvd` handles the denominator `(1+u)^k`, which is what the
Stirling ladder produces.  The shift ratio of a Gamma monomial produces an arbitrary denominator
that is merely nonzero at the origin, so the bound is restated for that case: the denominator is
bounded away from zero on a small enough disc, by its own value at the origin.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- A polynomial is bounded below near a point where it does not vanish. -/
theorem exists_radius_norm_polyEval_ge {Q : Polynomial ℂ} (hQ : Polynomial.eval 0 Q ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u : ℂ, ‖u‖ ≤ ρ → ‖Polynomial.eval 0 Q‖ / 2 ≤ ‖Q.eval u‖ := by
  classical
  have hdvd : (Polynomial.X : Polynomial ℂ) ∣ Q - Polynomial.C (Polynomial.eval 0 Q) := by
    have h1 : ((Polynomial.X : Polynomial ℂ) ^ 1) ∣ Q - Polynomial.C (Polynomial.eval 0 Q) := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      interval_cases d
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_eval_zero,
        sub_self]
    simpa using h1
  obtain ⟨W, hW⟩ := hdvd
  set B : ℝ := ∑ j ∈ Finset.range (W.natDegree + 1), ‖W.coeff j‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hQ0 : 0 < ‖Polynomial.eval 0 Q‖ := norm_pos_iff.mpr hQ
  refine ⟨min 1 (‖Polynomial.eval 0 Q‖ / (2 * (B + 1))), ?_, min_le_left _ _, fun u hu => ?_⟩
  · refine lt_min one_pos ?_
    positivity
  · have hu1 : ‖u‖ ≤ 1 := le_trans hu (min_le_left _ _)
    have hu2 : ‖u‖ ≤ ‖Polynomial.eval 0 Q‖ / (2 * (B + 1)) := le_trans hu (min_le_right _ _)
    have hWb : ‖W.eval u‖ ≤ B := norm_polyEval_le_of_norm_le_one W hu1
    have hval : Q.eval u = Polynomial.eval 0 Q + u * W.eval u := by
      have := congrArg (Polynomial.eval u) hW
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X] at this
      linear_combination this
    have hsmall : ‖u * W.eval u‖ ≤ ‖Polynomial.eval 0 Q‖ / 2 := by
      rw [norm_mul]
      have hstep : ‖u‖ * ‖W.eval u‖ ≤ (‖Polynomial.eval 0 Q‖ / (2 * (B + 1))) * (B + 1) := by
        refine mul_le_mul hu2 (by linarith) (norm_nonneg _) (by positivity)
      have hfin : (‖Polynomial.eval 0 Q‖ / (2 * (B + 1))) * (B + 1)
          = ‖Polynomial.eval 0 Q‖ / 2 := by
        field_simp
      linarith [hstep, hfin.le, hfin.symm.le]
    have hlow := norm_sub_le (Polynomial.eval 0 Q + u * W.eval u) (u * W.eval u)
    rw [add_sub_cancel_right] at hlow
    rw [hval]
    linarith [hlow, hsmall]

/-- **A rational function whose numerator vanishes to order `N` is `O(‖u‖^N)` near the origin.** -/
theorem exists_norm_polyEval_div_le_of_dvd {P Q : Polynomial ℂ} {N : ℕ}
    (h : (Polynomial.X ^ N : Polynomial ℂ) ∣ P) (hQ : Polynomial.eval 0 Q ≠ 0) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ u : ℂ, ‖u‖ ≤ ρ →
      ‖P.eval u / Q.eval u‖ ≤ C * ‖u‖ ^ N := by
  classical
  obtain ⟨W, hW⟩ := h
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_radius_norm_polyEval_ge hQ
  have hQ0 : 0 < ‖Polynomial.eval 0 Q‖ := norm_pos_iff.mpr hQ
  set B : ℝ := ∑ j ∈ Finset.range (W.natDegree + 1), ‖W.coeff j‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨2 * B / ‖Polynomial.eval 0 Q‖, ρ, by positivity, hρ0, fun u hu => ?_⟩
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hu1 : ‖u‖ ≤ 1 := le_trans hu hρ1
  have hlow := hρ u hu
  have hden : 0 < ‖Q.eval u‖ := by linarith
  have hWb : ‖W.eval u‖ ≤ B := norm_polyEval_le_of_norm_le_one W hu1
  have heval : P.eval u = u ^ N * W.eval u := by
    rw [hW, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [heval, norm_div, norm_mul, norm_pow, div_le_iff₀ hden]
  have hnum : ‖u‖ ^ N * ‖W.eval u‖ ≤ ‖u‖ ^ N * B :=
    mul_le_mul_of_nonneg_left hWb (by positivity)
  have hgoal : ‖u‖ ^ N * B ≤ 2 * B / ‖Polynomial.eval 0 Q‖ * ‖u‖ ^ N * ‖Q.eval u‖ := by
    have hfac : 2 * B / ‖Polynomial.eval 0 Q‖ * ‖u‖ ^ N * ‖Q.eval u‖
        = (‖u‖ ^ N * B) * (2 * ‖Q.eval u‖ / ‖Polynomial.eval 0 Q‖) := by
      field_simp
    rw [hfac]
    have hratio : (1 : ℝ) ≤ 2 * ‖Q.eval u‖ / ‖Polynomial.eval 0 Q‖ := by
      rw [le_div_iff₀ hQ0]
      linarith
    nlinarith [mul_nonneg (pow_nonneg hu0 N) hB0, hratio]
  linarith [hnum, hgoal]

end

end GaloisForLFunctions.HTGeometry
