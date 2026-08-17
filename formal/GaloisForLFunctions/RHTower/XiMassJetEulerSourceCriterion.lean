import GaloisForLFunctions.RHTower.XiMassJetPolynomialBridge
import GaloisForLFunctions.RHTower.XiMassCausticJetTraceCriterion

/-!
# The jet-modified Euler-line source criterion

Unnormalizing the jet Euler-contour source identity turns the spectral criterion `(22.5)` into a
criterion about one absolutely convergent Euler-line integral of the modified receiver against the
von-Mangoldt minus archimedean source.  No spectral object survives in the statement.
-/

open Complex Filter MeasureTheory

namespace RHTower

noncomputable section

/-- **The jet-modified Euler-line source is `π i` times the jet-weighted trace.** -/
theorem integral_xiMassJetBottomSourceIntegrand_eq_pi_I_mul_traceWC {a c : ℝ} (ha : 1 / 2 < a)
    (N : ℕ) (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassPolyBottomSourceIntegrand (xiMassJetPoly a N) a c τ x)
      = Real.pi * I * (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N) τ := by
  have hcontour := traceWC_xiMassCausticJet_eq_normalizedBottomEulerContour ha N hhalf hca hτ
  have hnorm : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hexp : (2 * Real.pi * I : ℂ) *
      ((xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N) τ)
      = 2 * ∫ x : ℝ, xiMassPolyBottomSourceIntegrand (xiMassJetPoly a N) a c τ x := by
    rw [hcontour, normalizedXiMassPolyBottomEulerContour, ← mul_assoc,
      mul_inv_cancel₀ hnorm, one_mul]
  have htwo : (2 : ℂ) * (Real.pi * I *
      (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N) τ)
      = 2 * ∫ x : ℝ, xiMassPolyBottomSourceIntegrand (xiMassJetPoly a N) a c τ x := by
    rw [← hexp]
    ring
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo).symm

/-- **(22.5), Euler-line form.**  For every mass above one half, every jet order and every legal
contour depth, RH is equivalent to uniform boundedness, on one positive vertical line, of the
absolutely convergent jet-modified Euler-line source integral. -/
theorem riemannHypothesis_iff_exists_xiMassJetBottomSource_line_bound {a c : ℝ} (ha : 1 / 2 < a)
    (N : ℕ) (hhalf : 1 / 2 < c) (hca : c < a) :
    RiemannHypothesis ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ,
        ‖∫ t : ℝ, xiMassPolyBottomSourceIntegrand (xiMassJetPoly a N) a c
            ((σ : ℂ) + (x : ℂ) * I) t‖ ≤ C := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnormpi : ‖(Real.pi * I : ℂ)‖ = Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpi]
  constructor
  · intro hRH
    obtain ⟨σ, C, hσ, hline⟩ :=
      (riemannHypothesis_iff_exists_xiMassCausticJetTrace_line_bound ha N).mp hRH
    refine ⟨σ, Real.pi * C, hσ, fun x => ?_⟩
    have hτ : (0 : ℝ) < ((σ : ℂ) + (x : ℂ) * I).re := by
      simpa [Complex.mul_re] using hσ
    rw [integral_xiMassJetBottomSourceIntegrand_eq_pi_I_mul_traceWC ha N hhalf hca hτ,
      norm_mul, hnormpi]
    exact mul_le_mul_of_nonneg_left (hline x) hpi.le
  · rintro ⟨σ, C, hσ, hline⟩
    refine (riemannHypothesis_iff_exists_xiMassCausticJetTrace_line_bound ha N).mpr
      ⟨σ, C / Real.pi, hσ, fun x => ?_⟩
    have hτ : (0 : ℝ) < ((σ : ℂ) + (x : ℂ) * I).re := by
      simpa [Complex.mul_re] using hσ
    have h := hline x
    rw [integral_xiMassJetBottomSourceIntegrand_eq_pi_I_mul_traceWC ha N hhalf hca hτ,
      norm_mul, hnormpi] at h
    rw [le_div_iff₀ hpi, mul_comm]
    exact h

end

end RHTower
