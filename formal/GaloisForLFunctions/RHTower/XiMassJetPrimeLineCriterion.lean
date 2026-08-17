import GaloisForLFunctions.RHTower.XiMassPolynomialArchUniform
import GaloisForLFunctions.RHTower.XiMassJetEulerSourceCriterion

/-!
# The jet-modified prime-line criterion

Splitting the jet Euler-line source into its von-Mangoldt and archimedean halves and discarding the
uniformly bounded archimedean half leaves an exact RH criterion with no auxiliary analytic term: the
Riemann hypothesis is equivalent to uniform boundedness, on one positive vertical line, of the
jet-modified von-Mangoldt Euler-line integral.
-/

open Complex Filter MeasureTheory

namespace RHTower

noncomputable section

/-- The jet prime channel is the jet archimedean channel minus `π` times the weighted trace. -/
theorem integral_xiMassJetBottomPrimeIntegrand_eq {a c : ℝ} (ha : 1 / 2 < a) (N : ℕ)
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassPolyBottomPrimeIntegrand (xiMassJetPoly a N) a c τ x)
      = (∫ x : ℝ, xiMassPolyBottomArchIntegrand (xiMassJetPoly a N) a c τ x)
        - Real.pi * (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N) τ := by
  have hsrc := integral_xiMassJetBottomSourceIntegrand_eq_pi_I_mul_traceWC ha N hhalf hca hτ
  have hsplit := integral_xiMassPolyBottomSourceIntegrand_split (xiMassJetPoly a N)
    hhalf hca hτ
  have hE : -I * (∫ x : ℝ, xiMassPolyBottomPrimeIntegrand (xiMassJetPoly a N) a c τ x) +
      I * (∫ x : ℝ, xiMassPolyBottomArchIntegrand (xiMassJetPoly a N) a c τ x)
      = Real.pi * I * (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N) τ := by
    rw [← hsplit, hsrc]
  have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
  linear_combination I * hE +
    ((∫ x : ℝ, xiMassPolyBottomPrimeIntegrand (xiMassJetPoly a N) a c τ x)
      - (∫ x : ℝ, xiMassPolyBottomArchIntegrand (xiMassJetPoly a N) a c τ x)
      + (Real.pi : ℂ) * (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N) τ) * hI

/-- **The jet prime-line RH criterion.**  For every mass above one half, every jet order and every
legal contour depth, RH is equivalent to uniform boundedness on one positive vertical line of the
jet-modified von-Mangoldt Euler-line integral.  The archimedean channel is uniformly bounded, so it
carries no RH-strength information. -/
theorem riemannHypothesis_iff_exists_xiMassJetBottomPrime_line_bound {a c : ℝ} (ha : 1 / 2 < a)
    (N : ℕ) (hhalf : 1 / 2 < c) (hca : c < a) :
    RiemannHypothesis ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ,
        ‖∫ t : ℝ, xiMassPolyBottomPrimeIntegrand (xiMassJetPoly a N) a c
            ((σ : ℂ) + (x : ℂ) * I) t‖ ≤ C := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnormpi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  constructor
  · intro hRH
    obtain ⟨σ, C, hσ, hline⟩ :=
      (riemannHypothesis_iff_exists_xiMassCausticJetTrace_line_bound ha N).mp hRH
    refine ⟨σ, xiMassPolyBottomArchUniformBound (xiMassJetPoly a N) a σ + Real.pi * C,
      hσ, fun x => ?_⟩
    have hτ : (0 : ℝ) < ((σ : ℂ) + (x : ℂ) * I).re := by
      simpa [Complex.mul_re] using hσ
    rw [integral_xiMassJetBottomPrimeIntegrand_eq ha N hhalf hca hτ]
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · exact norm_integral_xiMassPolyBottomArchIntegrand_le_uniform (xiMassJetPoly a N)
        hhalf hca hσ
    · rw [norm_mul, hnormpi]
      exact mul_le_mul_of_nonneg_left (hline x) hpi.le
  · rintro ⟨σ, C, hσ, hline⟩
    refine (riemannHypothesis_iff_exists_xiMassCausticJetTrace_line_bound ha N).mpr
      ⟨σ, (xiMassPolyBottomArchUniformBound (xiMassJetPoly a N) a σ + C) / Real.pi,
        hσ, fun x => ?_⟩
    have hτ : (0 : ℝ) < ((σ : ℂ) + (x : ℂ) * I).re := by
      simpa [Complex.mul_re] using hσ
    have hid := integral_xiMassJetBottomPrimeIntegrand_eq ha N hhalf hca hτ
    have hpiT : ((Real.pi : ℝ) : ℂ) *
        (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N)
          ((σ : ℂ) + (x : ℂ) * I)
        = (∫ t : ℝ, xiMassPolyBottomArchIntegrand (xiMassJetPoly a N) a c
              ((σ : ℂ) + (x : ℂ) * I) t)
          - ∫ t : ℝ, xiMassPolyBottomPrimeIntegrand (xiMassJetPoly a N) a c
              ((σ : ℂ) + (x : ℂ) * I) t := by
      rw [hid]
      ring
    have hnorm : Real.pi * ‖(xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N)
        ((σ : ℂ) + (x : ℂ) * I)‖
        ≤ xiMassPolyBottomArchUniformBound (xiMassJetPoly a N) a σ + C := by
      have hcalc : Real.pi * ‖(xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N)
          ((σ : ℂ) + (x : ℂ) * I)‖
          = ‖((Real.pi : ℝ) : ℂ) *
              (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N)
                ((σ : ℂ) + (x : ℂ) * I)‖ := by
        rw [norm_mul, hnormpi]
      rw [hcalc, hpiT]
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ (hline x))
      exact norm_integral_xiMassPolyBottomArchIntegrand_le_uniform (xiMassJetPoly a N)
        hhalf hca hσ
    rw [le_div_iff₀ hpi, mul_comm]
    exact hnorm

end

end RHTower
