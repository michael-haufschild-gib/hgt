import GaloisForLFunctions.RHTower.Sieve.PerronRectangleResidueUnderRH
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivCriticalBound

/-!
# A uniform bound for `ζ'/ζ` on a line right of the critical line

Under the Riemann hypothesis the logarithmic derivative is `O(log|t|)` above height `7`, and on the
remaining compact segment it is continuous — `ζ` has no zero there and the pole is to the right — so
one constant serves the whole line.
-/

namespace RHTower.Sieve

open Complex Topology

noncomputable section

/-- `ζ'/ζ` is continuous on a vertical segment right of the critical line. -/
theorem continuousOn_logDeriv_zeta_segment (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1) (T : ℝ) :
    ContinuousOn (fun t : ℝ => logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
      (Set.Icc (-T) T) := by
  intro t _
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have hne1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    rw [hcon] at hre
    simp only [Complex.one_re] at hre
    linarith
  have hzne : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_rh hRH (by rw [hre]; linarith) hne1
  have hcont : ContinuousAt (fun t : ℝ => logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)) t := by
    have hinner : ContinuousAt (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)) t := by
      fun_prop
    have hout : ContinuousAt (logDeriv riemannZeta) ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      have hd : DifferentiableAt ℂ (fun s : ℂ => deriv riemannZeta s / riemannZeta s)
          ((σ : ℂ) + (t : ℂ) * Complex.I) :=
        (differentiableAt_deriv_riemannZeta hne1).div (differentiableAt_riemannZeta hne1) hzne
      have hfun : (fun s : ℂ => deriv riemannZeta s / riemannZeta s) = logDeriv riemannZeta := by
        funext s
        rw [logDeriv_apply]
      rw [hfun] at hd
      exact hd.continuousAt
    have hcomp : ContinuousAt ((logDeriv riemannZeta) ∘
        (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)) t :=
      ContinuousAt.comp (g := logDeriv riemannZeta)
        (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) hout hinner
    exact hcomp
  exact hcont.continuousWithinAt

/-- **A uniform bound for `ζ'/ζ` on a line right of the critical line.** -/
theorem exists_logDeriv_zeta_line_bound (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ,
      ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ K * (1 + Real.log (2 + |t|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_logDeriv_zeta_bound_rh hRH
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc (a := (-7 : ℝ)) (b := 7)).exists_bound_of_continuousOn
    ((continuousOn_logDeriv_zeta_segment hRH hσ0 hσ1 7).norm)
  refine ⟨max K₀ (C / (σ - 1 / 2)) + 1, by positivity, ?_⟩
  intro t
  have hlogpos : (0 : ℝ) ≤ Real.log (2 + |t|) :=
    Real.log_nonneg (by have := abs_nonneg t; linarith)
  rcases le_or_gt |t| 7 with hle | hgt
  · have hmem : t ∈ Set.Icc (-7 : ℝ) 7 := by
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
    have h : ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K₀ := by
      simpa using hK₀ t hmem
    have hK0le : K₀ ≤ max K₀ (C / (σ - 1 / 2)) := le_max_left _ _
    have hCpos : (0 : ℝ) < C / (σ - 1 / 2) := by
      have : (0 : ℝ) < σ - 1 / 2 := by linarith
      positivity
    have hmax0 : (0 : ℝ) < max K₀ (C / (σ - 1 / 2)) :=
      lt_of_lt_of_le hCpos (le_max_right _ _)
    nlinarith [h, hlogpos, hK0le, hmax0]
  · have hb := hC σ t (by linarith) hσ0 (by linarith)
    have hlog7 : (1 : ℝ) ≤ Real.log |t| := by
      have he : Real.exp 1 < 7 := by
        have := Real.exp_one_lt_d9
        linarith
      have h := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ |t|)
      rwa [Real.log_exp] at h
    have hmono : Real.log |t| ≤ Real.log (2 + |t|) :=
      Real.log_le_log (by linarith) (by linarith)
    have hpos : (0 : ℝ) < σ - 1 / 2 := by linarith
    have hle : C * Real.log |t| / (σ - 1 / 2) ≤ (C / (σ - 1 / 2)) * Real.log (2 + |t|) := by
      have hid : C * Real.log |t| / (σ - 1 / 2) = (C / (σ - 1 / 2)) * Real.log |t| := by ring
      rw [hid]
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    have hKle : C / (σ - 1 / 2) ≤ max K₀ (C / (σ - 1 / 2)) := le_max_right _ _
    have hCpos : (0 : ℝ) < C / (σ - 1 / 2) := by positivity
    nlinarith [hb, hle, hKle, hlogpos, hCpos]

end

end RHTower.Sieve
