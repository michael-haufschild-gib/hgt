import GaloisForLFunctions.RHTower.CCMCriticalMellinResolventExponentialWidth

/-!
# Unconditional causal Laplace bridge for the CCM unit-Riesz source

The literal unit-rate causal resolvent of normalized Chebyshev error has an elementary
half-exponential envelope.  The rate is forced by the square-root normalization; it is not an
RH-quality estimate.  It nevertheless supplies the integrability that the causal
integration-by-parts identity requires, removing its former bounded-resolvent premise in the
honest half-plane `Re z > 1/2`.

Consequently the completed SP-E/Suzuki common charge, through its exact identification with this
source, has a source-faithful Laplace bridge to the regularized zeta logarithmic derivative.
The result records the full pre-prime correction `2/3`; no boundary term is discarded.
-/

open Set MeasureTheory Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Elementary half-exponential envelope for the square-root-normalized Chebyshev error. -/
theorem abs_criticalMellinChebyshevError_le_exp_half
    (x : ℝ) :
    |criticalMellinChebyshevError x| ≤
      (Real.log 4 + 5) * Real.exp (x / 2) := by
  have hpsi0 : 0 ≤ Chebyshev.psi (Real.exp x) := Chebyshev.psi_nonneg _
  have hpsi := Chebyshev.psi_le_const_mul_self (Real.exp_pos x).le
  have herr : |Chebyshev.psi (Real.exp x) - Real.exp x| ≤
      (Real.log 4 + 5) * Real.exp x := by
    calc
      |Chebyshev.psi (Real.exp x) - Real.exp x| ≤
          |Chebyshev.psi (Real.exp x)| + |Real.exp x| := abs_sub _ _
      _ = Chebyshev.psi (Real.exp x) + Real.exp x := by
        rw [abs_of_nonneg hpsi0, abs_of_pos (Real.exp_pos x)]
      _ ≤ (Real.log 4 + 4) * Real.exp x + Real.exp x := by gcongr
      _ = (Real.log 4 + 5) * Real.exp x := by ring
  rw [criticalMellinChebyshevError_eq_exp, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    |Chebyshev.psi (Real.exp x) - Real.exp x| * Real.exp (-x / 2) ≤
        ((Real.log 4 + 5) * Real.exp x) * Real.exp (-x / 2) := by
      gcongr
    _ = (Real.log 4 + 5) * Real.exp (x / 2) := by
      rw [show ((Real.log 4 + 5) * Real.exp x) * Real.exp (-x / 2) =
          (Real.log 4 + 5) * (Real.exp x * Real.exp (-x / 2)) by ring,
        ← Real.exp_add]
      congr 2
      ring

/-- The causal unit-Riesz source has its unconditional elementary envelope at rate `1/2`. -/
theorem abs_criticalMellinChebyshevResolventSource_le_exp_half
    (x : ℝ) :
    |criticalMellinChebyshevResolventSource x| ≤
      (2 / 3) * (Real.log 4 + 5) * Real.exp (x / 2) := by
  let C : ℝ := Real.log 4 + 5
  let f : ℝ → ℝ := fun t =>
    Real.exp (-t) * criticalMellinChebyshevError (x - t)
  let M : ℝ → ℝ := fun t =>
    C * Real.exp (x / 2) * Real.exp (-(3 / 2) * t)
  have herror : ∀ u : ℝ,
      |criticalMellinChebyshevError u| ≤ C * Real.exp (u / 2) := by
    intro u
    exact abs_criticalMellinChebyshevError_le_exp_half u
  have hpoint : ∀ t : ℝ, |f t| ≤ M t := by
    intro t
    dsimp only [f, M]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-t) * |criticalMellinChebyshevError (x - t)| ≤
          Real.exp (-t) * (C * Real.exp ((x - t) / 2)) := by
        gcongr
        exact herror (x - t)
      _ = C * Real.exp (x / 2) * Real.exp (-(3 / 2) * t) := by
        have hexp : Real.exp (-t) * Real.exp ((x - t) / 2) =
            Real.exp (x / 2) * Real.exp (-(3 / 2) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [show Real.exp (-t) * (C * Real.exp ((x - t) / 2)) =
            C * (Real.exp (-t) * Real.exp ((x - t) / 2)) by ring, hexp]
        ring
  have hmajor : IntegrableOn M (Ioi (0 : ℝ)) := by
    dsimp only [M]
    exact (integrableOn_exp_mul_Ioi (by norm_num : -(3 / 2 : ℝ) < 0) 0)
      |>.const_mul (C * Real.exp (x / 2))
  have herrorMeas : Measurable criticalMellinChebyshevError := by
    convert measurable_criticalMellinNormalizedChebyshevError using 1
    ext u
    exact (criticalMellinNormalizedChebyshevError_eq_apertureError u).symm
  have hfMeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) := by
    dsimp only [f]
    exact ((Real.measurable_exp.comp (measurable_id.neg)).mul
      (herrorMeas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable.restrict
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    refine hmajor.mono' hfMeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    exact hpoint t
  change |∫ t in Ioi (0 : ℝ), f t| ≤
    (2 / 3) * C * Real.exp (x / 2)
  calc
    |∫ t in Ioi (0 : ℝ), f t| = ‖∫ t in Ioi (0 : ℝ), f t‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖f t‖ := norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (0 : ℝ), |f t| := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact Real.norm_eq_abs _
    _ ≤ ∫ t in Ioi (0 : ℝ), M t := by
      apply setIntegral_mono_ae hf.norm hmajor
      filter_upwards with t
      rw [Real.norm_eq_abs]
      exact hpoint t
    _ = (2 / 3) * C * Real.exp (x / 2) := by
      dsimp only [M]
      rw [show (fun t : ℝ =>
          C * Real.exp (x / 2) * Real.exp (-(3 / 2) * t)) =
          fun t : ℝ => (C * Real.exp (x / 2)) * Real.exp (-(3 / 2) * t) by rfl,
        MeasureTheory.integral_const_mul,
        integral_exp_mul_Ioi (by norm_num : -(3 / 2 : ℝ) < 0) 0]
      norm_num
      ring

/-- The literal causal source satisfies the rate-one-half exponential-width certificate. -/
theorem criticalMellinChebyshevResolvent_halfExponentialBounded :
    CriticalMellinChebyshevResolventExponentialBounded (1 / 2 : ℝ) := by
  refine ⟨(2 / 3) * (Real.log 4 + 5), by positivity, ?_⟩
  intro t ht
  calc
    |criticalMellinChebyshevResolventSource t| ≤
        (2 / 3) * (Real.log 4 + 5) * Real.exp (t / 2) :=
      abs_criticalMellinChebyshevResolventSource_le_exp_half t
    _ = ((2 / 3) * (Real.log 4 + 5)) * Real.exp ((1 / 2 : ℝ) * t) := by
      congr 2
      ring

/-- In the naturally convergent half-plane, the causal-resolvent identity is unconditional. -/
theorem criticalNormalizedChebyshevErrorLaplace_eq_resolvent_on_real
    {r : ℝ} (hr : 1 / 2 < r) :
    criticalNormalizedChebyshevErrorLaplace (r : ℂ) =
      ((r : ℂ) + 1) * criticalMellinChebyshevResolventLaplace (r : ℂ) + 2 / 3 := by
  rcases criticalMellinChebyshevResolvent_halfExponentialBounded with ⟨B, hB0, hB⟩
  exact criticalNormalizedChebyshevErrorLaplace_eq_resolvent_on_real_of_exponentialBound
    hB0 hB hr hr

/-- The endpoint rate `1/2` still identifies the causal defect extension with the regularized
critical-Mellin defect throughout its exact right-half-plane domain.  This is the closed endpoint
of the generic exponential-width argument: its proof uses the real ray `r > 2` as an identity
set and does not require an artificial strict gap below `1/2`. -/
theorem criticalMellinChebyshevResolventDefectExtension_eq_regularized_rightHalfPlane
    {u : ℂ} (hu : 0 < u.re) :
    criticalMellinChebyshevResolventDefectExtension u =
      regularizedCriticalMellinDefect u := by
  rcases criticalMellinChebyshevResolvent_halfExponentialBounded with ⟨B, hB0, hB⟩
  let U : Set ℂ := {v : ℂ | 0 < v.re}
  have hAfull :=
    analyticOnNhd_criticalMellinChebyshevResolventDefectExtension_of_exponentialBound
      (alpha := 1 / 2) (by norm_num : 0 ≤ (1 / 2 : ℝ)) hB0 hB
  have hA : AnalyticOnNhd ℂ criticalMellinChebyshevResolventDefectExtension U :=
    hAfull.mono (by
      intro v hv
      change 0 < v.re at hv
      change (1 / 2 : ℝ) - 1 / 2 < v.re
      norm_num
      exact hv)
  have hR : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U := by
    simpa only [U] using analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
  have htwo : (2 : ℂ) ∈ U := by
    change 0 < (2 : ℂ).re
    norm_num
  have htend : Tendsto (fun r : ℝ => (r : ℂ))
      (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => (r : ℂ))
          (𝓝 (2 : ℝ)) (𝓝 (2 : ℂ)) := by
        simpa using Complex.continuous_ofReal.tendsto (2 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hcon
      have : r = 2 := by exact_mod_cast hcon
      exact absurd this (ne_of_gt hr)
  have hfreq : ∃ᶠ v in 𝓝[≠] (2 : ℂ),
      criticalMellinChebyshevResolventDefectExtension v =
        regularizedCriticalMellinDefect v := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    change (2 : ℝ) < r at hr
    exact criticalMellinChebyshevResolventDefectExtension_eq_regularized_on_real_of_exponentialBound
      hB0 hB (lt_trans (by norm_num) hr) (by linarith)
  have heq := hA.eqOn_of_preconnected_of_frequently_eq hR
    (convex_halfSpace_re_gt 0).isPreconnected htwo hfreq
  exact heq hu

/-- Exact source-faithful Laplace bridge from the causal unit-Riesz charge to zeta's
regularized logarithmic derivative, retaining the pre-prime `2/3` boundary mass. -/
theorem criticalMellinChebyshevResolventLaplace_eq_logDeriv_on_real
    {r : ℝ} (hr : 1 / 2 < r) :
    ((r : ℂ) + 1) * criticalMellinChebyshevResolventLaplace (r : ℂ) + 2 / 3 =
      -(logDeriv zetaResidueUnit ((r : ℂ) + 1 / 2) + 1) /
        ((r : ℂ) + 1 / 2) := by
  rw [← criticalNormalizedChebyshevErrorLaplace_eq_resolvent_on_real hr]
  apply criticalNormalizedChebyshevErrorLaplace_eq_logDeriv
  norm_num
  exact hr

end GaloisForLFunctions.RHTower
