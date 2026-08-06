import GaloisForLFunctions.HTGeometry.GaussianRadialAngularMixture
import GaloisForLFunctions.HTGeometry.BohrMeanMonotone
import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity

/-!
# The radial completion law for almost periodic observers

Every continuous Bohr almost periodic reporter, observed through a Gaussian
radial clock, converges as the observation time grows to its Bohr mean value —
the Haar average over the completed one-parameter time group.  The proof is the
Bochner--Fejér three-epsilon argument: trigonometric polynomials are handled
exactly by the radial action kernel, the radial average is a contraction, and the
Bohr mean is a contraction.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A trigonometric polynomial sampled at the Gaussian radius is a radial
spectral packet. -/
theorem trigPolyChar_eq_radialSpectralPacket (S : Finset ℝ) (a : ℝ → ℂ)
    (time r : ℝ) :
    (∑ lam ∈ S, a lam * expChar lam (time * r))
      = radialSpectralPacket S a (fun lam => -lam) time r := by
  rw [radialSpectralPacket]
  refine Finset.sum_congr rfl fun lam _ => ?_
  congr 1
  rw [expChar]
  congr 1
  push_cast
  ring

/-- **Radial completion of a trigonometric polynomial.**  The Gaussian radial
average of a trigonometric polynomial converges to its Bohr mean. -/
theorem tendsto_integral_trigPolyChar_radial {m : ℕ} (hm : 0 < m)
    (S : Finset ℝ) (a : ℝ → ℂ) :
    Tendsto
      (fun time : ℝ =>
        ∫ x, (∑ lam ∈ S, a lam * expChar lam (time * ‖x‖))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      atTop (𝓝 (bohrMean fun t : ℝ => ∑ lam ∈ S, a lam * expChar lam t)) := by
  classical
  have hmean : (bohrMean fun t : ℝ => ∑ lam ∈ S, a lam * expChar lam t)
      = ∑ lam ∈ S.filter fun lam => -lam = 0, a lam := by
    rw [bohrMean_sum_expChar S a (fun lam => lam), Finset.sum_filter]
    refine Finset.sum_congr rfl fun lam _ => ?_
    by_cases hlam : lam = 0
    · rw [if_pos hlam, if_pos (show -lam = 0 by simp [hlam])]
    · rw [if_neg hlam, if_neg (fun h => hlam (neg_eq_zero.mp h))]
  rw [hmean]
  have hpacket : ∀ time : ℝ,
      (∫ x, (∑ lam ∈ S, a lam * expChar lam (time * ‖x‖))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
        = ∫ x, radialSpectralPacket S a (fun lam => -lam) time ‖x‖
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    intro time
    exact congrArg _ (funext fun x =>
      trigPolyChar_eq_radialSpectralPacket S a time ‖x‖)
  refine Tendsto.congr (fun time => (hpacket time).symm) ?_
  exact tendsto_integral_radialSpectralPacket_atTop hm S a (fun lam => -lam)

/-- A bounded measurable reporter sampled at the Gaussian radius is
integrable. -/
theorem integrable_comp_norm_of_bounded {m : ℕ} {g : ℝ → ℂ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ t, ‖g t‖ ≤ C) (time : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) => g (time * ‖x‖))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  refine Integrable.mono' (integrable_const C) ?_ ?_
  · exact ((hg.comp (continuous_const.mul continuous_norm))).aestronglyMeasurable
  · filter_upwards with x
    exact hC _

/-- **General radial completion law.**  A continuous almost periodic reporter,
uniformly approximable by trigonometric polynomials, has Gaussian radial averages
converging to its Bohr mean. -/
theorem tendsto_integral_radial_bohrMean {m : ℕ} (hm : 0 < m) {f : ℝ → ℂ}
    (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ (S : Finset ℝ) (a : ℝ → ℂ),
      ∀ t, ‖f t - ∑ lam ∈ S, a lam * expChar lam t‖ ≤ δ) :
    Tendsto
      (fun time : ℝ => ∫ x, f (time * ‖x‖)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      atTop (𝓝 (bohrMean f)) := by
  classical
  obtain ⟨Cf, hCf⟩ := exists_bound_of_isBohrAlmostPeriodic hfc hfa
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨S, a, happ⟩ := happrox (ε / 3) (by linarith)
  set P : ℝ → ℂ := fun t => ∑ lam ∈ S, a lam * expChar lam t with hP
  have hPc : Continuous P := by
    refine continuous_finsetSum _ fun lam _ => ?_
    exact continuous_const.mul (continuous_expChar lam)
  have hPa : HTGeometry.IsBohrAlmostPeriodic P := by
    refine isBohrAlmostPeriodic_sum S (fun lam _ => continuous_const.mul
      (continuous_expChar lam)) fun lam _ => ?_
    exact isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar lam)
  have hPbound : ∀ t, ‖P t‖ ≤ Cf + ε / 3 := by
    intro t
    calc ‖P t‖ = ‖f t - (f t - P t)‖ := by ring_nf
      _ ≤ ‖f t‖ + ‖f t - P t‖ := norm_sub_le _ _
      _ ≤ Cf + ε / 3 := add_le_add (hCf t) (happ t)
  -- the mean of the approximant is within `ε/3` of the mean of `f`
  have hmeanClose : ‖bohrMean P - bohrMean f‖ ≤ ε / 3 := by
    rw [← bohrMean_sub hPc hPa hfc hfa]
    refine le_trans (norm_bohrMean_le_bohrMean_norm
      (hPc.sub hfc) (isBohrAlmostPeriodic_sub hPc hPa hfc hfa)) ?_
    rw [← bohrMean_const_real (ε / 3)]
    refine bohrMean_le_bohrMean ((hPc.sub hfc).norm)
      (isBohrAlmostPeriodic_norm_real (isBohrAlmostPeriodic_sub hPc hPa hfc hfa))
      continuous_const (isBohrAlmostPeriodic_const _) fun t => ?_
    rw [show P t - f t = -(f t - P t) by ring, norm_neg]
    exact happ t
  -- the radial average of the approximant converges to its mean
  have hlim := tendsto_integral_trigPolyChar_radial (m := m) hm S a
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨T, hT⟩ := hlim (ε / 3) (by linarith)
  refine ⟨T, fun time htime => ?_⟩
  have hfi := integrable_comp_norm_of_bounded (m := m) hfc hCf time
  have hPi := integrable_comp_norm_of_bounded (m := m) hPc hPbound time
  have hdiff : ‖(∫ x, f (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      - ∫ x, P (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))‖ ≤ ε / 3 := by
    rw [← integral_sub hfi hPi]
    have hbound : ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (Fin m))),
        ‖f (time * ‖x‖) - P (time * ‖x‖)‖ ≤ ε / 3 := by
      filter_upwards with x
      exact happ _
    simpa [measure_univ] using
      norm_integral_le_of_norm_le_const
        (μ := stdGaussian (EuclideanSpace ℝ (Fin m))) hbound
  have hPT := hT time htime
  rw [dist_eq_norm] at hPT ⊢
  calc ‖(∫ x, f (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))) - bohrMean f‖
      ≤ ‖(∫ x, f (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
          - ∫ x, P (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))‖
        + ‖(∫ x, P (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
          - bohrMean P‖
        + ‖bohrMean P - bohrMean f‖ := by
        have h1 := norm_add_le
          ((∫ x, f (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
            - ∫ x, P (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
          (((∫ x, P (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
            - bohrMean P) + (bohrMean P - bohrMean f))
        have h2 := norm_add_le
          ((∫ x, P (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
            - bohrMean P) (bohrMean P - bohrMean f)
        have h3 : (∫ x, f (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
            - bohrMean f
            = ((∫ x, f (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
              - ∫ x, P (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
              + (((∫ x, P (time * ‖x‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
                - bohrMean P) + (bohrMean P - bohrMean f)) := by ring
        rw [h3]
        linarith
    _ < ε := by linarith

/-- **Angular mixture of the radial completion law.**  Averaging a
direction-indexed family of almost periodic reporters over the direction law, the
Gaussian radial observation converges to the direction average of the
completed-time Haar means. -/
theorem tendsto_integral_radial_bohrMean_angularMixture
    {Ω : Type*} [MeasurableSpace Ω] (σμ : Measure Ω) [IsFiniteMeasure σμ]
    {m : ℕ} (hm : 0 < m) (f : Ω → ℝ → ℂ)
    (hfc : ∀ ω, Continuous (f ω))
    (hfa : ∀ ω, HTGeometry.IsBohrAlmostPeriodic (f ω))
    (happrox : ∀ ω, ∀ δ : ℝ, 0 < δ → ∃ (S : Finset ℝ) (a : ℝ → ℂ),
      ∀ t, ‖f ω t - ∑ lam ∈ S, a lam * expChar lam t‖ ≤ δ)
    {C : ℝ} (hC : ∀ ω t, ‖f ω t‖ ≤ C)
    (hmeas : ∀ time : ℝ, AEStronglyMeasurable
      (fun ω => ∫ x, f ω (time * ‖x‖)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))) σμ)
    (_hmeanMeas : AEStronglyMeasurable (fun ω => bohrMean (f ω)) σμ) :
    Tendsto
      (fun time : ℝ => ∫ ω, (∫ x, f ω (time * ‖x‖)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))) ∂σμ)
      atTop (𝓝 (∫ ω, bohrMean (f ω) ∂σμ)) := by
  classical
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
    (integrable_const C) ?_
  · filter_upwards with time
    exact hmeas time
  · filter_upwards with time
    filter_upwards with ω
    have hbound : ∀ᵐ x ∂(stdGaussian (EuclideanSpace ℝ (Fin m))),
        ‖f ω (time * ‖x‖)‖ ≤ C := by
      filter_upwards with x
      exact hC ω _
    simpa [measure_univ] using
      norm_integral_le_of_norm_le_const
        (μ := stdGaussian (EuclideanSpace ℝ (Fin m))) hbound
  · filter_upwards with ω
    exact tendsto_integral_radial_bohrMean hm (hfc ω) (hfa ω) (happrox ω)

end

end GaloisForLFunctions.HTGeometry
