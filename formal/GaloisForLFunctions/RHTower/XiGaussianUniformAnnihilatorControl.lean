import GaloisForLFunctions.RHTower.XiGaussianSampledPerturbation

/-!
# Uniform annihilator control at fixed positive heat time

One finite-divisor cutoff controls all test polynomials in the actual sampled
energy unit ball. Degree is unrestricted. This includes the complete mixed
term between the test and the annihilator, rather than only the latter's
diagonal energy.
-/

open Complex Filter Topology
noncomputable section

namespace RHTower

/-- The native energy of the entire annihilator family vanishes at fixed time. -/
theorem tendsto_xiGaussianNativeEnergy_annihilator_zero (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy => xiGaussianNativeEnergy (xiGaussianAnnihilator F) t)
      atTop (𝓝 0) := tendsto_xiGaussianAnnihilator_energy_zero t

/-- One cutoff controls both signed trace and positive energy, uniformly over
every polynomial in the actual unit ball, with no bound on degree. -/
theorem eventually_forall_xiGaussianAnnihilator_perturbation_small
    (t : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop,
      ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t ≤ 1},
        |xiPolynomialGaussianHeatTraceReal (P.1 + xiGaussianAnnihilator F) t -
          xiPolynomialGaussianHeatTraceReal P.1 t| < (ε : ℝ) ∧
        |xiGaussianNativeEnergy (P.1 + xiGaussianAnnihilator F) t -
          xiGaussianNativeEnergy P.1 t| < (ε : ℝ) := by
  let η : {η : ℝ // 0 < η} := ⟨(ε : ℝ) / 2, div_pos ε.property (by positivity)⟩
  have hlim : Tendsto (fun F : Finset XiZeroCopy =>
      (η : ℝ) + (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy (xiGaussianAnnihilator F) t)
      atTop (𝓝 (η : ℝ)) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add
      ((tendsto_xiGaussianNativeEnergy_annihilator_zero t).const_mul (1 + 1 / (η : ℝ)))
  have hsmall : (η : ℝ) < (ε : ℝ) := by dsimp only [η]; linarith [ε.property]
  filter_upwards [hlim.eventually (Iio_mem_nhds hsmall)] with F hF P
  have hunit : (η : ℝ) * xiGaussianNativeEnergy P.1 t ≤ (η : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left P.property η.property.le
  constructor
  · exact ((abs_xiGaussianHeatTraceReal_add_sub_le P.1 (xiGaussianAnnihilator F) t η).trans
      (add_le_add hunit le_rfl)).trans_lt hF
  · exact ((abs_xiGaussianNativeEnergy_add_sub_le P.1 (xiGaussianAnnihilator F) t η).trans
      (add_le_add hunit le_rfl)).trans_lt hF

/-- The whole complex heat trace of each annihilator tends to zero. -/
theorem tendsto_xiGaussianHeatTrace_annihilator_zero (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy =>
      xiPolynomialGaussianHeatTrace (xiGaussianAnnihilator F) t) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun F => norm_tsum_le_tsum_norm
      (summable_xiPolynomialGaussianHeatTerm t.property (xiGaussianAnnihilator F)).norm)
    (tendsto_xiGaussianNativeEnergy_annihilator_zero t)

/-- The complete signed Hankel trace vanishes along the same family. -/
theorem tendsto_xiGaussianHeatTraceReal_annihilator_zero (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy =>
      xiPolynomialGaussianHeatTraceReal (xiGaussianAnnihilator F) t) atTop (𝓝 0) := by
  simpa only [Complex.zero_re, Function.comp_def, xiPolynomialGaussianHeatTraceReal] using
    Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_xiGaussianHeatTrace_annihilator_zero t)

/-- Every mixed trace with an energy-unit test vanishes uniformly over all
orders. The full two-sided polynomial cross term is retained. -/
theorem eventually_forall_xiGaussianAnnihilator_mixed_trace_small
    (t : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop,
      ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t ≤ 1},
        |xiPolynomialGaussianHeatTraceReal (P.1 + xiGaussianAnnihilator F) t -
          xiPolynomialGaussianHeatTraceReal P.1 t -
          xiPolynomialGaussianHeatTraceReal (xiGaussianAnnihilator F) t| < (ε : ℝ) := by
  let e : {e : ℝ // 0 < e} := ⟨(ε : ℝ) / 2, div_pos ε.property (by positivity)⟩
  have he := (tendsto_xiGaussianNativeEnergy_annihilator_zero t).eventually
    (Iio_mem_nhds e.property)
  filter_upwards [eventually_forall_xiGaussianAnnihilator_perturbation_small t e, he]
    with F hF hE P
  have htrace := (abs_xiGaussianHeatTraceReal_le_nativeEnergy (xiGaussianAnnihilator F) t).trans_lt hE
  have h := abs_sub_le
    (xiPolynomialGaussianHeatTraceReal (P.1 + xiGaussianAnnihilator F) t -
      xiPolynomialGaussianHeatTraceReal P.1 t) 0
    (xiPolynomialGaussianHeatTraceReal (xiGaussianAnnihilator F) t)
  simp only [sub_zero, zero_sub, abs_neg] at h
  have hbound := (h.trans_lt (add_lt_add (hF P).1 htrace))
  dsimp only [e] at hbound
  linarith only [hbound]

end RHTower
