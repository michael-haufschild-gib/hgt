import GaloisForLFunctions.HTGeometry.HarmonicLogFourierMode

/-!
# Harmonic logarithmic equidistribution
-/

open Complex Filter Topology Finset MeasureTheory Set Submodule

namespace GaloisForLFunctions

noncomputable section

abbrev unitCircleHaar : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle

lemma harmonicLogCircleAverage_zero (β θ : ℝ) (N : ℕ) :
    harmonicLogCircleAverage β θ 0 N = 0 := by
  simp [harmonicLogCircleAverage]

lemma harmonicLogCircleAverage_add (β θ : ℝ) (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    harmonicLogCircleAverage β θ (f + g) N =
      harmonicLogCircleAverage β θ f N + harmonicLogCircleAverage β θ g N := by
  rw [harmonicLogCircleAverage, harmonicLogCircleAverage, harmonicLogCircleAverage]
  simp_rw [ContinuousMap.add_apply, mul_add]
  rw [Finset.sum_add_distrib, add_div]

lemma harmonicLogCircleAverage_smul (β θ : ℝ) (c : ℂ)
    (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    harmonicLogCircleAverage β θ (c • f) N = c * harmonicLogCircleAverage β θ f N := by
  rw [harmonicLogCircleAverage, harmonicLogCircleAverage]
  simp_rw [ContinuousMap.smul_apply, smul_eq_mul]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  ring

lemma harmonicLogCircleAverage_sub (β θ : ℝ) (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    harmonicLogCircleAverage β θ (f - g) N =
      harmonicLogCircleAverage β θ f N - harmonicLogCircleAverage β θ g N := by
  rw [harmonicLogCircleAverage, harmonicLogCircleAverage, harmonicLogCircleAverage]
  simp_rw [ContinuousMap.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib, sub_div]

lemma integral_fourier_unitCircleHaar (j : ℤ) :
    ∫ x : AddCircle (1 : ℝ), fourier j x ∂unitCircleHaar = if j = 0 then 1 else 0 := by
  have h := congr_fun (fourierCoeff_fourier (T := (1 : ℝ)) j) 0
  rw [fourierCoeff] at h
  simpa [unitCircleHaar, fourier_zero, Pi.single_apply, eq_comm] using h

theorem harmonicLogCircleAverage_span_fourier (β θ : ℝ) (hβ : β ≠ 0)
    {f : C(AddCircle (1 : ℝ), ℂ)} (hf : f ∈ span ℂ (Set.range (@fourier (1 : ℝ)))) :
    Tendsto (fun N : ℕ => harmonicLogCircleAverage β θ f N) atTop
      (nhds (∫ x, f x ∂unitCircleHaar)) := by
  refine Submodule.span_induction
    (p := fun f _ => Tendsto (fun N : ℕ => harmonicLogCircleAverage β θ f N) atTop
      (nhds (∫ x, f x ∂unitCircleHaar))) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨j, rfl⟩
    rw [integral_fourier_unitCircleHaar]
    exact harmonicLogCircleAverage_fourier β θ hβ j
  · simp [harmonicLogCircleAverage_zero]
  · intro f g hfs hgs hf hg
    have hadd := hf.add hg
    have hfi : Integrable f unitCircleHaar := by
      rw [← integrableOn_univ]
      exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
    have hgi : Integrable g unitCircleHaar := by
      rw [← integrableOn_univ]
      exact g.continuous.continuousOn.integrableOn_compact isCompact_univ
    simpa only [harmonicLogCircleAverage_add, ContinuousMap.add_apply,
      integral_add hfi hgi] using hadd
  · intro c f hfs hf
    have hsmul := hf.const_mul c
    have hint : (∫ x : AddCircle (1 : ℝ), (c • f) x ∂unitCircleHaar) =
        c * ∫ x : AddCircle (1 : ℝ), f x ∂unitCircleHaar := by
      simpa only [ContinuousMap.smul_apply, smul_eq_mul] using
        (integral_smul (μ := unitCircleHaar) c (fun x : AddCircle (1 : ℝ) => f x))
    simpa only [harmonicLogCircleAverage_smul, hint] using hsmul

/-- Uniform harmonic-mass bound for the sampling functional. -/
theorem norm_harmonicLogCircleAverage_le (β θ : ℝ) (f : C(AddCircle (1 : ℝ), ℂ))
    {N : ℕ} (hN : 2 ≤ N) :
    ‖harmonicLogCircleAverage β θ f N‖ ≤
      ((harmonic N : ℝ) / Real.log N) * ‖f‖ := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  rw [harmonicLogCircleAverage, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hlog]
  refine (div_le_div_of_nonneg_right (norm_sum_le _ _) hlog.le).trans ?_
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hlog.le
  calc
    ∑ n ∈ Finset.range N,
        ‖((n : ℂ) + 1)⁻¹ *
          f ((β * Real.log ((n : ℝ) + 1) + θ : ℝ) : AddCircle (1 : ℝ))‖
        ≤ ∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ * ‖f‖) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [norm_mul, norm_inv]
          have heval := ContinuousMap.norm_coe_le_norm f
            ((β * Real.log ((n : ℝ) + 1) + θ : ℝ) : AddCircle (1 : ℝ))
          have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
            rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
            positivity
          rw [hnorm]
          exact mul_le_mul_of_nonneg_left heval (by positivity)
    _ = (harmonic N : ℝ) * ‖f‖ := by
      rw [harmonic]
      push_cast
      rw [Finset.sum_mul]

lemma norm_integral_sub_unitCircleHaar_le_norm
    (f g : C(AddCircle (1 : ℝ), ℂ)) :
    ‖(∫ x, f x ∂unitCircleHaar) - ∫ x, g x ∂unitCircleHaar‖ ≤ ‖f - g‖ := by
  have hfi : Integrable f unitCircleHaar := by
    rw [← integrableOn_univ]
    exact f.continuous.continuousOn.integrableOn_compact isCompact_univ
  have hgi : Integrable g unitCircleHaar := by
    rw [← integrableOn_univ]
    exact g.continuous.continuousOn.integrableOn_compact isCompact_univ
  rw [← integral_sub hfi hgi]
  have hbound := norm_integral_le_of_norm_le_const
    (μ := unitCircleHaar)
    (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm (f - g) x)
  simpa only [ContinuousMap.sub_apply, integral_const, unitCircleHaar, probReal_univ,
    mul_one] using hbound

/-- Harmonic logarithmic rotation is Haar equidistributed on the unit additive circle. -/
theorem harmonicLogCircleAverage_tendsto_haar (β θ : ℝ) (hβ : β ≠ 0)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun N : ℕ => harmonicLogCircleAverage β θ f N) atTop
      (nhds (∫ x, f x ∂unitCircleHaar)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hfclosure : f ∈ (span ℂ (Set.range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨q, hqspan, hfq⟩ := Metric.mem_closure_iff.mp hfclosure (ε / 8) (by positivity)
  have hqconv := harmonicLogCircleAverage_span_fourier β θ hβ hqspan
  obtain ⟨Nq, hNq⟩ := (Metric.tendsto_atTop.mp hqconv) (ε / 4) (by positivity)
  have hmassEventually : ∀ᶠ N : ℕ in atTop, (harmonic N : ℝ) / Real.log N < 2 :=
    tendsto_harmonic_div_log.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨Nm, hNm⟩ := eventually_atTop.mp hmassEventually
  refine ⟨max 2 (max Nq Nm), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hNNq : Nq ≤ N := le_trans (le_max_left Nq Nm) (le_trans (le_max_right 2 _) hN)
  have hNNm : Nm ≤ N := le_trans (le_max_right Nq Nm) (le_trans (le_max_right 2 _) hN)
  have havg :
      ‖harmonicLogCircleAverage β θ f N - harmonicLogCircleAverage β θ q N‖ < ε / 4 := by
    rw [← harmonicLogCircleAverage_sub]
    refine (norm_harmonicLogCircleAverage_le β θ (f - q) hN2).trans_lt ?_
    have hmass := hNm N hNNm
    have hnorm : ‖f - q‖ < ε / 8 := by simpa [dist_eq_norm] using hfq
    nlinarith [norm_nonneg (f - q)]
  have hint :
      ‖(∫ x, q x ∂unitCircleHaar) - ∫ x, f x ∂unitCircleHaar‖ < ε / 8 := by
    refine (norm_integral_sub_unitCircleHaar_le_norm q f).trans_lt ?_
    simpa [dist_eq_norm, norm_sub_rev] using hfq
  rw [dist_eq_norm]
  calc
    ‖harmonicLogCircleAverage β θ f N - ∫ x, f x ∂unitCircleHaar‖
        ≤ ‖harmonicLogCircleAverage β θ f N - harmonicLogCircleAverage β θ q N‖ +
            ‖harmonicLogCircleAverage β θ q N - ∫ x, q x ∂unitCircleHaar‖ +
            ‖(∫ x, q x ∂unitCircleHaar) - ∫ x, f x ∂unitCircleHaar‖ := by
          calc
            _ = ‖(harmonicLogCircleAverage β θ f N - harmonicLogCircleAverage β θ q N) +
                  ((harmonicLogCircleAverage β θ q N - ∫ x, q x ∂unitCircleHaar) +
                    ((∫ x, q x ∂unitCircleHaar) - ∫ x, f x ∂unitCircleHaar))‖ := by ring_nf
            _ ≤ _ := by
              calc
                _ ≤ ‖harmonicLogCircleAverage β θ f N - harmonicLogCircleAverage β θ q N‖ +
                    ‖(harmonicLogCircleAverage β θ q N - ∫ x, q x ∂unitCircleHaar) +
                      ((∫ x, q x ∂unitCircleHaar) - ∫ x, f x ∂unitCircleHaar)‖ :=
                  norm_add_le _ _
                _ ≤ _ := by
                  have htail := norm_add_le
                    (harmonicLogCircleAverage β θ q N - ∫ x, q x ∂unitCircleHaar)
                    ((∫ x, q x ∂unitCircleHaar) - ∫ x, f x ∂unitCircleHaar)
                  linarith
    _ < ε / 4 + ε / 4 + ε / 8 := by
      gcongr
      simpa [dist_eq_norm] using hNq N hNNq
    _ < ε := by linarith

end

end GaloisForLFunctions
