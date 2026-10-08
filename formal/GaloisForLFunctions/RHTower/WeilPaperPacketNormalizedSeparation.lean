import GaloisForLFunctions.RHTower.WeilPaperPacketRationalSeparation
import GaloisForLFunctions.RHTower.WeilWorkPBAPSpectralMeasure
import GaloisForLFunctions.RHTower.WeilPaperFiniteObservations

/-!
# Distinct normalized null mixtures from prime-subset masks

The arbitrary rational sample difference furnished by the paper's masks survives
common positive normalization. The witnesses are actual mass-one mixtures in the
native spectral-probability interface, with every integer defect zero.
-/

open Complex MeasureTheory
noncomputable section
namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- The autocorrelation mass of every signed finite mixture is real. -/
theorem mixtureSample_zero_real (c : WeilTestFn →₀ ℝ) :
    mixtureSample c 0 = ((mixtureSample c 0).re : ℂ) := by
  simp only [mixtureSample_zero_eq_integral_density, Complex.ofReal_re]

/-- Every positive mixture correlation is bounded by its mass. -/
theorem mixtureSample_norm_le_mass (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) (y : ℝ) :
    ‖mixtureSample c y‖ ≤ (mixtureSample c 0).re := by
  calc
    _ ≤ ∫ ξ : ℝ, ‖(mixtureSpectralDensity c ξ : ℂ) *
        Complex.exp (2 * Real.pi * I * ξ * y)‖ := by
      rw [mixtureSample_eq_integral_density]
      exact norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, mixtureSpectralDensity c ξ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        simp [Complex.norm_exp, abs_of_nonneg (mixtureSpectralDensity_nonneg c hc ξ)]
    _ = (mixtureSample c 0).re := by
      rw [mixtureSample_zero_eq_integral_density, Complex.ofReal_re]

/-- Normalize a positive finite mixture with known positive mass. -/
def paperNormalizeMass (M : ℝ) (hM : 0 < M)
    (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    (hz : mixtureSample c 0 = (M : ℂ)) : NormalizedMixture :=
  ⟨M⁻¹ • c, (fun f => mul_nonneg (inv_nonneg.mpr hM.le) (hc f)), by
    rw [mixtureSample_smul, hz, Complex.real_smul, Complex.ofReal_inv,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hM.ne')]⟩

/-- Positive common normalization retains the rational separation and exact full-energy gap. -/
theorem exists_normalized_null_pair_rational_separation :
    ∃ (a b : NormalizedMixture) (M : ℝ),
      0 < M ∧ defect a.1 = 0 ∧ defect b.1 = 0 ∧
      mixtureSample a.1 (Real.log 2 - Real.log 3) -
        mixtureSample b.1 (Real.log 2 - Real.log 3) = ((M⁻¹ : ℝ) : ℂ) ∧
      energy a.1 - energy b.1 = M⁻¹ *
        packetArchPairing 4 (paperPacketCoprimeCovariance (paperPacketTwoThreeCoeffs 1)) := by
  obtain ⟨a, b, ha, hb, ha0, hb0, hm, hs, he⟩ :=
    exists_positive_null_equal_mass_pair_rational_difference 1
  let M : ℝ := (mixtureSample a 0).re
  have hbM : (mixtureSample b 0).re = M := by rw [← hm]
  have hM : 0 < M := by
    have hn : ‖(1 : ℂ)‖ ≤ M + M := calc
      _ = ‖mixtureSample a (Real.log 2 - Real.log 3) -
          mixtureSample b (Real.log 2 - Real.log 3)‖ := by rw [hs]
      _ ≤ ‖mixtureSample a (Real.log 2 - Real.log 3)‖ +
          ‖mixtureSample b (Real.log 2 - Real.log 3)‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (mixtureSample_norm_le_mass a ha _) (by
        simpa only [hbM] using mixtureSample_norm_le_mass b hb (Real.log 2 - Real.log 3))
    norm_num at hn
    linarith
  have hza : mixtureSample a 0 = (M : ℂ) := mixtureSample_zero_real a
  have hzb : mixtureSample b 0 = (M : ℂ) := hm.symm.trans hza
  let normalize := paperNormalizeMass M hM
  refine ⟨normalize a ha hza, normalize b hb hzb, M, hM, ?_, ?_, ?_, ?_⟩
  · change defect (M⁻¹ • a) = 0
    rw [map_smul, ha0, smul_zero]
  · change defect (M⁻¹ • b) = 0
    rw [map_smul, hb0, smul_zero]
  · change mixtureSample (M⁻¹ • a) _ - mixtureSample (M⁻¹ • b) _ = _
    rw [mixtureSample_smul, mixtureSample_smul, ← smul_sub, hs,
      Complex.real_smul, mul_one]
  · change energy (M⁻¹ • a) - energy (M⁻¹ • b) = _
    rw [map_smul, map_smul]
    change M⁻¹ * energy a - M⁻¹ * energy b = _
    rw [← mul_sub, he]

/-- Even mass-one positive mixtures with zero integer defect are separated by a rational sample. -/
theorem exists_normalized_null_pair_distinct_rational_sample :
    ∃ a b : NormalizedMixture, defect a.1 = 0 ∧ defect b.1 = 0 ∧
      mixtureSample a.1 (Real.log 2 - Real.log 3) ≠
        mixtureSample b.1 (Real.log 2 - Real.log 3) := by
  obtain ⟨a, b, M, hM, ha, hb, hs, _⟩ := exists_normalized_null_pair_rational_separation
  refine ⟨a, b, ha, hb, ?_⟩
  intro heq
  rw [heq, sub_self] at hs
  exact (Complex.ofReal_ne_zero.mpr (inv_ne_zero hM.ne')) hs.symm

/-- Normalizing to mass one does not make rational correlation a function of integer defects. -/
theorem no_normalized_rational_sample_factor_through_defect :
    ¬ ∃ F : (LogIndex →₀ ℝ) → ℂ, ∀ c : NormalizedMixture,
      mixtureSample c.1 (Real.log 2 - Real.log 3) = F (defect c.1) := by
  rintro ⟨F, hF⟩
  obtain ⟨a, b, ha, hb, hs⟩ := exists_normalized_null_pair_distinct_rational_sample
  apply hs
  rw [hF a, hF b, ha, hb]

/-- The separated normalized null mixtures yield distinct actual spectral probabilities
on the native compact prime torus. -/
theorem exists_distinct_spectralTorusProbabilities_of_integer_null :
    ∃ a b : NormalizedMixture, defect a.1 = 0 ∧ defect b.1 = 0 ∧
      spectralTorusProbability a ≠ spectralTorusProbability b := by
  obtain ⟨a, b, ha, hb, hs⟩ := exists_normalized_null_pair_distinct_rational_sample
  refine ⟨a, b, ha, hb, ?_⟩
  intro heq
  have h := congrArg (fun μ => phaseMoment μ 2 3) heq
  rw [phaseMoment_spectralTorusProbability a (by norm_num) (by norm_num),
    phaseMoment_spectralTorusProbability b (by norm_num) (by norm_num)] at h
  exact hs h

/-- Common normalization preserves any finite observation collision and its rational separation. -/
theorem exists_normalized_null_pair_same_finite_observations (k : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ a b : NormalizedMixture, defect a.1 = 0 ∧ defect b.1 = 0 ∧ T a.1 = T b.1 ∧
      ∃ r : PaperPacketPrimitiveEdge (k + 3),
        mixtureSample a.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) ≠
          mixtureSample b.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) := by
  obtain ⟨a, b, ha, hb, ha0, hb0, hm, hT, r, hr⟩ :=
    exists_positive_null_pair_same_finite_observations k T
  let M : ℝ := (mixtureSample a 0).re
  let y : ℝ := Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)
  have hbM : (mixtureSample b 0).re = M := by rw [← hm]
  have hM : 0 < M := by
    have hpos : 0 < ‖mixtureSample a y - mixtureSample b y‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hr)
    have hn : ‖mixtureSample a y - mixtureSample b y‖ ≤ M + M :=
      (norm_sub_le _ _).trans (add_le_add (mixtureSample_norm_le_mass a ha y) (by
        simpa only [hbM] using mixtureSample_norm_le_mass b hb y))
    linarith
  have hza : mixtureSample a 0 = (M : ℂ) := mixtureSample_zero_real a
  have hzb : mixtureSample b 0 = (M : ℂ) := hm.symm.trans hza
  refine ⟨paperNormalizeMass M hM a ha hza, paperNormalizeMass M hM b hb hzb, ?_, ?_, ?_, r, ?_⟩
  · change defect (M⁻¹ • a) = 0
    rw [map_smul, ha0, smul_zero]
  · change defect (M⁻¹ • b) = 0
    rw [map_smul, hb0, smul_zero]
  · change T (M⁻¹ • a) = T (M⁻¹ • b)
    rw [map_smul, map_smul, hT]
  · intro heq
    apply hr
    change mixtureSample (M⁻¹ • a) y = mixtureSample (M⁻¹ • b) y at heq
    rw [mixtureSample_smul, mixtureSample_smul, Complex.real_smul, Complex.real_smul] at heq
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hM.ne')) heq

/-- Mass-one mixtures can agree in full energy and every integer constraint, yet differ at
a primitive ratio with labels at most four. -/
theorem exists_normalized_null_same_energy_pair_distinct_sample :
    ∃ a b : NormalizedMixture, defect a.1 = 0 ∧ defect b.1 = 0 ∧ energy a.1 = energy b.1 ∧
      ∃ r : PaperPacketPrimitiveEdge 4,
        mixtureSample a.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) ≠
          mixtureSample b.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ)) := by
  obtain ⟨a, b, ha, hb, hT, hr⟩ :=
    exists_normalized_null_pair_same_finite_observations 1 (LinearMap.pi fun _ : Fin 1 => energy)
  exact ⟨a, b, ha, hb, congrFun hT 0, hr⟩

/-- Every finite linear observation family has a collision between distinct actual
spectral probabilities of normalized integer-null mixtures. -/
theorem exists_distinct_spectralTorusProbabilities_same_finite_observations (k : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ a b : NormalizedMixture, defect a.1 = 0 ∧ defect b.1 = 0 ∧ T a.1 = T b.1 ∧
      spectralTorusProbability a ≠ spectralTorusProbability b := by
  obtain ⟨a, b, ha, hb, hT, r, hr⟩ :=
    exists_normalized_null_pair_same_finite_observations k T
  refine ⟨a, b, ha, hb, hT, ?_⟩
  have hleft : (r.1.1 : ℕ) ≠ 0 := by
    have := (Finset.mem_Icc.mp r.1.1.property).1
    omega
  have hright : (r.1.2 : ℕ) ≠ 0 := by
    have := (Finset.mem_Icc.mp r.1.2.property).1
    omega
  intro heq
  have h := congrArg (fun μ => phaseMoment μ (r.1.1 : ℕ) (r.1.2 : ℕ)) heq
  rw [phaseMoment_spectralTorusProbability a hleft hright,
    phaseMoment_spectralTorusProbability b hleft hright] at h
  exact hr h

/-- Equal full energy does not determine the spectral probability, even after mass-one
normalization and exact satisfaction of every integer constraint. -/
theorem exists_distinct_spectralTorusProbabilities_same_energy :
    ∃ a b : NormalizedMixture, defect a.1 = 0 ∧ defect b.1 = 0 ∧ energy a.1 = energy b.1 ∧
      spectralTorusProbability a ≠ spectralTorusProbability b := by
  obtain ⟨a, b, ha, hb, hT, hp⟩ :=
    exists_distinct_spectralTorusProbabilities_same_finite_observations 1
      (LinearMap.pi fun _ : Fin 1 => energy)
  exact ⟨a, b, ha, hb, congrFun hT 0, hp⟩

end RHTower.WeilWorkPBAP
