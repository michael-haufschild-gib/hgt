import GaloisForLFunctions.RHTower.SelbergMaassCurrentMeasures

/-!
# The actual residual curvature is concentrated on source zeros

Every compact test away from original common zeros has a source-derived positive
amplitude floor. The actual regulator-gradient integral then tends to zero with
an integrable source bound. Compact cutoffs and regularity identify the residual
measure as concentrated on the literal common-zero set. No nodal mass is
silently discarded, and no spectral quarter comparison is asserted.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassResidualSupport
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassSourceCurrents
  SelbergMaassTraceRegularized SelbergMaassWeakCurvature SelbergMaassRegulatorMass
  SelbergMaassCurrentCurvature SelbergMaassCurrentMeasures SelbergUpperHalfPlaneCompactTests
  SelbergLocalTestGreen
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The actual source gradient density is continuous at every positive height. -/
theorem gradientDensity_continuousOn :
    ContinuousOn (gradientDensity N f) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hF (q : Deck N) : ContDiffAt ℝ 2 (field N f q) z := by
    simpa only [ofComplex_apply_of_im_pos hz] using field_smooth N f q (ofComplex z)
  have hD (q : Deck N) (v : ℂ) : ContinuousAt (dir v (field N f q)) z :=
    (dir_contDiffAt (hF q) v).continuousAt
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun w => ∑ q : Deck N,
    (normSq (dir 1 (field N f q) w) + normSq (dir Complex.I (field N f q) w))) z
  simp only [normSq_eq_norm_sq]
  fun_prop

/-- Compact support away from original common zeros supplies an actual positive amplitude floor. -/
theorem exists_amplitude_floor (g : C_c(ℍ, ℝ))
    (hg : ∀ z ∈ tsupport g, 0 < density N f z) :
    ∃ d : ℝ, 0 < d ∧ ∀ z ∈ tsupport (zeroExtend g),
      d ≤ SelbergMaassWeakCurvature.amplitude N f z := by
  have hk := zeroExtend_compact g
  have hp : ∀ z ∈ tsupport (zeroExtend g), 0 < SelbergMaassWeakCurvature.amplitude N f z := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := zeroExtend_tsupport_subset g hz
    apply Real.sqrt_pos.mpr
    simpa only [ofComplex_apply] using hg w hw
  by_cases hn : (tsupport (zeroExtend g)).Nonempty
  · obtain ⟨z, hz, hmin⟩ := hk.exists_isMinOn hn
      ((amplitude_continuousOn N f).mono (zeroExtend_support g))
    exact ⟨SelbergMaassWeakCurvature.amplitude N f z, hp z hz, fun w hw => hmin hw⟩
  · exact ⟨1, by norm_num, fun z hz => (hn ⟨z, hz⟩).elim⟩

/-- The original regulator-gradient integrals vanish on compact tests supported away from source zeros. -/
theorem regulator_limit_zero (g : C_c(ℍ, ℝ))
    (hg : ∀ z ∈ tsupport g, 0 < density N f z) :
    Tendsto (fun e : Ioi (0 : ℝ) => ∫ z, zeroExtend g z * regulatorGradientWeight N f e z)
      regulatorAtZero (𝓝 0) := by
  obtain ⟨d, hd, hfloor⟩ := exists_amplitude_floor N f g hg
  have hi := integrable_norm_test_mul (zeroExtend_continuous g) (zeroExtend_compact g)
    (gradientDensity_continuousOn N f) (zeroExtend_support g)
  have hb (e : Ioi (0 : ℝ)) :
      ‖∫ z, zeroExtend g z * regulatorGradientWeight N f e z‖ ≤
        ((e : ℝ) ^ 2 / d ^ 3) * ∫ z, ‖zeroExtend g z‖ * gradientDensity N f z := by
    calc
      _ ≤ ∫ z, ((e : ℝ) ^ 2 / d ^ 3) * (‖zeroExtend g z‖ * gradientDensity N f z) := by
        apply norm_integral_le_of_norm_le (hi.const_mul _)
        filter_upwards with z
        by_cases hz : z ∈ tsupport (zeroExtend g)
        · have hr : d ≤ radius N f e z := (hfloor z hz).trans
            (Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (e : ℝ))))
          have he : regulatorGradientWeight N f e z ≤ (e : ℝ) ^ 2 * gradientDensity N f z / d ^ 3 :=
            div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (gradientDensity_nonneg N f z))
              (pow_pos hd 3) (pow_le_pow_left₀ hd.le hr 3)
          rw [norm_mul, Real.norm_of_nonneg (regulatorGradientWeight_nonneg N f e z)]
          calc
            _ ≤ ‖zeroExtend g z‖ * ((e : ℝ) ^ 2 * gradientDensity N f z / d ^ 3) :=
              mul_le_mul_of_nonneg_left he (norm_nonneg _)
            _ = _ := by ring
        · simp only [image_eq_zero_of_notMem_tsupport hz, zero_mul, norm_zero, mul_zero, le_refl]
      _ = _ := integral_const_mul _ _
  have hl : Tendsto (fun e : Ioi (0 : ℝ) => ((e : ℝ) ^ 2 / d ^ 3) *
      ∫ z, ‖zeroExtend g z‖ * gradientDensity N f z) regulatorAtZero (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_mul] using
      ((regulator_coe_limit.pow 2).div_const (d ^ 3)).mul_const
        (∫ z, ‖zeroExtend g z‖ * gradientDensity N f z)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  exact tendsto_const_nhds.squeeze' hl (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall hb)

/-- The actual residual measure annihilates every compact test supported away from common source zeros. -/
theorem residual_integral_zero (g : C_c(ℍ, ℝ))
    (hg : ∀ z ∈ tsupport g, 0 < density N f z) :
    (∫ z, g z ∂residualMeasure N f) = 0 :=
  tendsto_nhds_unique (regulator_limit_integral N f g) (regulator_limit_zero N f g hg)

/-- The actual source density is continuous on the upper half-plane itself. -/
theorem density_continuous : Continuous (density N f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := ((density_contDiffOn N f).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).continuousAt
  simpa only [Function.comp_def, ofComplex_apply] using h.comp continuous_coe.continuousAt

/-- The positive-density locus has zero residual measure; all residual curvature is retained on original common zeros. -/
theorem residualMeasure_positive_density_zero :
    residualMeasure N f {z : ℍ | 0 < density N f z} = 0 := by
  have hV : IsOpen {z : ℍ | 0 < density N f z} := isOpen_lt continuous_const (density_continuous N f)
  rw [hV.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  intro K hKV hK
  obtain ⟨h, hone, hcomp, hs, h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  let g : C_c(ℍ, ℝ) := ⟨h, hcomp⟩
  have hz : (∫ z, g z ∂residualMeasure N f) = 0 := residual_integral_zero N f g (fun z hz => hs hz)
  have hb : residualMeasure N f K ≤ ENNReal.ofReal (∫ z, g z ∂residualMeasure N f) := by
    apply (residual_test_integrable N f g).measure_le_integral
    · exact Eventually.of_forall (fun z => (h01 z).1)
    · intro z hz
      change (1 : ℝ) ≤ h z
      rw [hone hz]
      exact le_rfl
  have hzero : residualMeasure N f K ≤ 0 := by
    simpa only [hz, ENNReal.ofReal_zero] using hb
  exact le_antisymm hzero bot_le

/-- The actual residual measure is concentrated on the literal common-zero set of the original source. -/
theorem residualMeasure_compl_node_zero :
    residualMeasure N f {z : ℍ | density N f z = 0}ᶜ = 0 := by
  have he : {z : ℍ | density N f z = 0}ᶜ = {z : ℍ | 0 < density N f z} := by
    ext z
    simp only [mem_compl_iff, mem_setOf_eq]
    constructor
    · intro hz
      exact lt_of_le_of_ne (density_nonneg N f z) (Ne.symm hz)
    · exact fun hz => hz.ne'
  rw [he]
  exact residualMeasure_positive_density_zero N f

end
end GaloisForLFunctions.RHTower.SelbergMaassResidualSupport
