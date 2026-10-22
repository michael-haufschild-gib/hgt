import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalLiftedEquation

/-!
Every compact planar localization of the actual modular scalar lift belongs to L¹ and L² by exact native density transport.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate ENNReal
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- Every compact chart localization of the actual global lift is full hyperbolic L². -/
theorem compact_chart_mul_lift_memLp (g : CompactChartTest) (u : Space) :
    MemLp (fun z => g.field z*globalLift u z) 2 (volume : Measure UpperHalfPlane) := by
  let K := tsupport g.field
  have hU := globalLift_memLp_compact u K g.compact
  obtain ⟨C,hC⟩ := g.compact.exists_bound_of_continuous (ChartSmooth.continuous g.smooth)
  have hp : MemLp (fun z => g.field z*globalLift u z) 2
      ((volume : Measure UpperHalfPlane).restrict K) := by
    apply hU.of_le_mul
      ((ChartSmooth.continuous g.smooth).aestronglyMeasurable.mul hU.aestronglyMeasurable)
    filter_upwards [] with z
    change ‖g.field z*globalLift u z‖ ≤ C*‖globalLift u z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)
  have he : K.indicator (fun z => g.field z*globalLift u z) =
      (fun z => g.field z*globalLift u z) := by
    funext z
    by_cases hz : z ∈ K
    · simp [hz]
    · simp [hz,image_eq_zero_of_notMem_tsupport hz]
  rw [← he]
  exact (memLp_indicator_iff_restrict g.compact.isClosed.measurableSet).mpr hp

/-- The actual compact chart pairing is integrable in full hyperbolic volume. -/
theorem compact_chart_mul_lift_integrable (g : CompactChartTest) (u : Space) :
    Integrable (fun z => g.field z*globalLift u z) (volume : Measure UpperHalfPlane) := by
  simpa only [smul_eq_mul] using
    (globalLift_locallyIntegrable u).integrable_smul_left_of_hasCompactSupport
      (𝕜 := ℂ) (g := g.field) (ChartSmooth.continuous g.smooth) g.compact

/-- A compact planar localization of the actual globally modular scalar lift. -/
def PlanarChartTest.localValue (g : PlanarChartTest) (u : Space) (z : ℂ) : ℂ :=
  g.field z*globalLift u (ofComplex z)

private theorem PlanarChartTest.localValue_support (g : PlanarChartTest) (u : Space) :
    Function.support (g.localValue u) ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  apply g.support
  apply subset_tsupport
  intro he
  exact hz (by simp [PlanarChartTest.localValue,he])

private theorem weighted_lift_local_memLp (g : PlanarChartTest) (u : Space) (n : ℕ) :
    MemLp (fun z : ℂ => (z.im : ℂ)^n*g.localValue u z) 2
      (Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane)) := by
  let a := g.mulSmooth (fun z => (z.im : ℂ)^n)
    ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).pow n)
  have hp := compact_chart_mul_lift_memLp a.toChartTest u
  apply UpperHalfPlane.measurableEmbedding_coe.memLp_map_measure_iff.mpr
  simpa only [Function.comp_def,a,PlanarChartTest.toChartTest,CompactChartTest.ofPlanar,
    PlanarChartTest.mulSmooth,PlanarChartTest.localValue,ofComplex_apply,coe_im,mul_assoc] using hp

private theorem weighted_lift_local_integrable (g : PlanarChartTest) (u : Space) (n : ℕ) :
    Integrable (fun z : ℂ => (z.im : ℂ)^n*g.localValue u z)
      (Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane)) := by
  let a := g.mulSmooth (fun z => (z.im : ℂ)^n)
    ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).pow n)
  have hp := compact_chart_mul_lift_integrable a.toChartTest u
  apply UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mpr
  simpa only [Function.comp_def,a,PlanarChartTest.toChartTest,CompactChartTest.ofPlanar,
    PlanarChartTest.mulSmooth,PlanarChartTest.localValue,ofComplex_apply,coe_im,mul_assoc] using hp

private theorem lift_density_measurable : Measurable chartDensity := by
  unfold chartDensity
  fun_prop

/-- Every compact localization of the global scalar lift is integrable in ordinary planar measure. -/
theorem PlanarChartTest.localValue_integrable (g : PlanarChartTest) (u : Space) :
    Integrable (g.localValue u) (volume : Measure ℂ) := by
  have h := weighted_lift_local_integrable g u 2
  rw [map_volume_chart_eq] at h
  have hh := (integrable_withDensity_iff_integrable_smul lift_density_measurable).mp h
  apply (integrableOn_iff_integrable_of_support_subset (g.localValue_support u)).mp
  apply hh.congr
  filter_upwards [ae_restrict_mem isOpen_upperHalfPlaneSet.measurableSet] with z hz
  change 0 < z.im at hz
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
    coe_nnnorm,Real.norm_eq_abs,abs_of_pos hz,Complex.real_smul,
    Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one]
  field_simp

/-- Every compact chart localization of the globally modular lift is planar L²,
including localizations crossing seams. The native density is canceled exactly. -/
theorem PlanarChartTest.localValue_memLp (g : PlanarChartTest) (u : Space) :
    MemLp (g.localValue u) 2 (volume : Measure ℂ) := by
  have hi := g.localValue_integrable u
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  have h := (weighted_lift_local_memLp g u 1).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  rw [map_volume_chart_eq] at h
  have hh := (integrable_withDensity_iff_integrable_smul lift_density_measurable).mp h
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
  · apply hh.congr
    filter_upwards [ae_restrict_mem isOpen_upperHalfPlaneSet.measurableSet] with z hz
    change 0 < z.im at hz
    have hy := ne_of_gt hz
    simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
      coe_nnnorm,Real.norm_eq_abs,smul_eq_mul,pow_one,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz,mul_pow]
    field_simp
  · intro z hz
    apply g.localValue_support u
    intro he
    exact hz (by simp [he])

/-- The actual global response and full forcing have every compact planar L² localization. -/
theorem full_response_global_local_L2 (q : XiZeroCopy) (minusBranch : Bool) (g : PlanarChartTest) :
    MemLp (g.localValue (embedding (weakResponse q minusBranch))) 2 (volume : Measure ℂ) ∧
      MemLp (g.localValue (forcingVector q minusBranch)) 2 (volume : Measure ℂ) :=
  ⟨g.localValue_memLp _,g.localValue_memLp _⟩

end
end RHTower.D4BMModularCore
