import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalCoreCutoff
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointCoreTransposition
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalWeightedResponse

/-! Compact physical tests converge against the actual height-admitted causal response. -/
open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMJointWave D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem cutoff_pairing_ae (r : XiZeroCopy) (n : ℕ) (h : RadialSpace) (u : SpatialSpace) :
    (fun p => inner ℂ (l2SeparatedProduct h (fieldVector (physicalCoreCutoff r n)) p) (u p)) =ᵐ[
      radialMeasure.prod D4BMModularCore.measure]
    fun p => modularCuspCutoff ((n:ℝ)+1) p.2*
      (conj (h p.1)*scalar (physicalAngularParameter r) (coordinates p.2)*u p) := by
  let g := physicalCoreCutoff r n
  have hg : (fun p : ℝ × UpperHalfPlane => fieldVector g p.2) =ᵐ[
      radialMeasure.prod D4BMModularCore.measure] fun p => g.field p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (core_field_memLp g.field g.smooth g.compact).coeFn_toLp
  filter_upwards [l2SeparatedProduct_ae h (fieldVector g),hg] with p hp hq
  simp only [l2SeparatedFun] at hp
  rw [hp,hq]
  simp only [g,physicalCoreCutoff,physicalTestField,RCLike.inner_apply,map_mul,
    modularCuspCutoff_real,starRingEnd_self_apply]
  ring

/-- Every compact physical test is the literal cutoff of the same original angular response pairing. -/
theorem physicalCoreCutoff_inner (r : XiZeroCopy) (n : ℕ) (h : RadialSpace) (u : SpatialSpace) :
    inner ℂ (l2SeparatedProduct h (fieldVector (physicalCoreCutoff r n))) u =
      ∫ p : ℝ × UpperHalfPlane, modularCuspCutoff ((n:ℝ)+1) p.2*
        (conj (h p.1)*scalar (physicalAngularParameter r) (coordinates p.2)*u p)
        ∂radialMeasure.prod D4BMModularCore.measure := by
  rw [L2.inner_def]
  exact integral_congr_ae (cutoff_pairing_ae r n h u)

/-- Height admission suffices to pass every mass pairing from original compact tests to the physical projection. -/
theorem physicalCoreCutoff_inner_tendsto (r : XiZeroCopy) (h : RadialSpace) (u : SpatialSpace)
    (hu : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*u p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    Tendsto (fun n : ℕ => inner ℂ (l2SeparatedProduct h (fieldVector (physicalCoreCutoff r n))) u)
      atTop (𝓝 (inner ℂ h (physicalJointProjection r (hu.toLp _)))) := by
  rw [physicalJointProjection_height_integral r h u hu]
  simp_rw [physicalCoreCutoff_inner]
  let P : ℝ × UpperHalfPlane → ℂ := fun p =>
    conj (h p.1)*scalar (physicalAngularParameter r) (coordinates p.2)*u p
  have hi : Integrable P (radialMeasure.prod D4BMModularCore.measure) :=
    physical_height_pairing_integrable r h u hu
  apply tendsto_integral_of_dominated_convergence (fun p => ‖P p‖)
  · intro n
    exact (L2.integrable_inner (𝕜 := ℂ)
      (l2SeparatedProduct h (fieldVector (physicalCoreCutoff r n))) u).aestronglyMeasurable.congr
        (cutoff_pairing_ae r n h u)
  · exact hi.norm
  · intro n
    filter_upwards [] with p
    change ‖modularCuspCutoff ((n:ℝ)+1) p.2*P p‖ ≤ ‖P p‖
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (modularCuspCutoff_norm_le_one _ _) (norm_nonneg _)).trans_eq
      (one_mul _)
  · have hfd : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
        p.2 ∈ ModularGroup.fd :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
    filter_upwards [hfd] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [modularCuspCutoff_eventually_one p.2 hp] with n hn
    rw [hn.eq_of_nhds,one_mul]

/-- The actual complete cusp response is recovered by compact physical tests, with weighted admission proved internally. -/
theorem physicalCuspResponse_compact_test_limit (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) (h : RadialSpace) :
    Tendsto (fun n : ℕ => inner ℂ (l2SeparatedProduct h (fieldVector (physicalCoreCutoff r n)))
      (jointEmbedding (jointWaveResponse w hw (continuedCuspResidualL2 q branch a w))))
      atTop (𝓝 (inner ℂ h (physicalCuspResponse q r branch w a hw hd hwi hwr))) :=
  physicalCoreCutoff_inner_tendsto r h _ (completeCuspResponse_height_memLp q branch w a hw hd hwi hwr)

/-- Every constructed compact physical test obeys the original forced response equation before taking the cusp limit. -/
theorem completeCuspResponse_compact_equation (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (f : RadialCore) (n : ℕ) :
    inner ℂ (l2SeparatedProduct (radialDerivative f.differentiate) (fieldVector (physicalCoreCutoff r n)))
      (jointEmbedding (jointWaveResponse w hw (continuedCuspResidualL2 q branch a w)))+
    inner ℂ (l2SeparatedProduct (radialWeightedValue f.angularWeighted)
      (fieldVector (physicalCoreCutoff r n).laplacian))
      (jointEmbedding (jointWaveResponse w hw (continuedCuspResidualL2 q branch a w)))-
    w^(2 : ℕ)*inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector (physicalCoreCutoff r n)))
      (jointEmbedding (jointWaveResponse w hw (continuedCuspResidualL2 q branch a w))) =
    -inner ℂ (l2SeparatedProduct (radialValue f) (fieldVector (physicalCoreCutoff r n)))
      (continuedCuspResidualL2 q branch a w) :=
  jointWaveResponse_transposed w hw _ f (physicalCoreCutoff r n)

end
end RHTower.D4BMJointSource
