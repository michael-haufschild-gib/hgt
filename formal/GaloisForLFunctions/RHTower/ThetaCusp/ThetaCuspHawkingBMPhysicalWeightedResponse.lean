import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspWeightLimit
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalJointProjection

/-! Height admission and literal physical testing of the original complete cusp response. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The height admission needed by the response estimate holds for the full original forcing class. -/
theorem continuedCuspResidualL2_height_memLp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*continuedCuspResidualL2 q branch a w p)
      2 (radialMeasure.prod D4BMModularCore.measure) := by
  have he : continuedCuspResidualL2 q branch a w =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      continuedCuspResidualForcing q branch w a := by
    unfold continuedCuspResidualL2
    rw [l2Family_eq_toLp _ (fun u => continuedCuspResidualForcing q branch u a) w
      (continuedCuspResidualForcing_band_memLp q branch w a hw hwr)]
    exact (continuedCuspResidualForcing_band_memLp q branch w a hw hwr).coeFn_toLp
  apply (weightedCuspResidualForcing_memLp q branch w a hw hwr).ae_eq
  filter_upwards [he] with p hp
  rw [hp]

/-- The actual causal response to all four native source channels is height-admitted.
The chamber assumptions are frequency restrictions, with no assumed weighted solution or new inverse. -/
theorem completeCuspResponse_height_memLp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*
      jointEmbedding (jointWaveResponse w hw (continuedCuspResidualL2 q branch a w)) p)
      2 (radialMeasure.prod D4BMModularCore.measure) :=
  jointWaveResponse_height_memLp w hw hd _ (continuedCuspResidualL2_height_memLp q branch w a hwi hwr)

private theorem physical_pairing_ae (r : XiZeroCopy) (h : RadialSpace) (u : SpatialSpace)
    (hu : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*u p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    (fun p => inner ℂ (l2SeparatedProduct h (physicalDualVector r) p) (hu.toLp _ p)) =ᵐ[
      radialMeasure.prod D4BMModularCore.measure]
      fun p => conj (h p.1)*scalar (physicalAngularParameter r) (coordinates p.2)*u p := by
  have hd : (fun p : ℝ × UpperHalfPlane => physicalDualVector r p.2) =ᵐ[
      radialMeasure.prod D4BMModularCore.measure] fun p => conj (physicalDualDensity r p.2) :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (physicalDualVector_coe r)
  filter_upwards [l2SeparatedProduct_ae h (physicalDualVector r),hu.coeFn_toLp,hd] with p hp hq hr
  simp only [l2SeparatedFun] at hp
  rw [hp,hq,hr]
  simp only [RCLike.inner_apply,map_mul,starRingEnd_self_apply,physicalDualDensity]
  field_simp [Complex.ofReal_ne_zero.mpr p.2.im_pos.ne']

/-- The full physical field times the response is integrable against every radial Hilbert test. -/
theorem physical_height_pairing_integrable (r : XiZeroCopy) (h : RadialSpace) (u : SpatialSpace)
    (hu : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*u p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    Integrable (fun p : ℝ × UpperHalfPlane =>
      conj (h p.1)*scalar (physicalAngularParameter r) (coordinates p.2)*u p)
      (radialMeasure.prod D4BMModularCore.measure) :=
  (L2.integrable_inner (𝕜 := ℂ) (l2SeparatedProduct h (physicalDualVector r)) (hu.toLp _)).congr
    (physical_pairing_ae r h u hu)

/-- The bounded physical map equals the original bilinear response integral, with both reciprocal weights cancelled. -/
theorem physicalJointProjection_height_integral (r : XiZeroCopy) (h : RadialSpace) (u : SpatialSpace)
    (hu : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*u p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    inner ℂ h (physicalJointProjection r (hu.toLp _)) =
      ∫ p : ℝ × UpperHalfPlane,
        conj (h p.1)*scalar (physicalAngularParameter r) (coordinates p.2)*u p
        ∂radialMeasure.prod D4BMModularCore.measure := by
  unfold physicalJointProjection
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (l2SeparatedProduct h (physicalDualVector r)) (hu.toLp _) = _
  rw [L2.inner_def]
  exact integral_congr_ae (physical_pairing_ae r h u hu)

/-- The physical response is constructed from the existing causal solution of the complete source. -/
def physicalCuspResponse (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) : RadialSpace :=
  physicalJointProjection r ((completeCuspResponse_height_memLp q branch w a hw hd hwi hwr).toLp _)

/-- Every radial test of the constructed physical response is the literal original response integral. -/
theorem physicalCuspResponse_integral (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) (h : RadialSpace) :
    inner ℂ h (physicalCuspResponse q r branch w a hw hd hwi hwr) =
      ∫ p : ℝ × UpperHalfPlane,
        conj (h p.1)*scalar (physicalAngularParameter r) (coordinates p.2)*
          jointEmbedding (jointWaveResponse w hw (continuedCuspResidualL2 q branch a w)) p
        ∂radialMeasure.prod D4BMModularCore.measure :=
  physicalJointProjection_height_integral r h _ (completeCuspResponse_height_memLp q branch w a hw hd hwi hwr)

end
end RHTower.D4BMJointSource
