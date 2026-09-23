import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalLaplacianPairingLimit

/-! The actual physical projection of the original complete causal response satisfies its original radial equation. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Height multiplication of the actual source representative gives the original complete weighted source class. -/
theorem continuedCuspResidualL2_height_eq (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    (continuedCuspResidualL2_height_memLp q branch w a hw hwr).toLp
      (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*continuedCuspResidualL2 q branch a w p) =
      weightedCuspResidualL2 q branch a w := by
  have he : continuedCuspResidualL2 q branch a w =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      continuedCuspResidualForcing q branch w a := by
    unfold continuedCuspResidualL2
    rw [l2Family_eq_toLp _ (fun u => continuedCuspResidualForcing q branch u a) w
      (continuedCuspResidualForcing_band_memLp q branch w a hw hwr)]
    exact (continuedCuspResidualForcing_band_memLp q branch w a hw hwr).coeFn_toLp
  unfold weightedCuspResidualL2
  rw [l2Family_eq_toLp _ _ w (weightedCuspResidualForcing_memLp q branch w a hw hwr)]
  apply Lp.ext
  filter_upwards [(continuedCuspResidualL2_height_memLp q branch w a hw hwr).coeFn_toLp,
    (weightedCuspResidualForcing_memLp q branch w a hw hwr).coeFn_toLp,he] with p hp hq hr
  rw [hp,hq,hr]

/-- The limiting source pairing is the actual complete four-channel angular source, with its original physical parameter. -/
theorem physicalCuspSource_height_projection (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalJointProjection r ((continuedCuspResidualL2_height_memLp q branch w a hw hwr).toLp _ ) =
      continuedAngularSourceL2 q branch (physicalAngularParameter r) a w := by
  rw [continuedCuspResidualL2_height_eq q branch w a hw hwr,
    physicalJointProjection_complete_source q r branch w a hw hwr]

/-- The original causal response's actual physical projection obeys the complete radial distribution equation.
Weighted admission, the noncompact angular test limit, and all source channels are discharged internally. -/
theorem physicalCuspResponse_radial_equation (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) (f : RadialCore) :
    inner ℂ (radialDerivative f.differentiate) (physicalCuspResponse q r branch w a hw hd hwi hwr)+
      (physicalAngularParameter r^(2 : ℕ)-1/4)*inner ℂ (radialWeightedValue f.angularWeighted)
        (physicalCuspResponse q r branch w a hw hd hwi hwr)-
      w^(2 : ℕ)*inner ℂ (radialValue f) (physicalCuspResponse q r branch w a hw hd hwi hwr) =
      -inner ℂ (radialValue f) (continuedAngularSourceL2 q branch (physicalAngularParameter r) a w) := by
  have h0 := physicalCuspResponse_compact_test_limit q r branch w a hw hd hwi hwr (radialDerivative f.differentiate)
  have h1 := physicalCoreCutoff_laplacian_inner_tendsto r (radialWeightedValue f.angularWeighted)
    (jointEmbedding (jointWaveResponse w hw (continuedCuspResidualL2 q branch a w)))
    (completeCuspResponse_height_memLp q branch w a hw hd hwi hwr)
  have h2 := physicalCuspResponse_compact_test_limit q r branch w a hw hd hwi hwr (radialValue f)
  have hF := physicalCoreCutoff_inner_tendsto r (radialValue f) (continuedCuspResidualL2 q branch a w)
    (continuedCuspResidualL2_height_memLp q branch w a hwi hwr)
  rw [physicalCuspSource_height_projection q r branch w a hwi hwr] at hF
  have hleft := (h0.add h1).sub (h2.const_mul (w^(2 : ℕ)))
  have hright := hF.neg
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Filter.Eventually.of_forall (fun n => (completeCuspResponse_compact_equation q r branch w a hw f n).symm)

end
end RHTower.D4BMJointSource
