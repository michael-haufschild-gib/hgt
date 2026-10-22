import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceTransformPairing

/-! Identification of the genuine original source-vector Bochner transform, including its physical onset factor. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

/-- The actual admitted independent-frequency radial source, retaining the fixed physical onset transform. -/
def radialSourceLaplaceVector (q : XiZeroCopy) (branch : Bool) (a w : ℂ) (hw : -2 < w.re) :
    Lp ℂ 2 radialMeasure :=
  (reducedCoefficient_memLp_horizon (physicalRate q branch) w a
    (onsetTransform (2*physicalRate q branch) w) hw).toLp
      (reducedCoefficient (physicalRate q branch) w a (onsetTransform (2*physicalRate q branch) w))

theorem radialSourceLaplaceVector_ae (q : XiZeroCopy) (branch : Bool) (a w : ℂ) (hw : -2 < w.re) :
    radialSourceLaplaceVector q branch a w hw =ᵐ[radialMeasure]
      reducedCoefficient (physicalRate q branch) w a (onsetTransform (2*physicalRate q branch) w) :=
  (reducedCoefficient_memLp_horizon (physicalRate q branch) w a
    (onsetTransform (2*physicalRate q branch) w) hw).coeFn_toLp

/-- Exact Bochner Laplace identity for the original radial source, proved through all L² probes. -/
theorem timeRadialSourceVector_laplace (q : XiZeroCopy) (branch : Bool) (a w : ℂ) (hw : -2 < w.re) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) •
      timeRadialSourceVector (physicalRate q branch) a τ) = radialSourceLaplaceVector q branch a w hw := by
  apply ext_inner_left ℂ
  intro u
  rw [← integral_inner (timeRadialSourceVector_laplace_integrable q branch a w hw) u]
  calc
    _ = ∫ τ in Ioi (0:ℝ), ∫ t, star (u t)*
        (Complex.exp (-w*(τ:ℂ))*timeReducedCoefficient (physicalRate q branch) a τ t) ∂radialMeasure := by
      apply integral_congr_ae
      filter_upwards [] with τ
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul (Complex.exp (-w*(τ:ℂ)))
        (timeRadialSourceVector (physicalRate q branch) a τ),
        timeRadialSourceVector_ae (physicalRate q branch) a τ] with t hs ht
      rw [hs]
      simp [Pi.smul_apply,smul_eq_mul,ht,RCLike.inner_apply,mul_comm]
    _ = ∫ t, star (u t)*reducedCoefficient (physicalRate q branch) w a
        (onsetTransform (2*physicalRate q branch) w) t ∂radialMeasure :=
      timeRadialSourceVector_laplace_pairing q branch a w hw u
    _ = inner ℂ u (radialSourceLaplaceVector q branch a w hw) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [radialSourceLaplaceVector_ae q branch a w hw] with t ht
      rw [ht]
      simp [RCLike.inner_apply,mul_comm]

/-- The exact square-remainder channel of the original frequency source in the full spatial Hilbert space. -/
def cuspMainLaplaceVector (q : XiZeroCopy) (branch : Bool) (a w : ℂ) (hw : -2 < w.re) : SpatialSpace :=
  l2SeparatedProduct (radialSourceLaplaceVector q branch a w hw) (squareResidualVector q)

theorem cuspMainLaplaceVector_ae (q : XiZeroCopy) (branch : Bool) (a w : ℂ) (hw : -2 < w.re) :
    cuspMainLaplaceVector q branch a w hw =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      (fun p : ℝ × UpperHalfPlane => reducedCoefficient (physicalRate q branch) w a
        (onsetTransform (2*physicalRate q branch) w) p.1*squareResidual q (coordinates p.2)) := by
  filter_upwards [l2SeparatedProduct_ae (radialSourceLaplaceVector q branch a w hw) (squareResidualVector q),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (radialSourceLaplaceVector_ae q branch a w hw),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (squareResidual_memLp q).coeFn_toLp] with p hp hr ha
  change l2SeparatedProduct _ _ p = _
  rw [hp]
  exact congrArg₂ (fun x y : ℂ => x*y) hr ha

/-- The actual original spatial source family has exactly its derived independent-frequency source
as Bochner Laplace transform throughout Re(w)>-2. The cutoff-principal channels are separate. -/
theorem timeCuspMainVector_laplace (q : XiZeroCopy) (branch : Bool) (a w : ℂ) (hw : -2 < w.re) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ)) • timeCuspMainVector q branch a τ) =
      cuspMainLaplaceVector q branch a w hw := by
  let L : Lp ℂ 2 radialMeasure →L[ℂ] SpatialSpace :=
    l2SeparatedProductContinuousBilinear.flip (squareResidualVector q)
  have he (τ : ℝ) : Complex.exp (-w*(τ:ℂ)) • timeCuspMainVector q branch a τ =
      L (Complex.exp (-w*(τ:ℂ)) • timeRadialSourceVector (physicalRate q branch) a τ) := by
    rw [map_smul]
    simp only [L,ContinuousLinearMap.flip_apply,l2SeparatedProductContinuousBilinear_apply,
      timeCuspMainVector_separated]
  simp only [he]
  rw [L.integral_comp_comm (timeRadialSourceVector_laplace_integrable q branch a w hw),
    timeRadialSourceVector_laplace]
  rfl

end
end RHTower.D4BMJointSource
