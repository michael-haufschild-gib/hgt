import GaloisForLFunctions.HTGeometry.HilbertHalfPlaneFullCausal
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeGreenBand
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceForcedCausal
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalResolventIdentification

/-! The original full joint causal response reaches the native physical Green band. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMNativeLaplace
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMNativeCircle D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem native_source_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ) (c : ℝ)
    (hc : principalKernelGrowth q < c) :
    IntegrableOn (fun t => expRay (c:ℂ) t • causalCuspSourceVector q branch a t) (Ioi (0:ℝ)) := by
  simpa only [expRay,neg_mul] using causalCuspSourceVector_laplace_integrable q branch a (c:ℂ) hc

private def nativeSourceBound (q : XiZeroCopy) (branch : Bool) (a : ℂ) (c : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), ‖expRay (c:ℂ) t • causalCuspSourceVector q branch a t‖

private theorem native_frequency_holo (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q < c) (w : ℂ) (hw : c < w.re) :
    DifferentiableAt ℂ (causalJointFrequencyResponse q branch a) w := by
  have hw0 : 0 < w.re := by linarith [(actualPrincipalKernel_common_growth q).1]
  have hS : DifferentiableAt ℂ (causalCuspLaplace q branch a) w :=
    bochnerLaplaceRay_differentiableAt (causalCuspSourceVector_continuous q branch a).aestronglyMeasurable
      (native_source_integrable q branch a c hc) w hw
  exact jointEmbedding.differentiableAt.comp w
    ((waveEnergyInverse_differentiableAt jointEmbedding jointEmbedding_norm_le w hw0).clm_apply
      (jointEmbedding.adjoint.differentiableAt.comp w hS))

private def nativeForcedBoundary (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q < c) : CauchyBoundedHilbertMap SpatialSpace where
  value := fun w => causalJointFrequencyResponse q branch a (w+c)
  shift := c
  shift_pos := by linarith [(actualPrincipalKernel_common_growth q).1]
  bound := nativeSourceBound q branch a c/c
  holo := by
    intro w hw
    exact (native_frequency_holo q branch a c hc (w+c)
      (by simp only [Complex.add_re,Complex.ofReal_re]; linarith)).comp w
        (differentiableAt_id.add_const _)
  norm_le := by
    intro w hw
    have hc0 : 0 < c := by linarith [(actualPrincipalKernel_common_growth q).1]
    have hb := shiftedWaveVector_bound jointEmbedding jointEmbedding_norm_le
      (causalCuspLaplace q branch a (w+c)) c hc0 w hw
    have hs : ‖causalCuspLaplace q branch a (w+c)‖ ≤ nativeSourceBound q branch a c :=
      bochnerLaplaceRay_norm_le (native_source_integrable q branch a c hc) (w+c)
        (by simp only [Complex.add_re,Complex.ofReal_re]; linarith)
    exact hb.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs hc0.le) (norm_nonneg _))

private def nativeForcedResponse (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q < c) (t : ℝ) : SpatialSpace :=
  (Real.exp (c*t):ℂ) • (nativeForcedBoundary q branch a c hc).causalDatum t

private theorem native_forced_integrand (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q < c) (w : ℂ) (t : ℝ) :
    expRay w t • nativeForcedResponse q branch a c hc t =
      expRay (w-c) t • (nativeForcedBoundary q branch a c hc).causalDatum t := by
  simp only [nativeForcedResponse,smul_smul,expRay,Complex.ofReal_exp,Complex.ofReal_mul,← Complex.exp_add]
  congr 2
  ring

private theorem native_forced_weighted_memLp (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q < c) (k : ℝ) (hk : c < k) :
    MemLp (fun t => expRay (k:ℂ) t • nativeForcedResponse q branch a c hc t) 2
      (volume.restrict (Ioi (0:ℝ))) := by
  have h := (nativeForcedBoundary q branch a c hc).causalDatum_memLp_pos (k-c) (sub_pos.mpr hk)
  simpa only [Complex.ofReal_sub,native_forced_integrand] using h

private theorem native_forced_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q < c) (w : ℂ) (hw : c < w.re) :
    IntegrableOn (fun t => expRay w t • nativeForcedResponse q branch a c hc t) (Ioi (0:ℝ)) := by
  have h := (nativeForcedBoundary q branch a c hc).causalDatum_integrable_rightHalfPlane (w-c)
    (by simp only [Complex.sub_re,Complex.ofReal_re]; linarith)
  simpa only [native_forced_integrand] using h

private theorem native_forced_laplace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q < c) (w : ℂ) (hw : c < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • nativeForcedResponse q branch a c hc t) =
      causalJointFrequencyResponse q branch a w := by
  simp only [native_forced_integrand]
  rw [(nativeForcedBoundary q branch a c hc).causalDatum_laplace_rightHalfPlane (w-c)
    (by simp only [Complex.sub_re,Complex.ofReal_re]; linarith)]
  change causalJointFrequencyResponse q branch a (w-c+c) = _
  rw [sub_add_cancel]

private theorem weighted_probe_transform {U : ℝ → SpatialSpace} (L : SpatialSpace →L[ℂ] ℂ)
    (k : ℝ) (w : ℂ) (hi : IntegrableOn (fun t => expRay (w+k) t • U t) (Ioi (0:ℝ))) :
    laplaceRay (fun t => L (expRay (k:ℂ) t • U t)) w =
      L (∫ t in Ioi (0:ℝ), expRay (w+k) t • U t) := by
  calc
    _ = ∫ t in Ioi (0:ℝ), L (expRay (w+k) t • U t) := by
      unfold laplaceRay
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [map_smul,smul_eq_mul]
      have he : expRay (k:ℂ) t*expRay w t = expRay (w+k) t := by
        simp only [expRay,← Complex.exp_add]
        congr 1
        ring
      calc
        _ = (expRay (k:ℂ) t*expRay w t)*L (U t) := by ring
        _ = _ := by rw [he]
    _ = _ := L.integral_comp_comm hi

/-- The construction at any admissible native shift is the already constructed physical joint response. -/
private theorem native_forced_eq_original (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q < c) :
    nativeForcedResponse q branch a c hc =ᵐ[volume.restrict (Ioi (0:ℝ))]
      causalJointForcedResponse q branch a := by
  let k := causalResponseShift q+c+2
  have hc0 : 0 < c := by linarith [(actualPrincipalKernel_common_growth q).1]
  have hk : c < k := by dsimp only [k]; linarith [causalResponseShift_pos q]
  have hkold : causalResponseShift q+1 < k := by dsimp only [k]; linarith
  let A := fun t => expRay (k:ℂ) t • nativeForcedResponse q branch a c hc t
  let B := fun t => expRay (k:ℂ) t • causalJointForcedResponse q branch a t
  have hA : MemLp A 2 (volume.restrict (Ioi (0:ℝ))) := native_forced_weighted_memLp q branch a c hc k hk
  have hB : MemLp B 2 (volume.restrict (Ioi (0:ℝ))) := by
    have h := (causalJointForcedBoundary q branch a).causalDatum_memLp_pos (k-causalResponseShift q) (by linarith)
    simpa only [Complex.ofReal_sub,causalJointForcedResponse_integrand,B] using h
  have hp : ∀ v : SpatialSpace, ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), inner ℂ v (A t-B t) = 0 := by
    intro v
    let L : SpatialSpace →L[ℂ] ℂ := innerSL ℂ v
    have hLA := L.comp_memLp' hA
    have hLB := L.comp_memLp' hB
    have hz := ae_eq_zero_of_laplaceRay_eq_zero (hLA.sub hLB) (fun w hw => by
      change (∫ t in Ioi (0:ℝ), (L (A t)-L (B t))*expRay w t) = 0
      simp_rw [sub_mul]
      have hsub := integral_sub (integrableOn_laplaceRay hLA hw) (integrableOn_laplaceRay hLB hw)
      simp only [Function.comp_def] at hsub
      rw [hsub]
      change laplaceRay (fun t => L (expRay (k:ℂ) t • nativeForcedResponse q branch a c hc t)) w-
        laplaceRay (fun t => L (expRay (k:ℂ) t • causalJointForcedResponse q branch a t)) w = 0
      have hwc : c < (w+k).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
      have hwo : causalResponseShift q+1 < (w+k).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
      rw [weighted_probe_transform L k w (native_forced_integrable q branch a c hc (w+k) hwc),
        weighted_probe_transform L k w (causalJointForcedResponse_integrable q branch a (w+k) hwo),
        native_forced_laplace q branch a c hc (w+k) hwc,
        causalJointForcedResponse_laplace q branch a (w+k) hwo,sub_self])
    filter_upwards [hz] with t ht
    rw [inner_sub_right]
    exact ht
  have hz := bochnerL2_ae_zero_on_of_inner_probes (fun t => A t-B t) (hA.sub hB)
    Set.univ MeasurableSet.univ (fun v => (hp v).mono (fun t ht _ => ht))
  filter_upwards [hz] with t ht
  have he := sub_eq_zero.mp (ht (Set.mem_univ t))
  exact smul_right_injective SpatialSpace (show expRay (k:ℂ) t ≠ 0 from Complex.exp_ne_zero _) he

/-- The original causal orbit has square-integrable damping at every native frequency. -/
theorem causalJointForcedResponse_memLp_of_native (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (k : ℝ) (hk : principalKernelGrowth q < k) :
    MemLp (fun t => expRay (k:ℂ) t • causalJointForcedResponse q branch a t) 2
      (volume.restrict (Ioi (0:ℝ))) := by
  obtain ⟨c,hc,hck⟩ := exists_between hk
  apply (native_forced_weighted_memLp q branch a c hc k hck).ae_eq
  filter_upwards [native_forced_eq_original q branch a c hc] with t ht
  rw [ht]

/-- Absolute Bochner convergence of the original full joint response in the native half-plane. -/
theorem causalJointForcedResponse_integrable_of_native (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) :
    IntegrableOn (fun t => expRay w t • causalJointForcedResponse q branch a t) (Ioi (0:ℝ)) := by
  let c := (principalKernelGrowth q+w.re)/2
  have hc : principalKernelGrowth q < c := by dsimp only [c]; linarith
  have hcw : c < w.re := by dsimp only [c]; linarith
  apply (native_forced_integrable q branch a c hc w hcw).congr
  filter_upwards [native_forced_eq_original q branch a c hc] with t ht
  rw [ht]

/-- The original physical response transforms to its original inverse without the previous unit shift. -/
theorem causalJointForcedResponse_laplace_of_native (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • causalJointForcedResponse q branch a t) =
      causalJointFrequencyResponse q branch a w := by
  let c := (principalKernelGrowth q+w.re)/2
  have hc : principalKernelGrowth q < c := by dsimp only [c]; linarith
  have hcw : c < w.re := by dsimp only [c]; linarith
  calc
    _ = ∫ t in Ioi (0:ℝ), expRay w t • nativeForcedResponse q branch a c hc t := by
      apply integral_congr_ae
      filter_upwards [native_forced_eq_original q branch a c hc] with t ht
      rw [ht]
    _ = _ := native_forced_laplace q branch a c hc w hcw

/-- The complete original joint response is the causal transform of the physical source in the Green overlap. -/
theorem causalJointForcedResponse_original_green (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • causalJointForcedResponse q branch a t) =
      jointEmbedding (jointWaveResponse w
        (by linarith [(actualPrincipalKernel_common_growth q).1])
        (cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w)
          (principalChamber_of_native_growth q w hw))) := by
  have hw0 : 0 < w.re := by linarith [(actualPrincipalKernel_common_growth q).1]
  rw [causalJointForcedResponse_laplace_of_native q branch a w hw]
  unfold causalJointFrequencyResponse
  have hs : causalCuspLaplace q branch a w =
      cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w)
        (principalChamber_of_native_growth q w hw) := by
    simpa only [causalCuspLaplace,bochnerLaplaceRay,expRay,neg_mul] using
      causalCuspSourceVector_laplace_original q branch a w hw
  rw [hs]
  exact congrArg jointEmbedding (waveEnergyInverse_jointResponse w hw0 _)

/-- Original operator-domain admission and the complete physical forcing hold in the new chamber. -/
theorem causalJointForcedResponse_operator_of_native (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) :
    let U := ∫ t in Ioi (0:ℝ), expRay w t • causalJointForcedResponse q branch a t
    ∃ hmem : U ∈ jointEnergyOperator.domain,
      jointEnergyOperator ⟨U,hmem⟩+(w^(2 : ℕ)-1) • U =
        ∫ t in Ioi (0:ℝ), expRay w t • causalCuspSourceVector q branch a t := by
  have hw0 : 0 < w.re := by linarith [(actualPrincipalKernel_common_growth q).1]
  dsimp only
  rw [causalJointForcedResponse_laplace_of_native q branch a w hw]
  have he : causalJointFrequencyResponse q branch a w =
      jointEmbedding (jointWaveResponse w hw0 (causalCuspLaplace q branch a w)) :=
    congrArg jointEmbedding (waveEnergyInverse_jointResponse w hw0 _)
  rw [he]
  exact jointWaveResponse_operator w hw0 (causalCuspLaplace q branch a w)

/-- A common nonreal point of the original physical Green band carries the actual full causal response and operator equation. -/
theorem actualJointCausal_original_green_band (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    ∃ w : ℂ, ∃ hw : principalKernelGrowth q < w.re, 3/2 < w.re ∧ w.re < 2 ∧ w.im = 1 ∧
      IntegrableOn (fun t => expRay w t • causalJointForcedResponse q branch a t) (Ioi (0:ℝ)) ∧
      ∃ hmem : (∫ t in Ioi (0:ℝ), expRay w t • causalJointForcedResponse q branch a t) ∈ jointEnergyOperator.domain,
        jointEnergyOperator ⟨∫ t in Ioi (0:ℝ), expRay w t • causalJointForcedResponse q branch a t,hmem⟩+
          (w^(2 : ℕ)-1) • (∫ t in Ioi (0:ℝ), expRay w t • causalJointForcedResponse q branch a t) =
            cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w)
              (principalChamber_of_native_growth q w hw) := by
  let c := (principalKernelGrowth q+2)/2
  let w : ℂ := (c:ℂ)+Complex.I
  have hwre : w.re = c := by simp [w]
  obtain ⟨hB,hB2,_⟩ := actualPrincipalKernel_common_growth q
  have hw : principalKernelGrowth q < w.re := by rw [hwre]; dsimp only [c]; linarith
  refine ⟨w,hw,by linarith,by rw [hwre]; dsimp only [c]; linarith,by simp [w],
    causalJointForcedResponse_integrable_of_native q branch a w hw,?_⟩
  have h := causalJointForcedResponse_operator_of_native q branch a w hw
  have hs : (∫ t in Ioi (0:ℝ), expRay w t • causalCuspSourceVector q branch a t) =
      cuspResidualVector q branch w a (onsetTransform (2*physicalRate q branch) w)
        (principalChamber_of_native_growth q w hw) := by
    simpa only [expRay,neg_mul] using causalCuspSourceVector_laplace_original q branch a w hw
  rw [hs] at h
  exact h

end
end RHTower.D4BMNativeLaplace

/-! Physical angular projection and radial traces of the actual causal joint transform. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMNativeLaplace
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMNativeCircle D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem native_band_positive (q : XiZeroCopy) (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    0 < w.re := by linarith [(actualPrincipalKernel_common_growth q).1]

private theorem native_band_three_halves (q : XiZeroCopy) (w : ℂ) (hw : principalKernelGrowth q < w.re) :
    3/2 < w.re := (actualPrincipalKernel_common_growth q).1.trans_lt hw

/-- The actual causal transform is the existing complete spatial response in the physical band. -/
theorem causalJointLaplace_eq_completeResponse (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) (hwi : w.im ≠ 0) :
    (∫ t in Ioi (0:ℝ), expRay w t • causalJointForcedResponse q branch a t) =
      jointEmbedding (jointWaveResponse w (native_band_positive q w hw) (continuedCuspResidualL2 q branch a w)) := by
  rw [causalJointForcedResponse_original_green q branch a w hw,
    continuedCuspResidualL2_eq_original q branch w a hwi (principalChamber_of_native_growth q w hw)]

/-- Height admission is proved for the original Bochner transform itself. -/
theorem causalJointLaplace_height_memLp (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*
      (∫ t in Ioi (0:ℝ), expRay w t • causalJointForcedResponse q branch a t) p)
      2 (radialMeasure.prod D4BMModularCore.measure) := by
  rw [causalJointLaplace_eq_completeResponse q branch a w hw hwi]
  exact completeCuspResponse_height_memLp q branch w a (native_band_positive q w hw)
    (native_band_three_halves q w hw) hwi hwr

/-- Literal physical angular projection of the height-admitted original causal transform. -/
def causalPhysicalProjection (q r : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) : RadialSpace :=
  physicalJointProjection r ((causalJointLaplace_height_memLp q branch a w hw hwi hwr).toLp _)

/-- The existing physical radial response is exactly the projection of the actual time-family transform. -/
theorem causalPhysicalProjection_eq_response (q r : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    causalPhysicalProjection q r branch a w hw hwi hwr =
      physicalCuspResponse q r branch w a (native_band_positive q w hw)
        (native_band_three_halves q w hw) hwi hwr := by
  unfold causalPhysicalProjection physicalCuspResponse
  congr 1
  apply Lp.ext
  filter_upwards [(causalJointLaplace_height_memLp q branch a w hw hwi hwr).coeFn_toLp,
    (completeCuspResponse_height_memLp q branch w a (native_band_positive q w hw)
      (native_band_three_halves q w hw) hwi hwr).coeFn_toLp] with p hp hq
  rw [hp,hq,causalJointLaplace_eq_completeResponse q branch a w hw hwi]

/-- The actual causal projection has the literal complete-source Green representative. -/
theorem causalPhysicalProjection_ae_green (q r : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    causalPhysicalProjection q r branch a w hw hwi hwr =ᵐ[radialMeasure]
      completePhysicalGreenProfile q r branch w a := by
  rw [causalPhysicalProjection_eq_response]
  exact physicalCuspResponse_ae_completePhysicalGreenProfile q r branch w a
    (native_band_positive q w hw) (native_band_three_halves q w hw) hwi hwr

/-- The original causal projection inherits its actual radial derivatives, Dirichlet trace,
complete source equation and collision-retaining cleared Green identity. -/
theorem causalPhysicalProjection_original_profile (q r : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : principalKernelGrowth q < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    ∃ f : ℝ → ℂ, Continuous f ∧ f =ᵐ[radialMeasure] causalPhysicalProjection q r branch a w hw hwi hwr ∧
      f 0 = 0 ∧ ∀ x : ℝ, x < 0 →
        HasDerivAt f (deriv f x) x ∧ HasDerivAt (deriv f) (deriv (deriv f) x) x ∧
        f x = completePhysicalGreenProfile q r branch w a x ∧
        w^(2 : ℕ)*f x-deriv (deriv f) x-(physicalAngularParameter r^(2 : ℕ)-1/4)*angularWeight x^(2 : ℕ)*f x =
          continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x ∧
        physicalAngularGapProduct q r*f x = clearedPhysicalGreen q r branch w a x := by
  let h0 := native_band_positive q w hw
  let hd := native_band_three_halves q w hw
  let f := physicalCuspProfile q r branch w a h0 hd hwi hwr
  refine ⟨f,physicalCuspProfile_continuous q r branch w a h0 hd hwi hwr,?_,
    physicalCuspProfile_zero q r branch w a h0 hd hwi hwr,fun x hx => ?_⟩
  · rw [causalPhysicalProjection_eq_response]
    exact physicalCuspProfile_ae q r branch w a h0 hd hwi hwr
  · have h := physicalCuspProfile_hasDerivAt q r branch w a h0 hd hwi hwr x hx
    exact ⟨h.1,h.2.differentiableAt.hasDerivAt,
      physicalCuspProfile_eq_completePhysicalGreenProfile q r branch w a h0 hd hwi hwr x hx,
      physicalCuspProfile_equation q r branch w a h0 hd hwi hwr x hx,
      physicalCuspProfile_mul_gapProduct q r branch w a h0 hd hwi hwr x hx⟩

end
end RHTower.D4BMNativeLaplace
