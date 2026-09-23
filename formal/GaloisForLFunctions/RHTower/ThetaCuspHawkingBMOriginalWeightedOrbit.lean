import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalCausalGreenBand
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMWeightedJointSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWeightLimit
import GaloisForLFunctions.RHTower.VectorFourierPlancherelIntegral

/-!
# Original causal orbit with a uniform cusp time-energy bound

The literal height-weighted source retains the native angular residual and all
three principal cutoff commutators. Its native-half-plane time admission gives
one source envelope that dominates every original bounded cusp multiplier.

The original rotated resolvent transfers this envelope to a Cauchy bound on
each Fourier line. Vector Plancherel then proves a cutoff-independent time
energy bound for the unchanged causal orbit. The Cauchy line integral fixes
the normalization factor one over twice the damping exponent.

This estimate precedes removal of the unbounded cusp weight and transport to
the complete temporal, metric and QNM action.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalWeightedOrbit
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMJointWave D4BMModularCore
open D4BMNativeLaplace D4BMNativeCircle
noncomputable section
set_option autoImplicit false

private abbrev spatialMeasure := radialMeasure.prod D4BMModularCore.measure

/-- The unchanged complete causal source multiplied by the original cusp height. -/
def heightSource (q : XiZeroCopy) (br : Bool) (amp : ℂ) (t : ℝ) : SpatialSpace :=
  l2SeparatedProduct (timeRadialSourceVector (physicalRate q br) amp t) (weightedResidualVector q)+
    ∑ i : Fin 3, l2SeparatedProduct (principalCutoffRadialOp (principalTimeResponse q br amp i t))
      (weightedCutoffVector (principalExponent q i))

private theorem separated_height (f : Lp ℂ 2 radialMeasure) (g G : D4BMModularCore.Space)
    (hG : G =ᵐ[D4BMModularCore.measure] fun z => (z.im:ℂ)*g z) :
    l2SeparatedProduct f G =ᵐ[spatialMeasure]
      fun p : ℝ×UpperHalfPlane => (p.2.im:ℂ)*l2SeparatedProduct f g p := by
  filter_upwards [l2SeparatedProduct_ae f G,l2SeparatedProduct_ae f g,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hG] with p h1 h2 hg
  rw [h1,h2]
  dsimp only [l2SeparatedFun]
  dsimp only [Function.comp_apply] at hg
  rw [hg]
  ring

/-- Height multiplication keeps every original principal commutator and its radial coefficient. -/
theorem heightSource_coe (q : XiZeroCopy) (br : Bool) (amp : ℂ) (t : ℝ) :
    heightSource q br amp t =ᵐ[spatialMeasure]
      fun p : ℝ×UpperHalfPlane => (p.2.im:ℂ)*causalCuspSourceVector q br amp t p := by
  have hm : weightedResidualVector q =ᵐ[D4BMModularCore.measure]
      fun z => (z.im:ℂ)*squareResidualVector q z := by
    filter_upwards [weightedResidualVector_coe q,(squareResidual_memLp q).coeFn_toLp] with z h1 h2
    rw [h1]
    change _=(z.im:ℂ)*(squareResidual_memLp q).toLp _ z
    rw [h2]
  have hc (i : Fin 3) : weightedCutoffVector (principalExponent q i) =ᵐ[D4BMModularCore.measure]
      fun z => (z.im:ℂ)*cutoffCommutatorVector (principalExponent q i) z := by
    filter_upwards [weightedCutoffVector_coe (principalExponent q i),
      (cutoffCommutator_memLp (principalExponent q i)).coeFn_toLp] with z h1 h2
    rw [h1]
    change _=(z.im:ℂ)*(cutoffCommutator_memLp (principalExponent q i)).toLp _ z
    rw [h2]
  have hmain := separated_height (timeRadialSourceVector (physicalRate q br) amp t) _ _ hm
  have hcut (i : Fin 3) := separated_height
    (principalCutoffRadialOp (principalTimeResponse q br amp i t)) _ _ (hc i)
  unfold heightSource causalCuspSourceVector
  rw [timeCuspMainVector_separated]
  filter_upwards [Lp.coeFn_add
      (l2SeparatedProduct (timeRadialSourceVector (physicalRate q br) amp t) (weightedResidualVector q))
      (∑ i : Fin 3, l2SeparatedProduct (principalCutoffRadialOp (principalTimeResponse q br amp i t))
        (weightedCutoffVector (principalExponent q i))),
    Lp.coeFn_add
      (l2SeparatedProduct (timeRadialSourceVector (physicalRate q br) amp t) (squareResidualVector q))
      (∑ i : Fin 3, principalCutoffTimeVector q br amp i t),
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 => l2SeparatedProduct
      (principalCutoffRadialOp (principalTimeResponse q br amp i t)) (weightedCutoffVector (principalExponent q i))),
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 => principalCutoffTimeVector q br amp i t),
    hmain,ae_all_iff.mpr hcut] with p h1 h2 hs1 hs2 hm' hc'
  rw [h1,h2]
  simp only [Pi.add_apply]
  rw [hs1,hs2]
  simp only [Finset.sum_apply]
  rw [hm',mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hc' i

/-- The complete height-weighted source has Bochner time admission on the native half-plane. -/
theorem heightSource_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : principalKernelGrowth q<w.re) :
    IntegrableOn (fun t => expRay w t • heightSource q br amp t) (Ioi (0:ℝ)) := by
  let M : Lp ℂ 2 radialMeasure →L[ℂ] SpatialSpace :=
    l2SeparatedProductContinuousBilinear.flip (weightedResidualVector q)
  let C (i : Fin 3) : FourierRealL2 →L[ℂ] SpatialSpace :=
    (l2SeparatedProductContinuousBilinear.flip (weightedCutoffVector (principalExponent q i))).comp
      principalCutoffRadialOp
  have hw0 : -2<w.re := by linarith [(actualPrincipalKernel_common_growth q).1]
  have hM := M.integrable_comp (timeRadialSourceVector_laplace_integrable q br amp w hw0)
  have hC := integrable_finsetSum Finset.univ (fun i _ =>
    (C i).integrable_comp (principalTimeResponse_laplace_integrable_of_kernel q br amp i w hw))
  apply (hM.add hC).congr
  filter_upwards with t
  simp only [Pi.add_apply,M,C,map_smul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,l2SeparatedProductContinuousBilinear_apply,
    heightSource,smul_add,Finset.smul_sum,expRay,neg_mul]

/-- One literal source vector dominates all bounded cusp multipliers. -/
def sourceEnvelope (q : XiZeroCopy) (br : Bool) (amp : ℂ) (t : ℝ) : SpatialSpace :=
  (cuspWeightBase:ℂ) • causalCuspSourceVector q br amp t+heightSource q br amp t

theorem sourceEnvelope_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : principalKernelGrowth q<w.re) :
    IntegrableOn (fun t => expRay w t • sourceEnvelope q br amp t) (Ioi (0:ℝ)) := by
  have hF : IntegrableOn (fun t => expRay w t • causalCuspSourceVector q br amp t) (Ioi (0:ℝ)) := by
    simpa only [expRay,neg_mul] using D4BMNativeLaplace.causalCuspSourceVector_laplace_integrable q br amp w hw
  apply ((hF.smul (cuspWeightBase:ℂ)).add (heightSource_integrable q br amp w hw)).congr
  filter_upwards with t
  change (cuspWeightBase:ℂ) • (expRay w t • causalCuspSourceVector q br amp t)+
      expRay w t • heightSource q br amp t = expRay w t • sourceEnvelope q br amp t
  rw [sourceEnvelope,smul_add]
  exact congrArg (fun u : SpatialSpace => u+expRay w t • heightSource q br amp t)
    (smul_comm (cuspWeightBase:ℂ) (expRay w t) (causalCuspSourceVector q br amp t))

private theorem profile_ae (N : ℝ) (hN : 0<N) (u : SpatialSpace) :
    cuspSpatialMultiply N hN u =ᵐ[spatialMeasure]
      fun p : ℝ×UpperHalfPlane => (cuspWeightProfile N p.2.im:ℂ)*u p := by
  have hfd : ∀ᵐ p : ℝ×UpperHalfPlane ∂spatialMeasure,p.2∈ModularGroup.fd :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)
  filter_upwards [cuspSpatialMultiply_coe N hN u,hfd] with p hp hf
  rw [hp]
  dsimp only [cuspWeightSymbol]
  rw [(modularCuspWeight_germ N p.2 hf).eq_of_nhds]

/-- Uniformity is derived from the original source, not the growing operator norms. -/
theorem source_multiplier_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (N : ℝ) (hN : 0<N) (t : ℝ) :
    ‖cuspSpatialMultiply N hN (causalCuspSourceVector q br amp t)‖≤‖sourceEnvelope q br amp t‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [profile_ae N hN (causalCuspSourceVector q br amp t),heightSource_coe q br amp t,
    Lp.coeFn_add ((cuspWeightBase:ℂ) • causalCuspSourceVector q br amp t) (heightSource q br amp t),
    Lp.coeFn_smul (cuspWeightBase:ℂ) (causalCuspSourceVector q br amp t)] with p hM hH ha hs
  change ‖cuspSpatialMultiply N hN (causalCuspSourceVector q br amp t) p‖≤
    ‖((cuspWeightBase:ℂ) • causalCuspSourceVector q br amp t+heightSource q br amp t) p‖
  rw [hM,ha]
  simp only [Pi.add_apply]
  rw [hs,hH]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [← add_mul,← Complex.ofReal_add,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (show 0<cuspWeightProfile N p.2.im by linarith [(cuspWeightProfile_bounds N p.2.im hN p.2.im_pos).1,cuspWeightBase_one_le]),
    abs_of_pos (show 0<cuspWeightBase+p.2.im by linarith [cuspWeightBase_one_le,p.2.im_pos])]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (cuspWeightProfile_le_limit N p.2.im hN p.2.im_pos).trans
  unfold cuspWeightLimit
  exact add_le_add le_rfl (mul_le_of_le_one_left p.2.im_pos.le (Real.smoothTransition.le_one _))

/-- The finite source envelope fixes the common spectral budget before any frequency selection. -/
def sourceBound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (c : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ),‖expRay (c:ℂ) t • sourceEnvelope q br amp t‖

theorem sourceBound_nonneg (q : XiZeroCopy) (br : Bool) (amp : ℂ) (c : ℝ) :
    0≤ sourceBound q br amp c := integral_nonneg (fun _ => norm_nonneg _)

/-- Every retained cusp multiplier has the same source-derived Laplace budget. -/
theorem source_transform_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q<c) (w : ℂ) (hw : c≤w.re)
    (N : ℝ) (hN : 0<N) :
    ‖cuspSpatialMultiply N hN (causalCuspLaplace q br amp w)‖≤ sourceBound q br amp c := by
  let M := cuspSpatialMultiply N hN
  have hS (z : ℂ) (hz : principalKernelGrowth q<z.re) :
      IntegrableOn (fun t => expRay z t • causalCuspSourceVector q br amp t) (Ioi (0:ℝ)) := by
    simpa only [expRay,neg_mul] using D4BMNativeLaplace.causalCuspSourceVector_laplace_integrable q br amp z hz
  have hM : IntegrableOn (fun t => expRay (c:ℂ) t • M (causalCuspSourceVector q br amp t)) (Ioi (0:ℝ)) := by
    simpa only [IntegrableOn,map_smul] using M.integrable_comp (hS c hc)
  have he : M (causalCuspLaplace q br amp w)=
      bochnerLaplaceRay (fun t => M (causalCuspSourceVector q br amp t)) w := by
    unfold causalCuspLaplace bochnerLaplaceRay
    calc
      _ = ∫ t in Ioi (0:ℝ),M (expRay w t • causalCuspSourceVector q br amp t) :=
        (M.integral_comp_comm (hS w (hc.trans_le hw))).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with t
        exact M.map_smul (expRay w t) (causalCuspSourceVector q br amp t)
  rw [he]
  apply (bochnerLaplaceRay_norm_le hM w hw).trans
  apply integral_mono_ae hM.norm (sourceEnvelope_integrable q br amp c hc).norm
  filter_upwards with t
  simp only [norm_smul]
  exact mul_le_mul_of_nonneg_left (source_multiplier_bound q br amp N hN t) (norm_nonneg _)

/-- The actual full causal response has a uniform Cauchy line bound after every cusp multiplier. -/
theorem response_transform_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q<c) (hca : 3/2<c)
    (w : ℂ) (hw : w.re=c) (N : ℝ) (hN : 0<N) :
    ‖cuspSpatialMultiply N hN (causalJointFrequencyResponse q br amp w)‖≤
      (c*sourceBound q br amp c/(c^(2 : ℕ)-9/4))*‖w⁻¹‖ := by
  have hw0 : 0<w.re := by linarith
  have he : causalJointFrequencyResponse q br amp w=
      jointEmbedding (jointWaveResponse w hw0 (causalCuspLaplace q br amp w)) := by
    unfold causalJointFrequencyResponse waveSpatialResolvent
    simp only [ContinuousLinearMap.comp_apply,waveEnergyInverse_jointResponse w hw0]
  rw [he]
  have hB := jointWaveResponse_cuspWeight_rotated_bound N hN w hw0 (by linarith) (causalCuspLaplace q br amp w)
  have hS := source_transform_uniform q br amp c hc w hw.ge N hN
  have hn : c^(2 : ℕ)+w.im^(2 : ℕ)=‖w‖^(2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,hw]
    ring
  have hn0 : ‖w‖≠0 := norm_ne_zero_iff.mpr (fun hz => by simp [hz] at hw0)
  have hd : 0<c^(2 : ℕ)-(9/4:ℝ) := by nlinarith
  rw [hw,hn] at hB
  apply (hB.trans (mul_le_mul_of_nonneg_left hS (by positivity))).trans_eq
  rw [norm_inv]
  field_simp [hn0,hd.ne']

/-- The original damped time orbit extended by zero, with its actual bounded cusp multiplier. -/
def dampedOrbit (q : XiZeroCopy) (br : Bool) (amp : ℂ) (c N : ℝ) (hN : 0<N) : ℝ→SpatialSpace :=
  (Ioi (0:ℝ)).indicator (fun t => expRay (c:ℂ) t • cuspSpatialMultiply N hN (causalJointForcedResponse q br amp t))

private theorem dampedOrbit_admitted (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q<c) (N : ℝ) (hN : 0<N) :
    Integrable (dampedOrbit q br amp c N hN) ∧ MemLp (dampedOrbit q br amp c N hN) 2 volume := by
  have h1 := (cuspSpatialMultiply N hN).integrable_comp (causalJointForcedResponse_integrable_of_native q br amp c hc)
  have h2 := (cuspSpatialMultiply N hN).comp_memLp' (causalJointForcedResponse_memLp_of_native q br amp c hc)
  simp only [Function.comp_def,map_smul] at h1 h2
  exact ⟨(integrable_indicator_iff measurableSet_Ioi).mpr h1,
    (memLp_indicator_iff_restrict measurableSet_Ioi).mpr h2⟩

private theorem dampedOrbit_fourier (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q<c) (N : ℝ) (hN : 0<N) (ξ : ℝ) :
    FourierTransform.fourier (dampedOrbit q br amp c N hN) ξ=
      cuspSpatialMultiply N hN (causalJointFrequencyResponse q br amp (rayLine c ξ)) := by
  let M := cuspSpatialMultiply N hN
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun t : ℝ => Complex.exp (((-2*Real.pi*t*ξ:ℝ):ℂ)*Complex.I) • dampedOrbit q br amp c N hN t)=
      (Ioi (0:ℝ)).indicator (fun t => M (expRay (rayLine c ξ) t • causalJointForcedResponse q br amp t)) := by
    funext t
    by_cases ht : t∈Ioi (0:ℝ)
    · simp only [dampedOrbit,Set.indicator_of_mem ht,map_smul,smul_smul,expRay,← Complex.exp_add]
      congr 2
      unfold rayLine
      push_cast
      ring
    · simp only [dampedOrbit,Set.indicator_of_notMem ht,smul_zero]
  rw [he,integral_indicator measurableSet_Ioi]
  have hi := causalJointForcedResponse_integrable_of_native q br amp (rayLine c ξ) (by simpa using hc)
  exact (M.integral_comp_comm hi).trans (congrArg M
    (causalJointForcedResponse_laplace_of_native q br amp (rayLine c ξ) (by simpa using hc)))

private theorem cauchy_line (c : ℝ) (hc : 0<c) :
    Integrable (fun ξ : ℝ => ‖(rayLine c ξ)⁻¹‖^(2 : ℕ)) ∧
      (∫ ξ : ℝ,‖(rayLine c ξ)⁻¹‖^(2 : ℕ))=1/(2*c) := by
  have hc2 : 0<(c/2:ℝ) := by positivity
  have hp := memLp_two_expRay_restrict (show 0<((c/2:ℝ):ℂ).re by simpa using hc2) 0
  have he (ξ : ℝ) : laplaceRay (expRay ((c/2:ℝ):ℂ)) (rayLine (c/2) ξ)=(rayLine c ξ)⁻¹ := by
    rw [laplaceRay_expRay (by simpa using hc2) (by simpa using hc2)]
    congr 1
    unfold rayLine
    push_cast
    ring
  have hmem := memLp_two_laplaceRay_line hp hc2
  simp_rw [he] at hmem
  refine ⟨(memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem,?_⟩
  have hi := integral_norm_sq_laplaceRay_line hp hc2
  simp_rw [he] at hi
  have hpoint (t : ℝ) : Real.exp (-(2*(c/2)*t))*‖expRay ((c/2:ℝ):ℂ) t‖^(2 : ℕ)=‖expRay (c:ℂ) t‖^(2 : ℕ) := by
    rw [norm_sq_expRay,norm_sq_expRay]
    simp only [Complex.ofReal_re]
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hpoint] at hi
  rw [integral_norm_sq_expRay (show 0<(c:ℂ).re by simpa using hc) 0] at hi
  simpa using hi

/-- A uniform time-energy estimate for the unchanged complete causal orbit, derived from its
source and the original rotated resolvent. The cutoff size does not occur on the right. -/
theorem original_cusp_time_energy_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (c : ℝ) (hc : principalKernelGrowth q<c) (hca : 3/2<c) (N : ℝ) (hN : 0<N) :
    (∫ t in Ioi (0:ℝ),Real.exp (-(2*c*t))*
      ‖cuspSpatialMultiply N hN (causalJointForcedResponse q br amp t)‖^(2 : ℕ))≤
      (c*sourceBound q br amp c/(c^(2 : ℕ)-9/4))^(2 : ℕ)/(2*c) := by
  have hc0 : 0<c := by linarith
  let B := c*sourceBound q br amp c/(c^(2 : ℕ)-9/4)
  have hd : 0<c^(2 : ℕ)-(9/4:ℝ) := by nlinarith
  have hB : 0≤B := by dsimp [B]; have := sourceBound_nonneg q br amp c; positivity
  obtain ⟨h1,h2⟩ := dampedOrbit_admitted q br amp c hc N hN
  have hP := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq_vector h1 h2
  have hFi := GaloisForLFunctions.RHTower.integrable_norm_sq_fourier_vector h1 h2
  have hk := cauchy_line c hc0
  have hbound : (∫ ξ : ℝ,‖FourierTransform.fourier (dampedOrbit q br amp c N hN) ξ‖^(2 : ℕ))≤B^(2 : ℕ)/(2*c) := by
    calc
      _ ≤ ∫ ξ : ℝ,B^(2 : ℕ)*‖(rayLine c ξ)⁻¹‖^(2 : ℕ) := by
        apply integral_mono_ae hFi (hk.1.const_mul (B^(2 : ℕ)))
        filter_upwards with ξ
        rw [dampedOrbit_fourier q br amp c hc N hN ξ]
        have h := response_transform_uniform q br amp c hc hca (rayLine c ξ) (by simp) N hN
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := by rw [integral_const_mul,hk.2];ring
  rw [hP] at hbound
  have he : (fun t : ℝ => ‖dampedOrbit q br amp c N hN t‖^(2 : ℕ))=
      (Ioi (0:ℝ)).indicator (fun t => Real.exp (-(2*c*t))*
        ‖cuspSpatialMultiply N hN (causalJointForcedResponse q br amp t)‖^(2 : ℕ)) := by
    funext t
    by_cases ht : t∈Ioi (0:ℝ)
    · simp only [dampedOrbit,Set.indicator_of_mem ht,norm_smul,mul_pow,norm_sq_expRay,Complex.ofReal_re]
    · simp only [dampedOrbit,Set.indicator_of_notMem ht,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
  rw [he,integral_indicator measurableSet_Ioi] at hbound
  exact hbound

end
end RHTower.D4BMOriginalWeightedOrbit
