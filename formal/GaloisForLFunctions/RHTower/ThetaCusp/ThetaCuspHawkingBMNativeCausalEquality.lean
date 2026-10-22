import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeTimeIntegralIdentification
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalVolterraEquation
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
/-! The literal native residual equals the original physical causal response.

Both actual bounded time equations are already proved. Two further time primitives
make their locally integrable difference classical; conserved positive covariance
energy then gives uniqueness without assuming a native growth bound.
-/
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem adjoint_contractive (x : SpatialSpace) : ‖jointEmbedding.adjoint x‖ ≤ ‖x‖ := by
  have hJ : ‖jointEmbedding‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simpa only [one_mul] using jointEmbedding_norm_le u
  calc
    ‖jointEmbedding.adjoint x‖ ≤ ‖jointEmbedding.adjoint‖*‖x‖ := jointEmbedding.adjoint.le_opNorm x
    _ = ‖jointEmbedding‖*‖x‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
    _ = ‖x‖ := one_mul _

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

private def covarianceEnergy (J : Y →L[ℂ] X) (z v : X) : ℂ :=
  inner ℂ (J.adjoint v) (J.adjoint v)+inner ℂ z z-
    inner ℂ (J.adjoint z) (J.adjoint z)

private theorem covarianceEnergy_derivative (J : Y →L[ℂ] X) (z v a : ℝ → X) (t : ℝ)
    (hz : HasDerivAt z (v t) t) (hv : HasDerivAt v (a t) t)
    (he : formEmbeddingCovariance J (a t)+
      (1-formEmbeddingCovariance J) (z t)=0) :
    HasDerivAt (fun s => covarianceEnergy J (z s) (v s)) 0 t := by
  let B := formEmbeddingCovariance J
  have hzJ := (J.adjoint.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hz
  have hvJ := (J.adjoint.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have h := ((HasDerivAt.inner ℂ hvJ hvJ).add (HasDerivAt.inner ℂ hz hz)).sub
    (HasDerivAt.inner ℂ hzJ hzJ)
  have he' : J (J.adjoint (a t)) = J (J.adjoint (z t))-z t := by
    change B (a t)+(1-B) (z t)=0 at he
    simp only [sub_apply,one_apply_eq_self] at he
    change J (J.adjoint (a t))+(z t-J (J.adjoint (z t)))=0 at he
    apply eq_sub_iff_add_eq.mpr
    apply sub_eq_zero.mp
    simpa only [add_sub_assoc] using he
  have hi1 : inner ℂ (J.adjoint (v t)) (J.adjoint (a t)) = inner ℂ (v t) (J (J.adjoint (a t))) :=
    J.adjoint_inner_left _ _
  have hi2 : inner ℂ (J.adjoint (a t)) (J.adjoint (v t)) = inner ℂ (J (J.adjoint (a t))) (v t) :=
    J.adjoint_inner_right _ _
  have hi3 : inner ℂ (J.adjoint (z t)) (J.adjoint (v t)) = inner ℂ (J (J.adjoint (z t))) (v t) :=
    J.adjoint_inner_right _ _
  have hi4 : inner ℂ (J.adjoint (v t)) (J.adjoint (z t)) = inner ℂ (v t) (J (J.adjoint (z t))) :=
    J.adjoint_inner_left _ _
  change HasDerivAt (fun s => covarianceEnergy J (z s) (v s))
    ((inner ℂ (J.adjoint (v t)) (J.adjoint (a t))+
      inner ℂ (J.adjoint (a t)) (J.adjoint (v t)))+
      (inner ℂ (z t) (v t)+inner ℂ (v t) (z t))-
      (inner ℂ (J.adjoint (z t)) (J.adjoint (v t))+
      inner ℂ (J.adjoint (v t)) (J.adjoint (z t)))) t at h
  rw [hi1,hi2,hi3,hi4,he',inner_sub_left,inner_sub_right] at h
  convert h using 1
  ring

private theorem covarianceEnergy_zero_velocity (J : Y →L[ℂ] X)
    (hcontr : ∀ x, ‖J.adjoint x‖ ≤ ‖x‖) (hinj : Function.Injective J.adjoint)
    (z v : X) (h : covarianceEnergy J z v=0) : v=0 := by
  have hr := congrArg Complex.re h
  simp only [covarianceEnergy,Complex.add_re,Complex.sub_re,Complex.zero_re] at hr
  have h1 : (inner ℂ (J.adjoint v) (J.adjoint v)).re=‖J.adjoint v‖^(2 : ℕ) :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h2 : (inner ℂ z z).re=‖z‖^(2 : ℕ) := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h3 : (inner ℂ (J.adjoint z) (J.adjoint z)).re=‖J.adjoint z‖^(2 : ℕ) :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [h1,h2,h3] at hr
  have hz := hcontr z
  have hn : ‖J.adjoint v‖=0 := by
    nlinarith [norm_nonneg (J.adjoint z),norm_nonneg z,
      norm_nonneg (J.adjoint v),sq_nonneg (‖J.adjoint v‖)]
  have hv : J.adjoint v=0 := norm_eq_zero.mp hn
  apply hinj
  simpa only [map_zero] using hv

private theorem covariance_homogeneous_unique (J : Y →L[ℂ] X)
    (hcontr : ∀ x, ‖J.adjoint x‖ ≤ ‖x‖) (hinj : Function.Injective J.adjoint) (z v a : ℝ → X)
    (hz : ∀ t, HasDerivAt z (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (he : ∀ t, formEmbeddingCovariance J (a t)+
      (1-formEmbeddingCovariance J) (z t)=0)
    (hz0 : z 0=0) (hv0 : v 0=0) : ∀ t, z t=0 ∧ v t=0 := by
  have hE (t : ℝ) : covarianceEnergy J (z t) (v t)=0 := by
    have hD (s : ℝ) := covarianceEnergy_derivative J z v a s (hz s) (hv s) (he s)
    have hc := is_const_of_deriv_eq_zero (fun s => (hD s).differentiableAt)
      (fun s => (hD s).deriv) t 0
    simpa only [hz0,hv0,covarianceEnergy,map_zero,inner_zero_left,add_zero,sub_zero] using hc
  have hvz (t : ℝ) := covarianceEnergy_zero_velocity J hcontr hinj (z t) (v t) (hE t)
  intro t
  refine ⟨?_,hvz t⟩
  have hc := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
    (fun s => by rw [(hz s).deriv,hvz s]) t 0
  exact hc.trans hz0
private def P2 (f : ℝ → X) (t : ℝ) : X := ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • f u

omit [InnerProductSpace ℂ X] [CompleteSpace X] in
private theorem local_interval {f : ℝ → X} (hf : LocallyIntegrable f volume) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc

omit [CompleteSpace X] in
private theorem local_smul (f : ℝ → X) (hf : LocallyIntegrable f volume)
    (c : ℝ → ℂ) (hc : Continuous c) : LocallyIntegrable (fun t => c t • f t) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (hf.integrableOn_isCompact hK).continuousOn_smul hc.continuousOn hK

omit [CompleteSpace X] in
private theorem P2_integrable (f : ℝ → X) (hf : LocallyIntegrable f volume) (t : ℝ) :
    IntervalIntegrable (fun u => ((t-u:ℝ):ℂ) • f u) volume 0 t := by
  apply (local_interval hf 0 t).continuousOn_smul
  fun_prop

omit [CompleteSpace X] in
private theorem P2_decomposition (f : ℝ → X) (hf : LocallyIntegrable f volume) (t : ℝ) :
    P2 f t = (t:ℂ) • (∫ u in (0:ℝ)..t, f u)-∫ u in (0:ℝ)..t, (u:ℂ) • f u := by
  unfold P2
  simp only [Complex.ofReal_sub,sub_smul]
  have h1 : IntervalIntegrable (fun u => (t:ℂ) • f u) volume 0 t := by
    simpa only [Pi.smul_apply] using! (local_interval hf 0 t).smul (t:ℂ)
  rw [intervalIntegral.integral_sub h1
    ((local_interval hf 0 t).continuousOn_smul Complex.continuous_ofReal.continuousOn),
    intervalIntegral.integral_smul]

omit [CompleteSpace X] in
private theorem P2_continuous (f : ℝ → X) (hf : LocallyIntegrable f volume) : Continuous (P2 f) := by
  have h1 := intervalIntegral.continuous_primitive (local_interval hf) 0
  have h2 := intervalIntegral.continuous_primitive
    (local_interval (local_smul f hf Complex.ofReal Complex.continuous_ofReal)) 0
  simp_rw [show P2 f=fun t : ℝ => (t:ℂ) • (∫ u in (0:ℝ)..t, f u)-∫ u in (0:ℝ)..t, (u:ℂ) • f u
    from funext (P2_decomposition f hf)]
  exact (Complex.continuous_ofReal.smul h1).sub h2

private theorem P2_derivative (f : ℝ → X) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (P2 f) (∫ u in (0:ℝ)..t, f u) t := by
  have h1 := (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h2 := ((Complex.continuous_ofReal.smul hf).integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := (Complex.ofRealCLM.hasDerivAt.smul h1).sub h2
  have he : P2 f=fun t : ℝ => (t:ℂ) • (∫ u in (0:ℝ)..t, f u)-∫ u in (0:ℝ)..t, (u:ℂ) • f u :=
    funext (P2_decomposition f hf.locallyIntegrable)
  rw [he]
  convert! h using 1
  simp only [Pi.smul_apply',Complex.ofRealCLM_apply,Complex.ofReal_one,one_smul,add_sub_cancel_left]

private theorem P2_map (L : X →L[ℂ] X) (f : ℝ → X) (hf : LocallyIntegrable f volume) (t : ℝ) :
    P2 (fun u => L (f u)) t = L (P2 f t) := by
  unfold P2
  rw [← L.intervalIntegral_comp_comm (P2_integrable f hf t)]
  apply intervalIntegral.integral_congr
  intro u hu
  exact (L.map_smul _ _).symm

omit [CompleteSpace X] in
private theorem P2_add (f g : ℝ → X) (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (t : ℝ) :
    P2 (fun u => f u+g u) t=P2 f t+P2 g t := by
  simp only [P2,smul_add]
  exact intervalIntegral.integral_add (P2_integrable f hf t) (P2_integrable g hg t)

omit [CompleteSpace X] in
private theorem P2_sub (f g : ℝ → X) (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (t : ℝ) :
    P2 (fun u => f u-g u) t=P2 f t-P2 g t := by
  simp only [P2,smul_sub]
  exact intervalIntegral.integral_sub (P2_integrable f hf t) (P2_integrable g hg t)

omit [CompleteSpace X] in
private theorem P2_congr (f g : ℝ → X) (he : f=ᵐ[volume] g) (t : ℝ) : P2 f t=P2 g t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [he] with u hu
  intro humem
  rw [hu]

omit [CompleteSpace X] in
private theorem local_map (L : X →L[ℂ] X) (f : ℝ → X) (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun t => L (f t)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  simpa only [Function.comp_apply] using! L.integrable_comp (hf.integrableOn_isCompact hK)

private theorem covariance_volterra_unique (u : ℝ → SpatialSpace)
    (hu : LocallyIntegrable u volume)
    (he : ∀ᵐ t ∂(volume : Measure ℝ), formEmbeddingCovariance jointEmbedding (u t)+
      (1-formEmbeddingCovariance jointEmbedding) (P2 u t)=0) : u=ᵐ[volume] 0 := by
  let B := formEmbeddingCovariance jointEmbedding
  let y := P2 u
  have hy : Continuous y := P2_continuous u hu
  have hyl : LocallyIntegrable y volume := hy.locallyIntegrable
  let z := P2 y
  let v : ℝ → SpatialSpace := fun t => ∫ s in (0:ℝ)..t, y s
  have hODE (t : ℝ) : B (y t)+(1-B) (z t)=0 := by
    change B (P2 u t)+(1-B) (P2 y t)=0
    rw [← P2_map B u hu,← P2_map (1-B) y hyl,
      ← P2_add _ _ (local_map B u hu) (local_map (1-B) y hyl)]
    have h := P2_congr (fun s => B (u s)+(1-B) (y s)) (fun _ => 0) he t
    simpa only [P2,smul_zero,intervalIntegral.integral_zero] using h
  have hzero := covariance_homogeneous_unique jointEmbedding adjoint_contractive
    (continuousLinearMap_adjoint_injective_of_dense_range jointEmbedding jointEmbedding_dense)
    z v y (fun t => P2_derivative y hy t)
    (fun t => (hy.integral_hasStrictDerivAt 0 t).hasDerivAt) hODE
    (by simp only [z,P2,intervalIntegral.integral_same])
    (by simp only [v,intervalIntegral.integral_same])
  have hy0 (t : ℝ) : y t=0 := by
    have hv0 : v=fun _ => 0 := funext (fun s => (hzero s).2)
    have hd := (hy.integral_hasStrictDerivAt 0 t).hasDerivAt
    change HasDerivAt v (y t) t at hd
    rw [hv0] at hd
    exact hd.unique (hasDerivAt_const t 0)
  filter_upwards [he] with t ht
  change B (u t)+(1-B) (y t)=0 at ht
  rw [hy0 t,map_zero,add_zero] at ht
  change u t=0
  apply formEmbeddingCovariance_injective jointEmbedding jointEmbedding_injective jointEmbedding_dense
  simpa only [map_zero] using ht

private theorem physical_locallyIntegrable (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    LocallyIntegrable (causalJointForcedResponse q branch a) volume := by
  let w : ℂ := (causalResponseShift q : ℂ)+1
  let f : ℝ → SpatialSpace := fun t => expRay w t • causalJointForcedResponse q branch a t
  have hf : LocallyIntegrable f volume :=
    (causalJointForcedResponse_weighted_memLp q branch a).locallyIntegrable (by norm_num)
  have hc : Continuous (fun t : ℝ => Complex.exp (w*(t:ℂ))) := by fun_prop
  apply (local_smul f hf _ hc).congr
  apply Eventually.of_forall
  intro t
  dsimp only [f]
  simp only [expRay,smul_smul,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_smul]

/-- The literal native cusp residual is the constructed physical causal response in
  the original radial/modular Hilbert space, almost everywhere in real time. -/
theorem nativeJointResidual_eq_causalJointForcedResponse (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    D4BMNativeResponse.nativeJointResidual q (physicalRate q branch) a =ᵐ[volume]
      causalJointForcedResponse q branch a := by
  let N := D4BMNativeResponse.nativeJointResidual q (physicalRate q branch) a
  let U := causalJointForcedResponse q branch a
  let B := formEmbeddingCovariance jointEmbedding
  have hN : LocallyIntegrable N volume :=
    (D4BMNativeResponse.nativeJointResidual_continuous q (physicalRate q branch) a).locallyIntegrable
  have hU := physical_locallyIntegrable q branch a
  have hu : LocallyIntegrable (fun t => N t-U t) volume := by
    simpa only [Pi.sub_apply] using! hN.sub hU
  have he : ∀ᵐ t ∂(volume : Measure ℝ), B (N t-U t)+(1-B) (P2 (fun s => N s-U s) t)=0 := by
    filter_upwards [causalJointForcedResponse_bochner_covariance_equation q branch a] with t ht
    have hn := D4BMNativeResponse.nativeJointResidual_bochner_covariance_equation q branch a t
    change B (N t)+(1-B) (P2 N t)=B (P2 (causalCuspSourceVector q branch a) t) at hn
    change B (U t)+(1-B) (P2 U t)=B (P2 (causalCuspSourceVector q branch a) t) at ht
    rw [P2_sub N U hN hU t,map_sub,map_sub]
    calc
      (B (N t)-B (U t))+((1-B) (P2 N t)-(1-B) (P2 U t)) =
        (B (N t)+(1-B) (P2 N t))-(B (U t)+(1-B) (P2 U t)) := by abel
      _ = 0 := by rw [hn,ht,sub_self]
  have h0 := covariance_volterra_unique (fun t => N t-U t) hu he
  filter_upwards [h0] with t ht
  exact sub_eq_zero.mp ht

end
end RHTower.D4BMJointSource
