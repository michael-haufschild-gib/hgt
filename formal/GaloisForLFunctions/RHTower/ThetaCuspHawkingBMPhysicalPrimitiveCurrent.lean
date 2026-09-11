import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCausalEquality
/-! Original-domain regularity and the complete-source Green balance of the physical causal time primitive. -/
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace RHTower.D4BMJointSource
open D4BMNativeResponse D4BMJointWave D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The Bochner double time primitive of the original physical causal response. -/
def physicalResponsePrimitive (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) : SpatialSpace :=
  ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • causalJointForcedResponse q branch a u

/-- The Bochner first time primitive of the original physical causal response. -/
def physicalResponseFirstPrimitive (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) : SpatialSpace :=
  ∫ u in (0:ℝ)..t, causalJointForcedResponse q branch a u

/-- The double time primitive of the complete original forcing, including all cutoff channels. -/
def physicalSourcePrimitive (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) : SpatialSpace :=
  ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • causalCuspSourceVector q branch a u

private theorem primitive_eq_native_bochner (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    physicalResponsePrimitive q branch a t =
      ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • nativeJointResidual q (physicalRate q branch) a u := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [nativeJointResidual_eq_causalJointForcedResponse q branch a] with u hu
  intro _
  rw [hu]

private theorem firstPrimitive_eq_native (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    physicalResponseFirstPrimitive q branch a t =
      ∫ u in (0:ℝ)..t, nativeJointResidual q (physicalRate q branch) a u := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [nativeJointResidual_eq_causalJointForcedResponse q branch a] with u hu
  intro _
  exact hu.symm

/-- The actual physical time primitive equals the literal native Hilbert vector at every time. -/
theorem physicalResponsePrimitive_eq_native (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    physicalResponsePrimitive q branch a t =
      (nativeJointTimePrimitiveField_memLp q (physicalRate q branch) a t).toLp
        (nativeJointTimePrimitiveField q (physicalRate q branch) a t) := by
  rw [nativeJointTimePrimitive_eq_bochner]
  exact primitive_eq_native_bochner q branch a t

private theorem doublePrimitive_decomposition (f : ℝ → SpatialSpace) (hf : Continuous f) (t : ℝ) :
    (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • f u) =
      (t:ℂ) • (∫ u in (0:ℝ)..t, f u)-(∫ u in (0:ℝ)..t, (u:ℂ) • f u) := by
  simp only [Complex.ofReal_sub,sub_smul]
  have h1 : IntervalIntegrable (fun u => (t:ℂ) • f u) volume 0 t := by
    simpa only [Pi.smul_apply] using! (hf.intervalIntegrable 0 t).smul (t:ℂ)
  have h2 : IntervalIntegrable (fun u => (u:ℂ) • f u) volume 0 t := by
    exact (show Continuous (fun u : ℝ => (u:ℂ) • f u) from Complex.continuous_ofReal.smul hf).intervalIntegrable 0 t
  rw [intervalIntegral.integral_sub h1 h2,intervalIntegral.integral_smul]

private theorem doublePrimitive_hasDerivAt (f : ℝ → SpatialSpace) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun v => ∫ u in (0:ℝ)..v, ((v-u:ℝ):ℂ) • f u)
      (∫ u in (0:ℝ)..t, f u) t := by
  have h1 := (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h2 := ((Complex.continuous_ofReal.smul hf).integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := (Complex.ofRealCLM.hasDerivAt.smul h1).sub h2
  have he := funext (doublePrimitive_decomposition f hf)
  rw [he]
  convert! h using 1
  simp only [Pi.smul_apply',Complex.ofRealCLM_apply,Complex.ofReal_one,one_smul,add_sub_cancel_left]

/-- Strong differentiation of the actual physical double primitive holds at every real time. -/
theorem physicalResponsePrimitive_hasDerivAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    HasDerivAt (physicalResponsePrimitive q branch a) (physicalResponseFirstPrimitive q branch a t) t := by
  rw [show physicalResponsePrimitive q branch a = _ from funext (primitive_eq_native_bochner q branch a),
    firstPrimitive_eq_native]
  exact doublePrimitive_hasDerivAt _ (nativeJointResidual_continuous q (physicalRate q branch) a) t

/-- The first physical primitive has the native continuous response as its strong derivative. -/
theorem physicalResponseFirstPrimitive_hasDerivAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    HasDerivAt (physicalResponseFirstPrimitive q branch a)
      (nativeJointResidual q (physicalRate q branch) a t) t := by
  rw [show physicalResponseFirstPrimitive q branch a = _ from funext (firstPrimitive_eq_native q branch a)]
  exact ((nativeJointResidual_continuous q (physicalRate q branch) a).integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The actual physical primitive has the original causal response as its second strong derivative almost everywhere. -/
theorem physicalResponsePrimitive_second_derivative (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    (fun t => deriv (deriv (physicalResponsePrimitive q branch a)) t) =ᵐ[volume]
      causalJointForcedResponse q branch a := by
  have he : deriv (physicalResponsePrimitive q branch a)=physicalResponseFirstPrimitive q branch a :=
    funext (fun t => (physicalResponsePrimitive_hasDerivAt q branch a t).deriv)
  rw [he]
  filter_upwards [nativeJointResidual_eq_causalJointForcedResponse q branch a] with t ht
  exact (physicalResponseFirstPrimitive_hasDerivAt q branch a t).deriv.trans ht

private theorem primitive_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (physicalResponsePrimitive q branch a) :=
  continuous_iff_continuousAt.mpr (fun t => (physicalResponsePrimitive_hasDerivAt q branch a t).continuousAt)

private theorem firstPrimitive_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (physicalResponseFirstPrimitive q branch a) :=
  continuous_iff_continuousAt.mpr (fun t => (physicalResponseFirstPrimitive_hasDerivAt q branch a t).continuousAt)

private theorem sourcePrimitive_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (physicalSourcePrimitive q branch a) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (doublePrimitive_hasDerivAt _ (causalCuspSourceVector_continuous q branch a) t).continuousAt)

private theorem ellipticForcing_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    (nativeJointEllipticForcing_memLp q (physicalRate q branch) a t).toLp
      (nativeJointEllipticForcing q (physicalRate q branch) a t) =
    physicalSourcePrimitive q branch a t-nativeJointResidual q (physicalRate q branch) a t := by
  rw [physicalSourcePrimitive,← nativeJointIntegratedForcing_eq_bochner]
  exact MemLp.toLp_sub (nativeJointIntegratedForcing_memLp q (physicalRate q branch) a t)
    (nativeJointResidualField_memLp q (physicalRate q branch) a t)

/-- The physical primitive is in the original Friedrichs domain, with the complete physical source action. -/
theorem physicalResponsePrimitive_operator (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    ∃ hmem : physicalResponsePrimitive q branch a t ∈ jointEnergyOperator.domain,
      jointEnergyOperator ⟨physicalResponsePrimitive q branch a t,hmem⟩ =
        physicalResponsePrimitive q branch a t+
          physicalSourcePrimitive q branch a t-nativeJointResidual q (physicalRate q branch) a t := by
  rw [physicalResponsePrimitive_eq_native]
  obtain ⟨hm,he⟩ := nativeJointTimePrimitive_operator_action q (physicalRate q branch) a t
  refine ⟨hm,?_⟩
  rw [ellipticForcing_eq] at he
  simpa only [add_sub_assoc] using he

/-- The physical primitive is continuous together with its original unbounded operator image. -/
theorem physicalResponsePrimitive_graph_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ) :
    Continuous (fun t => (physicalResponsePrimitive q branch a t,
      jointEnergyOperator ⟨physicalResponsePrimitive q branch a t,
        (physicalResponsePrimitive_operator q branch a t).choose⟩)) := by
  have he : (fun t => jointEnergyOperator ⟨physicalResponsePrimitive q branch a t,
      (physicalResponsePrimitive_operator q branch a t).choose⟩) =
      fun t => physicalResponsePrimitive q branch a t+physicalSourcePrimitive q branch a t-
        nativeJointResidual q (physicalRate q branch) a t :=
    funext (fun t => (physicalResponsePrimitive_operator q branch a t).choose_spec)
  simp_rw [show ∀ t, jointEnergyOperator ⟨physicalResponsePrimitive q branch a t,
      (physicalResponsePrimitive_operator q branch a t).choose⟩ =
      physicalResponsePrimitive q branch a t+physicalSourcePrimitive q branch a t-
        nativeJointResidual q (physicalRate q branch) a t from fun t => congrFun he t]
  exact (primitive_continuous q branch a).prodMk
    (((primitive_continuous q branch a).add (sourcePrimitive_continuous q branch a)).sub
      (nativeJointResidual_continuous q (physicalRate q branch) a))

/-- The actual physical primitive has the literal classical representative, with both actual radial derivatives and its original Dirichlet trace. -/
theorem physicalResponsePrimitive_classical_trace (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    (physicalResponsePrimitive q branch a t : ℝ × UpperHalfPlane → ℂ) =ᵐ[
      radialMeasure.prod D4BMModularCore.measure]
      nativeJointTimePrimitiveField q (physicalRate q branch) a t ∧
    ∀ X k : ℝ,
      nativeResidualTimePrimitive q (physicalRate q branch) a t 0 X k = 0 ∧
      ∀ x : ℝ,
        HasDerivAt (fun y => nativeResidualTimePrimitive q (physicalRate q branch) a t y X k)
          (deriv (fun y => nativeResidualTimePrimitive q (physicalRate q branch) a t y X k) x) x ∧
        HasDerivAt (deriv (fun y => nativeResidualTimePrimitive q (physicalRate q branch) a t y X k))
          (deriv (deriv (fun y => nativeResidualTimePrimitive q (physicalRate q branch) a t y X k)) x) x := by
  constructor
  · rw [physicalResponsePrimitive_eq_native]
    exact (nativeJointTimePrimitiveField_memLp q (physicalRate q branch) a t).coeFn_toLp
  · intro X k
    exact ⟨nativeResidualTimePrimitive_boundary q (physicalRate q branch) a t X k,
      fun x => nativeResidualTimePrimitive_radial_hasDerivAt q (physicalRate q branch) a t x X k⟩

/-- The full radial and angular energy of the physical primitive equals its complete forcing pairing in the original measure. -/
theorem physicalResponsePrimitive_gradient_energy (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    Integrable (nativeJointGradientEnergy q (physicalRate q branch) a t)
      (radialMeasure.prod D4BMModularCore.measure) ∧
    (∫ p, nativeJointGradientEnergy q (physicalRate q branch) a t p
      ∂radialMeasure.prod D4BMModularCore.measure) =
      (inner ℂ (physicalSourcePrimitive q branch a t-nativeJointResidual q (physicalRate q branch) a t)
        (physicalResponsePrimitive q branch a t)).re := by
  refine ⟨(nativeTimePrimitive_gradient_energy_integrable q (physicalRate q branch) a t).1,?_⟩
  rw [nativeTimePrimitive_global_energy,physicalResponsePrimitive_eq_native,← ellipticForcing_eq,L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [(nativeJointEllipticForcing_memLp q (physicalRate q branch) a t).coeFn_toLp,
    (nativeJointTimePrimitiveField_memLp q (physicalRate q branch) a t).coeFn_toLp] with p hG hW
  rw [hG,hW]
  simp only [RCLike.inner_apply,mul_comm]

private theorem primitive_covariance (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    formEmbeddingCovariance jointEmbedding
      (physicalResponsePrimitive q branch a t+physicalSourcePrimitive q branch a t-
        nativeJointResidual q (physicalRate q branch) a t) = physicalResponsePrimitive q branch a t := by
  have h := nativeJointTimePrimitive_covariance q (physicalRate q branch) a t
  rw [ellipticForcing_eq,← physicalResponsePrimitive_eq_native] at h
  simpa only [add_sub_assoc] using h

private theorem physical_spatial_cancellation (q r : XiZeroCopy) (b c : Bool) (a d : ℂ) (t : ℝ) :
    inner ℂ (physicalResponsePrimitive q b a t) (nativeJointResidual r (physicalRate r c) d t)-
      inner ℂ (nativeJointResidual q (physicalRate q b) a t) (physicalResponsePrimitive r c d t) =
    inner ℂ (physicalResponsePrimitive q b a t) (physicalSourcePrimitive r c d t)-
      inner ℂ (physicalSourcePrimitive q b a t) (physicalResponsePrimitive r c d t) := by
  let G := physicalResponsePrimitive q b a t+physicalSourcePrimitive q b a t-
    nativeJointResidual q (physicalRate q b) a t
  let H := physicalResponsePrimitive r c d t+physicalSourcePrimitive r c d t-
    nativeJointResidual r (physicalRate r c) d t
  have hq := primitive_covariance q b a t
  have hr := primitive_covariance r c d t
  change jointEmbedding (jointEmbedding.adjoint G)=physicalResponsePrimitive q b a t at hq
  change jointEmbedding (jointEmbedding.adjoint H)=physicalResponsePrimitive r c d t at hr
  have he : inner ℂ (physicalResponsePrimitive q b a t) H =
      inner ℂ G (physicalResponsePrimitive r c d t) := by
    rw [← hq,← hr,← jointEmbedding.adjoint_inner_right,← jointEmbedding.adjoint_inner_left]
  dsimp only [G,H] at he
  simp only [inner_add_left,inner_add_right,inner_sub_left,inner_sub_right] at he
  linear_combination -he

/-- Temporal Green current of two independently forced physical causal primitives. -/
def physicalPrimitiveCurrent (q r : XiZeroCopy) (b c : Bool) (a d : ℂ) (t : ℝ) : ℂ :=
  inner ℂ (physicalResponsePrimitive q b a t) (physicalResponseFirstPrimitive r c d t)-
    inner ℂ (physicalResponseFirstPrimitive q b a t) (physicalResponsePrimitive r c d t)

/-- The derivative of the actual physical current is the complete source pairing; the original spatial operator cancels within its admitted domain. -/
theorem physicalPrimitiveCurrent_source_hasDerivAt (q r : XiZeroCopy) (b c : Bool) (a d : ℂ) (t : ℝ) :
    HasDerivAt (physicalPrimitiveCurrent q r b c a d)
      (inner ℂ (physicalResponsePrimitive q b a t) (physicalSourcePrimitive r c d t)-
        inner ℂ (physicalSourcePrimitive q b a t) (physicalResponsePrimitive r c d t)) t := by
  have h := ((physicalResponsePrimitive_hasDerivAt q b a t).inner ℂ
    (physicalResponseFirstPrimitive_hasDerivAt r c d t)).sub
      ((physicalResponseFirstPrimitive_hasDerivAt q b a t).inner ℂ
        (physicalResponsePrimitive_hasDerivAt r c d t))
  change HasDerivAt (physicalPrimitiveCurrent q r b c a d) _ t at h
  convert! h using 1
  have he := physical_spatial_cancellation q r b c a d t
  linear_combination -he

/-- Exact finite-time physical Green balance, with the full final-time current retained. -/
theorem physicalPrimitiveCurrent_balance (q r : XiZeroCopy) (b c : Bool) (a d : ℂ) (T : ℝ) :
    (∫ t in (0:ℝ)..T,
      (inner ℂ (physicalResponsePrimitive q b a t) (physicalSourcePrimitive r c d t)-
        inner ℂ (physicalSourcePrimitive q b a t) (physicalResponsePrimitive r c d t))) =
    physicalPrimitiveCurrent q r b c a d T := by
  have hc : Continuous (fun t =>
      inner ℂ (physicalResponsePrimitive q b a t) (physicalSourcePrimitive r c d t)-
        inner ℂ (physicalSourcePrimitive q b a t) (physicalResponsePrimitive r c d t)) :=
    ((primitive_continuous q b a).inner (sourcePrimitive_continuous r c d)).sub
      ((sourcePrimitive_continuous q b a).inner (primitive_continuous r c d))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => physicalPrimitiveCurrent_source_hasDerivAt q r b c a d t) (hc.intervalIntegrable 0 T)
  simpa only [physicalPrimitiveCurrent,physicalResponsePrimitive,physicalResponseFirstPrimitive,
    intervalIntegral.integral_same,inner_zero_left,sub_self,sub_zero] using h

end
end RHTower.D4BMJointSource
