import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeOperatorIdentification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCausalCuspSource
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace RHTower.D4BMNativeResponse
open D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse D4BMJointSource GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
private theorem l2_integral_eq_of_le {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    (ν : Measure α) [SigmaFinite ν] (f : ℝ × α → ℂ) (hf : Continuous f)
    (u : ℝ → Lp ℂ 2 ν) (hu : Continuous u) (v : Lp ℂ 2 ν)
    {a b : ℝ} (hab : a ≤ b)
    (he : ∀ t ∈ Icc a b, (u t : α → ℂ) =ᵐ[ν] fun x => f (t,x))
    (hv : (v : α → ℂ) =ᵐ[ν] fun x => ∫ t in a..b, f (t,x)) :
    (∫ t in a..b, u t) = v := by
  apply ext_inner_left ℂ
  intro g
  have hinner := (innerSL ℂ g).intervalIntegral_comp_comm (hu.intervalIntegrable (μ := volume) a b)
  simp only [innerSL_apply_apply] at hinner
  rw [← hinner,L2.inner_def]
  let μ := volume.restrict (Ioc a b)
  let k (z : ℝ × α) := inner ℂ (g z.2) (f z)
  have hk : AEStronglyMeasurable k (μ.prod ν) :=
    (Lp.aestronglyMeasurable g).comp_snd.inner hf.measurable.aestronglyMeasurable
  have hslice (t : ℝ) (ht : t ∈ Icc a b) :
      (fun x => k (t,x)) =ᵐ[ν] fun x => inner ℂ (g x) (u t x) := by
    filter_upwards [he t ht] with x hx
    dsimp only [k]; rw [hx]
  have hi : Integrable k (μ.prod ν) := by
    apply (integrable_prod_iff hk).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (L2.integrable_inner g (u t)).congr (hslice t ⟨ht.1.le,ht.2⟩).symm
    · have hbound : Integrable (fun t => ‖g‖^(2 : ℕ)+‖u t‖^(2 : ℕ)) μ :=
        ((continuous_const.add (hu.norm.pow 2)).intervalIntegrable (μ := volume) a b).1
      apply hbound.mono' hk.norm.integral_prod_right'
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      have heq := integral_congr_ae ((hslice t ⟨ht.1.le,ht.2⟩).fun_comp norm)
      simp only [Function.comp_apply] at heq
      rw [heq]
      have hg := (Lp.memLp g).norm.integrable_sq
      have hu' := (Lp.memLp (u t)).norm.integrable_sq
      calc
        (∫ x, ‖inner ℂ (g x) (u t x)‖ ∂ν) ≤ ∫ x, ‖g x‖^(2 : ℕ)+‖u t x‖^(2 : ℕ) ∂ν := by
          apply integral_mono (L2.integrable_inner g (u t)).norm (hg.add hu')
          intro x
          dsimp only [Pi.add_apply]
          have hn := norm_inner_le_norm (g x) (u t x) (𝕜 := ℂ)
          nlinarith [sq_nonneg (‖g x‖-‖u t x‖)]
        _ = ‖g‖^(2 : ℕ)+‖u t‖^(2 : ℕ) := by
          rw [integral_add hg hu',← _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq,
            ← _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  have hleft : (∫ t in a..b, inner ℂ g (u t)) = ∫ t, ∫ x, k (t,x) ∂ν ∂μ := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [L2.inner_def]
    exact integral_congr_ae (hslice t ⟨ht.1.le,ht.2⟩).symm
  rw [hleft,integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx,intervalIntegral.integral_of_le hab]
  dsimp only [k]
  have hfx : IntegrableOn (fun t => f (t,x)) (Ioc a b) volume :=
    ((hf.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))).intervalIntegrable (μ := volume) a b).1
  exact (innerSL ℂ (g x)).integral_comp_comm hfx

private theorem l2_integral_eq {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    (ν : Measure α) [SigmaFinite ν] (f : ℝ × α → ℂ) (hf : Continuous f)
    (u : ℝ → Lp ℂ 2 ν) (hu : Continuous u) (v : Lp ℂ 2 ν) (a b : ℝ)
    (he : ∀ t, (u t : α → ℂ) =ᵐ[ν] fun x => f (t,x))
    (hv : (v : α → ℂ) =ᵐ[ν] fun x => ∫ t in a..b, f (t,x)) :
    (∫ t in a..b, u t) = v := by
  by_cases hab : a ≤ b
  · exact l2_integral_eq_of_le ν f hf u hu v hab (fun t _ => he t) hv
  · have hn : ((-v : Lp ℂ 2 ν) : α → ℂ) =ᵐ[ν] fun x => ∫ t in b..a, f (t,x) := by
      filter_upwards [Lp.coeFn_neg v,hv] with x hx hvx
      rw [hx]
      change -v x = _
      rw [hvx,intervalIntegral.integral_symm a b]
    have hi := l2_integral_eq_of_le ν f hf u hu (-v) (le_of_not_ge hab)
      (fun t _ => he t) hn
    rw [intervalIntegral.integral_symm b a,hi,neg_neg]

/-- The literal native double primitive equals the Bochner primitive of the original
joint-space residual, at every real time. -/
theorem nativeJointTimePrimitive_eq_bochner (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    (nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
      (nativeJointTimePrimitiveField q s amplitude t) =
      ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • nativeJointResidual q s amplitude u := by
  symm
  apply l2_integral_eq (radialMeasure.prod D4BMModularCore.measure)
    (fun p : ℝ × (ℝ × UpperHalfPlane) =>
      ((t-p.1:ℝ):ℂ)*nativeJointResidualField q s amplitude p.1 p.2)
  · exact (by fun_prop : Continuous (fun p : ℝ × (ℝ × UpperHalfPlane) =>
        ((t-p.1:ℝ):ℂ))).mul (nativeJointResidualField_joint_continuous q s amplitude)
  · exact (by fun_prop : Continuous (fun u : ℝ => ((t-u:ℝ):ℂ))).smul
      (nativeJointResidual_continuous q s amplitude)
  · intro u
    filter_upwards [Lp.coeFn_smul ((t-u:ℝ):ℂ) (nativeJointResidual q s amplitude u),
      (nativeJointResidualField_memLp q s amplitude u).coeFn_toLp] with z h0 h1
    change (((t-u:ℝ):ℂ) • nativeJointResidual q s amplitude u) z = _ at h0 ⊢
    rw [h0]
    simp only [Pi.smul_apply,smul_eq_mul]
    exact congrArg (fun c : ℂ => ((t-u:ℝ):ℂ)*c) h1
  · exact (nativeJointTimePrimitiveField_memLp q s amplitude t).coeFn_toLp

private theorem literalForcing_continuous (q : XiZeroCopy) (s a : ℂ) :
    Continuous (fun p : ℝ × (ℝ × UpperHalfPlane) =>
      nativeResidualStaticForcing q s a p.1 p.2.1 p.2.2.re (Real.log p.2.2.im)) := by
  have hz : Continuous (coordinates : UpperHalfPlane → Fin 2 → ℝ) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im
  have hQ := (squareResidual_continuousOn q).comp_continuous hz (fun z => z.im_pos)
  have hC (i : Fin 3) := (cutoffCommutator_continuousOn (principalExponent q i)).comp_continuous
    hz (fun z => z.im_pos)
  have hO : Continuous (fun p : ℝ × ℝ => oddSource s a p.1 p.2) := by
    have h₁ := (timeReducedCoefficient_joint_continuous s a).comp
      (show Continuous (fun p : ℝ × ℝ => (p.1,min p.2 0)) by fun_prop)
    have h₂ := (timeReducedCoefficient_joint_continuous s a).comp
      (show Continuous (fun p : ℝ × ℝ => (p.1,min (-p.2) 0)) by fun_prop)
    exact h₁.sub h₂
  have hP (i : Fin 3) : Continuous (fun p : ℝ × ℝ =>
      principalNullResponse q s a i (p.1+p.2) (p.1-p.2)) := by
    have he : (fun p : ℝ × ℝ => principalNullResponse q s a i (p.1+p.2) (p.1-p.2)) =
        fun p => principalAmplitude q i * radialResponse (-principalExponent q i) s a p.1 p.2 := by
      funext p
      simp only [principalNullResponse,show (p.1+p.2+(p.1-p.2))/2=p.1 by ring,
        show (p.1+p.2-(p.1-p.2))/2=p.2 by ring]
    rw [he]
    exact (radialResponse_continuous (-principalExponent q i) s a).const_mul (principalAmplitude q i)
  have hp : Continuous (fun p : ℝ × (ℝ × UpperHalfPlane) => (p.1,p.2.1)) := by fun_prop
  have ha : Continuous (fun p : ℝ × (ℝ × UpperHalfPlane) => p.2.2) := by fun_prop
  have he : (fun p : ℝ × (ℝ × UpperHalfPlane) =>
      nativeResidualStaticForcing q s a p.1 p.2.1 p.2.2.re (Real.log p.2.2.im)) =
      fun p => squareResidual q (coordinates p.2.2)*oddSource s a p.1 p.2.1+
        (∑ i : Fin 3, principalNullResponse q s a i (p.1+p.2.1) (p.1-p.2.1)*
          cutoffCommutator (principalExponent q i) (coordinates p.2.2))/(Real.cosh p.2.1:ℂ)^(2 : ℕ) := by
    funext p
    simp only [nativeResidualStaticForcing,Real.exp_log p.2.2.im_pos,coordinates]
  rw [he]
  refine ((hQ.comp ha).mul (hO.comp hp)).add ?_
  exact (continuous_finsetSum _ (fun i _ => ((hP i).comp hp).mul ((hC i).comp ha))).div
    (by fun_prop) (fun p => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (Real.cosh_pos p.2.1).ne'))

private theorem cutoffTime_literal_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (i : Fin 3) (t : ℝ) :
    (principalCutoffTimeVector q branch a i t : ℝ × UpperHalfPlane → ℂ) =ᵐ[
      radialMeasure.prod D4BMModularCore.measure] fun z =>
        principalNullResponse q (physicalRate q branch) a i (t+z.1) (t-z.1)*
          cutoffCommutator (principalExponent q i) (coordinates z.2)/(Real.cosh z.1:ℂ)^(2 : ℕ) := by
  have hr := (principalNullResponse_physical_ae q branch a i t).filter_mono
    (ae_mono (show radialMeasure ≤ volume from Measure.restrict_le_self))
  have he := l2SeparatedProduct_ae (principalCutoffRadialOp (principalTimeResponse q branch a i t))
    (cutoffCommutatorVector (principalExponent q i))
  filter_upwards [he,
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (principalCutoffRadialOp_ae (principalTimeResponse q branch a i t)),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hr,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (cutoffCommutator_memLp (principalExponent q i)).coeFn_toLp] with z h0 h1 h2 h3
  change principalCutoffTimeVector q branch a i t z = _ at h0 ⊢
  rw [h0]
  change principalCutoffRadialOp (principalTimeResponse q branch a i t) z.1*
    cutoffCommutatorVector (principalExponent q i) z.2 = _
  simp only [Function.comp_apply] at h1 h2 h3
  change cutoffCommutatorVector (principalExponent q i) z.2 = _ at h3
  rw [h1,h2,h3]
  have hh : horizonCoordinate z.1 = 1/(Real.cosh z.1)^(2 : ℕ) := by
    unfold horizonCoordinate radialUnit
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq z.1]
  rw [hh]
  push_cast
  ring

/-- The original physical source vector represents the complete literal native forcing,
including all three principal cutoff terms with their actual horizon factor. -/
theorem causalCuspSourceVector_native_forcing_ae (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (t : ℝ) :
    (causalCuspSourceVector q branch a t : ℝ × UpperHalfPlane → ℂ) =ᵐ[
      radialMeasure.prod D4BMModularCore.measure] fun z =>
        nativeResidualStaticForcing q (physicalRate q branch) a t z.1 z.2.re (Real.log z.2.im) := by
  have ht : ∀ᵐ z : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure, z.1 < 0 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Iio)
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i => principalCutoffTimeVector q branch a i t)
  filter_upwards [Lp.coeFn_add (timeCuspMainVector q branch a t)
      (∑ i : Fin 3, principalCutoffTimeVector q branch a i t), hs,
    timeCuspMainVector_ae q branch a t, ae_all_iff.mpr (fun i => cutoffTime_literal_ae q branch a i t),ht]
    with z h0 h1 h2 h3 hz
  change causalCuspSourceVector q branch a t z = _ at h0 ⊢
  rw [h0]
  simp only [Pi.add_apply,h1,h2]
  simp_rw [h3]
  simp only [nativeResidualStaticForcing,Real.exp_log z.2.im_pos,timeCuspMainForcing,
    coordinates,oddSource,min_eq_left hz.le,min_eq_right (neg_nonneg.mpr hz.le),
    source_boundary,sub_zero,Finset.sum_div]
  ring

/-- The literal integrated forcing equals the Bochner primitive of the original complete
physical source, with no forcing-identification premise. -/
theorem nativeJointIntegratedForcing_eq_bochner (q : XiZeroCopy) (branch : Bool) (a : ℂ) (t : ℝ) :
    (nativeJointIntegratedForcing_memLp q (physicalRate q branch) a t).toLp
      (nativeJointIntegratedForcing q (physicalRate q branch) a t) =
      ∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • causalCuspSourceVector q branch a u := by
  symm
  apply l2_integral_eq (radialMeasure.prod D4BMModularCore.measure)
    (fun p : ℝ × (ℝ × UpperHalfPlane) => ((t-p.1:ℝ):ℂ)*
      nativeResidualStaticForcing q (physicalRate q branch) a p.1 p.2.1 p.2.2.re (Real.log p.2.2.im))
  · exact (by fun_prop : Continuous (fun p : ℝ × (ℝ × UpperHalfPlane) =>
        ((t-p.1:ℝ):ℂ))).mul (literalForcing_continuous q (physicalRate q branch) a)
  · exact (by fun_prop : Continuous (fun u : ℝ => ((t-u:ℝ):ℂ))).smul
      (causalCuspSourceVector_continuous q branch a)
  · intro u
    filter_upwards [Lp.coeFn_smul ((t-u:ℝ):ℂ) (causalCuspSourceVector q branch a u),
      causalCuspSourceVector_native_forcing_ae q branch a u] with z h0 h1
    rw [h0]
    simp only [Pi.smul_apply,smul_eq_mul,h1]
  · exact (nativeJointIntegratedForcing_memLp q (physicalRate q branch) a t).coeFn_toLp

/-- The actual native residual satisfies the original bounded causal Volterra equation,
with the complete original physical source. -/
theorem nativeJointResidual_bochner_covariance_equation (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (t : ℝ) :
    formEmbeddingCovariance jointEmbedding (nativeJointResidual q (physicalRate q branch) a t)+
      (1-formEmbeddingCovariance jointEmbedding)
        (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • nativeJointResidual q (physicalRate q branch) a u) =
      formEmbeddingCovariance jointEmbedding
        (∫ u in (0:ℝ)..t, ((t-u:ℝ):ℂ) • causalCuspSourceVector q branch a u) := by
  have h := nativeJointResidual_covariance_equation q (physicalRate q branch) a t
  rw [nativeJointTimePrimitive_eq_bochner,nativeJointIntegratedForcing_eq_bochner] at h
  exact h

end
end RHTower.D4BMNativeResponse
