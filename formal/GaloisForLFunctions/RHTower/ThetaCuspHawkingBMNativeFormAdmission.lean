import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeFormBound
import GaloisForLFunctions.HTGeometry.WeakLimitBoundedFamily
import Mathlib.Analysis.InnerProductSpace.Adjoint
open MeasureTheory Set Filter Topology
open scoped TensorProduct ComplexConjugate
namespace RHTower.D4BMNativeResponse
open D4BMJointWave D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


private theorem bochner_product_value {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (h : Lp (Lp ℂ 2 ν) 2 μ) (F : α × β → ℂ) (hF : MemLp F 2 (μ.prod ν))
    (hr : ∀ᵐ x ∂μ, (h x : β → ℂ) =ᵐ[ν] fun y => F (x,y)) :
    bochnerL2ProductEquiv h = hF.toLp F := by
  have hp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
      inner ℂ (l2SeparatedProduct f g) (bochnerL2ProductEquiv h) =
      inner ℂ (l2SeparatedProduct f g) (hF.toLp F) := by
    rw [← bochnerL2ProductEquiv_pure f g,bochnerL2ProductEquiv.inner_map_map]
    rw [bochnerL2ProductEquiv_pure,L2.inner_def,L2.inner_def]
    have he : (fun p => inner ℂ (l2SeparatedProduct f g p) (hF.toLp F p)) =ᵐ[μ.prod ν]
        fun p => conj (f p.1)*conj (g p.2)*F p := by
      filter_upwards [l2SeparatedProduct_ae f g,hF.coeFn_toLp] with p h0 h1
      rw [h0,h1]
      simp only [l2SeparatedFun,RCLike.inner_apply,map_mul]
      ring
    have hi := (L2.integrable_inner (𝕜 := ℂ) (l2SeparatedProduct f g) (hF.toLp F)).congr he
    rw [integral_congr_ae he,integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [hr,bochnerL2Product_ae f g] with x hx hg
    rw [hg,inner_smul_left,L2.inner_def,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hx] with y hy
    rw [hy]
    simp only [RCLike.inner_apply]
    ring
  apply ext_inner_left ℂ
  intro y
  apply DenseRange.induction_on (p := fun y => inner ℂ y (bochnerL2ProductEquiv h) = inner ℂ y (hF.toLp F))
    l2TensorToProduct_denseRange y
    (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const))
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f g => simpa only [l2TensorToProduct_tmul] using hp f g
  | add z w hz hw => simp only [map_add,inner_add_left,hz,hw]

private theorem cutoff_literal_mem (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    MemLp (fun p : ℝ × UpperHalfPlane => modularCuspCutoff ((n:ℝ)+1) p.2*
      nativeJointTimePrimitiveField q s amplitude t p) 2 (radialMeasure.prod D4BMModularCore.measure) := by
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  have he := (modularCuspCutoff_smooth _ hN).continuous.comp
    (continuous_snd : Continuous (fun p : ℝ × UpperHalfPlane => p.2))
  have hw := nativeJointTimePrimitiveField_memLp q s amplitude t
  apply hw.norm.mono' (he.aestronglyMeasurable.mul hw.aestronglyMeasurable)
  apply Eventually.of_forall
  intro p
  change ‖modularCuspCutoff ((n:ℝ)+1) p.2*nativeJointTimePrimitiveField q s amplitude t p‖ ≤
    ‖nativeJointTimePrimitiveField q s amplitude t p‖
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (modularCuspCutoff_norm_le_one _ p.2) (norm_nonneg _)

/-- The value projection of the admitted cusp-cutoff graph is the actual original-product L² field. -/
theorem nativeCuspJointGraph_value (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) (n : ℕ) :
    nativeCuspJointGraph q s amplitude t n 0 =
      (cutoff_literal_mem q s amplitude t n).toLp (fun p : ℝ × UpperHalfPlane =>
        modularCuspCutoff ((n:ℝ)+1) p.2*nativeJointTimePrimitiveField q s amplitude t p) := by
  have hm := (nativeTimePrimitiveAngularEnergy_continuous q s amplitude t n).memLp_of_hasCompactSupport
    (p := 2) (μ := radialMeasure) (nativeTimePrimitiveAngularEnergy_compact q s amplitude t n)
  change bochnerL2ProductEquiv ((angularEnergySlot 0).compLp
    (hm.toLp (nativeTimePrimitiveAngularEnergy q s amplitude t n))) = _
  apply bochner_product_value
  filter_upwards [(angularEnergySlot 0).coeFn_compLp
    (hm.toLp (nativeTimePrimitiveAngularEnergy q s amplitude t n)),hm.coeFn_toLp] with x h0 h1
  rw [h0,h1]
  change (fieldVector (nativeTimePrimitiveCutoff q s amplitude t x n 0) : UpperHalfPlane → ℂ) =ᵐ[D4BMModularCore.measure] _
  let f := nativeTimePrimitiveCutoff q s amplitude t x n 0
  filter_upwards [(core_field_memLp f.field f.smooth f.compact).coeFn_toLp,
    ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz hfd
  change fieldVector f z = f.field z at hz
  rw [hz]
  change modularCuspCutoff ((n:ℝ)+1) z^(0+1)*globalNativeTimePrimitive q s amplitude t x z = _
  rw [(globalNativeTimePrimitive_germ q s amplitude t x z hfd).eq_of_nhds]
  simp only [Nat.zero_add,pow_one,nativeJointTimePrimitiveField]

/-- The original value projections converge strongly to the literal untruncated native primitive. -/
theorem nativeCuspJointGraph_value_tendsto (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    Tendsto (fun n => nativeCuspJointGraph q s amplitude t n 0) atTop
      (𝓝 ((nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t))) := by
  let W := nativeJointTimePrimitiveField q s amplitude t
  let F (n : ℕ) (p : ℝ × UpperHalfPlane) := modularCuspCutoff ((n:ℝ)+1) p.2*W p
  have hw := nativeJointTimePrimitiveField_memLp q s amplitude t
  have hf (n : ℕ) := cutoff_literal_mem q s amplitude t n
  have hl : Tendsto (fun n => ∫ p, ‖F n p-W p‖^(2 : ℕ)
      ∂radialMeasure.prod D4BMModularCore.measure) atTop (𝓝 0) := by
    have hc := tendsto_integral_of_dominated_convergence (f := fun _ => (0:ℝ)) (fun p => 4*‖W p‖^(2 : ℕ))
      (fun n => ((hf n).sub hw).aestronglyMeasurable.norm.pow 2)
      (hw.norm.integrable_sq.const_mul 4)
    have hb (n : ℕ) : ∀ᵐ p ∂radialMeasure.prod D4BMModularCore.measure,
        ‖‖F n p-W p‖^(2 : ℕ)‖ ≤ 4*‖W p‖^(2 : ℕ) := by
      apply Eventually.of_forall
      intro p
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hh : ‖F n p-W p‖ ≤ 2*‖W p‖ := by
        have hm := mul_le_mul_of_nonneg_right (modularCuspCutoff_norm_le_one ((n:ℝ)+1) p.2) (norm_nonneg (W p))
        have hn := norm_sub_le (F n p) (W p)
        change ‖modularCuspCutoff ((n:ℝ)+1) p.2*W p-W p‖ ≤ _
        dsimp only [F] at hn
        rw [norm_mul] at hn
        linarith
      have hh' := pow_le_pow_left₀ (norm_nonneg _) hh 2
      nlinarith
    have hp : ∀ᵐ p ∂radialMeasure.prod D4BMModularCore.measure,
        Tendsto (fun n => ‖F n p-W p‖^(2 : ℕ)) atTop (𝓝 (0:ℝ)) := by
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)] with p hfd
      apply tendsto_const_nhds.congr'
      filter_upwards [modularCuspCutoff_eventually_one p.2 hfd] with n hn
      dsimp only [F]
      rw [hn.eq_of_nhds,one_mul,sub_self,norm_zero,zero_pow (Nat.succ_ne_zero 1)]
    simpa only [integral_zero,Pi.pow_apply,Pi.sub_apply,F,W] using hc hb hp
  have hn (n : ℕ) :
      ‖nativeCuspJointGraph q s amplitude t n 0-hw.toLp W‖^(2 : ℕ) =
        ∫ p, ‖F n p-W p‖^(2 : ℕ) ∂radialMeasure.prod D4BMModularCore.measure := by
    rw [nativeCuspJointGraph_value,← MemLp.toLp_sub,_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [((hf n).sub hw).coeFn_toLp] with p hp
    rw [hp]
    rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun n => ‖nativeCuspJointGraph q s amplitude t n 0-hw.toLp W‖^(2 : ℕ)) atTop (𝓝 0) := by
    simpa only [hn] using hl
  have h := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _)] using h

private theorem bounded_admission {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (J : E →L[ℂ] F) (hJ : Function.Injective J) (u : ℕ → E) (M : ℝ)
    (hM : ∀ n, ‖u n‖ ≤ M) (w : F)
    (ht : Tendsto (fun n => J (u n)) atTop (𝓝 w)) :
    ∃ v : E, J v = w ∧ ‖v‖ ≤ M := by
  have hd : Dense (J.adjoint.range : Set E) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    rw [← J.orthogonal_ker,show J.ker = ⊥ from LinearMap.ker_eq_bot.mpr hJ,
      Submodule.bot_orthogonal_eq_top]
  obtain ⟨v,hv,hw⟩ := exists_weakLimit_of_bounded hM hd (by
    rintro φ ⟨ψ,rfl⟩
    refine ⟨inner ℂ w ψ,?_⟩
    have hψ : Tendsto (fun n => inner ℂ (J (u n)) ψ) atTop (𝓝 (inner ℂ w ψ)) :=
      ht.inner (𝕜 := ℂ) tendsto_const_nhds
    exact hψ.congr (fun n => (J.adjoint_inner_right (u n) ψ).symm))
  refine ⟨v,?_,hv⟩
  apply ext_inner_right ℂ
  intro ψ
  have hh := hw (J.adjoint ψ)
  simp only [J.adjoint_inner_right] at hh
  exact tendsto_nhds_unique hh (ht.inner (𝕜 := ℂ) tendsto_const_nhds)


/-- The literal untruncated native primitive belongs to the ORIGINAL joint form domain through its original value embedding. -/
theorem nativeJointTimePrimitive_form_admission (q : XiZeroCopy) (s amplitude : ℂ) (t : ℝ) :
    ∃ v : jointDomain, jointEmbedding v =
      (nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t) := by
  obtain ⟨M,hM⟩ := nativeCuspJointGraph_bounded q s amplitude t
  let u (n : ℕ) : jointDomain :=
    ⟨nativeCuspJointGraph q s amplitude t n,nativeCuspJointGraph_mem q s amplitude t n⟩
  have hu : ∀ n, ‖u n‖ ≤ M := hM
  have ht : Tendsto (fun n => jointEmbedding (u n)) atTop
      (𝓝 ((nativeJointTimePrimitiveField_memLp q s amplitude t).toLp
        (nativeJointTimePrimitiveField q s amplitude t))) :=
    nativeCuspJointGraph_value_tendsto q s amplitude t
  obtain ⟨v,hv,_⟩ := bounded_admission jointEmbedding jointEmbedding_injective u M hu _ ht
  exact ⟨v,hv⟩

end
end RHTower.D4BMNativeResponse
