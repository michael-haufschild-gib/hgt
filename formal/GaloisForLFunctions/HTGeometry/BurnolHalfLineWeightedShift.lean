import GaloisForLFunctions.HTGeometry.BurnolDepthCompletion
import GaloisForLFunctions.HTGeometry.HalfLineExponentialGram
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel

/-!
# Weighted shifts on the Burnol half-line

On `H = L²((0,∞))` let `(S_h f)(t) = f(t+h)` be the left shift, `(T_h g)(s) = 1_{s>h} g(s-h)` the
right shift and `M_w` multiplication by a bounded weight.  The weighted shift
`K_h = M_{t/(t+h)} S_h`, `(K_h f)(t) = t/(t+h) f(t+h)`, is a contraction semigroup
`K_h K_j = K_{h+j}` with eigenfeatures `K_h (t e^{-λt}) = e^{-hλ} t e^{-λt}` and adjoint
`(K_h^* g)(s) = 1_{s>h} (s-h)/s g(s-h)`.  For `h > 0` both `K_h` and `K_h^*` strictly decrease the
norm of every nonzero vector.  Features `t e^{-λt}` at distinct positive rates are linearly
independent.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

/-! ## Translations of the half-line measure -/

theorem measurePreserving_add_right_Ioi (h : ℝ) :
    MeasurePreserving (fun t : ℝ => t + h) (volume.restrict (Ioi 0)) (volume.restrict (Ioi h)) := by
  have := (measurePreserving_add_right volume h).restrict_preimage_emb
    (measurableEmbedding_addRight h) (Ioi h)
  rwa [preimage_add_const_Ioi, sub_self] at this

theorem measurePreserving_sub_right_Ioi (h : ℝ) :
    MeasurePreserving (fun s : ℝ => s - h) (volume.restrict (Ioi h)) (volume.restrict (Ioi 0)) := by
  have := (measurePreserving_sub_right volume h).restrict_preimage_emb
    (measurableEmbedding_subRight h) (Ioi 0)
  rwa [preimage_sub_const_Ioi, zero_add] at this

theorem restrict_Ioi_le_restrict_Ioi_zero {h : ℝ} (hh : 0 ≤ h) :
    volume.restrict (Ioi h) ≤ volume.restrict (Ioi (0 : ℝ)) :=
  Measure.restrict_mono (Ioi_subset_Ioi hh) le_rfl

theorem quasiMeasurePreserving_add_right_Ioi {h : ℝ} (hh : 0 ≤ h) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => t + h) (volume.restrict (Ioi 0))
      (volume.restrict (Ioi 0)) :=
  ⟨(measurePreserving_add_right_Ioi h).measurable, by
    rw [(measurePreserving_add_right_Ioi h).map_eq]
    exact Measure.absolutelyContinuous_of_le (restrict_Ioi_le_restrict_Ioi_zero hh)⟩

theorem restrict_Ioi_zero_restrict_Ioi {h : ℝ} (hh : 0 ≤ h) :
    (volume.restrict (Ioi (0 : ℝ))).restrict (Ioi h) = volume.restrict (Ioi h) := by
  rw [Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hh]

/-! ## Weighted left shifts -/

/-- The function-level weighted left shift `t ↦ w t * f (t + h)`. -/
def weightedLeftShiftFun (h : ℝ) (w f : ℝ → ℂ) (t : ℝ) : ℂ := w t * f (t + h)

variable {h : ℝ} {w : ℝ → ℂ}

theorem memLp_weightedLeftShiftFun (hh : 0 ≤ h) (hw : Measurable w)
    (hw1 : ∀ t, 0 < t → ‖w t‖ ≤ 1) {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioi 0))) :
    MemLp (weightedLeftShiftFun h w f) 2 (volume.restrict (Ioi 0)) := by
  have hc : MemLp (f ∘ fun t => t + h) 2 (volume.restrict (Ioi 0)) :=
    (hf.mono_measure (restrict_Ioi_le_restrict_Ioi_zero hh)).comp_measurePreserving
      (measurePreserving_add_right_Ioi h)
  refine hc.of_le (hw.aestronglyMeasurable.mul hc.1) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [weightedLeftShiftFun, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw1 t ht)

theorem eLpNorm_weightedLeftShiftFun_le (hh : 0 ≤ h) (hw1 : ∀ t, 0 < t → ‖w t‖ ≤ 1) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi 0))) :
    eLpNorm (weightedLeftShiftFun h w f) 2 (volume.restrict (Ioi 0)) ≤
      eLpNorm f 2 (volume.restrict (Ioi 0)) := by
  calc eLpNorm (weightedLeftShiftFun h w f) 2 (volume.restrict (Ioi 0))
      ≤ eLpNorm (f ∘ fun t => t + h) 2 (volume.restrict (Ioi 0)) := by
        refine eLpNorm_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [weightedLeftShiftFun, norm_mul, Function.comp_apply]
        exact mul_le_of_le_one_left (norm_nonneg _) (hw1 t ht)
    _ = eLpNorm f 2 (volume.restrict (Ioi h)) :=
        eLpNorm_comp_measurePreserving
          (hf.1.mono_measure (restrict_Ioi_le_restrict_Ioi_zero hh))
          (measurePreserving_add_right_Ioi h)
    _ ≤ eLpNorm f 2 (volume.restrict (Ioi 0)) :=
        eLpNorm_mono_measure f (restrict_Ioi_le_restrict_Ioi_zero hh)

theorem weightedLeftShiftFun_congr (hh : 0 ≤ h) {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume.restrict (Ioi 0)] g) :
    weightedLeftShiftFun h w f =ᵐ[volume.restrict (Ioi 0)] weightedLeftShiftFun h w g := by
  filter_upwards [(quasiMeasurePreserving_add_right_Ioi hh).ae_eq_comp hfg] with t ht
  simp only [Function.comp_apply] at ht
  rw [weightedLeftShiftFun, weightedLeftShiftFun, ht]

/-- The weighted left shift `(W f)(t) = w(t) f(t+h)` on `L²((0,∞))`, a contraction. -/
def weightedLeftShift (h : ℝ≥0) (w : ℝ → ℂ) (hw : Measurable w) (hw1 : ∀ t, 0 < t → ‖w t‖ ≤ 1) :
    BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_weightedLeftShiftFun h.coe_nonneg hw hw1 (Lp.memLp f)).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [weightedLeftShiftFun_congr (w := w) h.coe_nonneg (Lp.coeFn_add f g)] with t ht
        rw [ht]
        simp only [weightedLeftShiftFun, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [weightedLeftShiftFun_congr (w := w) h.coe_nonneg (Lp.coeFn_smul c f)] with t ht
        rw [ht]
        simp only [weightedLeftShiftFun, Pi.smul_apply, smul_eq_mul]
        ring }
    1 fun f => by
      rw [one_mul]
      change ‖(memLp_weightedLeftShiftFun h.coe_nonneg hw hw1 (Lp.memLp f)).toLp
        (weightedLeftShiftFun h w f)‖ ≤ ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_weightedLeftShiftFun_le h.coe_nonneg hw1 (Lp.memLp f))

theorem weightedLeftShift_coeFn (h : ℝ≥0) (hw : Measurable w) (hw1 : ∀ t, 0 < t → ‖w t‖ ≤ 1)
    (f : BurnolHalfLineL2) :
    (weightedLeftShift h w hw hw1 f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => w t * (f : ℝ → ℂ) (t + h) :=
  MemLp.coeFn_toLp (memLp_weightedLeftShiftFun h.coe_nonneg hw hw1 (Lp.memLp f))

theorem norm_weightedLeftShift_le (h : ℝ≥0) (hw : Measurable w)
    (hw1 : ∀ t, 0 < t → ‖w t‖ ≤ 1) : ‖weightedLeftShift h w hw hw1‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## The right shift -/

/-- The function-level right shift `s ↦ 1_{s>h} g(s-h)`. -/
def rightShiftFun (h : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := (Ioi h).indicator fun s => g (s - h)

theorem memLp_rightShiftFun (hh : 0 ≤ h) {g : ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (Ioi 0))) :
    MemLp (rightShiftFun h g) 2 (volume.restrict (Ioi 0)) := by
  rw [rightShiftFun, memLp_indicator_iff_restrict measurableSet_Ioi,
    restrict_Ioi_zero_restrict_Ioi hh]
  exact hg.comp_measurePreserving (measurePreserving_sub_right_Ioi h)

theorem eLpNorm_rightShiftFun (hh : 0 ≤ h) {g : ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (Ioi 0))) :
    eLpNorm (rightShiftFun h g) 2 (volume.restrict (Ioi 0)) =
      eLpNorm g 2 (volume.restrict (Ioi 0)) := by
  rw [rightShiftFun, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi,
    restrict_Ioi_zero_restrict_Ioi hh]
  exact eLpNorm_comp_measurePreserving hg.1 (measurePreserving_sub_right_Ioi h)

theorem rightShiftFun_congr (hh : 0 ≤ h) {f g : ℝ → ℂ} (hfg : f =ᵐ[volume.restrict (Ioi 0)] g) :
    rightShiftFun h f =ᵐ[volume.restrict (Ioi 0)] rightShiftFun h g := by
  refine (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioi).1 ?_
  rw [restrict_Ioi_zero_restrict_Ioi hh]
  exact (measurePreserving_sub_right_Ioi h).quasiMeasurePreserving.ae_eq_comp hfg

/-- The right shift `(T_h g)(s) = 1_{s>h} g(s-h)` on `L²((0,∞))`, an isometry. -/
def burnolRightShift (h : ℝ≥0) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  LinearMap.mkContinuous
    { toFun := fun g => (memLp_rightShiftFun h.coe_nonneg (Lp.memLp g)).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [rightShiftFun_congr h.coe_nonneg (Lp.coeFn_add f g)] with t ht
        rw [ht]
        by_cases hmem : t ∈ Ioi (h : ℝ) <;> simp [rightShiftFun, hmem]
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [rightShiftFun_congr h.coe_nonneg (Lp.coeFn_smul c f)] with t ht
        rw [ht]
        by_cases hmem : t ∈ Ioi (h : ℝ) <;> simp [rightShiftFun, hmem] }
    1 fun g => by
      rw [one_mul]
      change ‖(memLp_rightShiftFun h.coe_nonneg (Lp.memLp g)).toLp (rightShiftFun h g)‖ ≤ ‖g‖
      rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_rightShiftFun h.coe_nonneg (Lp.memLp g)]

theorem burnolRightShift_coeFn (h : ℝ≥0) (g : BurnolHalfLineL2) :
    (burnolRightShift h g : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      rightShiftFun h (g : ℝ → ℂ) :=
  MemLp.coeFn_toLp (memLp_rightShiftFun h.coe_nonneg (Lp.memLp g))

theorem norm_burnolRightShift_apply (h : ℝ≥0) (g : BurnolHalfLineL2) :
    ‖burnolRightShift h g‖ = ‖g‖ := by
  change ‖(memLp_rightShiftFun h.coe_nonneg (Lp.memLp g)).toLp (rightShiftFun h g)‖ = ‖g‖
  rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_rightShiftFun h.coe_nonneg (Lp.memLp g)]

/-! ## The weighted shift `K_h` -/

/-- The weight `t/(t+h)`. -/
def halfLineShiftWeight (h : ℝ) (t : ℝ) : ℂ := ((t / (t + h) : ℝ) : ℂ)

theorem measurable_halfLineShiftWeight (h : ℝ) : Measurable (halfLineShiftWeight h) := by
  unfold halfLineShiftWeight
  fun_prop

theorem norm_halfLineShiftWeight_le (hh : 0 ≤ h) (t : ℝ) (ht : 0 < t) :
    ‖halfLineShiftWeight h t‖ ≤ 1 := by
  rw [halfLineShiftWeight, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).2 (by linarith)

theorem norm_one_weight_le (t : ℝ) (_ : 0 < t) : ‖(1 : ℂ)‖ ≤ 1 := by simp

/-- The left shift `(S_h f)(t) = f(t+h)`. -/
def burnolLeftShift (h : ℝ≥0) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  weightedLeftShift h (fun _ => 1) measurable_const norm_one_weight_le

/-- Multiplication by the weight `t/(t+h)`. -/
def halfLineShiftWeightMul (h : ℝ≥0) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  weightedLeftShift 0 (halfLineShiftWeight h) (measurable_halfLineShiftWeight h)
    (norm_halfLineShiftWeight_le h.coe_nonneg)

/-- The weighted shift `(K_h f)(t) = t/(t+h) f(t+h)`. -/
def burnolWeightedShift (h : ℝ≥0) : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2 :=
  weightedLeftShift h (halfLineShiftWeight h) (measurable_halfLineShiftWeight h)
    (norm_halfLineShiftWeight_le h.coe_nonneg)

theorem burnolWeightedShift_coeFn (h : ℝ≥0) (f : BurnolHalfLineL2) :
    (burnolWeightedShift h f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => ((t / (t + h) : ℝ) : ℂ) * (f : ℝ → ℂ) (t + h) :=
  weightedLeftShift_coeFn _ _ _ f

theorem burnolLeftShift_coeFn (h : ℝ≥0) (f : BurnolHalfLineL2) :
    (burnolLeftShift h f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] fun t => (f : ℝ → ℂ) (t + h) := by
  filter_upwards [weightedLeftShift_coeFn (w := fun _ => (1 : ℂ)) h measurable_const
    norm_one_weight_le f] with t ht
  rw [burnolLeftShift, ht, one_mul]

theorem halfLineShiftWeightMul_coeFn (h : ℝ≥0) (f : BurnolHalfLineL2) :
    (halfLineShiftWeightMul h f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => ((t / (t + h) : ℝ) : ℂ) * (f : ℝ → ℂ) t := by
  filter_upwards [weightedLeftShift_coeFn (w := halfLineShiftWeight h) 0
    (measurable_halfLineShiftWeight h) (norm_halfLineShiftWeight_le h.coe_nonneg) f] with t ht
  rw [halfLineShiftWeightMul, ht, NNReal.coe_zero, add_zero]
  rfl

theorem norm_burnolWeightedShift_le (h : ℝ≥0) : ‖burnolWeightedShift h‖ ≤ 1 :=
  norm_weightedLeftShift_le _ _ _

/-- `K_h = M_{t/(t+h)} S_h`. -/
theorem burnolWeightedShift_eq_comp (h : ℝ≥0) :
    burnolWeightedShift h = halfLineShiftWeightMul h ∘L burnolLeftShift h := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [burnolWeightedShift_coeFn h f, halfLineShiftWeightMul_coeFn h (burnolLeftShift h f),
    burnolLeftShift_coeFn h f] with t h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, h1, h2, h3]

/-- **Semigroup law.**  `K_h K_j = K_{h+j}`. -/
theorem burnolWeightedShift_comp (h j : ℝ≥0) :
    burnolWeightedShift h ∘L burnolWeightedShift j = burnolWeightedShift (h + j) := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  have h2 := (quasiMeasurePreserving_add_right_Ioi h.coe_nonneg).ae_eq_comp (burnolWeightedShift_coeFn j f)
  filter_upwards [burnolWeightedShift_coeFn h (burnolWeightedShift j f), h2,
    burnolWeightedShift_coeFn (h + j) f, ae_restrict_mem measurableSet_Ioi] with t e1 e2 e3 ht
  simp only [Function.comp_apply] at e2
  rw [ContinuousLinearMap.comp_apply, e1, e3, e2, NNReal.coe_add, add_assoc]
  have ht' : (0 : ℝ) < t := ht
  have hh : (0 : ℝ) ≤ h := h.coe_nonneg
  have hj : (0 : ℝ) ≤ j := j.coe_nonneg
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  field_simp

/-- **Eigenfeatures.**  `K_h (t e^{-(n+1)ℓt}) = e^{-h(n+1)ℓ} t e^{-(n+1)ℓt}`. -/
theorem burnolWeightedShift_depthFeature (h : ℝ≥0) (ell : Ioi (0 : ℝ)) (n : ℕ) :
    burnolWeightedShift h (burnolDepthFeatureL2 ell n) =
      ((Real.exp (-(h * ((n + 1 : ℝ) * ell))) : ℝ) : ℂ) • burnolDepthFeatureL2 ell n := by
  refine Lp.ext ?_
  have h2 := (quasiMeasurePreserving_add_right_Ioi h.coe_nonneg).ae_eq_comp (burnolDepthFeatureL2_ae ell n)
  filter_upwards [burnolWeightedShift_coeFn h (burnolDepthFeatureL2 ell n), h2,
    Lp.coeFn_smul ((Real.exp (-(h * ((n + 1 : ℝ) * ell))) : ℝ) : ℂ) (burnolDepthFeatureL2 ell n),
    burnolDepthFeatureL2_ae ell n, ae_restrict_mem measurableSet_Ioi] with t e1 e2 e3 e4 ht
  simp only [Function.comp_apply] at e2
  rw [e1, e2, e3, Pi.smul_apply, e4, smul_eq_mul]
  have ht' : (0 : ℝ) < t := ht
  have hh : (0 : ℝ) ≤ h := h.coe_nonneg
  simp only [burnolDepthFeature]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [show -((n + 1 : ℝ) * ell * (t + h)) = -(h * ((n + 1 : ℝ) * ell)) + -((n + 1 : ℝ) * ell * t)
    by ring, Real.exp_add]
  field_simp

/-! ## Adjoints -/

theorem adjoint_burnolLeftShift (h : ℝ≥0) :
    ContinuousLinearMap.adjoint (burnolLeftShift h) = burnolRightShift h := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun g f => ?_).symm
  rw [L2.inner_def, L2.inner_def]
  have hR : ∫ s, ⟪(g : ℝ → ℂ) s, (burnolLeftShift h f : ℝ → ℂ) s⟫_ℂ ∂(volume.restrict (Ioi 0)) =
      ∫ s, ⟪(g : ℝ → ℂ) s, (f : ℝ → ℂ) (s + h)⟫_ℂ ∂(volume.restrict (Ioi 0)) :=
    integral_congr_ae (by
      filter_upwards [burnolLeftShift_coeFn h f] with s hs
      rw [hs])
  have hL : ∫ s, ⟪(burnolRightShift h g : ℝ → ℂ) s, (f : ℝ → ℂ) s⟫_ℂ
      ∂(volume.restrict (Ioi 0)) =
      ∫ s in Ioi (h : ℝ), ⟪(g : ℝ → ℂ) (s - h), (f : ℝ → ℂ) s⟫_ℂ := by
    have e1 : ∫ s in Ioi (h : ℝ), ⟪(g : ℝ → ℂ) (s - h), (f : ℝ → ℂ) s⟫_ℂ =
        ∫ s, (Ioi (h : ℝ)).indicator (fun s => ⟪(g : ℝ → ℂ) (s - h), (f : ℝ → ℂ) s⟫_ℂ) s
          ∂(volume.restrict (Ioi 0)) := by
      rw [integral_indicator measurableSet_Ioi, restrict_Ioi_zero_restrict_Ioi h.coe_nonneg]
    rw [e1]
    refine integral_congr_ae ?_
    filter_upwards [burnolRightShift_coeFn h g] with s hs
    rw [hs]
    by_cases hmem : s ∈ Ioi (h : ℝ) <;> simp [rightShiftFun, hmem]
  rw [hL, hR]
  have hmp := (measurePreserving_add_right_Ioi (h : ℝ)).integral_comp
    (measurableEmbedding_addRight (h : ℝ)) (fun s => ⟪(g : ℝ → ℂ) (s - h), (f : ℝ → ℂ) s⟫_ℂ)
  simp only [add_sub_cancel_right] at hmp
  exact hmp.symm

theorem adjoint_halfLineShiftWeightMul (h : ℝ≥0) :
    ContinuousLinearMap.adjoint (halfLineShiftWeightMul h) = halfLineShiftWeightMul h := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun g f => ?_).symm
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [halfLineShiftWeightMul_coeFn h f, halfLineShiftWeightMul_coeFn h g] with s hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- **The adjoint.**  `K_h^* = T_h M_{t/(t+h)}`, i.e. `(K_h^* g)(s) = 1_{s>h} (s-h)/s g(s-h)`. -/
theorem adjoint_burnolWeightedShift (h : ℝ≥0) :
    ContinuousLinearMap.adjoint (burnolWeightedShift h) =
      burnolRightShift h ∘L halfLineShiftWeightMul h := by
  rw [burnolWeightedShift_eq_comp, ContinuousLinearMap.adjoint_comp, adjoint_burnolLeftShift,
    adjoint_halfLineShiftWeightMul]

theorem adjoint_burnolWeightedShift_coeFn (h : ℝ≥0) (g : BurnolHalfLineL2) :
    (ContinuousLinearMap.adjoint (burnolWeightedShift h) g : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      (Ioi (h : ℝ)).indicator fun s => (((s - h) / s : ℝ) : ℂ) * (g : ℝ → ℂ) (s - h) := by
  rw [adjoint_burnolWeightedShift, ContinuousLinearMap.comp_apply]
  refine (burnolRightShift_coeFn h _).trans ?_
  refine (rightShiftFun_congr h.coe_nonneg (halfLineShiftWeightMul_coeFn h g)).trans ?_
  refine Eventually.of_forall fun s => ?_
  by_cases hmem : s ∈ Ioi (h : ℝ)
  · simp only [rightShiftFun, indicator_of_mem hmem, sub_add_cancel]
  · simp only [rightShiftFun, indicator_of_notMem hmem]

/-! ## Strict norm decrease -/

theorem norm_sq_burnolWeightedShift (h : ℝ≥0) (f : BurnolHalfLineL2) :
    ‖burnolWeightedShift h f‖ ^ 2 =
      ∫ s in Ioi (h : ℝ), ((s - h) / s) ^ 2 * ‖(f : ℝ → ℂ) s‖ ^ 2 := by
  rw [Lp_two_norm_sq_eq_integral]
  have h1 : ∫ t, ‖(burnolWeightedShift h f : ℝ → ℂ) t‖ ^ 2 ∂(volume.restrict (Ioi 0)) =
      ∫ t, ((t / (t + h)) ^ 2 * ‖(f : ℝ → ℂ) (t + h)‖ ^ 2) ∂(volume.restrict (Ioi 0)) :=
    integral_congr_ae (by
      filter_upwards [burnolWeightedShift_coeFn h f, ae_restrict_mem measurableSet_Ioi] with t ht htp
      have htp' : (0 : ℝ) < t := htp
      rw [ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow])
  rw [h1]
  have hmp := (measurePreserving_add_right_Ioi (h : ℝ)).integral_comp
    (measurableEmbedding_addRight (h : ℝ)) (fun s => ((s - h) / s) ^ 2 * ‖(f : ℝ → ℂ) s‖ ^ 2)
  simp only [add_sub_cancel_right] at hmp
  exact hmp

theorem norm_sq_adjoint_burnolWeightedShift (h : ℝ≥0) (g : BurnolHalfLineL2) :
    ‖ContinuousLinearMap.adjoint (burnolWeightedShift h) g‖ ^ 2 =
      ∫ t in Ioi (0 : ℝ), (t / (t + h)) ^ 2 * ‖(g : ℝ → ℂ) t‖ ^ 2 := by
  rw [Lp_two_norm_sq_eq_integral]
  have h1 : ∫ s, ‖(ContinuousLinearMap.adjoint (burnolWeightedShift h) g : ℝ → ℂ) s‖ ^ 2
      ∂(volume.restrict (Ioi 0)) =
      ∫ s, (Ioi (h : ℝ)).indicator (fun s => ((s - h) / s) ^ 2 * ‖(g : ℝ → ℂ) (s - h)‖ ^ 2) s
        ∂(volume.restrict (Ioi 0)) :=
    integral_congr_ae (by
      filter_upwards [adjoint_burnolWeightedShift_coeFn h g] with s hs
      rw [hs]
      by_cases hmem : s ∈ Ioi (h : ℝ)
      · have hs0 : (0 : ℝ) ≤ (s - h) / s := div_nonneg (by linarith [mem_Ioi.1 hmem])
          (by linarith [mem_Ioi.1 hmem, h.coe_nonneg])
        simp only [indicator_of_mem hmem, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hs0, mul_pow]
      · simp only [indicator_of_notMem hmem, norm_zero, zero_pow two_ne_zero])
  rw [h1, integral_indicator measurableSet_Ioi, restrict_Ioi_zero_restrict_Ioi h.coe_nonneg]
  have hmp := (measurePreserving_add_right_Ioi (h : ℝ)).integral_comp
    (measurableEmbedding_addRight (h : ℝ))
    (fun s => ((s - h) / s) ^ 2 * ‖(g : ℝ → ℂ) (s - h)‖ ^ 2)
  simp only [add_sub_cancel_right] at hmp
  rw [← hmp]

theorem integrable_norm_sq_burnol (f : BurnolHalfLineL2) :
    Integrable (fun s => ‖(f : ℝ → ℂ) s‖ ^ 2) (volume.restrict (Ioi 0)) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)

theorem eq_zero_of_integral_weight_mul_norm_sq {φ : ℝ → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ s, 0 < s → 0 < φ s) (hφ1 : ∀ s, 0 < s → φ s ≤ 1) (f : BurnolHalfLineL2)
    (hint : ∫ s in Ioi (0 : ℝ), φ s * ‖(f : ℝ → ℂ) s‖ ^ 2 = 0) : f = 0 := by
  have hint' : Integrable (fun s => φ s * ‖(f : ℝ → ℂ) s‖ ^ 2) (volume.restrict (Ioi 0)) := by
    refine (integrable_norm_sq_burnol f).mono' (hφm.aestronglyMeasurable.mul
      (integrable_norm_sq_burnol f).1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφ0 s hs).le (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (hφ1 s hs)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun s => φ s * ‖(f : ℝ → ℂ) s‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (hφ0 s hs).le (sq_nonneg _)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint').1 hint
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with s hs hsp
  have := (mul_eq_zero.1 hs).resolve_left (hφ0 s hsp).ne'
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- **Strict decrease for `K_h`.**  For `h > 0`, `‖K_h f‖ < ‖f‖` whenever `f ≠ 0`. -/
theorem norm_burnolWeightedShift_lt {h : ℝ≥0} (hh : 0 < h) {f : BurnolHalfLineL2} (hf : f ≠ 0) :
    ‖burnolWeightedShift h f‖ < ‖f‖ := by
  have hh' : (0 : ℝ) < h := hh
  set φ : ℝ → ℝ := fun s => 1 - (Ioi (h : ℝ)).indicator (fun s => ((s - h) / s) ^ 2) s
  have hφm : Measurable φ := by
    refine measurable_const.sub (Measurable.indicator ?_ measurableSet_Ioi)
    fun_prop
  have hφ0 : ∀ s, 0 < s → 0 < φ s := fun s hs => by
    simp only [φ]
    by_cases hmem : s ∈ Ioi (h : ℝ)
    · rw [indicator_of_mem hmem, sub_pos]
      have h1 : 0 ≤ (s - h) / s := div_nonneg (by linarith [mem_Ioi.1 hmem]) hs.le
      have h2 : (s - h) / s < 1 := (div_lt_one hs).2 (by linarith)
      nlinarith
    · rw [indicator_of_notMem hmem]
      norm_num
  have hφ1 : ∀ s, 0 < s → φ s ≤ 1 := fun s _ => by
    simp only [φ]
    by_cases hmem : s ∈ Ioi (h : ℝ)
    · rw [indicator_of_mem hmem]
      nlinarith [sq_nonneg ((s - h) / s)]
    · rw [indicator_of_notMem hmem]
      norm_num
  have hsplit : ‖f‖ ^ 2 - ‖burnolWeightedShift h f‖ ^ 2 =
      ∫ s in Ioi (0 : ℝ), φ s * ‖(f : ℝ → ℂ) s‖ ^ 2 := by
    have e1 : ∫ s in Ioi (h : ℝ), ((s - h) / s) ^ 2 * ‖(f : ℝ → ℂ) s‖ ^ 2 =
        ∫ s, (Ioi (h : ℝ)).indicator (fun s => ((s - h) / s) ^ 2 * ‖(f : ℝ → ℂ) s‖ ^ 2) s
          ∂(volume.restrict (Ioi 0)) := by
      rw [integral_indicator measurableSet_Ioi, restrict_Ioi_zero_restrict_Ioi h.coe_nonneg]
    rw [norm_sq_burnolWeightedShift, Lp_two_norm_sq_eq_integral, e1,
      ← integral_sub (integrable_norm_sq_burnol f)]
    · refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [φ]
      by_cases hmem : s ∈ Ioi (h : ℝ)
      · simp only [indicator_of_mem hmem]
        ring
      · simp only [indicator_of_notMem hmem]
        ring
    · refine ((integrable_norm_sq_burnol f).indicator (s := Ioi (h : ℝ)) measurableSet_Ioi).mono'
        ?_ ?_
      · exact ((show Measurable fun s : ℝ => ((s - h) / s) ^ 2 by fun_prop).aestronglyMeasurable.mul
          (integrable_norm_sq_burnol f).1).indicator measurableSet_Ioi
      · refine Eventually.of_forall fun s => ?_
        by_cases hmem : s ∈ Ioi (h : ℝ)
        · have hs : 0 < s := lt_trans hh' hmem
          have h1 : 0 ≤ (s - h) / s := div_nonneg (by linarith [mem_Ioi.1 hmem]) hs.le
          have h2 : (s - h) / s ≤ 1 := (div_le_one hs).2 (by linarith)
          simp only [indicator_of_mem hmem, Real.norm_eq_abs]
          rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
          exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
        · simp only [indicator_of_notMem hmem, norm_zero]
          exact le_rfl
  have hpos : 0 < ‖f‖ ^ 2 - ‖burnolWeightedShift h f‖ ^ 2 := by
    rw [hsplit]
    refine lt_of_le_of_ne ?_ (fun h0 => hf (eq_zero_of_integral_weight_mul_norm_sq hφm hφ0 hφ1 f
      h0.symm))
    refine setIntegral_nonneg measurableSet_Ioi fun s hs => mul_nonneg (hφ0 s hs).le (sq_nonneg _)
  nlinarith [norm_nonneg (burnolWeightedShift h f), norm_nonneg f]

/-- **Strict decrease for `K_h^*`.**  For `h > 0`, `‖K_h^* g‖ < ‖g‖` whenever `g ≠ 0`. -/
theorem norm_adjoint_burnolWeightedShift_lt {h : ℝ≥0} (hh : 0 < h) {g : BurnolHalfLineL2}
    (hg : g ≠ 0) : ‖ContinuousLinearMap.adjoint (burnolWeightedShift h) g‖ < ‖g‖ := by
  have hh' : (0 : ℝ) < h := hh
  set φ : ℝ → ℝ := fun t => 1 - (t / (t + h)) ^ 2
  have hφm : Measurable φ := by fun_prop
  have hφ0 : ∀ t, 0 < t → 0 < φ t := fun t ht => by
    have h1 : 0 ≤ t / (t + h) := by positivity
    have h2 : t / (t + h) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    simp only [φ]
    nlinarith
  have hφ1 : ∀ t, 0 < t → φ t ≤ 1 := fun t _ => by
    simp only [φ]
    nlinarith [sq_nonneg (t / (t + h))]
  have hsplit : ‖g‖ ^ 2 - ‖ContinuousLinearMap.adjoint (burnolWeightedShift h) g‖ ^ 2 =
      ∫ t in Ioi (0 : ℝ), φ t * ‖(g : ℝ → ℂ) t‖ ^ 2 := by
    rw [norm_sq_adjoint_burnolWeightedShift, Lp_two_norm_sq_eq_integral,
      ← integral_sub (integrable_norm_sq_burnol g)]
    · refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [φ]
      ring
    · refine (integrable_norm_sq_burnol g).mono' ((show Measurable fun t : ℝ => (t / (t + h)) ^ 2
        by fun_prop).aestronglyMeasurable.mul (integrable_norm_sq_burnol g).1) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := ht
      have h1 : 0 ≤ t / (t + h) := by positivity
      have h2 : t / (t + h) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
  have hpos : 0 < ‖g‖ ^ 2 - ‖ContinuousLinearMap.adjoint (burnolWeightedShift h) g‖ ^ 2 := by
    rw [hsplit]
    refine lt_of_le_of_ne ?_ (fun h0 => hg (eq_zero_of_integral_weight_mul_norm_sq hφm hφ0 hφ1 g
      h0.symm))
    exact setIntegral_nonneg measurableSet_Ioi fun t ht => mul_nonneg (hφ0 t ht).le (sq_nonneg _)
  nlinarith [norm_nonneg (ContinuousLinearMap.adjoint (burnolWeightedShift h) g), norm_nonneg g]

/-! ## Independence of the depth features -/

/-- The feature `t e^{-λt}` at a positive rate. -/
def burnolRateFeature (lam : ℝ) (hlam : 0 < lam) : BurnolHalfLineL2 :=
  burnolDepthFeatureL2 ⟨lam, hlam⟩ 0

theorem burnolRateFeature_ae (lam : ℝ) (hlam : 0 < lam) :
    (burnolRateFeature lam hlam : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => ((t * Real.exp (-(lam * t)) : ℝ) : ℂ) := by
  filter_upwards [burnolDepthFeatureL2_ae ⟨lam, hlam⟩ 0] with t ht
  rw [burnolRateFeature, ht, burnolDepthFeature]
  simp

theorem burnolDepthFeatureL2_eq_rateFeature (ell : Ioi (0 : ℝ)) (n : ℕ) :
    burnolDepthFeatureL2 ell n =
      burnolRateFeature ((n + 1 : ℝ) * ell) (mul_pos (by positivity) ell.2) := by
  refine Lp.ext ?_
  filter_upwards [burnolDepthFeatureL2_ae ell n, burnolRateFeature_ae ((n + 1 : ℝ) * ell)
    (mul_pos (by positivity) ell.2)] with t h1 h2
  rw [h1, h2, burnolDepthFeature, mul_assoc]

theorem expFeature_ae (lam : ℝ) (hlam : 0 < lam) :
    (expFeature lam hlam : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => ((Real.exp (-(lam * t)) : ℝ) : ℂ) := by
  filter_upwards [(halfLineLaplaceFeatureRaw_memLp (w := (lam : ℂ)) (by simpa using hlam)).coeFn_toLp]
    with t ht
  rw [expFeature, halfLineLaplaceFeature, ht, halfLineLaplaceFeatureRaw]
  push_cast
  congr 1
  simp

/-- **Independence.**  Features `t e^{-λt}` at finitely many distinct positive rates are linearly
independent in `L²((0,∞))`. -/
theorem linearIndependent_burnolRateFeature {N : ℕ} (lam : Fin N → ℝ) (hpos : ∀ i, 0 < lam i)
    (hinj : Function.Injective lam) :
    LinearIndependent ℂ (fun i => burnolRateFeature (lam i) (hpos i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hexp := (Fintype.linearIndependent_iff.1 (linearIndependent_expFeature lam hpos hinj)) c
  refine hexp (Lp.eq_zero_iff_ae_eq_zero.2 ?_)
  have hsum := Lp.eq_zero_iff_ae_eq_zero.1 hc
  have hcoe1 := Lp.coeFn_finsetSum (μ := volume.restrict (Ioi 0)) Finset.univ
    (fun i => c i • burnolRateFeature (lam i) (hpos i))
  have hcoe2 : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      ((∑ i, c i • expFeature (lam i) (hpos i) : Lp ℂ 2 halfLineLaplaceMeasure) : ℝ → ℂ) t =
        (∑ i, ((c i • expFeature (lam i) (hpos i) : Lp ℂ 2 halfLineLaplaceMeasure) : ℝ → ℂ)) t :=
    Lp.coeFn_finsetSum (μ := halfLineLaplaceMeasure) Finset.univ
      (fun i => c i • expFeature (lam i) (hpos i))
  have hfe : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ i, (burnolRateFeature (lam i) (hpos i) : ℝ → ℂ) t =
      ((t * Real.exp (-(lam i * t)) : ℝ) : ℂ) :=
    ae_all_iff.2 fun i => burnolRateFeature_ae (lam i) (hpos i)
  have hee : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ i, (expFeature (lam i) (hpos i) : ℝ → ℂ) t =
      ((Real.exp (-(lam i * t)) : ℝ) : ℂ) :=
    ae_all_iff.2 fun i => expFeature_ae (lam i) (hpos i)
  have hfs : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ i,
      ((c i • burnolRateFeature (lam i) (hpos i) : BurnolHalfLineL2) : ℝ → ℂ) t =
        c i * (burnolRateFeature (lam i) (hpos i) : ℝ → ℂ) t :=
    ae_all_iff.2 fun i => (Lp.coeFn_smul (c i) (burnolRateFeature (lam i) (hpos i))).mono
      fun t ht => by rw [ht]; rfl
  have hes : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ i,
      ((c i • expFeature (lam i) (hpos i) : Lp ℂ 2 halfLineLaplaceMeasure) : ℝ → ℂ) t =
        c i * (expFeature (lam i) (hpos i) : ℝ → ℂ) t :=
    ae_all_iff.2 fun i => (Lp.coeFn_smul (c i) (expFeature (lam i) (hpos i))).mono
      fun t ht => by rw [ht]; rfl
  change ∀ᵐ t ∂(volume.restrict (Ioi 0)), _ = _
  filter_upwards [hsum, hcoe1, hcoe2, hfe, hee, hfs, hes, ae_restrict_mem measurableSet_Ioi]
    with t h1 h2 h3 h4 h5 h6 h7 ht
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
  rw [h3, Finset.sum_apply]
  rw [h2, Finset.sum_apply] at h1
  simp only [h6, h4, Pi.zero_apply] at h1
  simp only [h7, h5]
  have : (t : ℂ) * ∑ i, c i * ((Real.exp (-(lam i * t)) : ℝ) : ℂ) = 0 := by
    rw [Finset.mul_sum]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  exact (mul_eq_zero.1 this).resolve_left ht'

end GaloisForLFunctions.HTGeometry
