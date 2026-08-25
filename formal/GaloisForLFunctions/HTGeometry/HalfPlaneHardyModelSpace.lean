import GaloisForLFunctions.HTGeometry.HardyHorizontalLayerLeakage

open Complex Filter Topology MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance : CompleteSpace UpperHardyL2 :=
  RHTower.isClosed_hardyL2.completeSpace_coe

/-- Upper-half-plane evaluation kernel, realized as a lower-pole Hardy boundary vector. -/
def lowerCauchyFeatureAt (w : ℂ) (hw : 0 < w.im) : UpperHardyL2 :=
  let v := (starRingEnd ℂ) w
  have hv : v.im < 0 := by simpa [v] using hw
  ⟨(RHTower.memLp_cauchyKernel (ne_of_lt hv)).toLp
      (fun x : ℝ => (((x : ℝ) : ℂ) - v)⁻¹),
    RHTower.cauchyKernel_mem_hardyL2 hv⟩

theorem coe_lowerCauchyFeatureAt {w : ℂ} (hw : 0 < w.im) :
    ((((lowerCauchyFeatureAt w hw : UpperHardyL2) : RealLineL2) : ℝ → ℂ))
      =ᵐ[volume] fun x : ℝ => (((x : ℝ) : ℂ) - (starRingEnd ℂ) w)⁻¹ := by
  simpa [lowerCauchyFeatureAt] using
    (RHTower.memLp_cauchyKernel
      (show ((starRingEnd ℂ) w).im ≠ 0 by simpa using ne_of_gt hw)).coeFn_toLp

/-- Reproducing pairing is the upper Cauchy transform. -/
theorem inner_lowerCauchyFeatureAt {w : ℂ} (hw : 0 < w.im) (f : UpperHardyL2) :
    inner ℂ (lowerCauchyFeatureAt w hw) f =
      ∫ x : ℝ, ((f : RealLineL2) : ℝ → ℂ) x /
        (((x : ℝ) : ℂ) - w) := by
  rw [UpperHardyL2.coe_inner, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [coe_lowerCauchyFeatureAt hw] with x hx
  rw [RCLike.inner_apply, hx, map_inv₀, map_sub, Complex.conj_ofReal,
    Complex.conj_conj, div_eq_mul_inv]

theorem inner_lowerCauchyFeatureAt_self {w : ℂ} (hw : 0 < w.im) :
    inner ℂ (lowerCauchyFeatureAt w hw) (lowerCauchyFeatureAt w hw) =
      ((Real.pi / w.im : ℝ) : ℂ) := by
  rw [inner_lowerCauchyFeatureAt]
  calc
    (∫ x : ℝ, ((lowerCauchyFeatureAt w hw : UpperHardyL2) : RealLineL2) x /
        (((x : ℝ) : ℂ) - w)) =
        ∫ x : ℝ, ((((x : ℂ) - w) *
          ((x : ℂ) - (starRingEnd ℂ) w))⁻¹) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [coe_lowerCauchyFeatureAt hw] with x hx
      rw [hx, mul_inv_rev]
      ring
    _ = ((Real.pi / w.im : ℝ) : ℂ) := integral_cauchyPair hw

theorem lowerCauchyFeatureAt_ne_zero {w : ℂ} (hw : 0 < w.im) :
    lowerCauchyFeatureAt w hw ≠ 0 := by
  intro hzero
  have hself := inner_lowerCauchyFeatureAt_self hw
  rw [hzero, inner_zero_left] at hself
  have hpos : 0 < Real.pi / w.im := div_pos Real.pi_pos hw
  exact (ofReal_ne_zero.mpr (ne_of_gt hpos)) hself.symm

/-- Cauchy evaluation as a bounded functional on upper Hardy boundary space. -/
def upperHardyCauchyEval (w : ℂ) (hw : 0 < w.im) : UpperHardyL2 →L[ℂ] ℂ :=
  innerSL ℂ (lowerCauchyFeatureAt w hw)

theorem upperHardyCauchyEval_apply (w : ℂ) (hw : 0 < w.im) (f : UpperHardyL2) :
    upperHardyCauchyEval w hw f =
      ∫ x : ℝ, ((f : RealLineL2) : ℝ → ℂ) x /
        (((x : ℝ) : ℂ) - w) := by
  exact inner_lowerCauchyFeatureAt hw f

/-- Upper-Hardy restriction of multiplication by the inner factor attached to `w`. -/
def upperHardyInnerBlaschke (w : ℂ) (hw : 0 < w.im) :
    UpperHardyL2 →L[ℂ] UpperHardyL2 :=
  ((RHTower.blaschkeMulInv w).comp UpperHardyL2.subtypeL).codRestrict
    UpperHardyL2 (fun f => RHTower.blaschkeMulInv_mem_hardyL2 hw f.property)

@[simp] theorem coe_upperHardyInnerBlaschke (w : ℂ) (hw : 0 < w.im)
    (f : UpperHardyL2) :
    ((upperHardyInnerBlaschke w hw f : UpperHardyL2) : RealLineL2) =
      RHTower.blaschkeMulInv w ((f : UpperHardyL2) : RealLineL2) := rfl

theorem norm_upperHardyInnerBlaschke (w : ℂ) (hw : 0 < w.im)
    (f : UpperHardyL2) :
    ‖upperHardyInnerBlaschke w hw f‖ = ‖f‖ := by
  change ‖RHTower.blaschkeMulInv w ((f : UpperHardyL2) : RealLineL2)‖ =
    ‖((f : UpperHardyL2) : RealLineL2)‖
  exact RHTower.norm_blaschkeMulInv (ne_of_gt hw) _

theorem blaschkeMul_blaschkeMulInv {w : ℂ} (hw : 0 < w.im) (f : RealLineL2) :
    RHTower.blaschkeMul w (RHTower.blaschkeMulInv w f) = f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [RHTower.coeFn_blaschkeMul w (RHTower.blaschkeMulInv w f),
    RHTower.coeFn_blaschkeMulInv w f] with x hmul hinv
  rw [hmul, hinv, RHTower.blaschkeSymbol, RHTower.blaschkeSymbolInv]
  have h1 := RHTower.ofReal_sub_ne_zero (ne_of_gt hw) x
  have hc : ((starRingEnd ℂ) w).im ≠ 0 := by simpa using ne_of_gt hw
  have h2 := RHTower.ofReal_sub_ne_zero (w := (starRingEnd ℂ) w) hc x
  field_simp

theorem blaschkeMulInv_blaschkeMul {w : ℂ} (hw : 0 < w.im) (f : RealLineL2) :
    RHTower.blaschkeMulInv w (RHTower.blaschkeMul w f) = f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [RHTower.coeFn_blaschkeMulInv w (RHTower.blaschkeMul w f),
    RHTower.coeFn_blaschkeMul w f] with x hinv hmul
  rw [hinv, hmul, RHTower.blaschkeSymbol, RHTower.blaschkeSymbolInv]
  have h1 := RHTower.ofReal_sub_ne_zero (ne_of_gt hw) x
  have hc : ((starRingEnd ℂ) w).im ≠ 0 := by simpa using ne_of_gt hw
  have h2 := RHTower.ofReal_sub_ne_zero (w := (starRingEnd ℂ) w) hc x
  field_simp

/-- One upper-half-plane inner factor has range exactly the zero-evaluation hyperplane. -/
theorem range_upperHardyInnerBlaschke (w : ℂ) (hw : 0 < w.im) :
    LinearMap.range (upperHardyInnerBlaschke w hw :
      UpperHardyL2 →ₗ[ℂ] UpperHardyL2) =
      LinearMap.ker (upperHardyCauchyEval w hw : UpperHardyL2 →ₗ[ℂ] ℂ) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    rw [LinearMap.mem_ker]
    change upperHardyCauchyEval w hw (upperHardyInnerBlaschke w hw g) = 0
    rw [upperHardyCauchyEval_apply]
    have hcg : (∫ x : ℝ, ((g : UpperHardyL2) : RealLineL2) x /
        (((x : ℝ) : ℂ) - (starRingEnd ℂ) w)) = 0 :=
      RHTower.integral_cauchyTransform_eq_zero g.property (by simpa using hw)
    have hae : (fun x : ℝ =>
        ((upperHardyInnerBlaschke w hw g : UpperHardyL2) : RealLineL2) x /
          (((x : ℝ) : ℂ) - w)) =ᵐ[volume]
        fun x : ℝ => ((g : UpperHardyL2) : RealLineL2) x /
          (((x : ℝ) : ℂ) - (starRingEnd ℂ) w) := by
      filter_upwards [RHTower.coeFn_blaschkeMulInv w
        ((g : UpperHardyL2) : RealLineL2)] with x hx
      rw [show ((upperHardyInnerBlaschke w hw g : UpperHardyL2) : RealLineL2) x =
        RHTower.blaschkeMulInv w ((g : UpperHardyL2) : RealLineL2) x from rfl, hx,
        RHTower.blaschkeSymbolInv]
      have h1 := RHTower.ofReal_sub_ne_zero (ne_of_gt hw) x
      have h2 := RHTower.ofReal_sub_ne_zero (by simpa using ne_of_gt hw) x
      field_simp
    rw [MeasureTheory.integral_congr_ae hae, hcg]
  · intro hf
    rw [LinearMap.mem_ker] at hf
    change upperHardyCauchyEval w hw f = 0 at hf
    rw [upperHardyCauchyEval_apply] at hf
    let g : UpperHardyL2 :=
      ⟨RHTower.blaschkeMul w ((f : UpperHardyL2) : RealLineL2),
        RHTower.blaschkeMul_mem_hardyL2 hw f.property hf⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact blaschkeMulInv_blaschkeMul hw ((f : UpperHardyL2) : RealLineL2)

/-- The range hyperplane is the orthogonal complement of its reproducing vector. -/
theorem range_upperHardyInnerBlaschke_eq_orthogonal_span
    (w : ℂ) (hw : 0 < w.im) :
    LinearMap.range (upperHardyInnerBlaschke w hw :
      UpperHardyL2 →ₗ[ℂ] UpperHardyL2) =
      (ℂ ∙ lowerCauchyFeatureAt w hw)ᗮ := by
  rw [range_upperHardyInnerBlaschke]
  ext f
  rw [LinearMap.mem_ker]
  constructor
  · intro hf y hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
    change inner ℂ (lowerCauchyFeatureAt w hw) f = 0 at hf
    rw [inner_smul_left, hf]
    simp
  · intro hf
    exact hf (lowerCauchyFeatureAt w hw) (Submodule.mem_span_singleton_self _)

/-- One half-plane Blaschke factor removes exactly one Hardy direction. -/
theorem finrank_orthogonal_range_upperHardyInnerBlaschke
    (w : ℂ) (hw : 0 < w.im) :
    Module.finrank ℂ ((LinearMap.range (upperHardyInnerBlaschke w hw :
      UpperHardyL2 →ₗ[ℂ] UpperHardyL2))ᗮ : Submodule ℂ UpperHardyL2) = 1 := by
  rw [range_upperHardyInnerBlaschke_eq_orthogonal_span]
  letI : FiniteDimensional ℂ (ℂ ∙ lowerCauchyFeatureAt w hw) :=
    FiniteDimensional.span_singleton ℂ _
  letI : CompleteSpace (ℂ ∙ lowerCauchyFeatureAt w hw) :=
    FiniteDimensional.complete ℂ _
  letI : (ℂ ∙ lowerCauchyFeatureAt w hw).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  rw [Submodule.orthogonal_orthogonal]
  exact finrank_span_singleton (lowerCauchyFeatureAt_ne_zero hw)

end GaloisForLFunctions.HTGeometry
