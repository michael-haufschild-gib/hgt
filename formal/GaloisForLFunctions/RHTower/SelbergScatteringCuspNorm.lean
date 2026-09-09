import GaloisForLFunctions.RHTower.SelbergScatteringQuarterShiftSource
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Sharp cusp norm of the complete Xi scattering source

All Fourier modes remain present. The uniform weighted tail estimate admits the
entire tail in the two-dimensional cusp norm, so the nonzero original Weyl
coefficient fixes its exact threshold. The quarter-shifted field is admitted
precisely to the right of the critical line; the unique modular power compensation
restores the divergent original norm. No entire-operator occurrence is asserted.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.SelbergScatteringHeightConjugation
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMJointSource
noncomputable section

/-- Product coordinates for the complete unit-width cusp above height two. -/
def cuspMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (-1/2:ℝ) (1/2))).prod (volume.restrict (Ioi (2:ℝ)))

/-- The height factor includes the square root of the native density `dy/y²`. -/
def cuspLift (a : ℝ) (f : (Fin 2 → ℝ) → ℂ) (xy : ℝ × ℝ) : ℂ :=
  (xy.2:ℂ)^((a:ℂ)-1) * f ![xy.1,xy.2]

private theorem cuspMeasure_ae : ∀ᵐ xy ∂cuspMeasure, 2 < xy.2 := by
  rw [cuspMeasure,Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with xy hxy
  exact hxy.2

private theorem lift_measurable (a : ℝ) {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContinuousOn f domain) : AEStronglyMeasurable (cuspLift a f) cuspMeasure := by
  rw [cuspMeasure,Measure.prod_restrict]
  apply ContinuousOn.aestronglyMeasurable _ (measurableSet_Ioc.prod measurableSet_Ioi)
  have hp := ((height_cpow_contDiffOn ((a:ℂ)-1) 0).continuousOn.mul hf)
  apply hp.comp (show ContinuousOn (fun xy : ℝ × ℝ => ![xy.1,xy.2]) _ by fun_prop)
  intro xy hxy
  change 0 < xy.2
  exact lt_trans (by norm_num) hxy.2

private theorem power_integrable_iff (r : ℝ) :
    Integrable (fun xy : ℝ × ℝ => xy.2^r) cuspMeasure ↔ r < -1 := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1/2:ℝ) (1/2))
  let ν : Measure ℝ := volume.restrict (Ioi (2:ℝ))
  letI : IsProbabilityMeasure μ := ⟨by simp [μ,Real.volume_Ioc]; norm_num⟩
  have hp : MeasurePreserving Prod.snd (μ.prod ν) ν := measurePreserving_snd
  have hm : AEStronglyMeasurable (fun y : ℝ => y^r) ν := by fun_prop
  change Integrable ((fun y : ℝ => y^r) ∘ Prod.snd) (μ.prod ν) ↔ _
  rw [hp.integrable_comp hm]
  exact integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ)<2)

/-- Every real-power-weighted complete Fourier tail is admitted in the native cusp norm. -/
theorem cuspLift_tail_memLp (u : ℂ) (a : ℝ) : MemLp (cuspLift a (tail u)) 2 cuspMeasure := by
  have hm := lift_measurable a (cuspTailPart_contDiffOn .scalar u).continuousOn
  change AEStronglyMeasurable (cuspLift a (tail u)) cuspMeasure at hm
  rw [memLp_two_iff_integrable_sq_norm hm]
  obtain ⟨C,hC,hbound⟩ := weighted_tail_bounded u (a:ℂ) 2 (by norm_num)
  have hi := ((power_integrable_iff (-2)).2 (by norm_num)).const_mul (C^2)
  apply hi.mono' (hm.norm.pow 2)
  filter_upwards [cuspMeasure_ae] with xy hxy
  have hy : 0 < xy.2 := lt_trans (by norm_num) hxy
  have he : cuspLift a (tail u) xy =
      (xy.2:ℂ)^(-1:ℂ) * ((xy.2:ℂ)^(a:ℂ)*tail u ![xy.1,xy.2]) := by
    rw [cuspLift,← mul_assoc,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
    congr 2
    ring
  have hb : ‖cuspLift a (tail u) xy‖ ≤ xy.2^(-1:ℝ)*C := by
    rw [he,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
    norm_num only [Complex.neg_re,Complex.one_re]
    exact mul_le_mul_of_nonneg_left (hbound ![xy.1,xy.2] hxy.le) (Real.rpow_nonneg hy.le _)
  simp only [Pi.pow_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (xy.2^(-1:ℝ)*C)^2 := by
      have hn := norm_nonneg (cuspLift a (tail u) xy)
      nlinarith
    _ = C^2*xy.2^(-2:ℝ) := by
      rw [mul_pow,← Real.rpow_mul_natCast hy.le]
      norm_num
      ring


private theorem xi_coefficient_ne (q : XiZeroCopy) :
    reflectedCompletedLambda ((q.1:ℂ)-1) ≠ 0 := by
  obtain ⟨he,hn,_⟩ := physicalScalar_cutoff_calibration q
  intro hz
  apply hn
  rw [he,hz,mul_zero]

private theorem principal_norm (q : XiZeroCopy) (a : ℝ) (xy : ℝ × ℝ)
    (hy : 0 < xy.2) :
    ‖cuspLift a (principal (physicalAngularParameter q)) xy‖^2 =
      ‖reflectedCompletedLambda ((q.1:ℂ)-1)‖^2 * xy.2^(2*a-(q.1:ℂ).re) := by
  have he : cuspLift a (principal (physicalAngularParameter q)) xy =
      reflectedCompletedLambda ((q.1:ℂ)-1) * (xy.2:ℂ)^((a:ℂ)-(q.1:ℂ)/2) := by
    rw [cuspLift,physicalScalar_principal]
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
    rw [mul_left_comm,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
    congr 2
    ring
  rw [he,norm_mul,mul_pow,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    ← Real.rpow_mul_natCast hy.le]
  congr 2
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.div_ofNat_re]
  ring

private theorem principal_memLp_iff (q : XiZeroCopy) (a : ℝ) :
    MemLp (cuspLift a (principal (physicalAngularParameter q))) 2 cuspMeasure ↔
      2*a+1 < (q.1:ℂ).re := by
  have hm := lift_measurable a
    (cuspConstantPart_contDiffOn .scalar (physicalAngularParameter q)).continuousOn
  change AEStronglyMeasurable (cuspLift a (principal (physicalAngularParameter q))) cuspMeasure at hm
  rw [memLp_two_iff_integrable_sq_norm hm]
  have he : (fun xy => ‖cuspLift a (principal (physicalAngularParameter q)) xy‖^2) =ᵐ[cuspMeasure]
      (fun xy : ℝ × ℝ => ‖reflectedCompletedLambda ((q.1:ℂ)-1)‖^2 * xy.2^(2*a-(q.1:ℂ).re)) := by
    filter_upwards [cuspMeasure_ae] with xy hxy
    exact principal_norm q a xy (lt_trans (by norm_num) hxy)
  rw [integrable_congr he,integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (xi_coefficient_ne q)))),
    power_integrable_iff]
  constructor <;> intro h <;> linarith

/-- Exact cusp admission of the full original Xi source, with every Fourier mode retained. -/
theorem cuspLift_xi_memLp_iff (q : XiZeroCopy) (a : ℝ) :
    MemLp (cuspLift a (scalarSource (physicalAngularParameter q))) 2 cuspMeasure ↔
      2*a+1 < (q.1:ℂ).re := by
  have ht := cuspLift_tail_memLp (physicalAngularParameter q) a
  have he : cuspLift a (scalarSource (physicalAngularParameter q)) =
      cuspLift a (principal (physicalAngularParameter q)) + cuspLift a (tail (physicalAngularParameter q)) := by
    funext xy
    dsimp [cuspLift,scalarSource,D4BMGlobalAngularResponse.principal,tail,d4BMCompletedEisensteinCuspLeg]
    ring
  rw [he,← principal_memLp_iff]
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using h.sub ht
  · intro h
    exact h.add ht


/-- The product-space lift has exactly the weighted native hyperbolic norm density. -/
theorem cuspLift_norm_sq (a : ℝ) (f : (Fin 2 → ℝ) → ℂ) (xy : ℝ × ℝ)
    (hy : 0 < xy.2) :
    ‖cuspLift a f xy‖^2 = xy.2^(2*a)*‖f ![xy.1,xy.2]‖^2 / xy.2^2 := by
  rw [cuspLift,norm_mul,mul_pow,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    ← Real.rpow_mul_natCast hy.le]
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re]
  norm_num only [Nat.cast_ofNat]
  rw [show (a-1)*(2:ℝ)=2*a-2 by ring,Real.rpow_sub hy,Real.rpow_two]
  ring

/-- Sharp admission in the literal two-dimensional weighted cusp density. -/
theorem scalarSource_cusp_norm_iff (q : XiZeroCopy) (a : ℝ) :
    Integrable (fun xy : ℝ × ℝ => xy.2^(2*a)*
      ‖scalarSource (physicalAngularParameter q) ![xy.1,xy.2]‖^2/xy.2^2) cuspMeasure ↔
      2*a+1 < (q.1:ℂ).re := by
  have hm := lift_measurable a (cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).continuousOn
  change AEStronglyMeasurable (cuspLift a (scalarSource (physicalAngularParameter q))) cuspMeasure at hm
  rw [← cuspLift_xi_memLp_iff q a,memLp_two_iff_integrable_sq_norm hm]
  apply integrable_congr
  filter_upwards [cuspMeasure_ae] with xy hxy
  exact (cuspLift_norm_sq a _ xy (lt_trans (by norm_num) hxy)).symm

/-- The original complete source has divergent native cusp norm at every actual Xi copy. -/
theorem scalarSource_native_cusp_not_integrable (q : XiZeroCopy) :
    ¬ Integrable (fun xy : ℝ × ℝ =>
      ‖scalarSource (physicalAngularParameter q) ![xy.1,xy.2]‖^2/xy.2^2) cuspMeasure := by
  have h := scalarSource_cusp_norm_iff q 0
  norm_num only [mul_zero,Real.rpow_zero,one_mul,zero_add] at h
  rw [h]
  have hq := (xi_divisor_support_re_mem_open_unit q.1).2
  linarith

/-- Complete power-density classification for the literal quarter-shifted source. -/
theorem quarterShiftSource_weighted_cusp_norm_iff (q : XiZeroCopy) (b : ℝ) :
    Integrable (fun xy : ℝ × ℝ => xy.2^b*
      ‖quarterShiftSource (physicalAngularParameter q) ![xy.1,xy.2]‖^2/xy.2^2) cuspMeasure ↔
      b+1/2 < (q.1:ℂ).re := by
  have he : (fun xy : ℝ × ℝ => xy.2^b*
      ‖quarterShiftSource (physicalAngularParameter q) ![xy.1,xy.2]‖^2/xy.2^2) =ᵐ[cuspMeasure]
      (fun xy : ℝ × ℝ => xy.2^(2*((b-1/2)/2))*
        ‖scalarSource (physicalAngularParameter q) ![xy.1,xy.2]‖^2/xy.2^2) := by
    filter_upwards [cuspMeasure_ae] with xy hxy
    rw [show 2*((b-1/2)/2)=b-1/2 by ring]
    exact congrArg (fun v : ℝ => v/xy.2^2)
      (quarterShiftSource_weighted_norm (physicalAngularParameter q) b ![xy.1,xy.2]
        (lt_trans (by norm_num) hxy))
  rw [integrable_congr he,scalarSource_cusp_norm_iff]
  constructor <;> intro h <;> linarith

/-- The quarter multiplier gives finite cusp norm exactly on the right of the critical line. -/
theorem quarterShiftSource_cusp_norm_iff (q : XiZeroCopy) :
    Integrable (fun xy : ℝ × ℝ =>
      ‖quarterShiftSource (physicalAngularParameter q) ![xy.1,xy.2]‖^2/xy.2^2) cuspMeasure ↔
      1/2 < (q.1:ℂ).re := by
  simpa only [Real.rpow_zero,one_mul,zero_add] using quarterShiftSource_weighted_cusp_norm_iff q 0

/-- The unique inversion-invariant power compensation has divergent cusp norm at every Xi copy. -/
theorem quarterShiftSource_compensated_cusp_not_integrable (q : XiZeroCopy) :
    ¬ Integrable (fun xy : ℝ × ℝ => xy.2^(1/2:ℝ)*
      ‖quarterShiftSource (physicalAngularParameter q) ![xy.1,xy.2]‖^2/xy.2^2) cuspMeasure := by
  rw [quarterShiftSource_weighted_cusp_norm_iff]
  have hq := (xi_divisor_support_re_mem_open_unit q.1).2
  linarith

end
end RHTower.SelbergScatteringHeightConjugation
