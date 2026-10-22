import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspResponseFlux
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Absolute convergence of both original cusp source moments and flux limits.

The field is the original native energy response. Its identification with
continued retarded propagation and any extinction law remain separate.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection D4BMGlobalAngularResponse
noncomputable section

private theorem weighted_mean_tail_sq_bounded (u w : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
      ‖(y:ℂ)^w*mean (fun x => tail u ![x,y] ^2)‖ ≤ C := by
  obtain ⟨A,hA,hAt⟩ := weighted_tail_bounded u w 1 (by norm_num)
  obtain ⟨B,hB,hBt⟩ := weighted_tail_bounded u 0 1 (by norm_num)
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro y hy
  have he : (y:ℂ)^w*mean (fun x => tail u ![x,y] ^2) =
      ∫ x in Ioc (-1/2:ℝ) (1/2), ((y:ℂ)^w*tail u ![x,y])*tail u ![x,y] := by
    rw [mean,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [he]
  have h := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc (-1/2:ℝ) (1/2))) (C := A*B)
    (f := fun x => ((y:ℂ)^w*tail u ![x,y])*tail u ![x,y]) (by
      filter_upwards with x
      rw [norm_mul]
      have h1 := hAt ![x,y] hy
      have h0 := hBt ![x,y] hy
      simp only [Matrix.cons_val_one,Complex.cpow_zero,one_mul] at h1 h0
      exact mul_le_mul h1 h0 (norm_nonneg _) hA)
  norm_num [Measure.real,Real.volume_Ioc] at h
  simpa only [neg_div] using h

private theorem fluxSource_tail (q : XiZeroCopy) (branch alternate : Bool)
    {y : ℝ} (hy : 3 < y) :
    fluxSource q branch alternate y =
      (parameter q branch/2)*
        ((y:ℂ)^(root q branch alternate)*mean (fun x => tail (center q) ![x,y] ^2))/(y:ℂ)^2 := by
  have hp : 0 < y := by linarith
  rw [fluxSource,globalForcing_average q branch (by linarith),mean_forcing_high q branch hy,
    mean_tail_sq (center q) hp]
  have hw : (y:ℂ)^(root q branch alternate) =
      (y:ℂ)^(root q branch alternate-2)*(y:ℂ)^2 := by
    have he : (y:ℂ)^(2:ℂ)=(y:ℂ)^2 := by norm_cast
    rw [← he,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hp.ne')]
    congr 1
    ring
  rw [hw]
  field_simp [Complex.ofReal_ne_zero.mpr hp.ne']
  ring

/-- Both actual source moments have a uniform inverse-square integrable majorant;
this follows from the full complex tail, with no positivity of its square assumed. -/
theorem fluxSource_norm_bound (q : XiZeroCopy) (branch alternate : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 3 < y → ‖fluxSource q branch alternate y‖ ≤ C/y^2 := by
  obtain ⟨A,hA,hAt⟩ := weighted_mean_tail_sq_bounded (center q) (root q branch alternate)
  refine ⟨‖parameter q branch/2‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
  intro y hy
  rw [fluxSource_tail q branch alternate hy,norm_div,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (by linarith : 0 < y)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hAt y (by linarith)) (norm_nonneg _)) (sq_nonneg y)

/-- Each original indicial source moment is absolutely integrable over the infinite cusp. -/
theorem fluxSource_integrable (q : XiZeroCopy) (branch alternate : Bool) :
    IntegrableOn (fluxSource q branch alternate) (Ioi (3:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := fluxSource_norm_bound q branch alternate
  have hi : IntegrableOn (fun y : ℝ => y^(-2:ℝ)) (Ioi (3:ℝ)) :=
    (integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ)<3)).mpr (by norm_num)
  have hc : ContinuousOn (fluxSource q branch alternate) (Ioi (3:ℝ)) :=
    fun y hy => (fluxSource_continuousAt q branch alternate (by change 3 < y at hy; linarith)).continuousWithinAt
  apply (hi.const_mul C).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  convert hbound y hy using 1
  norm_num [Real.rpow_neg,Real.rpow_two,div_eq_mul_inv]
  left
  norm_cast

/-- The actual limiting boundary flux retains the response's boundary jet at height four
and the complete infinite source moment. -/
def limitingFlux (q : XiZeroCopy) (branch alternate : Bool) : ℂ :=
  responseFlux q branch alternate 4 + ∫ y in Ioi (4:ℝ), fluxSource q branch alternate y

/-- The original response has a proved finite Wronskian limit for both indicial powers. -/
theorem responseFlux_tendsto (q : XiZeroCopy) (branch alternate : Bool) :
    Tendsto (responseFlux q branch alternate) atTop (𝓝 (limitingFlux q branch alternate)) := by
  have hi := (fluxSource_integrable q branch alternate).mono_set
    (Ioi_subset_Ioi (by norm_num : (3:ℝ)≤4))
  have h := (intervalIntegral_tendsto_integral_Ioi (4:ℝ) hi tendsto_id).const_add
    (responseFlux q branch alternate 4)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  dsimp only [id_eq]
  rw [responseFlux_segment q branch alternate (by norm_num) hy]
  ring

end
end RHTower.D4BMCuspResponse
