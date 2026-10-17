import GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Exact information lost by the literal weighted left shift. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

theorem burnolWeightedShift_eq_zero_iff (h : ℝ≥0) (f : BurnolHalfLineL2) :
    burnolWeightedShift h f = 0 ↔
      (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (h : ℝ))] 0 := by
  constructor
  · intro hf
    have hz := Lp.eq_zero_iff_ae_eq_zero.mp hf
    have hs : (fun t : ℝ => (f : ℝ → ℂ) (t + h))
        =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [burnolWeightedShift_coeFn h f, hz,
        ae_restrict_mem measurableSet_Ioi] with t he ht hpos
      have hc : ((t / (t + h) : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (div_ne_zero hpos.ne'
          (add_pos_of_pos_of_nonneg hpos h.coe_nonneg).ne')
      rw [he] at ht
      exact (mul_eq_zero.mp ht).resolve_left hc
    have hp := (measurePreserving_sub_right_Ioi (h : ℝ)).quasiMeasurePreserving.ae_eq_comp hs
    filter_upwards [hp] with s hs
    simpa only [Function.comp_apply, sub_add_cancel, Pi.zero_apply] using hs
  · intro hf
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    have hp := (measurePreserving_add_right_Ioi (h : ℝ)).quasiMeasurePreserving.ae_eq_comp hf
    filter_upwards [burnolWeightedShift_coeFn h f, hp] with t he ht
    simp only [Function.comp_apply, Pi.zero_apply] at ht
    simp only [he, ht, mul_zero, Pi.zero_apply]

theorem exists_nonzero_burnolWeightedShift_kernel {h : ℝ≥0} (hh : 0 < h) :
    ∃ f : BurnolHalfLineL2, f ≠ 0 ∧ burnolWeightedShift h f = 0 := by
  have hhr : 0 < (h : ℝ) := hh
  have hm : (volume.restrict (Ioi (0 : ℝ))) (Ioo 0 (h : ℝ)) = ENNReal.ofReal h := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (fun _ hx => hx.1), Real.volume_Ioo, sub_zero]
  have hfin : (volume.restrict (Ioi (0 : ℝ))) (Ioo 0 (h : ℝ)) ≠ ∞ := by
    rw [hm]
    exact ENNReal.ofReal_ne_top
  let f : BurnolHalfLineL2 := indicatorConstLp 2 measurableSet_Ioo hfin (1 : ℂ)
  refine ⟨f, ?_, ?_⟩
  · apply norm_ne_zero_iff.mp
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), measureReal_def, hm,
      ENNReal.toReal_ofReal h.coe_nonneg, norm_one, one_mul]
    exact (Real.rpow_pos_of_pos hhr _).ne'
  · apply (burnolWeightedShift_eq_zero_iff h f).mpr
    have he : (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (h : ℝ))]
        (Ioo 0 (h : ℝ)).indicator (fun _ => (1 : ℂ)) :=
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioo) (hμs := hfin)
        (c := (1 : ℂ))).filter_mono (ae_mono (restrict_Ioi_le_restrict_Ioi_zero h.coe_nonneg))
    filter_upwards [he, ae_restrict_mem measurableSet_Ioi] with t ht hpos
    rw [ht]
    exact Set.indicator_of_notMem (s := Ioo 0 (h : ℝ))
      (fun hmem => (not_lt_of_ge hpos.le) hmem.2) (fun _ => (1 : ℂ))

theorem burnolWeightedShift_injective_iff (h : ℝ≥0) :
    Function.Injective (burnolWeightedShift h) ↔ h = 0 := by
  constructor
  · intro hinj
    by_contra hh
    obtain ⟨f, hf, hzero⟩ := exists_nonzero_burnolWeightedShift_kernel (pos_iff_ne_zero.mpr hh)
    exact hf (hinj (hzero.trans (map_zero _).symm))
  · rintro rfl f g hfg
    apply sub_eq_zero.mp
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    apply (burnolWeightedShift_eq_zero_iff 0 (f - g)).mp
    rw [map_sub, hfg, sub_self]

end GaloisForLFunctions.HTGeometry
