import GaloisForLFunctions.HTGeometry.LevyLaplaceLimits
import GaloisForLFunctions.RHTower.PrimeBurnolLevyMinimumInverse

/-! Killing, drift and unbounded recovery are intrinsic to the actual physical evolution. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ComplexOrder
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
namespace BurnolLevyData
variable (D : BurnolLevyData)

theorem tendsto_exponent_zero :
    Tendsto (fun x : ℝ => D.exponent (x : ℂ)) (𝓝[>] 0) (𝓝 ((D.killing : ℝ) : ℂ)) := by
  have hx : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa only [exponent, mul_zero, add_zero] using!
    ((tendsto_const_nhds (x := ((D.killing : ℝ) : ℂ))).add
      ((tendsto_const_nhds (x := ((D.drift : ℝ) : ℂ))).mul hx)).add
        (tendsto_levyLaplaceJump_zero D.control)

theorem tendsto_exponent_div_atTop :
    Tendsto (fun x : ℝ => D.exponent (x : ℂ) / (x : ℂ)) atTop (𝓝 ((D.drift : ℝ) : ℂ)) := by
  have hx : Tendsto (fun x : ℝ => (x : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using!
      Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hl : Tendsto (fun x : ℝ => ((D.killing : ℝ) : ℂ) * (x : ℂ)⁻¹ +
      ((D.drift : ℝ) : ℂ) + levyLaplaceJump D.control (x : ℂ) / (x : ℂ)) atTop
        (𝓝 ((D.drift : ℝ) : ℂ)) := by
    simpa only [mul_zero, zero_add, add_zero] using!
      (((tendsto_const_nhds (x := ((D.killing : ℝ) : ℂ))).mul hx).add
        (tendsto_const_nhds (x := ((D.drift : ℝ) : ℂ)))).add
          (tendsto_levyLaplaceJump_div_atTop D.control)
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold exponent
  field_simp

def withoutKilling : BurnolLevyData := { D with killing := 0 }

theorem evolution_killing_factor (t : ℝ≥0) :
    D.evolution t = (Real.exp (-((t : ℝ) * (D.killing : ℝ))) : ℂ) • D.withoutKilling.evolution t := by
  apply primeBurnol_operator_ext
  intro p
  rw [D.evolution_prime, smul_apply, D.withoutKilling.evolution_prime,
    smul_smul, Complex.ofReal_exp, ← Complex.exp_add]
  apply congrArg (fun z : ℂ => Complex.exp z • primeLogCriticalLaplaceFeatureL2 p)
  simp only [exponent, withoutKilling, NNReal.coe_zero, Complex.ofReal_zero,
    zero_add, Complex.ofReal_neg, Complex.ofReal_mul]
  ring

theorem norm_evolution_le_killing (t : ℝ≥0) :
    ‖D.evolution t‖ ≤ Real.exp (-((t : ℝ) * (D.killing : ℝ))) := by
  rw [D.evolution_killing_factor, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (D.withoutKilling.norm_evolution_le t) (Real.exp_nonneg (-((t : ℝ) * (D.killing : ℝ))))

theorem norm_evolution (t : ℝ≥0) :
    ‖D.evolution t‖ = Real.exp (-((t : ℝ) * (D.killing : ℝ))) := by
  apply le_antisymm (D.norm_evolution_le_killing t)
  have hl : Tendsto (fun x : ℝ => ‖Complex.exp (-((t : ℝ) : ℂ) * D.exponent (x : ℂ))‖)
      (𝓝[>] 0) (𝓝 (Real.exp (-((t : ℝ) * (D.killing : ℝ))))) := by
    have he := Complex.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := -((t : ℝ) : ℂ))).mul D.tendsto_exponent_zero)
    simpa only [Function.comp_def, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, mul_zero,
      sub_zero, neg_mul] using! he.norm
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with x hx
  let f := burnolComplexFeature (x : ℂ) hx
  have hf : f ≠ 0 := burnolComplexFeature_ne_zero (z := (x : ℂ)) hx
  have he : D.evolution t f = Complex.exp (-((t : ℝ) : ℂ) * D.exponent (x : ℂ)) • f :=
    D.symbol.evolution_feature t (x : ℂ) hx
  have hb := (D.evolution t).le_opNorm f
  rw [he, norm_smul] at hb
  exact le_of_mul_le_mul_right hb (norm_pos_iff.mpr hf)

theorem no_bounded_leftInverse_of_exponent_unbounded
    (hψ : Tendsto (fun x : ℝ => (D.exponent (x : ℂ)).re) atTop atTop)
    {t : ℝ≥0} (ht : 0 < t) :
    ¬ ∃ B : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2, ∀ f, B (D.evolution t f) = f := by
  rintro ⟨B, hB⟩
  have he : Tendsto (fun x : ℝ => Real.exp (-((t : ℝ) * (D.exponent (x : ℂ)).re)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_comm] using!
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.Tendsto.atTop_mul_const (show 0 < (t : ℝ) from ht) hψ)
  have hl : Tendsto (fun x : ℝ => ‖B‖ *
      Real.exp (-((t : ℝ) * (D.exponent (x : ℂ)).re))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := ‖B‖)).mul he
  have hb : ∀ᶠ x : ℝ in atTop,
      1 ≤ ‖B‖ * Real.exp (-((t : ℝ) * (D.exponent (x : ℂ)).re)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    let f := burnolComplexFeature (x : ℂ) hx
    have hf : 0 < ‖f‖ := norm_pos_iff.mpr (burnolComplexFeature_ne_zero (z := (x : ℂ)) hx)
    have hE : D.evolution t f = Complex.exp (-((t : ℝ) : ℂ) * D.exponent (x : ℂ)) • f :=
      D.symbol.evolution_feature t (x : ℂ) hx
    have hn := B.le_opNorm (D.evolution t f)
    rw [hB f, hE, norm_smul] at hn
    have hcancel : 1 ≤ ‖B‖ * ‖Complex.exp (-((t : ℝ) : ℂ) * D.exponent (x : ℂ))‖ := by
      have hm : 1 * ‖f‖ ≤
          (‖B‖ * ‖Complex.exp (-((t : ℝ) : ℂ) * D.exponent (x : ℂ))‖) * ‖f‖ := by
        simpa only [one_mul, mul_assoc] using hn
      exact le_of_mul_le_mul_right hm hf
    simpa only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, neg_mul] using hcancel
  have hbad : (1 : ℝ) ≤ 0 := le_of_tendsto (α := OrderDual ℝ) hl hb
  norm_num at hbad

/-- A genuinely unbounded closed inverse, with its original physical source norm. -/
theorem minimumNormInverse_not_bounded
    (hψ : Tendsto (fun x : ℝ => (D.exponent (x : ℂ)).re) atTop atTop)
    {t : ℝ≥0} (ht : 0 < t) (hdrift : D.drift * t = 0) :
    ¬ ∃ B : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2,
      ∀ u : (D.minimumNormInverse t).domain, B u = D.minimumNormInverse t u := by
  rintro ⟨B, hB⟩
  apply D.no_bounded_leftInverse_of_exponent_unbounded hψ ht
  refine ⟨B, fun f => ?_⟩
  let u : (D.minimumNormInverse t).domain := ⟨D.evolution t f, by
    rw [D.minimumNormInverse_domain]
    exact ⟨f, rfl⟩⟩
  have he : D.minimumNormInverse t u = f :=
    ((D.evolution_injective_iff t).mpr hdrift) (D.minimumNormInverse_solves t u).1
  exact (hB u).trans he

end BurnolLevyData
end RHTower
