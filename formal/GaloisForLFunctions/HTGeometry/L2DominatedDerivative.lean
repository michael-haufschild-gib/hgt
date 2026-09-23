import GaloisForLFunctions.HTGeometry.L2DominatedContinuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Norm differentiation of actual L² classes from a square-integrable derivative majorant. -/
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fixed L² bound on the pointwise derivative controls the genuine Hilbert-space slope limit. -/
theorem hasDerivAt_toLp_two_of_dominated (μ : Measure A) (f f' : ℝ → A → E)
    (hf : ∀ t, MemLp (f t) 2 μ) (hf' : ∀ t, MemLp (f' t) 2 μ)
    (b : A → ℝ) (hb : MemLp b 2 μ)
    (hd : ∀ᵐ a ∂μ, ∀ t, HasDerivAt (fun r => f r a) (f' t a) t)
    (hbound : ∀ᵐ a ∂μ, ∀ t, ‖f' t a‖ ≤ b a) (t : ℝ) :
    HasDerivAt (fun r => (hf r).toLp (f r)) ((hf' t).toLp (f' t)) t := by
  let g (r : ℝ) (a : A) : E := (r-t)⁻¹ • (f r a-f t a)
  have hg (r : ℝ) : MemLp (g r) 2 μ := ((hf r).sub (hf t)).const_smul (r-t)⁻¹
  have hgb (r : ℝ) : ∀ᵐ a ∂μ, ‖g r a‖ ≤ b a := by
    filter_upwards [hd,hbound] with a hd hb
    have hb₀ : 0 ≤ b a := (norm_nonneg _).trans (hb t)
    by_cases hr : r = t
    · subst r
      simpa [g] using hb₀
    have he : ‖f r a-f t a‖ ≤ b a*‖r-t‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x (_ : x ∈ (univ : Set ℝ)) => (hd x).hasDerivWithinAt)
        (fun x _ => hb x) convex_univ (mem_univ t) (mem_univ r)
    change ‖(r-t)⁻¹ • (f r a-f t a)‖ ≤ _
    rw [norm_smul,norm_inv]
    calc
      _ ≤ ‖r-t‖⁻¹*(b a*‖r-t‖) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = b a := by
        rw [mul_left_comm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hr)),mul_one]
  have hi : Integrable (fun a => 4*(b a)^(2 : ℕ)) μ :=
    ((memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb).const_mul 4
  have hlim : Tendsto (fun r => ∫ a, ‖g r a-f' t a‖^(2 : ℕ) ∂μ) (𝓝[≠] t) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[≠] t)
      (F := fun r a => ‖g r a-f' t a‖^(2 : ℕ)) (f := fun _ : A => (0:ℝ)) (fun a => 4*(b a)^(2 : ℕ))
      (Eventually.of_forall (fun r => ((hg r).aestronglyMeasurable.sub
        (hf' t).aestronglyMeasurable).norm.pow 2))
      (Eventually.of_forall (fun r => ?_)) hi ?_
    · simpa only [integral_zero] using h
    · filter_upwards [hgb r,hbound] with a ha hb
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have he := norm_sub_le (g r a) (f' t a)
      have hn := norm_nonneg (g r a-f' t a)
      have hb' := hb t
      nlinarith [norm_nonneg (f' t a)]
    · filter_upwards [hd] with a ha
      have h := ((ha t).tendsto_slope.sub (tendsto_const_nhds (x := f' t a))).norm.pow 2
      simpa only [slope_def_module,g,sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using h
  have he (r : ℝ) : (hg r).toLp (g r) =
      (r-t)⁻¹ • ((hf r).toLp (f r)-(hf t).toLp (f t)) := by
    change (((hf r).sub (hf t)).const_smul (r-t)⁻¹).toLp _ = _
    rw [MemLp.toLp_const_smul _ ((hf r).sub (hf t)),MemLp.toLp_sub]
  have hn (r : ℝ) : ‖(hg r).toLp (g r)-(hf' t).toLp (f' t)‖^(2 : ℕ) =
      ∫ a, ‖g r a-f' t a‖^(2 : ℕ) ∂μ := by
    rw [← MemLp.toLp_sub,_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [((hg r).sub (hf' t)).coeFn_toLp] with a ha
    rw [ha]
    rfl
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun r => ‖(hg r).toLp (g r)-(hf' t).toLp (f' t)‖^(2 : ℕ))
      (𝓝[≠] t) (𝓝 0) := by simpa only [hn] using hlim
  have h := (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _),he,slope_def_module] using h

end
end GaloisForLFunctions.HTGeometry
