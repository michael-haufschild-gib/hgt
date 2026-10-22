import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandEnergy
import GaloisForLFunctions.HTGeometry.IntegralGronwall

/-!
# Comparing two solutions by what the perturbations do, not by their norms

The Lipschitz estimate of statement 136 measures the difference of two solutions by the *operator
norm* of the difference of the perturbations. That is the right measure when the perturbations are
close as operators, and useless when they are not — a perturbation can be far from another in norm and
still act almost identically on the states that actually occur.

This file replaces the operator norm by exactly that: the difference of the two solutions is bounded
by the difference of the data plus the accumulated action of `W₁ − W₂` **on the second solution**,

`‖u₁(t) − u₂(t)‖ ≤ (‖f₁−f₂‖ + ‖h₁−h₂‖ + ∫₀ᵗ‖(W₁−W₂)u₂(s)‖ds)·e^{bt}`.

Splitting `W₁u₁ − W₂u₂ = (W₁−W₂)u₂ + W₁(u₁−u₂)` puts the whole discrepancy into a source evaluated
along a *known* curve, and Grönwall closes it. Statement 136 is the special case where the source is
bounded by `‖W₁−W₂‖‖u₂‖`; the point of the sharper form is that it survives when the perturbations
converge only strongly.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Difference

variable {W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The difference of two solutions with different perturbations *and* different data. -/
theorem kgFieldMild_sub_general (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (x : ℝ) :
    kgFieldMild W₁ f₁ h₁ x - kgFieldMild W₂ f₂ h₂ x
      = (kgFieldFree f₁ h₁ x - kgFieldFree f₂ h₂ x)
        + ((∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (kgFieldMild W₂ f₂ h₂ s)))
          + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
              (W₁ (kgFieldMild W₁ f₁ h₁ s - kgFieldMild W₂ f₂ h₂ s))) := by
  have hc1 := continuous_kgFieldMild hb0 hW₁ f₁ h₁
  have hc2 := continuous_kgFieldMild hb0 hW₂ f₂ h₂
  have hk1 : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₁ (kgFieldMild W₁ f₁ h₁ s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) (W₁.continuous.comp hc1)
  have hk2 : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₂ (kgFieldMild W₂ f₂ h₂ s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) (W₂.continuous.comp hc2)
  have hA : Continuous fun s : ℝ =>
      kgSinFreqOp (x - s) ((W₁ - W₂) (kgFieldMild W₂ f₂ h₂ s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
      ((W₁ - W₂).continuous.comp hc2)
  have hB : Continuous fun s : ℝ =>
      kgSinFreqOp (x - s) (W₁ (kgFieldMild W₁ f₁ h₁ s - kgFieldMild W₂ f₂ h₂ s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
      (W₁.continuous.comp (hc1.sub hc2))
  have hsum : (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (kgFieldMild W₂ f₂ h₂ s)))
        + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
            (W₁ (kgFieldMild W₁ f₁ h₁ s - kgFieldMild W₂ f₂ h₂ s))
      = (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ (kgFieldMild W₁ f₁ h₁ s)))
        - ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ (kgFieldMild W₂ f₂ h₂ s)) := by
    rw [← intervalIntegral.integral_add (hA.intervalIntegrable (μ := volume) 0 x)
      (hB.intervalIntegrable (μ := volume) 0 x),
      ← intervalIntegral.integral_sub (hk1.intervalIntegrable (μ := volume) 0 x)
      (hk2.intervalIntegrable (μ := volume) 0 x)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hvec : (W₁ - W₂) (kgFieldMild W₂ f₂ h₂ s)
        + W₁ (kgFieldMild W₁ f₁ h₁ s - kgFieldMild W₂ f₂ h₂ s)
        = W₁ (kgFieldMild W₁ f₁ h₁ s) - W₂ (kgFieldMild W₂ f₂ h₂ s) := by
      simp only [sub_apply, map_sub]
      abel
    rw [← map_add, ← map_sub, hvec]
  have he1 := kgFieldMild_eq hb0 hW₁ f₁ h₁ x
  have he2 := kgFieldMild_eq hb0 hW₂ f₂ h₂ x
  have hker1 : (∫ s in (0 : ℝ)..x, kgFieldKernel W₁ x s (kgFieldMild W₁ f₁ h₁ s))
      = ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ (kgFieldMild W₁ f₁ h₁ s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernel_apply W₁ x s _
  have hker2 : (∫ s in (0 : ℝ)..x, kgFieldKernel W₂ x s (kgFieldMild W₂ f₂ h₂ s))
      = ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ (kgFieldMild W₂ f₂ h₂ s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernel_apply W₂ x s _
  rw [hsum, he1, he2, hker1, hker2]
  abel

/-- **The difference of two solutions, measured by the action of the perturbations.** The bound uses
only what `W₁ − W₂` does along the second solution, not its operator norm. -/
theorem norm_kgFieldMild_sub_general_le (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldMild W₁ f₁ h₁ t - kgFieldMild W₂ f₂ h₂ t‖
      ≤ (‖f₁ - f₂‖ + ‖h₁ - h₂‖
          + ∫ s in (0 : ℝ)..t, ‖(W₁ - W₂) (kgFieldMild W₂ f₂ h₂ s)‖) * Real.exp (b * t) := by
  set u₁ := kgFieldMild W₁ f₁ h₁ with hu₁
  set u₂ := kgFieldMild W₂ f₂ h₂ with hu₂
  have hc1 : Continuous u₁ := continuous_kgFieldMild hb0 hW₁ f₁ h₁
  have hc2 : Continuous u₂ := continuous_kgFieldMild hb0 hW₂ f₂ h₂
  have hsrc : Continuous fun s : ℝ => ‖(W₁ - W₂) (u₂ s)‖ :=
    ((W₁ - W₂).continuous.comp hc2).norm
  set C : ℝ := ‖f₁ - f₂‖ + ‖h₁ - h₂‖
    + ∫ s in (0 : ℝ)..t, ‖(W₁ - W₂) (u₂ s)‖ with hCdef
  have hScont : ContinuousOn (fun x => ‖u₁ x - u₂ x‖) (Icc 0 t) := ((hc1.sub hc2).norm).continuousOn
  have hbound : ∀ x ∈ Icc (0 : ℝ) t,
      ‖u₁ x - u₂ x‖ ≤ C + ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hA : Continuous fun s : ℝ => kgSinFreqOp (x - s) ((W₁ - W₂) (u₂ s)) :=
      continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
        ((W₁ - W₂).continuous.comp hc2)
    have hB : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₁ (u₁ s - u₂ s)) :=
      continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
        (W₁.continuous.comp (hc1.sub hc2))
    have hAint : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (u₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, ‖(W₁ - W₂) (u₂ s)‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hA.norm).intervalIntegrable (μ := volume) 0 x)
        (hsrc.intervalIntegrable (μ := volume) 0 x) fun s _ => ?_
      exact norm_kgSinFreqOp_apply_le (x - s) _
    have hmono : (∫ s in (0 : ℝ)..x, ‖(W₁ - W₂) (u₂ s)‖)
        ≤ ∫ s in (0 : ℝ)..t, ‖(W₁ - W₂) (u₂ s)‖ := by
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hsrc.intervalIntegrable (μ := volume) 0 x) (hsrc.intervalIntegrable (μ := volume) x t)
      have htail : (0 : ℝ) ≤ ∫ s in x..t, ‖(W₁ - W₂) (u₂ s)‖ :=
        intervalIntegral.integral_nonneg hx.2 fun s _ => norm_nonneg _
      linarith [hsplit, htail]
    have hBint : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ (u₁ s - u₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hB.norm).intervalIntegrable (μ := volume) 0 x)
        ((continuous_const.mul ((hc1.sub hc2).norm)).intervalIntegrable (μ := volume) 0 x)
        fun s _ => ?_
      exact (norm_kgSinFreqOp_apply_le (x - s) _).trans (W₁.le_of_opNorm_le hW₁ _)
    have hfree : ‖kgFieldFree f₁ h₁ x - kgFieldFree f₂ h₂ x‖ ≤ ‖f₁ - f₂‖ + ‖h₁ - h₂‖ := by
      rw [kgFieldFree_sub]
      exact norm_kgFieldFree_le _ _ x
    have hsplit : u₁ x - u₂ x
        = (kgFieldFree f₁ h₁ x - kgFieldFree f₂ h₂ x)
          + ((∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (u₂ s)))
            + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ (u₁ s - u₂ s))) :=
      kgFieldMild_sub_general hb0 hW₁ hW₂ f₁ h₁ f₂ h₂ x
    rw [hsplit, hCdef]
    have htri1 := norm_add_le (kgFieldFree f₁ h₁ x - kgFieldFree f₂ h₂ x)
      ((∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (u₂ s)))
        + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ (u₁ s - u₂ s)))
    have htri2 := norm_add_le (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (u₂ s)))
      (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ (u₁ s - u₂ s)))
    linarith [hfree, hAint, hBint, hmono, htri1, htri2]
  have hgron := le_mul_exp_integral_of_le_add_integral (S := fun x => ‖u₁ x - u₂ x‖)
    (k := fun _ => b) (C := C) ht hScont continuousOn_const (fun _ _ => hb0) hbound
    t (right_mem_Icc.mpr ht)
  refine hgron.trans ?_
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [mul_comm t b]

end Difference

end GaloisForLFunctions.HTGeometry
