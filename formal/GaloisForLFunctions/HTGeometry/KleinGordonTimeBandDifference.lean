import GaloisForLFunctions.HTGeometry.KleinGordonBandUniform
import GaloisForLFunctions.HTGeometry.KleinGordonTimePotentialVelocity

/-!
# Comparing two moving backgrounds by what they do

A clock reads a field in a background that changes with time, and the band programme so far compresses
only a fixed perturbation. This file carries the sharp difference estimate of statement 234 to the
moving case.

Nothing in the argument used autonomy. The splitting `W₁(s)u₁ − W₂(s)u₂ = (W₁(s)−W₂(s))u₂ + W₁(s)(u₁−u₂)`
is pointwise in the time, so it holds verbatim for curves of operators, and the Grönwall step only
needs the uniform bound the moving theory already assumes:

`‖u₁(t) − u₂(t)‖ ≤ (‖f₁−f₂‖ + ‖h₁−h₂‖ + ∫₀ᵗ‖(W₁(s)−W₂(s))u₂(s)‖ds)·e^{bt}`.

The band compression of a moving background is the compression at each time, and it inherits both
hypotheses of the moving theory — the uniform bound and the strong continuity — from the background
it compresses.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The band compression of a moving background -/

/-- The band compression of a moving background: the compression at each time. -/
def kgBandOpT (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))) (R t : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  kgBandOp (W t) R

theorem kgBandOpT_apply (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (R t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgBandOpT W R t x = kgLowPassOp R (W t (kgLowPassOp R x)) := rfl

section BandT

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The compression inherits the uniform bound. -/
theorem norm_kgBandOpT_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b) (R t : ℝ) :
    ‖kgBandOpT W R t‖ ≤ b :=
  norm_kgBandOp_le hb0 (hWb t) R

/-- The compression inherits the strong continuity. -/
theorem continuous_kgBandOpT_apply (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
    Continuous fun r : ℝ => W r x) (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    Continuous fun r : ℝ => kgBandOpT W R r x :=
  (kgLowPassOp R).continuous.comp (hWs (kgLowPassOp R x))

/-- **The compressions of a moving background converge strongly at each time.** -/
theorem tendsto_kgBandOpT_apply (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ]
    Lp ℂ 2 (volume : Measure E))) (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun R : ℝ => kgBandOpT W R t x) atTop (𝓝 (W t x)) :=
  tendsto_kgBandOp_apply (W₀ := W t) x

end BandT

/-! ## The difference of two solutions in different moving backgrounds -/

section DifferenceT

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The difference of two solutions in different moving backgrounds and with different data. -/
theorem kgFieldMildT_sub_general (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (x : ℝ) :
    kgFieldMildT W₁ f₁ h₁ x - kgFieldMildT W₂ f₂ h₂ x
      = (kgFieldFree f₁ h₁ x - kgFieldFree f₂ h₂ x)
        + ((∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
              ((W₁ s - W₂ s) (kgFieldMildT W₂ f₂ h₂ s)))
          + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
              (W₁ s (kgFieldMildT W₁ f₁ h₁ s - kgFieldMildT W₂ f₂ h₂ s))) := by
  have hc1 := continuous_kgFieldMildT hb0 hW₁b hW₁s f₁ h₁
  have hc2 := continuous_kgFieldMildT hb0 hW₂b hW₂s f₂ h₂
  have hs1 : Continuous fun s : ℝ => W₁ s (kgFieldMildT W₁ f₁ h₁ s) :=
    continuous_of_strong_comp hW₁b hW₁s continuous_id hc1
  have hs2 : Continuous fun s : ℝ => W₂ s (kgFieldMildT W₂ f₂ h₂ s) :=
    continuous_of_strong_comp hW₂b hW₂s continuous_id hc2
  have hs12 : Continuous fun s : ℝ => W₁ s (kgFieldMildT W₂ f₂ h₂ s) :=
    continuous_of_strong_comp hW₁b hW₁s continuous_id hc2
  have hsD : Continuous fun s : ℝ => (W₁ s - W₂ s) (kgFieldMildT W₂ f₂ h₂ s) := by
    refine (hs12.sub hs2).congr fun s => ?_
    simp only [Pi.sub_apply, sub_apply]
  have hsB : Continuous fun s : ℝ =>
      W₁ s (kgFieldMildT W₁ f₁ h₁ s - kgFieldMildT W₂ f₂ h₂ s) := by
    refine (hs1.sub hs12).congr fun s => ?_
    simp only [Pi.sub_apply, map_sub]
  have hk1 : Continuous fun s : ℝ =>
      kgSinFreqOp (x - s) (W₁ s (kgFieldMildT W₁ f₁ h₁ s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hs1
  have hk2 : Continuous fun s : ℝ =>
      kgSinFreqOp (x - s) (W₂ s (kgFieldMildT W₂ f₂ h₂ s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hs2
  have hA : Continuous fun s : ℝ =>
      kgSinFreqOp (x - s) ((W₁ s - W₂ s) (kgFieldMildT W₂ f₂ h₂ s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hsD
  have hB : Continuous fun s : ℝ => kgSinFreqOp (x - s)
      (W₁ s (kgFieldMildT W₁ f₁ h₁ s - kgFieldMildT W₂ f₂ h₂ s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hsB
  have hsum : (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          ((W₁ s - W₂ s) (kgFieldMildT W₂ f₂ h₂ s)))
        + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
            (W₁ s (kgFieldMildT W₁ f₁ h₁ s - kgFieldMildT W₂ f₂ h₂ s))
      = (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ s (kgFieldMildT W₁ f₁ h₁ s)))
        - ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ s (kgFieldMildT W₂ f₂ h₂ s)) := by
    rw [← intervalIntegral.integral_add (hA.intervalIntegrable (μ := volume) 0 x)
      (hB.intervalIntegrable (μ := volume) 0 x),
      ← intervalIntegral.integral_sub (hk1.intervalIntegrable (μ := volume) 0 x)
      (hk2.intervalIntegrable (μ := volume) 0 x)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hvec : (W₁ s - W₂ s) (kgFieldMildT W₂ f₂ h₂ s)
        + W₁ s (kgFieldMildT W₁ f₁ h₁ s - kgFieldMildT W₂ f₂ h₂ s)
        = W₁ s (kgFieldMildT W₁ f₁ h₁ s) - W₂ s (kgFieldMildT W₂ f₂ h₂ s) := by
      simp only [sub_apply, map_sub]
      abel
    rw [← map_add, ← map_sub, hvec]
  have he1 := kgFieldMildT_eq hb0 hW₁b hW₁s f₁ h₁ x
  have he2 := kgFieldMildT_eq hb0 hW₂b hW₂s f₂ h₂ x
  have hker1 : (∫ s in (0 : ℝ)..x, kgFieldKernelT W₁ x s (kgFieldMildT W₁ f₁ h₁ s))
      = ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ s (kgFieldMildT W₁ f₁ h₁ s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernelT_apply W₁ x s _
  have hker2 : (∫ s in (0 : ℝ)..x, kgFieldKernelT W₂ x s (kgFieldMildT W₂ f₂ h₂ s))
      = ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ s (kgFieldMildT W₂ f₂ h₂ s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernelT_apply W₂ x s _
  rw [hsum, he1, he2, hker1, hker2]
  abel

set_option maxHeartbeats 1000000 in
/-- **The difference of two solutions in different moving backgrounds**, measured by the action of
the backgrounds along the second solution rather than by their operator norms. -/
theorem norm_kgFieldMildT_sub_general_le (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldMildT W₁ f₁ h₁ t - kgFieldMildT W₂ f₂ h₂ t‖
      ≤ (‖f₁ - f₂‖ + ‖h₁ - h₂‖
          + ∫ s in (0 : ℝ)..t, ‖(W₁ s - W₂ s) (kgFieldMildT W₂ f₂ h₂ s)‖)
        * Real.exp (b * t) := by
  set u₁ := kgFieldMildT W₁ f₁ h₁ with hu₁
  set u₂ := kgFieldMildT W₂ f₂ h₂ with hu₂
  have hc1 : Continuous u₁ := continuous_kgFieldMildT hb0 hW₁b hW₁s f₁ h₁
  have hc2 : Continuous u₂ := continuous_kgFieldMildT hb0 hW₂b hW₂s f₂ h₂
  have hs1 : Continuous fun s : ℝ => W₁ s (u₁ s) :=
    continuous_of_strong_comp hW₁b hW₁s continuous_id hc1
  have hs2 : Continuous fun s : ℝ => W₂ s (u₂ s) :=
    continuous_of_strong_comp hW₂b hW₂s continuous_id hc2
  have hs12 : Continuous fun s : ℝ => W₁ s (u₂ s) :=
    continuous_of_strong_comp hW₁b hW₁s continuous_id hc2
  have hsD : Continuous fun s : ℝ => (W₁ s - W₂ s) (u₂ s) := by
    refine (hs12.sub hs2).congr fun s => ?_
    simp only [Pi.sub_apply, sub_apply]
  have hsB : Continuous fun s : ℝ => W₁ s (u₁ s - u₂ s) := by
    refine (hs1.sub hs12).congr fun s => ?_
    simp only [Pi.sub_apply, map_sub]
  have hsrc : Continuous fun s : ℝ => ‖(W₁ s - W₂ s) (u₂ s)‖ := hsD.norm
  set C : ℝ := ‖f₁ - f₂‖ + ‖h₁ - h₂‖
    + ∫ s in (0 : ℝ)..t, ‖(W₁ s - W₂ s) (u₂ s)‖ with hCdef
  have hScont : ContinuousOn (fun x => ‖u₁ x - u₂ x‖) (Icc 0 t) :=
    ((hc1.sub hc2).norm).continuousOn
  have hbound : ∀ x ∈ Icc (0 : ℝ) t,
      ‖u₁ x - u₂ x‖ ≤ C + ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hA : Continuous fun s : ℝ => kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₂ s)) :=
      continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hsD
    have hB : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₁ s (u₁ s - u₂ s)) :=
      continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hsB
    have hAint : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, ‖(W₁ s - W₂ s) (u₂ s)‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hA.norm).intervalIntegrable (μ := volume) 0 x)
        (hsrc.intervalIntegrable (μ := volume) 0 x) fun s _ => ?_
      exact norm_kgSinFreqOp_apply_le (x - s) _
    have hmono : (∫ s in (0 : ℝ)..x, ‖(W₁ s - W₂ s) (u₂ s)‖)
        ≤ ∫ s in (0 : ℝ)..t, ‖(W₁ s - W₂ s) (u₂ s)‖ := by
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hsrc.intervalIntegrable (μ := volume) 0 x) (hsrc.intervalIntegrable (μ := volume) x t)
      have htail : (0 : ℝ) ≤ ∫ s in x..t, ‖(W₁ s - W₂ s) (u₂ s)‖ :=
        intervalIntegral.integral_nonneg hx.2 fun s _ => norm_nonneg _
      linarith [hsplit, htail]
    have hBint : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ s (u₁ s - u₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hB.norm).intervalIntegrable (μ := volume) 0 x)
        ((continuous_const.mul ((hc1.sub hc2).norm)).intervalIntegrable (μ := volume) 0 x)
        fun s _ => ?_
      exact (norm_kgSinFreqOp_apply_le (x - s) _).trans ((W₁ s).le_of_opNorm_le (hW₁b s) _)
    have hfree : ‖kgFieldFree f₁ h₁ x - kgFieldFree f₂ h₂ x‖ ≤ ‖f₁ - f₂‖ + ‖h₁ - h₂‖ := by
      rw [kgFieldFree_sub]
      exact norm_kgFieldFree_le _ _ x
    have hsplit : u₁ x - u₂ x
        = (kgFieldFree f₁ h₁ x - kgFieldFree f₂ h₂ x)
          + ((∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₂ s)))
            + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ s (u₁ s - u₂ s))) :=
      kgFieldMildT_sub_general hb0 hW₁b hW₁s hW₂b hW₂s f₁ h₁ f₂ h₂ x
    rw [hsplit, hCdef]
    have htri1 := norm_add_le (kgFieldFree f₁ h₁ x - kgFieldFree f₂ h₂ x)
      ((∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₂ s)))
        + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ s (u₁ s - u₂ s)))
    have htri2 := norm_add_le (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₂ s)))
      (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ s (u₁ s - u₂ s)))
    linarith [hfree, hAint, hBint, hmono, htri1, htri2]
  have hgron := le_mul_exp_integral_of_le_add_integral (S := fun x => ‖u₁ x - u₂ x‖)
    (k := fun _ => b) (C := C) ht hScont continuousOn_const (fun _ _ => hb0) hbound
    t (right_mem_Icc.mpr ht)
  refine hgron.trans ?_
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [mul_comm t b]

end DifferenceT

end GaloisForLFunctions.HTGeometry
