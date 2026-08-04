import GaloisForLFunctions.HTGeometry.KleinGordonSourceVanishing
import GaloisForLFunctions.HTGeometry.KleinGordonTimePotentialVelocity
import GaloisForLFunctions.HTGeometry.IntegralGronwall

/-!
# The moving background is determined by the field, and depends on it stably

The two halves of the inverse problem, for a time-dependent perturbation.

The Lipschitz estimate is the autonomous one with the potential evaluated at the source time: the
difference of the two Duhamel formulas splits into a source `(W₁(s)-W₂(s))u₁(s)` and a memory term
`W₂(s)(u₁(s)-u₂(s))`, and Grönwall closes it.

The injectivity half is sharper here than in the autonomous case, because the vanishing statement for
Duhamel sources is now available at every time and not only at the origin. If two moving backgrounds
produce the same field, then `W₁(r)` and `W₂(r)` agree on the state the field occupies at time `r`,
for every `r` and every Cauchy datum — a statement about the whole history, not one instant.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Stability

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b δ : ℝ}

/-- The difference of two solutions with different moving backgrounds, in Duhamel form. -/
theorem kgFieldMildT_sub_potential (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    (f h : Lp ℂ 2 (volume : Measure E)) (x : ℝ) :
    kgFieldMildT W₁ f h x - kgFieldMildT W₂ f h x
      = (∫ s in (0 : ℝ)..x,
          kgSinFreqOp (x - s) ((W₁ s - W₂ s) (kgFieldMildT W₁ f h s)))
        + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
            (W₂ s (kgFieldMildT W₁ f h s - kgFieldMildT W₂ f h s)) := by
  have hc1 := continuous_kgFieldMildT hb0 hW₁b hW₁s f h
  have hc2 := continuous_kgFieldMildT hb0 hW₂b hW₂s f h
  have hk1 : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₁ s (kgFieldMildT W₁ f h s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
      (continuous_kgPotentialSource hb0 hW₁b hW₁s f h)
  have hk2 : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₂ s (kgFieldMildT W₂ f h s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
      (continuous_kgPotentialSource hb0 hW₂b hW₂s f h)
  have hd1 : Continuous fun s : ℝ => W₁ s (kgFieldMildT W₁ f h s) :=
    continuous_kgPotentialSource hb0 hW₁b hW₁s f h
  have hd2 : Continuous fun s : ℝ => W₂ s (kgFieldMildT W₁ f h s) :=
    continuous_of_strong_comp hW₂b hW₂s continuous_id hc1
  have hd3 : Continuous fun s : ℝ => W₂ s (kgFieldMildT W₂ f h s) :=
    continuous_kgPotentialSource hb0 hW₂b hW₂s f h
  have hA : Continuous fun s : ℝ =>
      kgSinFreqOp (x - s) ((W₁ s - W₂ s) (kgFieldMildT W₁ f h s)) := by
    refine continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) ?_
    refine (hd1.sub hd2).congr fun s => ?_
    simp only [Pi.sub_apply, sub_apply]
  have hB : Continuous fun s : ℝ =>
      kgSinFreqOp (x - s) (W₂ s (kgFieldMildT W₁ f h s - kgFieldMildT W₂ f h s)) := by
    refine continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) ?_
    refine (hd2.sub hd3).congr fun s => ?_
    simp only [Pi.sub_apply, map_sub]
  have hsum : (∫ s in (0 : ℝ)..x,
          kgSinFreqOp (x - s) ((W₁ s - W₂ s) (kgFieldMildT W₁ f h s)))
        + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
            (W₂ s (kgFieldMildT W₁ f h s - kgFieldMildT W₂ f h s))
      = (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ s (kgFieldMildT W₁ f h s)))
        - ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ s (kgFieldMildT W₂ f h s)) := by
    rw [← intervalIntegral.integral_add (hA.intervalIntegrable (μ := volume) 0 x)
      (hB.intervalIntegrable (μ := volume) 0 x),
      ← intervalIntegral.integral_sub (hk1.intervalIntegrable (μ := volume) 0 x)
      (hk2.intervalIntegrable (μ := volume) 0 x)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hvec : (W₁ s - W₂ s) (kgFieldMildT W₁ f h s)
        + W₂ s (kgFieldMildT W₁ f h s - kgFieldMildT W₂ f h s)
        = W₁ s (kgFieldMildT W₁ f h s) - W₂ s (kgFieldMildT W₂ f h s) := by
      simp only [sub_apply, map_sub]
      abel
    rw [← map_add, ← map_sub, hvec]
  have he1 := kgFieldMildT_eq hb0 hW₁b hW₁s f h x
  have he2 := kgFieldMildT_eq hb0 hW₂b hW₂s f h x
  have hker1 : (∫ s in (0 : ℝ)..x, kgFieldKernelT W₁ x s (kgFieldMildT W₁ f h s))
      = ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ s (kgFieldMildT W₁ f h s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernelT_apply W₁ x s _
  have hker2 : (∫ s in (0 : ℝ)..x, kgFieldKernelT W₂ x s (kgFieldMildT W₂ f h s))
      = ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ s (kgFieldMildT W₂ f h s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernelT_apply W₂ x s _
  rw [hsum, he1, he2, hker1, hker2]
  abel

/-- **The solution is Lipschitz in the moving background**, forwards in time. -/
theorem norm_kgFieldMildT_sub_potential_le_of_nonneg (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    (hδ0 : 0 ≤ δ) (hδ : ∀ r : ℝ, ‖W₁ r - W₂ r‖ ≤ δ) (f h : Lp ℂ 2 (volume : Measure E))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldMildT W₁ f h t - kgFieldMildT W₂ f h t‖
      ≤ δ * ((‖f‖ + ‖h‖) * t) * Real.exp (2 * (b * t)) := by
  set u₁ := kgFieldMildT W₁ f h with hu₁
  set u₂ := kgFieldMildT W₂ f h with hu₂
  set D : ℝ := ‖f‖ + ‖h‖ with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  set M : ℝ := D * Real.exp (b * t) with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hc1 : Continuous u₁ := continuous_kgFieldMildT hb0 hW₁b hW₁s f h
  have hc2 : Continuous u₂ := continuous_kgFieldMildT hb0 hW₂b hW₂s f h
  have hScont : ContinuousOn (fun x => ‖u₁ x - u₂ x‖) (Icc 0 t) := ((hc1.sub hc2).norm).continuousOn
  have hu₁bound : ∀ s ∈ Icc (0 : ℝ) t, ‖u₁ s‖ ≤ M := by
    intro s hs
    have h1 : ‖u₁ s‖ ≤ D * Real.exp (b * |s|) := norm_kgFieldMildT_le hb0 hW₁b hW₁s f h s
    have habs : |s| ≤ t := by rw [abs_of_nonneg hs.1]; exact hs.2
    have h2 : Real.exp (b * |s|) ≤ Real.exp (b * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hD0)
  have hbound : ∀ x ∈ Icc (0 : ℝ) t,
      ‖u₁ x - u₂ x‖ ≤ δ * (M * t) + ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hd1 : Continuous fun s : ℝ => W₁ s (u₁ s) :=
      continuous_kgPotentialSource hb0 hW₁b hW₁s f h
    have hd2 : Continuous fun s : ℝ => W₂ s (u₁ s) :=
      continuous_of_strong_comp hW₂b hW₂s continuous_id hc1
    have hd3 : Continuous fun s : ℝ => W₂ s (u₂ s) :=
      continuous_kgPotentialSource hb0 hW₂b hW₂s f h
    have hA : Continuous fun s : ℝ => kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₁ s)) := by
      refine continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) ?_
      refine (hd1.sub hd2).congr fun s => ?_
      simp only [Pi.sub_apply, sub_apply]
    have hB : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₂ s (u₁ s - u₂ s)) := by
      refine continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) ?_
      refine (hd2.sub hd3).congr fun s => ?_
      simp only [Pi.sub_apply, map_sub]
    have hAbd : ∀ s ∈ Set.uIoc (0 : ℝ) x,
        ‖kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₁ s))‖ ≤ δ * M := by
      intro s hs
      have hsmem : s ∈ Icc (0 : ℝ) t := by
        rcases Set.mem_uIoc.mp hs with hs' | hs'
        · exact ⟨le_of_lt hs'.1, le_trans hs'.2 hx.2⟩
        · exact absurd (hs'.1.trans_le (hs'.2.trans hx0)) (lt_irrefl x)
      have h1 := norm_kgSinFreqOp_apply_le (x - s) ((W₁ s - W₂ s) (u₁ s))
      have h2 : ‖(W₁ s - W₂ s) (u₁ s)‖ ≤ δ * ‖u₁ s‖ := (W₁ s - W₂ s).le_of_opNorm_le (hδ s) _
      have h3 : ‖u₁ s‖ ≤ M := hu₁bound s hsmem
      calc ‖kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₁ s))‖ ≤ ‖(W₁ s - W₂ s) (u₁ s)‖ := h1
        _ ≤ δ * ‖u₁ s‖ := h2
        _ ≤ δ * M := mul_le_mul_of_nonneg_left h3 hδ0
    have hAint : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₁ s))‖
        ≤ δ * M * x := by
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const hAbd
      simpa [abs_of_nonneg hx0] using hle
    have hBint : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ s (u₁ s - u₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hB.norm).intervalIntegrable (μ := volume) 0 x)
        ((continuous_const.mul ((hc1.sub hc2).norm)).intervalIntegrable (μ := volume) 0 x)
        fun s _ => ?_
      have h1 := norm_kgSinFreqOp_apply_le (x - s) (W₂ s (u₁ s - u₂ s))
      have h2 : ‖W₂ s (u₁ s - u₂ s)‖ ≤ b * ‖u₁ s - u₂ s‖ := (W₂ s).le_of_opNorm_le (hW₂b s) _
      exact h1.trans h2
    have hsplit : u₁ x - u₂ x
        = (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ s - W₂ s) (u₁ s)))
          + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ s (u₁ s - u₂ s)) :=
      kgFieldMildT_sub_potential hb0 hW₁b hW₁s hW₂b hW₂s f h x
    have hstep : ‖u₁ x - u₂ x‖ ≤ δ * M * x + ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (add_le_add hAint hBint)
    refine hstep.trans ?_
    have hxt : δ * M * x ≤ δ * (M * t) := by
      have hle : δ * M * x ≤ δ * M * t := mul_le_mul_of_nonneg_left hx.2 (by positivity)
      linarith
    linarith
  have hgron := le_mul_exp_integral_of_le_add_integral (S := fun x => ‖u₁ x - u₂ x‖)
    (k := fun _ => b) (C := δ * (M * t)) ht hScont continuousOn_const (fun _ _ => hb0) hbound
    t (right_mem_Icc.mpr ht)
  refine hgron.trans ?_
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hexp2 : Real.exp (2 * (b * t)) = Real.exp (b * t) * Real.exp (b * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htb : t * b = b * t := mul_comm t b
  refine le_of_eq ?_
  rw [hMdef, hexp2, htb]
  ring

/-- **The solution is Lipschitz in the moving background.** -/
theorem norm_kgFieldMildT_sub_potential_le (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    (hδ0 : 0 ≤ δ) (hδ : ∀ r : ℝ, ‖W₁ r - W₂ r‖ ≤ δ) (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMildT W₁ f h t - kgFieldMildT W₂ f h t‖
      ≤ δ * ((‖f‖ + ‖h‖) * |t|) * Real.exp (2 * (b * |t|)) := by
  rcases le_total (0 : ℝ) t with ht | ht
  · rw [abs_of_nonneg ht]
    exact norm_kgFieldMildT_sub_potential_le_of_nonneg hb0 hW₁b hW₁s hW₂b hW₂s hδ0 hδ f h ht
  · have hneg : (0 : ℝ) ≤ -t := by linarith
    have hV₁b : ∀ r : ℝ, ‖W₁ (-r)‖ ≤ b := fun r => hW₁b (-r)
    have hV₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ (-r) x := fun x =>
      (hW₁s x).comp continuous_neg
    have hV₂b : ∀ r : ℝ, ‖W₂ (-r)‖ ≤ b := fun r => hW₂b (-r)
    have hV₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ (-r) x := fun x =>
      (hW₂s x).comp continuous_neg
    have hVδ : ∀ r : ℝ, ‖W₁ (-r) - W₂ (-r)‖ ≤ δ := fun r => hδ (-r)
    have hkey := norm_kgFieldMildT_sub_potential_le_of_nonneg hb0 hV₁b hV₁s hV₂b hV₂s hδ0 hVδ
      f (-h) hneg
    rw [← kgFieldMildT_neg hb0 hW₁b hW₁s f h (-t), ← kgFieldMildT_neg hb0 hW₂b hW₂s f h (-t),
      neg_neg, norm_neg] at hkey
    rw [abs_of_nonpos ht]
    exact hkey

/-! ## The moving background is seen by the field -/

/-- **The perturbation is determined along the history of the solution.** If two moving backgrounds
produce the same field from every Cauchy datum, then at every time they agree on the state the field
occupies at that time. -/
theorem kgFieldMildT_potential_apply_eq (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    (heq : ∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ),
      kgFieldMildT W₁ f h t = kgFieldMildT W₂ f h t)
    (f h : Lp ℂ 2 (volume : Measure E)) (r : ℝ) :
    W₁ r (kgFieldMildT W₁ f h r) = W₂ r (kgFieldMildT W₁ f h r) := by
  have hc1 := continuous_kgFieldMildT hb0 hW₁b hW₁s f h
  have hd1 : Continuous fun s : ℝ => W₁ s (kgFieldMildT W₁ f h s) :=
    continuous_kgPotentialSource hb0 hW₁b hW₁s f h
  have hd2 : Continuous fun s : ℝ => W₂ s (kgFieldMildT W₁ f h s) :=
    continuous_of_strong_comp hW₂b hW₂s continuous_id hc1
  have hg : Continuous fun s : ℝ => (W₁ s - W₂ s) (kgFieldMildT W₁ f h s) := by
    refine (hd1.sub hd2).congr fun s => ?_
    simp only [Pi.sub_apply, sub_apply]
  have hdiff : ∀ s : ℝ, kgFieldMildT W₁ f h s - kgFieldMildT W₂ f h s = 0 := fun s =>
    sub_eq_zero.mpr (heq f h s)
  have hzero : ∀ x : ℝ,
      (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ s - W₂ s) (kgFieldMildT W₁ f h s))) = 0 := by
    intro x
    have hsplit := kgFieldMildT_sub_potential hb0 hW₁b hW₁s hW₂b hW₂s f h x
    have h2 : (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
        (W₂ s (kgFieldMildT W₁ f h s - kgFieldMildT W₂ f h s))) = 0 := by
      have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) x, kgSinFreqOp (x - s)
          (W₂ s (kgFieldMildT W₁ f h s - kgFieldMildT W₂ f h s)) = 0 := by
        intro s _
        rw [hdiff s, map_zero, map_zero]
      rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_zero]
    rw [hdiff x, h2, add_zero] at hsplit
    exact hsplit.symm
  have hgr := eq_zero_of_intervalIntegral_kgSinFreqOp_eq_zero' hg hzero r
  rw [sub_apply] at hgr
  exact sub_eq_zero.mp hgr

/-- **The moving background is determined at the initial time.** -/
theorem eq_zero_of_kgFieldMildT_eq (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    (heq : ∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ),
      kgFieldMildT W₁ f h t = kgFieldMildT W₂ f h t) :
    W₁ 0 = W₂ 0 := by
  refine ContinuousLinearMap.ext fun f => ?_
  have hkey := kgFieldMildT_potential_apply_eq hb0 hW₁b hW₁s hW₂b hW₂s heq f 0 0
  rwa [kgFieldMildT_zero hb0 hW₁b hW₁s f 0] at hkey

end Stability

end GaloisForLFunctions.HTGeometry
