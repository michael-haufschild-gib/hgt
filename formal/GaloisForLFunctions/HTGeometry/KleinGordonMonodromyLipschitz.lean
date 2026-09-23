import GaloisForLFunctions.HTGeometry.KleinGordonFloquetTrichotomy

/-!
# The monodromy depends Lipschitz-continuously on the background

The Floquet criterion is a statement about one operator built from one background. For it to be usable
the operator must not jump when the background is perturbed, and it does not: the state estimate of
statement 269, applied with the same datum for both backgrounds, bounds the difference of the two
monodromies by the accumulated discrepancy over one period, and a uniform operator-norm distance `δ`
between the backgrounds bounds that by `2Tδe^{2bT}`.

The consequence is that the decaying regime is **open**: a clock whose monodromy is a strict
contraction stays a strict contraction under every small enough perturbation of its background, so it
still damps out. The Floquet verdict survives an inexactly known background.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Lipschitz

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- Each component of a datum is bounded by its energy norm. -/
theorem norm_fst_le_norm_kgPair (g h : Lp ℂ 2 (volume : Measure E)) :
    ‖g‖ ≤ ‖kgPair E (g, h)‖ := by
  have hsq := norm_kgPair_sq g h
  have h1 : (0 : ℝ) ≤ ‖kgPair E (g, h)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖g‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ‖h‖ := norm_nonneg _
  nlinarith [hsq, h1, h2, h3]

theorem norm_snd_le_norm_kgPair (g h : Lp ℂ 2 (volume : Measure E)) :
    ‖h‖ ≤ ‖kgPair E (g, h)‖ := by
  have hsq := norm_kgPair_sq g h
  have h1 : (0 : ℝ) ≤ ‖kgPair E (g, h)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖g‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ‖h‖ := norm_nonneg _
  nlinarith [hsq, h1, h2, h3]

set_option maxHeartbeats 1000000 in
/-- **A uniform distance between two backgrounds bounds the distance of their states.** -/
theorem norm_kgFieldStateT_sub_le_of_uniform (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ r : ℝ, ‖W₁ r - W₂ r‖ ≤ δ)
    (g h : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldStateT W₁ g h t - kgFieldStateT W₂ g h t‖
      ≤ t * (δ * ((‖g‖ + ‖h‖) * Real.exp (b * t))) * Real.exp (b * t) := by
  set K : ℝ := δ * ((‖g‖ + ‖h‖) * Real.exp (b * t)) with hK
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hcu : Continuous (kgFieldMildT W₂ (kgFreqInvOp g) h) :=
    continuous_kgFieldMildT hb0 hW₂b hW₂s _ _
  have hsrc : Continuous fun s : ℝ =>
      ‖(W₁ s - W₂ s) (kgFieldMildT W₂ (kgFreqInvOp g) h s)‖ := by
    have h1 : Continuous fun s : ℝ => W₁ s (kgFieldMildT W₂ (kgFreqInvOp g) h s) :=
      continuous_of_strong_comp hW₁b hW₁s continuous_id hcu
    have h2 : Continuous fun s : ℝ => W₂ s (kgFieldMildT W₂ (kgFreqInvOp g) h s) :=
      continuous_of_strong_comp hW₂b hW₂s continuous_id hcu
    refine (h1.sub h2).norm.congr fun s => ?_
    simp only [Pi.sub_apply, sub_apply]
  have hptbd : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      ‖(W₁ s - W₂ s) (kgFieldMildT W₂ (kgFreqInvOp g) h s)‖ ≤ K := by
    intro s hs
    have hs0 : 0 ≤ s := (Set.uIcc_of_le ht ▸ hs : s ∈ Set.Icc (0 : ℝ) t).1
    have hst : s ≤ t := (Set.uIcc_of_le ht ▸ hs : s ∈ Set.Icc (0 : ℝ) t).2
    have hop : ‖(W₁ s - W₂ s) (kgFieldMildT W₂ (kgFreqInvOp g) h s)‖
        ≤ δ * ‖kgFieldMildT W₂ (kgFreqInvOp g) h s‖ :=
      le_trans ((W₁ s - W₂ s).le_opNorm _)
        (mul_le_mul_of_nonneg_right (hδ s) (norm_nonneg _))
    have hu : ‖kgFieldMildT W₂ (kgFreqInvOp g) h s‖
        ≤ (‖kgFreqInvOp (E := E) g‖ + ‖h‖) * Real.exp (b * |s|) :=
      norm_kgFieldMildT_le hb0 hW₂b hW₂s _ _ s
    have hgi : ‖kgFreqInvOp (E := E) g‖ ≤ ‖g‖ := by
      have hc := (kgFreqInvOp (E := E)).le_of_opNorm_le norm_kgFreqInvOp_le g
      rwa [one_mul] at hc
    have habs : |s| = s := abs_of_nonneg hs0
    have hexp : Real.exp (b * |s|) ≤ Real.exp (b * t) := by
      rw [habs]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hb0)
    have hu' : ‖kgFieldMildT W₂ (kgFreqInvOp g) h s‖ ≤ (‖g‖ + ‖h‖) * Real.exp (b * t) := by
      refine hu.trans ?_
      exact mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)
    refine hop.trans ?_
    rw [hK]
    exact mul_le_mul_of_nonneg_left hu' hδ0
  have hint : (∫ s in (0 : ℝ)..t, ‖(W₁ s - W₂ s) (kgFieldMildT W₂ (kgFreqInvOp g) h s)‖)
      ≤ t * K := by
    have hmono := intervalIntegral.integral_mono_on ht
      (hsrc.intervalIntegrable (μ := volume) 0 t) intervalIntegrable_const
      (fun s hs => hptbd s (Set.uIcc_of_le ht ▸ hs))
    simpa using hmono
  have hkey := norm_kgFieldStateT_sub_general_le hb0 hW₁b hW₁s hW₂b hW₂s g h g h ht
  have hzero : kgPair E ((g : Lp ℂ 2 (volume : Measure E)) - g, h - h) = 0 := by
    rw [sub_self, sub_self]
    exact map_zero (kgPair E)
  rw [hzero, norm_zero, zero_add] at hkey
  refine hkey.trans ?_
  exact mul_le_mul_of_nonneg_right hint (Real.exp_pos _).le

/-- **The monodromy is Lipschitz in the background**, with constant `2Te^{2bT}`. -/
theorem norm_kgMonodromy_sub_le (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    {δ T : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ r : ℝ, ‖W₁ r - W₂ r‖ ≤ δ) (hT : 0 ≤ T) :
    ‖kgMonodromy W₁ b hb0 hW₁b hW₁s T - kgMonodromy W₂ b hb0 hW₂b hW₂s T‖
      ≤ 2 * T * δ * Real.exp (b * T) ^ (2 : ℕ) := by
  have hC0 : (0 : ℝ) ≤ 2 * T * δ * Real.exp (b * T) ^ (2 : ℕ) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun v => ?_
  have hval : (kgMonodromy W₁ b hb0 hW₁b hW₁s T - kgMonodromy W₂ b hb0 hW₂b hW₂s T) v
      = kgFieldStateT W₁ v.fst v.snd T - kgFieldStateT W₂ v.fst v.snd T := rfl
  rw [hval]
  refine (norm_kgFieldStateT_sub_le_of_uniform hb0 hW₁b hW₁s hW₂b hW₂s hδ0 hδ
    v.fst v.snd hT).trans ?_
  have h1 : ‖v.fst‖ ≤ ‖v‖ := by
    have h := norm_fst_le_norm_kgPair v.fst v.snd
    rwa [kgPair_fst_snd] at h
  have h2 : ‖v.snd‖ ≤ ‖v‖ := by
    have h := norm_snd_le_norm_kgPair v.fst v.snd
    rwa [kgPair_fst_snd] at h
  have hsum : ‖v.fst‖ + ‖v.snd‖ ≤ 2 * ‖v‖ := by linarith
  have hexp0 : (0 : ℝ) < Real.exp (b * T) := Real.exp_pos _
  have hstep : T * (δ * ((‖v.fst‖ + ‖v.snd‖) * Real.exp (b * T))) * Real.exp (b * T)
      ≤ T * (δ * ((2 * ‖v‖) * Real.exp (b * T))) * Real.exp (b * T) := by
    have hinner : (‖v.fst‖ + ‖v.snd‖) * Real.exp (b * T) ≤ (2 * ‖v‖) * Real.exp (b * T) :=
      mul_le_mul_of_nonneg_right hsum hexp0.le
    have hδinner : δ * ((‖v.fst‖ + ‖v.snd‖) * Real.exp (b * T))
        ≤ δ * ((2 * ‖v‖) * Real.exp (b * T)) := mul_le_mul_of_nonneg_left hinner hδ0
    have hTinner : T * (δ * ((‖v.fst‖ + ‖v.snd‖) * Real.exp (b * T)))
        ≤ T * (δ * ((2 * ‖v‖) * Real.exp (b * T))) := mul_le_mul_of_nonneg_left hδinner hT
    exact mul_le_mul_of_nonneg_right hTinner hexp0.le
  refine hstep.trans ?_
  apply le_of_eq
  ring

end Lipschitz

/-! ## The decaying regime is open -/

section Robust

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **A strict contraction survives a small perturbation of the background**, so the clock still
damps out. -/
theorem tendsto_kgFieldStateT_zero_of_perturbed (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    {δ T : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ r : ℝ, ‖W₁ r - W₂ r‖ ≤ δ) (hT : 0 < T)
    (hper : ∀ r : ℝ, W₁ (r + T) = W₁ r)
    (hM : ‖kgMonodromy W₂ b hb0 hW₂b hW₂s T‖ + 2 * T * δ * Real.exp (b * T) ^ (2 : ℕ) < 1)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun t : ℝ => kgFieldStateT W₁ g h t) atTop (𝓝 0) := by
  have hlip := norm_kgMonodromy_sub_le hb0 hW₁b hW₁s hW₂b hW₂s hδ0 hδ hT.le
  have hsplit : ‖kgMonodromy W₁ b hb0 hW₁b hW₁s T‖
      ≤ ‖kgMonodromy W₂ b hb0 hW₂b hW₂s T‖
        + ‖kgMonodromy W₁ b hb0 hW₁b hW₁s T - kgMonodromy W₂ b hb0 hW₂b hW₂s T‖ := by
    have h := norm_add_le (kgMonodromy W₂ b hb0 hW₂b hW₂s T)
      (kgMonodromy W₁ b hb0 hW₁b hW₁s T - kgMonodromy W₂ b hb0 hW₂b hW₂s T)
    rwa [add_sub_cancel] at h
  have hlt : ‖kgMonodromy W₁ b hb0 hW₁b hW₁s T‖ < 1 := by linarith
  exact tendsto_kgFieldStateT_zero hb0 hW₁b hW₁s hper hT hlt g h

end Robust

end GaloisForLFunctions.HTGeometry
