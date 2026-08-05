import GaloisForLFunctions.HTGeometry.KleinGordonBandEnergyUniform

/-!
# The state estimate in a moving background, and its uniform band approximation

The state estimate of statement 262 and the moving theory of statements 144–154 meet here. The
energy-space kernel of the moving equation is `P(t−s)∘S(W(s))`, so the splitting is again pointwise in
the time and the source difference is again the field difference, giving

`‖v₁(t) − v₂(t)‖ ≤ (‖(g₁−g₂, h₁−h₂)‖ + ∫₀ᵗ‖(W₁(s)−W₂(s))u₂(s)‖ds)·e^{bt}`

for the whole state. Its right-hand side is monotone in the endpoint, so the band approximation of a
moving background is uniform on every window in the state — hence in the gradient, the velocity and the
energy — and not only in the field.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section SourceCurve

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The energy-space source of a moving background is continuous along a continuous state. -/
theorem continuous_kgSourceOpT_apply (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    {v : ℝ → KGEnergy E} (hv : Continuous v) :
    Continuous fun s : ℝ => kgSourceOp (W s) (v s) := by
  have hfz : Continuous fun s : ℝ => kgFreqInvOp (v s).fst :=
    (kgFreqInvOp (E := E)).continuous.comp ((kgFst E).continuous.comp hv)
  have hWz : Continuous fun s : ℝ => W s (kgFreqInvOp (v s).fst) :=
    continuous_of_strong_comp hWb hWs continuous_id hfz
  have hzero : Continuous fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E)) := continuous_const
  refine ((kgPair E).continuous.comp (hzero.prodMk hWz)).congr fun s => ?_
  exact (kgSourceOp_apply (W s) (v s)).symm

end SourceCurve

section StateDifferenceT

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The difference of two states in different moving backgrounds and with different data. -/
theorem kgStateMildT_sub_general (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r z)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r z)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (x : ℝ) :
    kgStateMildT W₁ g₁ h₁ x - kgStateMildT W₂ g₂ h₂ x
      = (kgStateFree g₁ h₁ x - kgStateFree g₂ h₂ x)
        + ((∫ s in (0 : ℝ)..x, kgPropagator (x - s)
              ((kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (kgStateMildT W₂ g₂ h₂ s)))
          + ∫ s in (0 : ℝ)..x, kgPropagator (x - s)
              (kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s - kgStateMildT W₂ g₂ h₂ s))) := by
  have hc1 := continuous_kgStateMildT hb0 hW₁b hW₁s g₁ h₁
  have hc2 := continuous_kgStateMildT hb0 hW₂b hW₂s g₂ h₂
  have hs1 : Continuous fun s : ℝ => kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s) :=
    continuous_kgSourceOpT_apply hW₁b hW₁s hc1
  have hs2 : Continuous fun s : ℝ => kgSourceOp (W₂ s) (kgStateMildT W₂ g₂ h₂ s) :=
    continuous_kgSourceOpT_apply hW₂b hW₂s hc2
  have hs12 : Continuous fun s : ℝ => kgSourceOp (W₁ s) (kgStateMildT W₂ g₂ h₂ s) :=
    continuous_kgSourceOpT_apply hW₁b hW₁s hc2
  have hsD : Continuous fun s : ℝ =>
      (kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (kgStateMildT W₂ g₂ h₂ s) := by
    refine (hs12.sub hs2).congr fun s => ?_
    simp only [Pi.sub_apply, sub_apply]
  have hsB : Continuous fun s : ℝ =>
      kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s - kgStateMildT W₂ g₂ h₂ s) := by
    refine (hs1.sub hs12).congr fun s => ?_
    simp only [Pi.sub_apply, map_sub]
  have hk1 : Continuous fun s : ℝ =>
      kgPropagator (x - s) (kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s)) :=
    continuous_kgPropagator_comp (continuous_const.sub continuous_id) hs1
  have hk2 : Continuous fun s : ℝ =>
      kgPropagator (x - s) (kgSourceOp (W₂ s) (kgStateMildT W₂ g₂ h₂ s)) :=
    continuous_kgPropagator_comp (continuous_const.sub continuous_id) hs2
  have hA : Continuous fun s : ℝ => kgPropagator (x - s)
      ((kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (kgStateMildT W₂ g₂ h₂ s)) :=
    continuous_kgPropagator_comp (continuous_const.sub continuous_id) hsD
  have hB : Continuous fun s : ℝ => kgPropagator (x - s)
      (kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s - kgStateMildT W₂ g₂ h₂ s)) :=
    continuous_kgPropagator_comp (continuous_const.sub continuous_id) hsB
  have hsum : (∫ s in (0 : ℝ)..x, kgPropagator (x - s)
          ((kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (kgStateMildT W₂ g₂ h₂ s)))
        + ∫ s in (0 : ℝ)..x, kgPropagator (x - s)
            (kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s - kgStateMildT W₂ g₂ h₂ s))
      = (∫ s in (0 : ℝ)..x, kgPropagator (x - s)
            (kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s)))
        - ∫ s in (0 : ℝ)..x, kgPropagator (x - s)
            (kgSourceOp (W₂ s) (kgStateMildT W₂ g₂ h₂ s)) := by
    rw [← intervalIntegral.integral_add (hA.intervalIntegrable (μ := volume) 0 x)
      (hB.intervalIntegrable (μ := volume) 0 x),
      ← intervalIntegral.integral_sub (hk1.intervalIntegrable (μ := volume) 0 x)
      (hk2.intervalIntegrable (μ := volume) 0 x)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hvec : (kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (kgStateMildT W₂ g₂ h₂ s)
        + kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s - kgStateMildT W₂ g₂ h₂ s)
        = kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s)
          - kgSourceOp (W₂ s) (kgStateMildT W₂ g₂ h₂ s) := by
      simp only [sub_apply, map_sub]
      abel
    rw [← map_add, ← map_sub, hvec]
  have he1 := kgStateMildT_eq hb0 hW₁b hW₁s g₁ h₁ x
  have he2 := kgStateMildT_eq hb0 hW₂b hW₂s g₂ h₂ x
  have hker1 : (∫ s in (0 : ℝ)..x, kgStateKernelT W₁ x s (kgStateMildT W₁ g₁ h₁ s))
      = ∫ s in (0 : ℝ)..x, kgPropagator (x - s)
          (kgSourceOp (W₁ s) (kgStateMildT W₁ g₁ h₁ s)) :=
    intervalIntegral.integral_congr fun s _ => kgStateKernelT_apply W₁ x s _
  have hker2 : (∫ s in (0 : ℝ)..x, kgStateKernelT W₂ x s (kgStateMildT W₂ g₂ h₂ s))
      = ∫ s in (0 : ℝ)..x, kgPropagator (x - s)
          (kgSourceOp (W₂ s) (kgStateMildT W₂ g₂ h₂ s)) :=
    intervalIntegral.integral_congr fun s _ => kgStateKernelT_apply W₂ x s _
  rw [hsum, he1, he2, hker1, hker2]
  abel

set_option maxHeartbeats 1000000 in
/-- **The sharp difference estimate for the state in a moving background.** -/
theorem norm_kgStateMildT_sub_general_le (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r z)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r z)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    ‖kgStateMildT W₁ g₁ h₁ t - kgStateMildT W₂ g₂ h₂ t‖
      ≤ (‖kgPair E (g₁ - g₂, h₁ - h₂)‖
          + ∫ s in (0 : ℝ)..t,
              ‖(W₁ s - W₂ s) (kgFreqInvOp (kgStateMildT W₂ g₂ h₂ s).fst)‖)
        * Real.exp (b * t) := by
  set v₁ := kgStateMildT W₁ g₁ h₁ with hv₁
  set v₂ := kgStateMildT W₂ g₂ h₂ with hv₂
  have hc1 : Continuous v₁ := continuous_kgStateMildT hb0 hW₁b hW₁s g₁ h₁
  have hc2 : Continuous v₂ := continuous_kgStateMildT hb0 hW₂b hW₂s g₂ h₂
  have hs1 : Continuous fun s : ℝ => kgSourceOp (W₁ s) (v₁ s) :=
    continuous_kgSourceOpT_apply hW₁b hW₁s hc1
  have hs2 : Continuous fun s : ℝ => kgSourceOp (W₂ s) (v₂ s) :=
    continuous_kgSourceOpT_apply hW₂b hW₂s hc2
  have hs12 : Continuous fun s : ℝ => kgSourceOp (W₁ s) (v₂ s) :=
    continuous_kgSourceOpT_apply hW₁b hW₁s hc2
  have hsD : Continuous fun s : ℝ => (kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (v₂ s) := by
    refine (hs12.sub hs2).congr fun s => ?_
    simp only [Pi.sub_apply, sub_apply]
  have hsB : Continuous fun s : ℝ => kgSourceOp (W₁ s) (v₁ s - v₂ s) := by
    refine (hs1.sub hs12).congr fun s => ?_
    simp only [Pi.sub_apply, map_sub]
  have hsrc : Continuous fun s : ℝ => ‖(W₁ s - W₂ s) (kgFreqInvOp (v₂ s).fst)‖ := by
    refine hsD.norm.congr fun s => ?_
    exact norm_kgSourceOp_sub_apply (v₂ s)
  set C : ℝ := ‖kgPair E (g₁ - g₂, h₁ - h₂)‖
    + ∫ s in (0 : ℝ)..t, ‖(W₁ s - W₂ s) (kgFreqInvOp (v₂ s).fst)‖ with hCdef
  have hScont : ContinuousOn (fun x => ‖v₁ x - v₂ x‖) (Icc 0 t) :=
    ((hc1.sub hc2).norm).continuousOn
  have hbound : ∀ x ∈ Icc (0 : ℝ) t,
      ‖v₁ x - v₂ x‖ ≤ C + ∫ s in (0 : ℝ)..x, b * ‖v₁ s - v₂ s‖ := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hA : Continuous fun s : ℝ =>
        kgPropagator (x - s) ((kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (v₂ s)) :=
      continuous_kgPropagator_comp (continuous_const.sub continuous_id) hsD
    have hB : Continuous fun s : ℝ => kgPropagator (x - s) (kgSourceOp (W₁ s) (v₁ s - v₂ s)) :=
      continuous_kgPropagator_comp (continuous_const.sub continuous_id) hsB
    have hAint : ‖∫ s in (0 : ℝ)..x, kgPropagator (x - s)
          ((kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (v₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, ‖(W₁ s - W₂ s) (kgFreqInvOp (v₂ s).fst)‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hA.norm).intervalIntegrable (μ := volume) 0 x)
        (hsrc.intervalIntegrable (μ := volume) 0 x) fun s _ => ?_
      rw [norm_kgPropagator_apply, norm_kgSourceOp_sub_apply]
    have hmono : (∫ s in (0 : ℝ)..x, ‖(W₁ s - W₂ s) (kgFreqInvOp (v₂ s).fst)‖)
        ≤ ∫ s in (0 : ℝ)..t, ‖(W₁ s - W₂ s) (kgFreqInvOp (v₂ s).fst)‖ := by
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hsrc.intervalIntegrable (μ := volume) 0 x) (hsrc.intervalIntegrable (μ := volume) x t)
      have htail : (0 : ℝ) ≤ ∫ s in x..t, ‖(W₁ s - W₂ s) (kgFreqInvOp (v₂ s).fst)‖ :=
        intervalIntegral.integral_nonneg hx.2 fun s _ => norm_nonneg _
      linarith [hsplit, htail]
    have hBint : ‖∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp (W₁ s) (v₁ s - v₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, b * ‖v₁ s - v₂ s‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hB.norm).intervalIntegrable (μ := volume) 0 x)
        ((continuous_const.mul ((hc1.sub hc2).norm)).intervalIntegrable (μ := volume) 0 x)
        fun s _ => ?_
      rw [norm_kgPropagator_apply]
      exact (kgSourceOp (W₁ s)).le_of_opNorm_le (norm_kgSourceOp_le hb0 (hW₁b s)) _
    have hfree : ‖kgStateFree g₁ h₁ x - kgStateFree g₂ h₂ x‖ ≤ ‖kgPair E (g₁ - g₂, h₁ - h₂)‖ := by
      have hEq : kgStateFree g₁ h₁ x - kgStateFree (E := E) g₂ h₂ x
          = kgPropagator x (kgPair E (g₁ - g₂, h₁ - h₂)) := by
        rw [kgStateFree, kgStateFree, ← map_sub, ← map_sub]
        congr 2
      rw [hEq, norm_kgPropagator_apply]
    have hsplit : v₁ x - v₂ x
        = (kgStateFree g₁ h₁ x - kgStateFree g₂ h₂ x)
          + ((∫ s in (0 : ℝ)..x, kgPropagator (x - s)
                ((kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (v₂ s)))
            + ∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp (W₁ s) (v₁ s - v₂ s))) :=
      kgStateMildT_sub_general hb0 hW₁b hW₁s hW₂b hW₂s g₁ h₁ g₂ h₂ x
    rw [hsplit, hCdef]
    have htri1 := norm_add_le (kgStateFree g₁ h₁ x - kgStateFree (E := E) g₂ h₂ x)
      ((∫ s in (0 : ℝ)..x, kgPropagator (x - s)
          ((kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (v₂ s)))
        + ∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp (W₁ s) (v₁ s - v₂ s)))
    have htri2 := norm_add_le
      (∫ s in (0 : ℝ)..x, kgPropagator (x - s)
        ((kgSourceOp (W₁ s) - kgSourceOp (W₂ s)) (v₂ s)))
      (∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp (W₁ s) (v₁ s - v₂ s)))
    linarith [hfree, hAint, hBint, hmono, htri1, htri2]
  have hgron := le_mul_exp_integral_of_le_add_integral (S := fun x => ‖v₁ x - v₂ x‖)
    (k := fun _ => b) (C := C) ht hScont continuousOn_const (fun _ _ => hb0) hbound
    t (right_mem_Icc.mpr ht)
  refine hgron.trans ?_
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [mul_comm t b]

/-- **The sharp difference estimate for the state of the field in a moving background.** -/
theorem norm_kgFieldStateT_sub_general_le (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r z)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r z)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldStateT W₁ g₁ h₁ t - kgFieldStateT W₂ g₂ h₂ t‖
      ≤ (‖kgPair E (g₁ - g₂, h₁ - h₂)‖
          + ∫ s in (0 : ℝ)..t,
              ‖(W₁ s - W₂ s) (kgFieldMildT W₂ (kgFreqInvOp g₂) h₂ s)‖) * Real.exp (b * t) := by
  have hkey := norm_kgStateMildT_sub_general_le hb0 hW₁b hW₁s hW₂b hW₂s g₁ h₁ g₂ h₂ ht
  have hpt : ∀ s : ℝ, kgFreqInvOp (kgStateMildT W₂ g₂ h₂ s).fst
      = kgFieldMildT W₂ (kgFreqInvOp g₂) h₂ s := by
    intro s
    rw [← kgFieldStateT_eq_kgStateMildT hb0 hW₂b hW₂s g₂ h₂]
    exact kgFreqInvOp_kgFieldGradT hb0 hW₂b hW₂s g₂ h₂ s
  have hint : (∫ s in (0 : ℝ)..t, ‖(W₁ s - W₂ s) (kgFreqInvOp (kgStateMildT W₂ g₂ h₂ s).fst)‖)
      = ∫ s in (0 : ℝ)..t, ‖(W₁ s - W₂ s) (kgFieldMildT W₂ (kgFreqInvOp g₂) h₂ s)‖ :=
    intervalIntegral.integral_congr fun s _ => by rw [hpt s]
  rw [kgFieldStateT_eq_kgStateMildT hb0 hW₁b hW₁s g₁ h₁,
    kgFieldStateT_eq_kgStateMildT hb0 hW₂b hW₂s g₂ h₂, ← hint]
  exact hkey

end StateDifferenceT

/-! ## The uniform band approximation of the state in a moving background -/

section BandStateUniformT

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **One cut-off bounds the state over the whole window**, in a moving background. -/
theorem norm_kgFieldStateT_band_sub_le_endpoint (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (g y : Lp ℂ 2 (volume : Measure E)) (R : ℝ) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖kgFieldStateT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t
        - kgFieldStateT W g y t‖
      ≤ (‖kgLowPassOp R g - g‖ + ‖kgLowPassOp R y - y‖
          + ∫ s in (0 : ℝ)..T,
              ‖(kgBandOpT W R s - W s) (kgFieldMildT W (kgFreqInvOp g) y s)‖)
        * Real.exp (b * T) := by
  have hcu : Continuous (kgFieldMildT W (kgFreqInvOp g) y) :=
    continuous_kgFieldMildT hb0 hWb hWs _ _
  have hWu : Continuous fun s : ℝ => W s (kgFieldMildT W (kgFreqInvOp g) y s) :=
    continuous_of_strong_comp hWb hWs continuous_id hcu
  have hBu : Continuous fun s : ℝ => kgBandOpT W R s (kgFieldMildT W (kgFreqInvOp g) y s) :=
    continuous_of_strong_comp (norm_kgBandOpT_le hb0 hWb R)
      (continuous_kgBandOpT_apply hWs R) continuous_id hcu
  have hsrc : Continuous fun s : ℝ =>
      ‖(kgBandOpT W R s - W s) (kgFieldMildT W (kgFreqInvOp g) y s)‖ := by
    refine (hBu.sub hWu).norm.congr fun s => ?_
    simp only [Pi.sub_apply, sub_apply]
  have hI : IntervalIntegrable
      (fun s : ℝ => ‖(kgBandOpT W R s - W s) (kgFieldMildT W (kgFreqInvOp g) y s)‖)
      volume 0 T := hsrc.intervalIntegrable 0 T
  have hmono : (∫ s in (0 : ℝ)..t,
        ‖(kgBandOpT W R s - W s) (kgFieldMildT W (kgFreqInvOp g) y s)‖)
      ≤ ∫ s in (0 : ℝ)..T, ‖(kgBandOpT W R s - W s) (kgFieldMildT W (kgFreqInvOp g) y s)‖ :=
    intervalIntegral.integral_mono_interval le_rfl ht0 htT
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hI
  have hIT0 : (0 : ℝ)
      ≤ ∫ s in (0 : ℝ)..T, ‖(kgBandOpT W R s - W s) (kgFieldMildT W (kgFreqInvOp g) y s)‖ :=
    intervalIntegral.integral_nonneg (ht0.trans htT) fun _ _ => norm_nonneg _
  have hexp : Real.exp (b * t) ≤ Real.exp (b * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hb0)
  have hdata : ‖kgPair E (kgLowPassOp R g - g, kgLowPassOp R y - y)‖
      ≤ ‖kgLowPassOp R g - g‖ + ‖kgLowPassOp R y - y‖ :=
    norm_kgPair_le (E := E) (kgLowPassOp R g - g, kgLowPassOp R y - y)
  have hkey := norm_kgFieldStateT_sub_general_le hb0 (norm_kgBandOpT_le hb0 hWb R)
    (continuous_kgBandOpT_apply hWs R) hWb hWs (kgLowPassOp R g) (kgLowPassOp R y) g y ht0
  refine hkey.trans ?_
  refine mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)

/-- **The state converges uniformly on a finite observation window**, in a moving background. -/
theorem tendstoUniformlyOn_kgFieldStateT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (g y : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    TendstoUniformlyOn
      (fun R : ℝ => fun t : ℝ =>
        kgFieldStateT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      (kgFieldStateT W g y) atTop (Icc 0 T) := by
  have hcu : Continuous (kgFieldMildT W (kgFreqInvOp g) y) :=
    continuous_kgFieldMildT hb0 hWb hWs _ _
  have h1 : Tendsto (fun R : ℝ => ‖kgLowPassOp R g - g‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply g)
  have h2 : Tendsto (fun R : ℝ => ‖kgLowPassOp R y - y‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgLowPassOp_apply y)
  have h3 := tendsto_integral_kgBandOpT_sub hb0 hWb hWs
    (kgFieldMildT W (kgFreqInvOp g) y) hcu T
  have hg : Tendsto (fun R : ℝ => (‖kgLowPassOp R g - g‖ + ‖kgLowPassOp R y - y‖
      + ∫ s in (0 : ℝ)..T, ‖(kgBandOpT W R s - W s) (kgFieldMildT W (kgFreqInvOp g) y s)‖)
        * Real.exp (b * T)) atTop (𝓝 0) := by
    have hadd := (h1.add h2).add h3
    have hmul := hadd.mul_const (Real.exp (b * T))
    simpa using hmul
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hg.eventually_lt_const hε] with R hR t ht
  have hle := norm_kgFieldStateT_band_sub_le_endpoint hb0 hWb hWs g y R ht.1 ht.2
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hle hR

/-- **The gradient converges uniformly on a window**, in a moving background. -/
theorem tendstoUniformlyOn_kgFieldGradT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (g y : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    TendstoUniformlyOn
      (fun R : ℝ => fun t : ℝ =>
        kgFieldGradT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      (kgFieldGradT W g y) atTop (Icc 0 T) := by
  have hstate := tendstoUniformlyOn_kgFieldStateT_band hb0 hWb hWs g y T
  rw [Metric.tendstoUniformlyOn_iff] at hstate ⊢
  intro ε hε
  filter_upwards [hstate ε hε] with R hR t ht
  refine lt_of_le_of_lt ?_ (hR t ht)
  rw [dist_eq_norm, dist_eq_norm]
  have hfst : kgFieldGradT W g y t
      - kgFieldGradT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t
      = (kgFieldStateT W g y t
          - kgFieldStateT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t).fst := by
    rw [← kgFst_apply, map_sub]
    rfl
  rw [hfst]
  exact WithLp.norm_fst_le _ _

/-- **The velocity converges uniformly on a window**, in a moving background. -/
theorem tendstoUniformlyOn_kgFieldVelT_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (g y : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    TendstoUniformlyOn
      (fun R : ℝ => fun t : ℝ =>
        kgFieldVelT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t)
      (kgFieldVelT W g y) atTop (Icc 0 T) := by
  have hstate := tendstoUniformlyOn_kgFieldStateT_band hb0 hWb hWs g y T
  rw [Metric.tendstoUniformlyOn_iff] at hstate ⊢
  intro ε hε
  filter_upwards [hstate ε hε] with R hR t ht
  refine lt_of_le_of_lt ?_ (hR t ht)
  rw [dist_eq_norm, dist_eq_norm]
  have hsnd : kgFieldVelT W g y t
      - kgFieldVelT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t
      = (kgFieldStateT W g y t
          - kgFieldStateT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t).snd := by
    rw [← kgSnd_apply, map_sub]
    rfl
  rw [hsnd]
  exact WithLp.norm_snd_le _ _

end BandStateUniformT

end GaloisForLFunctions.HTGeometry
