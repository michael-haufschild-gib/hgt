import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimeBandStateConvergence

/-!
# The sharp difference estimate for the whole state

Statement 234 compares two solutions by the action of the perturbations along the second solution.
It compares the *fields*. The energy estimate is about the state `(⟨D⟩u, ∂ₜu)`, and the state solves a
Volterra equation of its own in the energy space, with the same free term (an isometry applied to the
datum) and the kernel `P(t−s)∘S(W)`, where `S(W)v = (0, W⟨D⟩⁻¹v₁)`.

The same splitting applies there, and the source difference is the same quantity as before: since
`S(W₁) − S(W₂)` sends `v` to `(0, (W₁−W₂)⟨D⟩⁻¹v₁)` and the second component of the energy norm is the
whole norm of a state with vanishing first component,

`‖(S(W₁) − S(W₂))v₂(s)‖ = ‖(W₁ − W₂)u₂(s)‖`.

So the state obeys the *same* bound as the field, with the free term replaced by the energy norm of
the difference of the data:

`‖(⟨D⟩u₁, ∂ₜu₁)(t) − (⟨D⟩u₂, ∂ₜu₂)(t)‖ ≤ (‖(g₁−g₂, h₁−h₂)‖ + ∫₀ᵗ‖(W₁−W₂)u₂(s)‖ds)·e^{bt}`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A state with vanishing first component has the norm of its second. -/
theorem norm_kgPair_zero_left (z : Lp ℂ 2 (volume : Measure E)) :
    ‖kgPair E ((0 : Lp ℂ 2 (volume : Measure E)), z)‖ = ‖z‖ := by
  have h : ‖kgPair E ((0 : Lp ℂ 2 (volume : Measure E)), z)‖ ^ (2 : ℕ) = ‖z‖ ^ (2 : ℕ) := by
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgPair_fst, kgPair_snd, norm_zero]
    ring
  have h1 : (0 : ℝ) ≤ ‖kgPair E ((0 : Lp ℂ 2 (volume : Measure E)), z)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  nlinarith [h, h1, h2]

section SourceDifference

variable {W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}

/-- The difference of two energy-space sources acts only on the second component. -/
theorem kgSourceOp_sub_apply (v : KGEnergy E) :
    (kgSourceOp W₁ - kgSourceOp W₂) v
      = kgPair E ((0 : Lp ℂ 2 (volume : Measure E)), (W₁ - W₂) (kgFreqInvOp v.fst)) := by
  have h : kgPair E ((0 : Lp ℂ 2 (volume : Measure E)), W₁ (kgFreqInvOp v.fst))
      - kgPair E ((0 : Lp ℂ 2 (volume : Measure E)), W₂ (kgFreqInvOp v.fst))
      = kgPair E ((0 : Lp ℂ 2 (volume : Measure E)), (W₁ - W₂) (kgFreqInvOp v.fst)) := by
    rw [← map_sub]
    congr 1
    rw [Prod.mk_sub_mk, sub_self, sub_apply]
  rw [sub_apply, kgSourceOp_apply, kgSourceOp_apply, h]

/-- **The source difference is the field difference.** -/
theorem norm_kgSourceOp_sub_apply (v : KGEnergy E) :
    ‖(kgSourceOp W₁ - kgSourceOp W₂) v‖ = ‖(W₁ - W₂) (kgFreqInvOp v.fst)‖ := by
  rw [kgSourceOp_sub_apply, norm_kgPair_zero_left]

end SourceDifference

section StateDifference

variable {W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The difference of two states with different perturbations *and* different data. -/
theorem kgStateMild_sub_general (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) (x : ℝ) :
    kgStateMild W₁ g₁ h₁ x - kgStateMild W₂ g₂ h₂ x
      = (kgStateFree g₁ h₁ x - kgStateFree g₂ h₂ x)
        + ((∫ s in (0 : ℝ)..x, kgPropagator (x - s)
              ((kgSourceOp W₁ - kgSourceOp W₂) (kgStateMild W₂ g₂ h₂ s)))
          + ∫ s in (0 : ℝ)..x, kgPropagator (x - s)
              (kgSourceOp W₁ (kgStateMild W₁ g₁ h₁ s - kgStateMild W₂ g₂ h₂ s))) := by
  have hc1 := continuous_kgStateMild hb0 hW₁ g₁ h₁
  have hc2 := continuous_kgStateMild hb0 hW₂ g₂ h₂
  have hk1 : Continuous fun s : ℝ =>
      kgPropagator (x - s) (kgSourceOp W₁ (kgStateMild W₁ g₁ h₁ s)) :=
    continuous_kgPropagator_comp (continuous_const.sub continuous_id)
      ((kgSourceOp W₁).continuous.comp hc1)
  have hk2 : Continuous fun s : ℝ =>
      kgPropagator (x - s) (kgSourceOp W₂ (kgStateMild W₂ g₂ h₂ s)) :=
    continuous_kgPropagator_comp (continuous_const.sub continuous_id)
      ((kgSourceOp W₂).continuous.comp hc2)
  have hA : Continuous fun s : ℝ =>
      kgPropagator (x - s) ((kgSourceOp W₁ - kgSourceOp W₂) (kgStateMild W₂ g₂ h₂ s)) :=
    continuous_kgPropagator_comp (continuous_const.sub continuous_id)
      ((kgSourceOp W₁ - kgSourceOp W₂).continuous.comp hc2)
  have hB : Continuous fun s : ℝ =>
      kgPropagator (x - s)
        (kgSourceOp W₁ (kgStateMild W₁ g₁ h₁ s - kgStateMild W₂ g₂ h₂ s)) :=
    continuous_kgPropagator_comp (continuous_const.sub continuous_id)
      ((kgSourceOp W₁).continuous.comp (hc1.sub hc2))
  have hsum : (∫ s in (0 : ℝ)..x, kgPropagator (x - s)
          ((kgSourceOp W₁ - kgSourceOp W₂) (kgStateMild W₂ g₂ h₂ s)))
        + ∫ s in (0 : ℝ)..x, kgPropagator (x - s)
            (kgSourceOp W₁ (kgStateMild W₁ g₁ h₁ s - kgStateMild W₂ g₂ h₂ s))
      = (∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp W₁ (kgStateMild W₁ g₁ h₁ s)))
        - ∫ s in (0 : ℝ)..x, kgPropagator (x - s)
            (kgSourceOp W₂ (kgStateMild W₂ g₂ h₂ s)) := by
    rw [← intervalIntegral.integral_add (hA.intervalIntegrable (μ := volume) 0 x)
      (hB.intervalIntegrable (μ := volume) 0 x),
      ← intervalIntegral.integral_sub (hk1.intervalIntegrable (μ := volume) 0 x)
      (hk2.intervalIntegrable (μ := volume) 0 x)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hvec : (kgSourceOp W₁ - kgSourceOp W₂) (kgStateMild W₂ g₂ h₂ s)
        + kgSourceOp W₁ (kgStateMild W₁ g₁ h₁ s - kgStateMild W₂ g₂ h₂ s)
        = kgSourceOp W₁ (kgStateMild W₁ g₁ h₁ s) - kgSourceOp W₂ (kgStateMild W₂ g₂ h₂ s) := by
      simp only [sub_apply, map_sub]
      abel
    rw [← map_add, ← map_sub, hvec]
  have he1 := kgStateMild_eq hb0 hW₁ g₁ h₁ x
  have he2 := kgStateMild_eq hb0 hW₂ g₂ h₂ x
  have hker1 : (∫ s in (0 : ℝ)..x, kgStateKernel W₁ x s (kgStateMild W₁ g₁ h₁ s))
      = ∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp W₁ (kgStateMild W₁ g₁ h₁ s)) :=
    intervalIntegral.integral_congr fun s _ => kgStateKernel_apply W₁ x s _
  have hker2 : (∫ s in (0 : ℝ)..x, kgStateKernel W₂ x s (kgStateMild W₂ g₂ h₂ s))
      = ∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp W₂ (kgStateMild W₂ g₂ h₂ s)) :=
    intervalIntegral.integral_congr fun s _ => kgStateKernel_apply W₂ x s _
  rw [hsum, he1, he2, hker1, hker2]
  abel

/-- **The difference of two states, measured by the action of the perturbations.** The whole state —
gradient and velocity together — obeys the bound of statement 234 with the free term replaced by the
energy norm of the difference of the data. -/
theorem norm_kgStateMild_sub_general_le (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    ‖kgStateMild W₁ g₁ h₁ t - kgStateMild W₂ g₂ h₂ t‖
      ≤ (‖kgPair E (g₁ - g₂, h₁ - h₂)‖
          + ∫ s in (0 : ℝ)..t,
              ‖(W₁ - W₂) (kgFreqInvOp (kgStateMild W₂ g₂ h₂ s).fst)‖) * Real.exp (b * t) := by
  set v₁ := kgStateMild W₁ g₁ h₁ with hv₁
  set v₂ := kgStateMild W₂ g₂ h₂ with hv₂
  have hc1 : Continuous v₁ := continuous_kgStateMild hb0 hW₁ g₁ h₁
  have hc2 : Continuous v₂ := continuous_kgStateMild hb0 hW₂ g₂ h₂
  have hfstc : Continuous fun s : ℝ => (v₂ s).fst := (kgFst E).continuous.comp hc2
  have hsrc : Continuous fun s : ℝ => ‖(W₁ - W₂) (kgFreqInvOp (v₂ s).fst)‖ :=
    (((W₁ - W₂).continuous.comp ((kgFreqInvOp (E := E)).continuous.comp hfstc))).norm
  set C : ℝ := ‖kgPair E (g₁ - g₂, h₁ - h₂)‖
    + ∫ s in (0 : ℝ)..t, ‖(W₁ - W₂) (kgFreqInvOp (v₂ s).fst)‖ with hCdef
  have hScont : ContinuousOn (fun x => ‖v₁ x - v₂ x‖) (Icc 0 t) := ((hc1.sub hc2).norm).continuousOn
  have hbound : ∀ x ∈ Icc (0 : ℝ) t,
      ‖v₁ x - v₂ x‖ ≤ C + ∫ s in (0 : ℝ)..x, b * ‖v₁ s - v₂ s‖ := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hA : Continuous fun s : ℝ =>
        kgPropagator (x - s) ((kgSourceOp W₁ - kgSourceOp W₂) (v₂ s)) :=
      continuous_kgPropagator_comp (continuous_const.sub continuous_id)
        ((kgSourceOp W₁ - kgSourceOp W₂).continuous.comp hc2)
    have hB : Continuous fun s : ℝ =>
        kgPropagator (x - s) (kgSourceOp W₁ (v₁ s - v₂ s)) :=
      continuous_kgPropagator_comp (continuous_const.sub continuous_id)
        ((kgSourceOp W₁).continuous.comp (hc1.sub hc2))
    have hAint : ‖∫ s in (0 : ℝ)..x, kgPropagator (x - s)
          ((kgSourceOp W₁ - kgSourceOp W₂) (v₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, ‖(W₁ - W₂) (kgFreqInvOp (v₂ s).fst)‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hA.norm).intervalIntegrable (μ := volume) 0 x)
        (hsrc.intervalIntegrable (μ := volume) 0 x) fun s _ => ?_
      rw [norm_kgPropagator_apply, norm_kgSourceOp_sub_apply]
    have hmono : (∫ s in (0 : ℝ)..x, ‖(W₁ - W₂) (kgFreqInvOp (v₂ s).fst)‖)
        ≤ ∫ s in (0 : ℝ)..t, ‖(W₁ - W₂) (kgFreqInvOp (v₂ s).fst)‖ := by
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hsrc.intervalIntegrable (μ := volume) 0 x) (hsrc.intervalIntegrable (μ := volume) x t)
      have htail : (0 : ℝ) ≤ ∫ s in x..t, ‖(W₁ - W₂) (kgFreqInvOp (v₂ s).fst)‖ :=
        intervalIntegral.integral_nonneg hx.2 fun s _ => norm_nonneg _
      linarith [hsplit, htail]
    have hBint : ‖∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp W₁ (v₁ s - v₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, b * ‖v₁ s - v₂ s‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hB.norm).intervalIntegrable (μ := volume) 0 x)
        ((continuous_const.mul ((hc1.sub hc2).norm)).intervalIntegrable (μ := volume) 0 x)
        fun s _ => ?_
      rw [norm_kgPropagator_apply]
      exact (kgSourceOp W₁).le_of_opNorm_le (norm_kgSourceOp_le hb0 hW₁) _
    have hfree : ‖kgStateFree g₁ h₁ x - kgStateFree g₂ h₂ x‖ ≤ ‖kgPair E (g₁ - g₂, h₁ - h₂)‖ := by
      have hEq : kgStateFree g₁ h₁ x - kgStateFree (E := E) g₂ h₂ x
          = kgPropagator x (kgPair E (g₁ - g₂, h₁ - h₂)) := by
        rw [kgStateFree, kgStateFree, ← map_sub, ← map_sub]
        congr 2
      rw [hEq, norm_kgPropagator_apply]
    have hsplit : v₁ x - v₂ x
        = (kgStateFree g₁ h₁ x - kgStateFree g₂ h₂ x)
          + ((∫ s in (0 : ℝ)..x, kgPropagator (x - s)
                ((kgSourceOp W₁ - kgSourceOp W₂) (v₂ s)))
            + ∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp W₁ (v₁ s - v₂ s))) :=
      kgStateMild_sub_general hb0 hW₁ hW₂ g₁ h₁ g₂ h₂ x
    rw [hsplit, hCdef]
    have htri1 := norm_add_le (kgStateFree g₁ h₁ x - kgStateFree (E := E) g₂ h₂ x)
      ((∫ s in (0 : ℝ)..x, kgPropagator (x - s) ((kgSourceOp W₁ - kgSourceOp W₂) (v₂ s)))
        + ∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp W₁ (v₁ s - v₂ s)))
    have htri2 := norm_add_le
      (∫ s in (0 : ℝ)..x, kgPropagator (x - s) ((kgSourceOp W₁ - kgSourceOp W₂) (v₂ s)))
      (∫ s in (0 : ℝ)..x, kgPropagator (x - s) (kgSourceOp W₁ (v₁ s - v₂ s)))
    linarith [hfree, hAint, hBint, hmono, htri1, htri2]
  have hgron := le_mul_exp_integral_of_le_add_integral (S := fun x => ‖v₁ x - v₂ x‖)
    (k := fun _ => b) (C := C) ht hScont continuousOn_const (fun _ _ => hb0) hbound
    t (right_mem_Icc.mpr ht)
  refine hgron.trans ?_
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [mul_comm t b]

/-- **The sharp difference estimate for the state of the field.** Gradient and velocity together are
controlled by the difference of the data in the energy norm and the accumulated action of the
perturbations along the second solution. -/
theorem norm_kgFieldState_sub_general_le (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (g₁ h₁ g₂ h₂ : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldState W₁ g₁ h₁ t - kgFieldState W₂ g₂ h₂ t‖
      ≤ (‖kgPair E (g₁ - g₂, h₁ - h₂)‖
          + ∫ s in (0 : ℝ)..t,
              ‖(W₁ - W₂) (kgFieldMild W₂ (kgFreqInvOp g₂) h₂ s)‖) * Real.exp (b * t) := by
  have hkey := norm_kgStateMild_sub_general_le hb0 hW₁ hW₂ g₁ h₁ g₂ h₂ ht
  have hpt : ∀ s : ℝ, kgFreqInvOp (kgStateMild W₂ g₂ h₂ s).fst
      = kgFieldMild W₂ (kgFreqInvOp g₂) h₂ s := by
    intro s
    rw [← kgFieldState_eq_kgStateMild hb0 hW₂ g₂ h₂]
    exact kgFreqInvOp_kgFieldGrad hb0 hW₂ g₂ h₂ s
  have hint : (∫ s in (0 : ℝ)..t, ‖(W₁ - W₂) (kgFreqInvOp (kgStateMild W₂ g₂ h₂ s).fst)‖)
      = ∫ s in (0 : ℝ)..t, ‖(W₁ - W₂) (kgFieldMild W₂ (kgFreqInvOp g₂) h₂ s)‖ :=
    intervalIntegral.integral_congr fun s _ => by rw [hpt s]
  rw [kgFieldState_eq_kgStateMild hb0 hW₁ g₁ h₁, kgFieldState_eq_kgStateMild hb0 hW₂ g₂ h₂]
  rw [← hint]
  exact hkey

end StateDifference

end GaloisForLFunctions.HTGeometry
