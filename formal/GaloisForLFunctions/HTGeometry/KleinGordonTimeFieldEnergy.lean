import GaloisForLFunctions.HTGeometry.KleinGordonFieldEnergy

/-!
# The energy estimate is sharp, and survives a moving background

Two completions of the energy estimate.

The constant one cannot be improved: with no perturbation the estimate is an **equality**, because the
propagator is an isometry of the energy space and the Duhamel term is absent. So the free field
conserves `‖⟨D⟩u‖² + ‖∂ₜu‖²` exactly, and the exponential factor of the perturbed estimate is the
only room there is.

The estimate itself never used the autonomy of the perturbation. Replacing `W` by a uniformly bounded,
strongly continuous curve `W(t)` changes the kernel of the energy-space Volterra equation from
`v ↦ (0, W⟨D⟩⁻¹v₁)` to `v ↦ (0, W(s)⟨D⟩⁻¹v₁)`, whose norm is bounded by the same uniform bound, and
nothing else in the argument moves. So a clock in a time-varying background obeys the same sharp
estimate with `‖W‖` replaced by the uniform bound.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The free field conserves the energy exactly -/

theorem kgFieldGrad_zero_op (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldGrad 0 g h t = kgCosOp t g + kgSinOp t h := by
  rw [kgFieldGrad]
  have hzero : ∀ s : ℝ,
      kgSinOp (t - s) ((0 : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
        (kgFieldMild 0 (kgFreqInvOp g) h s)) = 0 := by
    intro s
    rw [zero_apply, map_zero]
  rw [intervalIntegral.integral_congr fun s _ => hzero s, intervalIntegral.integral_zero, add_zero]

theorem kgFieldVel_zero_op (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldVel 0 g h t = -(kgSinOp t g) + kgCosOp t h := by
  rw [kgFieldVel]
  have hzero : ∀ s : ℝ,
      kgCosOp (t - s) ((0 : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
        (kgFieldMild 0 (kgFreqInvOp g) h s)) = 0 := by
    intro s
    rw [zero_apply, map_zero]
  rw [intervalIntegral.integral_congr fun s _ => hzero s, intervalIntegral.integral_zero, add_zero]

/-- **The free field conserves the energy exactly**, so the constant one in the perturbed estimate
cannot be improved. -/
theorem kgFieldEnergy_zero_op (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad 0 g h t‖ ^ (2 : ℕ) + ‖kgFieldVel 0 g h t‖ ^ (2 : ℕ) = ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ) := by
  have hstate : kgFieldState (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
      g h t = kgPropagator t (kgPair E (g, h)) := by
    rw [kgFieldState, kgFieldGrad_zero_op, kgFieldVel_zero_op, kgPropagator_apply]
    rfl
  have hnorm : ‖kgFieldState (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
      g h t‖ = ‖kgPair E (g, h)‖ := by
    rw [hstate]
    exact norm_kgPropagator_apply t _
  have hsqL : ‖kgFieldState (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
        g h t‖ ^ (2 : ℕ)
      = ‖kgFieldGrad 0 g h t‖ ^ (2 : ℕ) + ‖kgFieldVel 0 g h t‖ ^ (2 : ℕ) := by
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgFieldState, kgPair_fst, kgPair_snd]
  have hsqR : ‖kgPair E (g, h)‖ ^ (2 : ℕ) = ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ) := by
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgPair_fst, kgPair_snd]
  rw [← hsqL, ← hsqR, hnorm]

/-! ## The energy-space equation with a moving background -/

section TimeState

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The Duhamel kernel of the energy-space equation with a moving background. -/
def kgStateKernelT (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (t s : ℝ) : KGEnergy E →L[ℝ] KGEnergy E :=
  (((kgPropagator (t - s)).comp (kgSourceOp (W s)) :
    KGEnergy E →L[ℂ] KGEnergy E).restrictScalars ℝ)

theorem kgStateKernelT_apply
    (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))) (t s : ℝ)
    (v : KGEnergy E) : kgStateKernelT W t s v = kgPropagator (t - s) (kgSourceOp (W s) v) := rfl

theorem norm_kgStateKernelT_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b) (t s : ℝ) :
    ‖kgStateKernelT W t s‖ ≤ b := by
  rw [kgStateKernelT, ContinuousLinearMap.norm_restrictScalars]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h := mul_le_mul (norm_kgPropagator_le_one (E := E) (t - s))
    (norm_kgSourceOp_le hb0 (hWb s)) (norm_nonneg _) zero_le_one
  rwa [one_mul] at h

/-- **The moving-background energy kernel is strongly continuous.** -/
theorem strongKernel_kgStateKernelT (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y) :
    StrongKernel (kgStateKernelT W) := by
  intro v hv
  have hcomp : Continuous fun s : ℝ => W s (kgFreqInvOp (kgFst E (v s))) :=
    continuous_of_strong_comp hWb hWs continuous_id
      ((kgFreqInvOp (E := E)).continuous.comp ((kgFst E).continuous.comp hv))
  have hsrc : Continuous fun s : ℝ => kgSourceOp (W s) (v s) := by
    have hpair : Continuous fun s : ℝ =>
        kgPair E ((0 : Lp ℂ 2 (volume : Measure E)), W s (kgFreqInvOp (kgFst E (v s)))) :=
      (kgPair E).continuous.comp (continuous_const.prodMk hcomp)
    exact hpair.congr fun s => (kgSourceOp_apply (W s) (v s)).symm
  have hjoint : Continuous fun p : ℝ × ℝ => kgPropagator (p.1 - p.2) (kgSourceOp (W p.2) (v p.2)) :=
    continuous_kgPropagator_comp (continuous_fst.sub continuous_snd) (hsrc.comp continuous_snd)
  exact hjoint.congr fun p => (kgStateKernelT_apply W p.1 p.2 (v p.2)).symm

/-- **The state of the mild solution in a moving background.** -/
def kgStateMildT (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : KGEnergy E :=
  volterraSolution (kgStateFree g h) (kgStateKernelT W) t

theorem continuous_kgStateMildT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgStateMildT W g h) :=
  continuous_volterraSolution_of_strong (continuous_kgStateFree g h)
    (strongKernel_kgStateKernelT hWb hWs) hb0 (norm_nonneg _)
    (fun t s => norm_kgStateKernelT_le hb0 hWb t s) (norm_kgStateFree_le g h)

theorem kgStateMildT_eq (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgStateMildT W g h t
      = kgStateFree g h t + ∫ s in (0 : ℝ)..t, kgStateKernelT W t s (kgStateMildT W g h s) :=
  volterraSolution_eq_of_strong (continuous_kgStateFree g h)
    (strongKernel_kgStateKernelT hWb hWs) hb0 (norm_nonneg _)
    (fun t s => norm_kgStateKernelT_le hb0 hWb t s) (norm_kgStateFree_le g h) t

theorem norm_kgStateMildT_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgStateMildT W g h t‖ ≤ ‖kgPair E (g, h)‖ * Real.exp (b * |t|) :=
  norm_volterraSolution_le_of_strong (continuous_kgStateFree g h)
    (strongKernel_kgStateKernelT hWb hWs) hb0 (norm_nonneg _)
    (fun t s => norm_kgStateKernelT_le hb0 hWb t s) (norm_kgStateFree_le g h) t

theorem eq_kgStateMildT_of_duhamel (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) {v : ℝ → KGEnergy E} (hv : Continuous v)
    (hduh : ∀ t : ℝ, v t = kgStateFree g h t + ∫ s in (0 : ℝ)..t, kgStateKernelT W t s (v s)) :
    v = kgStateMildT W g h :=
  volterra_eq_of_eq_of_eq_of_strong (strongKernel_kgStateKernelT hWb hWs) hb0
    (fun t s => norm_kgStateKernelT_le hb0 hWb t s) hv
    (continuous_kgStateMildT hb0 hWb hWs g h) hduh (kgStateMildT_eq hb0 hWb hWs g h)

end TimeState

/-! ## The gradient and the velocity in a moving background -/

section TimeField

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The gradient `⟨D⟩u` of the mild solution in a moving background. -/
def kgFieldGradT (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  kgCosOp t g + kgSinOp t h
    + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s))

/-- The velocity `∂ₜu` of the mild solution in a moving background. -/
def kgFieldVelT (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  -(kgSinOp t g) + kgCosOp t h
    + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s))

theorem kgFieldVelT_eq_deriv (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldVelT W g h t = deriv (kgFieldMildT W (kgFreqInvOp g) h) t :=
  (deriv_kgFieldMildT hb0 hWb hWs g h t).symm

theorem continuous_kgFieldGradT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgFieldGradT W g h) := by
  have hsrc := continuous_kgPotentialSource hb0 hWb hWs (kgFreqInvOp g) h
  have hF : Continuous fun p : ℝ × ℝ =>
      kgSinOp (p.1 - p.2) (W p.2 (kgFieldMildT W (kgFreqInvOp g) h p.2)) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply
      (continuous_fst.sub continuous_snd) (hsrc.comp continuous_snd)
  exact ((continuous_kgCosOp_apply g).add (continuous_kgSinOp_apply h)).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_id)

theorem continuous_kgFieldVelT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgFieldVelT W g h) := by
  have hsrc := continuous_kgPotentialSource hb0 hWb hWs (kgFreqInvOp g) h
  have hF : Continuous fun p : ℝ × ℝ =>
      kgCosOp (p.1 - p.2) (W p.2 (kgFieldMildT W (kgFreqInvOp g) h p.2)) :=
    continuous_kgCosOp_comp (continuous_fst.sub continuous_snd) (hsrc.comp continuous_snd)
  exact ((continuous_kgSinOp_apply g).neg.add (continuous_kgCosOp_apply h)).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_id)

/-- **The gradient really is `⟨D⟩u`**, in a moving background. -/
theorem kgFreqInvOp_kgFieldGradT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFreqInvOp (kgFieldGradT W g h t) = kgFieldMildT W (kgFreqInvOp g) h t := by
  have hsrc := continuous_kgPotentialSource hb0 hWb hWs (kgFreqInvOp g) h
  have hI : IntervalIntegrable
      (fun s : ℝ => kgSinOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s))) volume 0 t :=
    (continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply
      (continuous_const.sub continuous_id) hsrc).intervalIntegrable 0 t
  have hker : (∫ s in (0 : ℝ)..t, kgFieldKernelT W t s (kgFieldMildT W (kgFreqInvOp g) h s))
      = ∫ s in (0 : ℝ)..t, kgSinFreqOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernelT_apply W t s _
  have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgFreqInvOp (kgSinOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)))
        = kgSinFreqOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)) := by
    intro s _
    rw [kgFreqInvOp_kgSinOp, kgSinFreqOp_eq_comp]
    rfl
  rw [kgFieldGradT, map_add, map_add, kgFreqInvOp_kgCosOp, kgFreqInvOp_kgSinOp,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI,
    intervalIntegral.integral_congr hpt, kgFieldMildT_eq hb0 hWb hWs _ h t, hker, kgFieldFree]
  congr 1
  rw [kgSinFreqOp_eq_comp]
  rfl

/-- The state of the mild solution in a moving background. -/
def kgFieldStateT (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : KGEnergy E :=
  kgPair E (kgFieldGradT W g h t, kgFieldVelT W g h t)

theorem continuous_kgFieldStateT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgFieldStateT W g h) :=
  (kgPair E).continuous.comp
    ((continuous_kgFieldGradT hb0 hWb hWs g h).prodMk (continuous_kgFieldVelT hb0 hWb hWs g h))

set_option maxHeartbeats 1000000 in
theorem kgFieldStateT_duhamel (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT W g h t
      = kgStateFree g h t + ∫ s in (0 : ℝ)..t, kgStateKernelT W t s (kgFieldStateT W g h s) := by
  have hcs := continuous_kgFieldStateT hb0 hWb hWs g h
  have hI : IntervalIntegrable
      (fun s : ℝ => kgStateKernelT W t s (kgFieldStateT W g h s)) volume 0 t :=
    (((strongKernel_kgStateKernelT hWb hWs) _ hcs).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
  have hsrc : ∀ s : ℝ, kgSourceOp (W s) (kgFieldStateT W g h s)
      = kgPair E (0, W s (kgFieldMildT W (kgFreqInvOp g) h s)) := by
    intro s
    have hproj : (kgFieldStateT W g h s).fst = kgFieldGradT W g h s := rfl
    rw [kgSourceOp_apply, hproj, kgFreqInvOp_kgFieldGradT hb0 hWb hWs g h s]
  have hfst : ∀ s : ℝ, kgFst E (kgStateKernelT W t s (kgFieldStateT W g h s))
      = kgSinOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)) := by
    intro s
    rw [kgStateKernelT_apply, hsrc s, kgPropagator_apply]
    show kgCosOp (t - s) (0 : Lp ℂ 2 (volume : Measure E))
      + kgSinOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)) = _
    rw [map_zero, zero_add]
  have hsnd : ∀ s : ℝ, kgSnd E (kgStateKernelT W t s (kgFieldStateT W g h s))
      = kgCosOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)) := by
    intro s
    rw [kgStateKernelT_apply, hsrc s, kgPropagator_apply]
    show -(kgSinOp (t - s) (0 : Lp ℂ 2 (volume : Measure E)))
      + kgCosOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)) = _
    rw [map_zero, neg_zero, zero_add]
  refine kgEnergy_ext ?_ ?_
  · show kgFieldGradT W g h t = _
    rw [kgFieldGradT]
    have hcomp : kgFst E (kgStateFree g h t
        + ∫ s in (0 : ℝ)..t, kgStateKernelT W t s (kgFieldStateT W g h s))
        = (kgCosOp t g + kgSinOp t h)
          + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)) := by
      rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI]
      congr 1
      exact intervalIntegral.integral_congr fun s _ => hfst s
    exact hcomp.symm
  · show kgFieldVelT W g h t = _
    rw [kgFieldVelT]
    have hcomp : kgSnd E (kgStateFree g h t
        + ∫ s in (0 : ℝ)..t, kgStateKernelT W t s (kgFieldStateT W g h s))
        = (-(kgSinOp t g) + kgCosOp t h)
          + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)) := by
      rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI]
      congr 1
      exact intervalIntegral.integral_congr fun s _ => hsnd s
    exact hcomp.symm

theorem kgFieldStateT_eq_kgStateMildT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) : kgFieldStateT W g h = kgStateMildT W g h :=
  eq_kgStateMildT_of_duhamel hb0 hWb hWs g h (continuous_kgFieldStateT hb0 hWb hWs g h)
    (kgFieldStateT_duhamel hb0 hWb hWs g h)

/-- **The hyperbolic energy estimate in a moving background**, with the same sharp constant. -/
theorem kgFieldEnergyT_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT W g h t‖ ^ (2 : ℕ) + ‖kgFieldVelT W g h t‖ ^ (2 : ℕ)
      ≤ (‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ)) * Real.exp (2 * (b * |t|)) := by
  have hnorm : ‖kgFieldStateT W g h t‖ ≤ ‖kgPair E (g, h)‖ * Real.exp (b * |t|) := by
    rw [kgFieldStateT_eq_kgStateMildT hb0 hWb hWs g h]
    exact norm_kgStateMildT_le hb0 hWb hWs g h t
  have hsqL : ‖kgFieldStateT W g h t‖ ^ (2 : ℕ)
      = ‖kgFieldGradT W g h t‖ ^ (2 : ℕ) + ‖kgFieldVelT W g h t‖ ^ (2 : ℕ) := by
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgFieldStateT, kgPair_fst, kgPair_snd]
  have hsqR : ‖kgPair E (g, h)‖ ^ (2 : ℕ) = ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ) := by
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgPair_fst, kgPair_snd]
  have hnn : (0 : ℝ) ≤ ‖kgFieldStateT W g h t‖ := norm_nonneg _
  have hsq := mul_self_le_mul_self hnn hnorm
  rw [← sq, ← sq, mul_pow, hsqL, hsqR] at hsq
  have hexp : Real.exp (b * |t|) ^ (2 : ℕ) = Real.exp (2 * (b * |t|)) := by
    rw [two_mul, Real.exp_add, sq]
  rwa [hexp] at hsq

end TimeField

end GaloisForLFunctions.HTGeometry
