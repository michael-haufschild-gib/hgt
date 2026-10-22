import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonRealPotential

/-!
# The reduced state of a moving background

The exact conservation law for a fixed self-adjoint perturbation rests on carrying the state back to
time zero by the free evolution: there the fundamental theorem of calculus applies and the unbounded
generator never appears. Nothing in that step used the autonomy of the perturbation, and this file
redoes it for a moving background.

The outcome is the differentiated energy identity

`d/dt (‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖²) = 2 re⟪W(t)u(t), ∂ₜu(t)⟫`,

valid for any uniformly bounded, strongly continuous curve of perturbations and any Cauchy datum with
one power of `⟨D⟩⁻¹` on the position. It is the input to the adiabatic estimate: the energy of the
field changes only through the work the background does on it.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TimeReduced

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The state of a moving background, carried back to time zero by the free evolution. -/
def kgReducedStateT (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : KGEnergy E :=
  kgPropagator (-t) (kgFieldStateT W g h t)

theorem kgFieldStateT_zero (g h : Lp ℂ 2 (volume : Measure E)) :
    kgFieldStateT W g h 0 = kgPair E (g, h) := by
  rw [kgFieldStateT, kgFieldGradT, kgFieldVelT, intervalIntegral.integral_same, kgCosOp_zero,
    kgSinOp_zero]
  simp

theorem norm_kgReducedStateT (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgReducedStateT W g h t‖ = ‖kgFieldStateT W g h t‖ :=
  norm_kgPropagator_apply _ _

/-- **The reduced state of a moving background is an ordinary integral.** -/
theorem kgReducedStateT_eq (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgReducedStateT W g h t
      = kgPair E (g, h)
        + ∫ s in (0 : ℝ)..t, kgPropagator (-s) (kgSourceOp (W s) (kgFieldStateT W g h s)) := by
  have hcs := continuous_kgFieldStateT hb0 hWb hWs g h
  have hI : IntervalIntegrable
      (fun s : ℝ => kgStateKernelT W t s (kgFieldStateT W g h s)) volume 0 t :=
    (((strongKernel_kgStateKernelT hWb hWs) _ hcs).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
  have hfree : kgPropagator (-t) (kgStateFree g h t) = kgPair E (g, h) := by
    rw [kgStateFree, ← ContinuousLinearMap.comp_apply, ← kgPropagator_add, neg_add_cancel]
    exact kgPropagator_zero_apply _
  have hgroup : ∀ s : ℝ, kgPropagator (-t) (kgStateKernelT W t s (kgFieldStateT W g h s))
      = kgPropagator (-s) (kgSourceOp (W s) (kgFieldStateT W g h s)) := by
    intro s
    rw [kgStateKernelT_apply, ← ContinuousLinearMap.comp_apply, ← kgPropagator_add]
    congr 2
    ring
  rw [kgReducedStateT, kgFieldStateT_duhamel hb0 hWb hWs g h t, map_add,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI, hfree]
  congr 1
  exact intervalIntegral.integral_congr fun s _ => hgroup s

/-- **The reduced state of a moving background is differentiable.** -/
theorem hasDerivAt_kgReducedStateT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgReducedStateT W g h)
      (kgPropagator (-t) (kgSourceOp (W t) (kgFieldStateT W g h t))) t := by
  have hcs := continuous_kgFieldStateT hb0 hWb hWs g h
  have hsrc : Continuous fun s : ℝ => kgSourceOp (W s) (kgFieldStateT W g h s) := by
    have hcomp : Continuous fun s : ℝ => W s (kgFreqInvOp (kgFst E (kgFieldStateT W g h s))) :=
      continuous_of_strong_comp hWb hWs continuous_id
        ((kgFreqInvOp (E := E)).continuous.comp ((kgFst E).continuous.comp hcs))
    have hpair : Continuous fun s : ℝ =>
        kgPair E ((0 : Lp ℂ 2 (volume : Measure E)),
          W s (kgFreqInvOp (kgFst E (kgFieldStateT W g h s)))) :=
      (kgPair E).continuous.comp (continuous_const.prodMk hcomp)
    exact hpair.congr fun s => (kgSourceOp_apply (W s) (kgFieldStateT W g h s)).symm
  have hcont : Continuous fun s : ℝ =>
      kgPropagator (-s) (kgSourceOp (W s) (kgFieldStateT W g h s)) :=
    continuous_kgPropagator_comp continuous_neg hsrc
  have hFTC : HasDerivAt
      (fun r : ℝ => ∫ s in (0 : ℝ)..r,
        kgPropagator (-s) (kgSourceOp (W s) (kgFieldStateT W g h s)))
      (kgPropagator (-t) (kgSourceOp (W t) (kgFieldStateT W g h t))) t :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable (μ := volume) 0 t)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hshift := hFTC.const_add (kgPair E (g, h))
  refine hshift.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun r => kgReducedStateT_eq hb0 hWb hWs g h r

/-- **The differentiated energy identity for a moving background.** The energy of the field changes
only through the work the background does on it. -/
theorem hasDerivAt_normSq_kgFieldStateT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (fun s => ‖kgFieldStateT W g h s‖ ^ (2 : ℕ))
      (RCLike.re (inner ℂ (kgFieldVelT W g h t) (W t (kgFieldMildT W (kgFreqInvOp g) h t))
        + inner ℂ (W t (kgFieldMildT W (kgFreqInvOp g) h t)) (kgFieldVelT W g h t))) t := by
  have hZ := hasDerivAt_kgReducedStateT hb0 hWb hWs g h t
  have hZsq := hasDerivAt_norm_sq_energy hZ
  have hnormeq : ∀ s : ℝ, ‖kgReducedStateT W g h s‖ ^ (2 : ℕ) = ‖kgFieldStateT W g h s‖ ^ (2 : ℕ) := by
    intro s
    rw [norm_kgReducedStateT]
  have hstateSq : HasDerivAt (fun s => ‖kgFieldStateT W g h s‖ ^ (2 : ℕ))
      (RCLike.re (inner ℂ (kgReducedStateT W g h t)
          (kgPropagator (-t) (kgSourceOp (W t) (kgFieldStateT W g h t)))
        + inner ℂ (kgPropagator (-t) (kgSourceOp (W t) (kgFieldStateT W g h t)))
          (kgReducedStateT W g h t))) t := by
    refine hZsq.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => (hnormeq s).symm
  have hin1 : (inner ℂ (kgReducedStateT W g h t)
        (kgPropagator (-t) (kgSourceOp (W t) (kgFieldStateT W g h t))) : ℂ)
      = inner ℂ (kgFieldStateT W g h t) (kgSourceOp (W t) (kgFieldStateT W g h t)) := by
    rw [kgReducedStateT, inner_kgPropagator]
  have hin2 : (inner ℂ (kgPropagator (-t) (kgSourceOp (W t) (kgFieldStateT W g h t)))
        (kgReducedStateT W g h t) : ℂ)
      = inner ℂ (kgSourceOp (W t) (kgFieldStateT W g h t)) (kgFieldStateT W g h t) := by
    rw [kgReducedStateT, inner_kgPropagator]
  have hsrc : kgSourceOp (W t) (kgFieldStateT W g h t)
      = kgPair E (0, W t (kgFieldMildT W (kgFreqInvOp g) h t)) := by
    have hproj : (kgFieldStateT W g h t).fst = kgFieldGradT W g h t := rfl
    rw [kgSourceOp_apply, hproj, kgFreqInvOp_kgFieldGradT hb0 hWb hWs g h t]
  have hcomp1 : (inner ℂ (kgFieldStateT W g h t)
        (kgSourceOp (W t) (kgFieldStateT W g h t)) : ℂ)
      = inner ℂ (kgFieldVelT W g h t) (W t (kgFieldMildT W (kgFreqInvOp g) h t)) := by
    rw [hsrc, inner_kgEnergy]
    show (inner ℂ (kgFieldGradT W g h t) (0 : Lp ℂ 2 (volume : Measure E))
      + inner ℂ (kgFieldVelT W g h t) (W t (kgFieldMildT W (kgFreqInvOp g) h t)) : ℂ) = _
    rw [inner_zero_right, zero_add]
  have hcomp2 : (inner ℂ (kgSourceOp (W t) (kgFieldStateT W g h t))
        (kgFieldStateT W g h t) : ℂ)
      = inner ℂ (W t (kgFieldMildT W (kgFreqInvOp g) h t)) (kgFieldVelT W g h t) := by
    rw [hsrc, inner_kgEnergy]
    show (inner ℂ (0 : Lp ℂ 2 (volume : Measure E)) (kgFieldGradT W g h t)
      + inner ℂ (W t (kgFieldMildT W (kgFreqInvOp g) h t)) (kgFieldVelT W g h t) : ℂ) = _
    rw [inner_zero_left, zero_add]
  rw [hin1, hin2, hcomp1, hcomp2] at hstateSq
  exact hstateSq

end TimeReduced

end GaloisForLFunctions.HTGeometry
