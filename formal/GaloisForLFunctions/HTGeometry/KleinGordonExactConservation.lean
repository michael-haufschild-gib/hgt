import GaloisForLFunctions.HTGeometry.KleinGordonTimeFieldEnergy

/-!
# Exact conservation for a self-adjoint perturbation

The exponential estimate is what a general bounded perturbation allows. A *real* potential allows
much more: when `W` is self-adjoint the total energy

`E(t) = ‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖² − re⟪W u(t), u(t)⟫`

is **exactly conserved**, for the mild solution and with no regularity beyond one power of `⟨D⟩⁻¹` on
the position datum.

The obstacle to proving this in the mild theory is that the classical computation differentiates
`‖⟨D⟩u‖² + ‖∂ₜu‖²` term by term, and each term's derivative involves the unbounded generator; only
their sum is finite. The way around it is to carry the state back to time zero by the free evolution.
The reduced state

`Z(t) = S(−t)V(t) = V(0) + ∫₀ᵗ S(−s)(0, Wu(s)) ds`

is differentiable by the fundamental theorem of calculus alone — no generator appears — and `S(−t)` is
unitary, so `‖V(t)‖ = ‖Z(t)‖` and the inner products transport. What is left is the product rule for
the sesquilinear form and the self-adjointness of `W`, which makes the two derivatives cancel.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The energy space as a Hilbert space -/

/-- The inner product of the energy space is the sum of the componentwise ones. -/
theorem inner_kgEnergy (v w : KGEnergy E) :
    (inner ℂ v w : ℂ) = inner ℂ v.fst w.fst + inner ℂ v.snd w.snd :=
  Complex.ext rfl rfl

/-- The propagator, as a linear isometry of the energy space. -/
def kgPropagatorIsom (t : ℝ) : KGEnergy E →ₗᵢ[ℂ] KGEnergy E :=
  ⟨(kgPropagator t).toLinearMap, norm_kgPropagator_apply t⟩

/-- **The propagator is unitary**: it preserves the inner product, not only the norm. -/
theorem inner_kgPropagator (t : ℝ) (v w : KGEnergy E) :
    (inner ℂ (kgPropagator t v) (kgPropagator t w) : ℂ) = inner ℂ v w :=
  (kgPropagatorIsom t).inner_map_map v w

/-- The squared norm of a differentiable curve in the energy space is differentiable. -/
theorem hasDerivAt_norm_sq_energy {x : ℝ → KGEnergy E} {x' : KGEnergy E} {t : ℝ}
    (h : HasDerivAt x x' t) :
    HasDerivAt (fun s => ‖x s‖ ^ 2) (RCLike.re (inner ℂ (x t) x' + inner ℂ x' (x t))) t := by
  have hi := HasDerivAt.inner ℂ h h
  have hre := (RCLike.reCLM (K := ℂ)).hasFDerivAt.comp_hasDerivAt t hi
  refine hre.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s => norm_sq_eq_re_inner (𝕜 := ℂ) (x s)

/-! ## The reduced state -/

section Reduced

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The state carried back to time zero by the free evolution. -/
def kgReducedState (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : KGEnergy E :=
  kgPropagator (-t) (kgFieldState W g h t)

theorem kgFieldState_zero (g h : Lp ℂ 2 (volume : Measure E)) :
    kgFieldState W g h 0 = kgPair E (g, h) := by
  rw [kgFieldState, kgFieldGrad, kgFieldVel, intervalIntegral.integral_same, kgCosOp_zero,
    kgSinOp_zero]
  simp

theorem norm_kgReducedState (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgReducedState W g h t‖ = ‖kgFieldState W g h t‖ :=
  norm_kgPropagator_apply _ _

/-- **The reduced state is an ordinary integral**: no generator appears. -/
theorem kgReducedState_eq (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (g h : Lp ℂ 2 (volume : Measure E))
    (t : ℝ) :
    kgReducedState W g h t
      = kgPair E (g, h)
        + ∫ s in (0 : ℝ)..t, kgPropagator (-s) (kgSourceOp W (kgFieldState W g h s)) := by
  have hcs := continuous_kgFieldState hb0 hW g h
  have hI : IntervalIntegrable
      (fun s : ℝ => kgStateKernel W t s (kgFieldState W g h s)) volume 0 t :=
    (((strongKernel_kgStateKernel W) _ hcs).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
  have hfree : kgPropagator (-t) (kgStateFree g h t) = kgPair E (g, h) := by
    rw [kgStateFree, ← ContinuousLinearMap.comp_apply, ← kgPropagator_add]
    rw [neg_add_cancel]
    exact kgPropagator_zero_apply _
  have hgroup : ∀ s : ℝ, kgPropagator (-t) (kgStateKernel W t s (kgFieldState W g h s))
      = kgPropagator (-s) (kgSourceOp W (kgFieldState W g h s)) := by
    intro s
    rw [kgStateKernel_apply, ← ContinuousLinearMap.comp_apply, ← kgPropagator_add]
    congr 2
    ring
  rw [kgReducedState, kgFieldState_duhamel hb0 hW g h t, map_add,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI, hfree]
  congr 1
  exact intervalIntegral.integral_congr fun s _ => hgroup s

/-- **The reduced state is differentiable**, by the fundamental theorem of calculus. -/
theorem hasDerivAt_kgReducedState (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgReducedState W g h)
      (kgPropagator (-t) (kgSourceOp W (kgFieldState W g h t))) t := by
  have hcs := continuous_kgFieldState hb0 hW g h
  have hcont : Continuous fun s : ℝ => kgPropagator (-s) (kgSourceOp W (kgFieldState W g h s)) :=
    continuous_kgPropagator_comp continuous_neg ((kgSourceOp W).continuous.comp hcs)
  have hFTC : HasDerivAt
      (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgPropagator (-s) (kgSourceOp W (kgFieldState W g h s)))
      (kgPropagator (-t) (kgSourceOp W (kgFieldState W g h t))) t :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable (μ := volume) 0 t)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hshift := hFTC.const_add (kgPair E (g, h))
  refine hshift.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun r => kgReducedState_eq hb0 hW g h r

end Reduced

/-! ## Exact conservation -/

section Conservation

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The total energy of the mild solution: the kinetic and gradient terms, less the potential term.
For a self-adjoint perturbation this is exactly conserved. -/
def kgTotalEnergy (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : ℝ :=
  ‖kgFieldState W g h t‖ ^ 2
    - RCLike.re (inner ℂ (W (kgFieldMild W (kgFreqInvOp g) h t))
        (kgFieldMild W (kgFreqInvOp g) h t))

set_option maxHeartbeats 1000000 in
/-- **The derivative of the total energy vanishes** when the perturbation is self-adjoint. -/
theorem hasDerivAt_kgTotalEnergy (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W x) y : ℂ) = inner ℂ x (W y))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgTotalEnergy W g h) 0 t := by
  set u := kgFieldMild W (kgFreqInvOp g) h with hu
  set u' := kgFieldVel W g h t with hu'
  have hderiv : HasDerivAt u u' t := by
    rw [hu, hu', kgFieldVel]
    exact hasDerivAt_kgFieldMild hb0 hW g h t
  -- the derivative of the squared norm of the state
  have hZ := hasDerivAt_kgReducedState hb0 hW g h t
  have hZsq := hasDerivAt_norm_sq_energy hZ
  have hnormeq : ∀ s : ℝ, ‖kgReducedState W g h s‖ ^ 2 = ‖kgFieldState W g h s‖ ^ 2 := by
    intro s
    rw [norm_kgReducedState]
  have hstateSq : HasDerivAt (fun s => ‖kgFieldState W g h s‖ ^ 2)
      (RCLike.re (inner ℂ (kgReducedState W g h t)
          (kgPropagator (-t) (kgSourceOp W (kgFieldState W g h t)))
        + inner ℂ (kgPropagator (-t) (kgSourceOp W (kgFieldState W g h t)))
          (kgReducedState W g h t))) t := by
    refine hZsq.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => (hnormeq s).symm
  -- transport the inner products through the unitary
  have hin1 : (inner ℂ (kgReducedState W g h t)
        (kgPropagator (-t) (kgSourceOp W (kgFieldState W g h t))) : ℂ)
      = inner ℂ (kgFieldState W g h t) (kgSourceOp W (kgFieldState W g h t)) := by
    rw [kgReducedState, inner_kgPropagator]
  have hin2 : (inner ℂ (kgPropagator (-t) (kgSourceOp W (kgFieldState W g h t)))
        (kgReducedState W g h t) : ℂ)
      = inner ℂ (kgSourceOp W (kgFieldState W g h t)) (kgFieldState W g h t) := by
    rw [kgReducedState, inner_kgPropagator]
  -- and evaluate them componentwise
  have hsrc : kgSourceOp W (kgFieldState W g h t) = kgPair E (0, W (u t)) := by
    have hproj : (kgFieldState W g h t).fst = kgFieldGrad W g h t := rfl
    rw [kgSourceOp_apply, hproj, hu, kgFreqInvOp_kgFieldGrad hb0 hW g h t]
  have hcomp1 : (inner ℂ (kgFieldState W g h t) (kgSourceOp W (kgFieldState W g h t)) : ℂ)
      = inner ℂ u' (W (u t)) := by
    rw [hsrc, inner_kgEnergy]
    show (inner ℂ (kgFieldGrad W g h t) (0 : Lp ℂ 2 (volume : Measure E))
      + inner ℂ (kgFieldVel W g h t) (W (u t)) : ℂ) = _
    rw [inner_zero_right, zero_add, hu']
  have hcomp2 : (inner ℂ (kgSourceOp W (kgFieldState W g h t)) (kgFieldState W g h t) : ℂ)
      = inner ℂ (W (u t)) u' := by
    rw [hsrc, inner_kgEnergy]
    show (inner ℂ (0 : Lp ℂ 2 (volume : Measure E)) (kgFieldGrad W g h t)
      + inner ℂ (W (u t)) (kgFieldVel W g h t) : ℂ) = _
    rw [inner_zero_left, zero_add, hu']
  rw [hin1, hin2, hcomp1, hcomp2] at hstateSq
  -- the derivative of the potential term
  have hpot : HasDerivAt (fun s => (inner ℂ (W (u s)) (u s) : ℂ))
      (inner ℂ (W (u t)) u' + inner ℂ (W u') (u t)) t :=
    HasDerivAt.inner ℂ (hasDerivAt_clm W hderiv) hderiv
  have hpotRe : HasDerivAt (fun s => RCLike.re (inner ℂ (W (u s)) (u s) : ℂ))
      (RCLike.re (inner ℂ (W (u t)) u' + inner ℂ (W u') (u t))) t :=
    (RCLike.reCLM (K := ℂ)).hasFDerivAt.comp_hasDerivAt t hpot
  have hdiff := hstateSq.sub hpotRe
  have hzero : RCLike.re (inner ℂ u' (W (u t)) + inner ℂ (W (u t)) u')
      - RCLike.re (inner ℂ (W (u t)) u' + inner ℂ (W u') (u t)) = 0 := by
    have hswap : (inner ℂ (W u') (u t) : ℂ) = inner ℂ u' (W (u t)) := hsa u' (u t)
    rw [hswap, map_add, map_add]
    ring
  rw [hzero] at hdiff
  exact hdiff

/-- **The total energy of a self-adjoint perturbation is exactly conserved.** No regularity beyond
one power of `⟨D⟩⁻¹` on the position datum, and no smallness: the conservation is exact. -/
theorem kgTotalEnergy_const (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W x) y : ℂ) = inner ℂ x (W y))
    (g h : Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    kgTotalEnergy W g h t = kgTotalEnergy W g h s :=
  is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (fun x => (hasDerivAt_kgTotalEnergy hb0 hW hsa g h x).differentiableAt)
    (fun x => (hasDerivAt_kgTotalEnergy hb0 hW hsa g h x).deriv) t s

/-- **The conservation law in explicit form.** -/
theorem kgFieldEnergy_conserved (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W x) y : ℂ) = inner ℂ x (W y))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad W g h t‖ ^ 2 + ‖kgFieldVel W g h t‖ ^ 2
        - RCLike.re (inner ℂ (W (kgFieldMild W (kgFreqInvOp g) h t))
            (kgFieldMild W (kgFreqInvOp g) h t))
      = ‖g‖ ^ 2 + ‖h‖ ^ 2
        - RCLike.re (inner ℂ (W (kgFreqInvOp g)) (kgFreqInvOp g)) := by
  have hconst := kgTotalEnergy_const hb0 hW hsa g h t 0
  have hsq : ∀ r : ℝ, ‖kgFieldState W g h r‖ ^ 2
      = ‖kgFieldGrad W g h r‖ ^ 2 + ‖kgFieldVel W g h r‖ ^ 2 := by
    intro r
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgFieldState, kgPair_fst, kgPair_snd]
  have hzeroSq : ‖kgFieldState W g h 0‖ ^ 2 = ‖g‖ ^ 2 + ‖h‖ ^ 2 := by
    rw [kgFieldState_zero, ← kgEnergy_eq_norm_sq, kgEnergy, kgPair_fst, kgPair_snd]
  have hzeroU : kgFieldMild W (kgFreqInvOp g) h 0 = kgFreqInvOp g :=
    kgFieldMild_zero hb0 hW _ h
  rw [kgTotalEnergy, kgTotalEnergy, hsq t, hzeroSq, hzeroU] at hconst
  exact hconst

end Conservation

end GaloisForLFunctions.HTGeometry
