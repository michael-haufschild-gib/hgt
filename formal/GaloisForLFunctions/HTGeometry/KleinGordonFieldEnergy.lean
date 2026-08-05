import GaloisForLFunctions.HTGeometry.KleinGordonOptimalProbe

/-!
# The hyperbolic energy estimate, sharp, for an arbitrary bounded perturbation

The card opens with the energy method for pointwise solutions. This file closes it in the register
the rest of the corpus works in: the mild `L²` solution of `∂ₜ²u = -⟨D⟩²u + Wu`, with `W` an
arbitrary bounded operator and no regularity or smoothing hypothesis at all, obeys

`‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖² ≤ (‖⟨D⟩u(0)‖² + ‖∂ₜu(0)‖²)·e^{2‖W‖|t|}`

with **constant one** and rate exactly `‖W‖`. Both are sharp: the free evolution conserves the energy
exactly, so no constant smaller than one is possible, and the rate is attained.

The proof is the energy method read through the propagator rather than through an integration by
parts. The gradient and the velocity are given in closed form by the two Duhamel formulas, and the
pair they form solves a Volterra equation in the energy space whose free term is the propagator —
an **isometry** — and whose kernel is the propagator composed with `v ↦ (0, W⟨D⟩⁻¹v₁)`, of norm at
most `‖W‖` because `⟨D⟩⁻¹` is a contraction. The Volterra layer's own exponential bound is then
already the sharp estimate; the work is the identification of the pair with `(⟨D⟩u, ∂ₜu)`, which is
uniqueness applied to the two closed formulas.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Two energy states agree when their components do. -/
theorem kgEnergy_ext {v w : KGEnergy E} (h1 : v.fst = w.fst) (h2 : v.snd = w.snd) : v = w := by
  rw [← kgPair_fst_snd v, ← kgPair_fst_snd w, h1, h2]

/-! ## The source of the energy-space equation -/

/-- The source term of the energy-space equation: the perturbation applied to the field, which is the
first component divided by the frequency. -/
def kgSourceOp (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :
    KGEnergy E →L[ℂ] KGEnergy E :=
  (kgPair E).comp
    ((0 : KGEnergy E →L[ℂ] Lp ℂ 2 (volume : Measure E)).prod
      (W.comp (kgFreqInvOp.comp (kgFst E))))

theorem kgSourceOp_apply (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (v : KGEnergy E) : kgSourceOp W v = kgPair E (0, W (kgFreqInvOp v.fst)) := rfl

theorem norm_kgSourceOp_le {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {b : ℝ} (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) : ‖kgSourceOp W‖ ≤ b := by
  refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun v => ?_
  rw [kgSourceOp_apply]
  refine (norm_kgPair_le (E := E) (0, W (kgFreqInvOp v.fst))).trans ?_
  have h1 : ‖W (kgFreqInvOp (E := E) v.fst)‖ ≤ b * ‖kgFreqInvOp (E := E) v.fst‖ :=
    W.le_of_opNorm_le hW _
  have h2 : ‖kgFreqInvOp (E := E) v.fst‖ ≤ ‖v.fst‖ := by
    have h := (kgFreqInvOp (E := E)).le_of_opNorm_le norm_kgFreqInvOp_le v.fst
    rwa [one_mul] at h
  have h3 : ‖v.fst‖ ≤ ‖v‖ := WithLp.norm_fst_le _ v
  have h4 : ‖W (kgFreqInvOp (E := E) v.fst)‖ ≤ b * ‖v‖ :=
    h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) hb0)
  simpa using h4

/-! ## The state equation in the energy space -/

/-- The free evolution of the energy datum. -/
def kgStateFree (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : KGEnergy E :=
  kgPropagator t (kgPair E (g, h))

theorem continuous_kgStateFree (g h : Lp ℂ 2 (volume : Measure E)) :
    Continuous (kgStateFree g h) :=
  continuous_kgPropagator_comp continuous_id continuous_const

theorem norm_kgStateFree_le (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgStateFree g h t‖ ≤ ‖kgPair E (g, h)‖ :=
  le_of_eq (norm_kgPropagator_apply t _)

/-- The Duhamel kernel of the energy-space equation. -/
def kgStateKernel (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    KGEnergy E →L[ℝ] KGEnergy E :=
  (((kgPropagator (t - s)).comp (kgSourceOp W) : KGEnergy E →L[ℂ] KGEnergy E).restrictScalars ℝ)

theorem kgStateKernel_apply (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (t s : ℝ) (v : KGEnergy E) :
    kgStateKernel W t s v = kgPropagator (t - s) (kgSourceOp W v) := rfl

theorem norm_kgStateKernel_le {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {b : ℝ} (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (t s : ℝ) : ‖kgStateKernel W t s‖ ≤ b := by
  rw [kgStateKernel, ContinuousLinearMap.norm_restrictScalars]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h := mul_le_mul (norm_kgPropagator_le_one (E := E) (t - s)) (norm_kgSourceOp_le hb0 hW)
    (norm_nonneg _) zero_le_one
  rwa [one_mul] at h

/-- **The energy-space Duhamel kernel is strongly continuous.** -/
theorem strongKernel_kgStateKernel
    (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :
    StrongKernel (kgStateKernel W) := by
  intro v hv
  have hcomp : Continuous fun p : ℝ × ℝ => kgPropagator (p.1 - p.2) (kgSourceOp W (v p.2)) :=
    continuous_kgPropagator_comp (continuous_fst.sub continuous_snd)
      ((kgSourceOp W).continuous.comp (hv.comp continuous_snd))
  exact hcomp.congr fun p => (kgStateKernel_apply W p.1 p.2 (v p.2)).symm

/-- **The state of the mild solution**, as the solution of the energy-space Volterra equation. -/
def kgStateMild (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : KGEnergy E :=
  volterraSolution (kgStateFree g h) (kgStateKernel W) t

section State

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

theorem continuous_kgStateMild (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgStateMild W g h) :=
  continuous_volterraSolution_of_strong (continuous_kgStateFree g h)
    (strongKernel_kgStateKernel W) hb0 (norm_nonneg _)
    (fun t s => norm_kgStateKernel_le hb0 hW t s) (norm_kgStateFree_le g h)

theorem kgStateMild_eq (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgStateMild W g h t
      = kgStateFree g h t + ∫ s in (0 : ℝ)..t, kgStateKernel W t s (kgStateMild W g h s) :=
  volterraSolution_eq_of_strong (continuous_kgStateFree g h) (strongKernel_kgStateKernel W)
    hb0 (norm_nonneg _) (fun t s => norm_kgStateKernel_le hb0 hW t s) (norm_kgStateFree_le g h) t

/-- **The sharp energy estimate**, in the energy space: constant one, rate `‖W‖`. -/
theorem norm_kgStateMild_le (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (g h : Lp ℂ 2 (volume : Measure E))
    (t : ℝ) : ‖kgStateMild W g h t‖ ≤ ‖kgPair E (g, h)‖ * Real.exp (b * |t|) :=
  norm_volterraSolution_le_of_strong (continuous_kgStateFree g h) (strongKernel_kgStateKernel W)
    hb0 (norm_nonneg _) (fun t s => norm_kgStateKernel_le hb0 hW t s) (norm_kgStateFree_le g h) t

theorem eq_kgStateMild_of_duhamel (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) {v : ℝ → KGEnergy E} (hv : Continuous v)
    (hduh : ∀ t : ℝ, v t = kgStateFree g h t + ∫ s in (0 : ℝ)..t, kgStateKernel W t s (v s)) :
    v = kgStateMild W g h :=
  volterra_eq_of_eq_of_eq_of_strong (strongKernel_kgStateKernel W) hb0
    (fun t s => norm_kgStateKernel_le hb0 hW t s) hv (continuous_kgStateMild hb0 hW g h) hduh
    (kgStateMild_eq hb0 hW g h)

end State
/-! ## The gradient and the velocity of the field solution -/

section Field

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The gradient `⟨D⟩u` of the mild solution, in closed form. -/
def kgFieldGrad (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  kgCosOp t g + kgSinOp t h
    + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s))

/-- The velocity `∂ₜu` of the mild solution, in closed form. -/
def kgFieldVel (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  -(kgSinOp t g) + kgCosOp t h
    + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s))

theorem kgFieldVel_eq_deriv (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (g h : Lp ℂ 2 (volume : Measure E))
    (t : ℝ) : kgFieldVel W g h t = deriv (kgFieldMild W (kgFreqInvOp g) h) t :=
  (deriv_kgFieldMild hb0 hW g h t).symm

theorem continuous_kgSourceCurve (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    Continuous fun s : ℝ => W (kgFieldMild W (kgFreqInvOp g) h s) :=
  W.continuous.comp (continuous_kgFieldMild hb0 hW _ h)

theorem continuous_kgFieldGrad (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgFieldGrad W g h) := by
  have hsrc := continuous_kgSourceCurve hb0 hW g h
  have hF : Continuous fun p : ℝ × ℝ =>
      kgSinOp (p.1 - p.2) (W (kgFieldMild W (kgFreqInvOp g) h p.2)) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply
      (continuous_fst.sub continuous_snd) (hsrc.comp continuous_snd)
  exact ((continuous_kgCosOp_apply g).add (continuous_kgSinOp_apply h)).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_id)

theorem continuous_kgFieldVel (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgFieldVel W g h) := by
  have hsrc := continuous_kgSourceCurve hb0 hW g h
  have hF : Continuous fun p : ℝ × ℝ =>
      kgCosOp (p.1 - p.2) (W (kgFieldMild W (kgFreqInvOp g) h p.2)) :=
    continuous_kgCosOp_comp (continuous_fst.sub continuous_snd) (hsrc.comp continuous_snd)
  exact ((continuous_kgSinOp_apply g).neg.add (continuous_kgCosOp_apply h)).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_id)

/-- **The gradient really is `⟨D⟩u`**: dividing it by the frequency returns the mild solution. -/
theorem kgFreqInvOp_kgFieldGrad (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFreqInvOp (kgFieldGrad W g h t) = kgFieldMild W (kgFreqInvOp g) h t := by
  have hsrc := continuous_kgSourceCurve hb0 hW g h
  have hI : IntervalIntegrable
      (fun s : ℝ => kgSinOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s))) volume 0 t :=
    (continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply
      (continuous_const.sub continuous_id) hsrc).intervalIntegrable 0 t
  have hker : (∫ s in (0 : ℝ)..t, kgFieldKernel W t s (kgFieldMild W (kgFreqInvOp g) h s))
      = ∫ s in (0 : ℝ)..t, kgSinFreqOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernel_apply W t s _
  have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      kgFreqInvOp (kgSinOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)))
        = kgSinFreqOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)) := by
    intro s _
    rw [kgFreqInvOp_kgSinOp, kgSinFreqOp_eq_comp]
    rfl
  rw [kgFieldGrad, map_add, map_add, kgFreqInvOp_kgCosOp, kgFreqInvOp_kgSinOp,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI,
    intervalIntegral.integral_congr hpt, kgFieldMild_eq hb0 hW _ h t, hker, kgFieldFree]
  congr 1
  rw [kgSinFreqOp_eq_comp]
  rfl

/-- The state of the mild solution: its gradient and its velocity. -/
def kgFieldState (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : KGEnergy E :=
  kgPair E (kgFieldGrad W g h t, kgFieldVel W g h t)

theorem continuous_kgFieldState (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgFieldState W g h) :=
  (kgPair E).continuous.comp
    ((continuous_kgFieldGrad hb0 hW g h).prodMk (continuous_kgFieldVel hb0 hW g h))

set_option maxHeartbeats 1000000 in
/-- **The state satisfies the energy-space Duhamel equation.** -/
theorem kgFieldState_duhamel (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldState W g h t
      = kgStateFree g h t + ∫ s in (0 : ℝ)..t, kgStateKernel W t s (kgFieldState W g h s) := by
  have hcs := continuous_kgFieldState hb0 hW g h
  have hI : IntervalIntegrable
      (fun s : ℝ => kgStateKernel W t s (kgFieldState W g h s)) volume 0 t :=
    (((strongKernel_kgStateKernel W) _ hcs).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
  have hsrc : ∀ s : ℝ, kgSourceOp W (kgFieldState W g h s)
      = kgPair E (0, W (kgFieldMild W (kgFreqInvOp g) h s)) := by
    intro s
    have hproj : (kgFieldState W g h s).fst = kgFieldGrad W g h s := rfl
    rw [kgSourceOp_apply, hproj, kgFreqInvOp_kgFieldGrad hb0 hW g h s]
  have hfst : ∀ s : ℝ, kgFst E (kgStateKernel W t s (kgFieldState W g h s))
      = kgSinOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)) := by
    intro s
    rw [kgStateKernel_apply, hsrc s, kgPropagator_apply]
    show kgCosOp (t - s) (0 : Lp ℂ 2 (volume : Measure E))
      + kgSinOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)) = _
    rw [map_zero, zero_add]
  have hsnd : ∀ s : ℝ, kgSnd E (kgStateKernel W t s (kgFieldState W g h s))
      = kgCosOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)) := by
    intro s
    rw [kgStateKernel_apply, hsrc s, kgPropagator_apply]
    show -(kgSinOp (t - s) (0 : Lp ℂ 2 (volume : Measure E)))
      + kgCosOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)) = _
    rw [map_zero, neg_zero, zero_add]
  refine kgEnergy_ext ?_ ?_
  · show kgFieldGrad W g h t = _
    rw [kgFieldGrad]
    have hcomp : kgFst E (kgStateFree g h t
        + ∫ s in (0 : ℝ)..t, kgStateKernel W t s (kgFieldState W g h s))
        = (kgCosOp t g + kgSinOp t h)
          + ∫ s in (0 : ℝ)..t, kgSinOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)) := by
      rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI]
      congr 1
      exact intervalIntegral.integral_congr fun s _ => hfst s
    exact hcomp.symm
  · show kgFieldVel W g h t = _
    rw [kgFieldVel]
    have hcomp : kgSnd E (kgStateFree g h t
        + ∫ s in (0 : ℝ)..t, kgStateKernel W t s (kgFieldState W g h s))
        = (-(kgSinOp t g) + kgCosOp t h)
          + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W (kgFieldMild W (kgFreqInvOp g) h s)) := by
      rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hI]
      congr 1
      exact intervalIntegral.integral_congr fun s _ => hsnd s
    exact hcomp.symm

theorem kgFieldState_eq_kgStateMild (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) : kgFieldState W g h = kgStateMild W g h :=
  eq_kgStateMild_of_duhamel hb0 hW g h (continuous_kgFieldState hb0 hW g h)
    (kgFieldState_duhamel hb0 hW g h)

/-- **The hyperbolic energy estimate, sharp.** The mild solution of `∂ₜ²u = -⟨D⟩²u + Wu`, for an
arbitrary bounded perturbation and arbitrary `L²` data, obeys

`‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖² ≤ (‖⟨D⟩u(0)‖² + ‖∂ₜu(0)‖²)e^{2‖W‖|t|}`,

with constant one and rate exactly `‖W‖`. -/
theorem kgFieldEnergy_le (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (g h : Lp ℂ 2 (volume : Measure E))
    (t : ℝ) :
    ‖kgFieldGrad W g h t‖ ^ 2 + ‖kgFieldVel W g h t‖ ^ 2
      ≤ (‖g‖ ^ 2 + ‖h‖ ^ 2) * Real.exp (2 * (b * |t|)) := by
  have hnorm : ‖kgFieldState W g h t‖ ≤ ‖kgPair E (g, h)‖ * Real.exp (b * |t|) := by
    rw [kgFieldState_eq_kgStateMild hb0 hW g h]
    exact norm_kgStateMild_le hb0 hW g h t
  have hsqL : ‖kgFieldState W g h t‖ ^ 2
      = ‖kgFieldGrad W g h t‖ ^ 2 + ‖kgFieldVel W g h t‖ ^ 2 := by
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgFieldState, kgPair_fst, kgPair_snd]
  have hsqR : ‖kgPair E (g, h)‖ ^ 2 = ‖g‖ ^ 2 + ‖h‖ ^ 2 := by
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgPair_fst, kgPair_snd]
  have hnn : (0 : ℝ) ≤ ‖kgFieldState W g h t‖ := norm_nonneg _
  have hR : (0 : ℝ) ≤ ‖kgPair E (g, h)‖ * Real.exp (b * |t|) := by positivity
  have hsq := mul_self_le_mul_self hnn hnorm
  rw [← sq, ← sq, mul_pow, hsqL, hsqR] at hsq
  have hexp : Real.exp (b * |t|) ^ 2 = Real.exp (2 * (b * |t|)) := by
    rw [two_mul, Real.exp_add, sq]
  rwa [hexp] at hsq

end Field

end GaloisForLFunctions.HTGeometry
