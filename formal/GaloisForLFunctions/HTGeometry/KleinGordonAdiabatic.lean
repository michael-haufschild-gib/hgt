import GaloisForLFunctions.HTGeometry.KleinGordonTimeReducedState

/-!
# The adiabatic estimate

A fixed real potential conserves the energy exactly. A *moving* real background does work on the
field, and the rate at which it does so is exactly the rate at which the background itself moves:

`d/dt (‖⟨D⟩u‖² + ‖∂ₜu‖² − re⟪W(t)u, u⟫) = −re⟪Ẇ(t)u, u⟫`.

Everything on the right is bounded by `‖Ẇ(t)‖·‖u‖²`, and `‖u‖² ≤ ‖state‖²`, which the mass gap
already gave; and when `‖W‖ ≤ b < 1` the state is in turn bounded by the energy itself. So the energy
obeys the differential inequality `|E'| ≤ (L/(1−b))·E` with `L` a bound for `‖Ẇ‖`, and therefore

`E(t) ≤ E(0)·e^{L|t|/(1−b)}`.

This is the adiabatic principle in quantitative form: a background that changes slowly heats the
field slowly, at a rate proportional to its own rate of change and to nothing else. A static
background is `L = 0`, where the bound degenerates to exact conservation.

No Grönwall inequality is needed: `E(t)e^{∓Kt}` is monotone because its derivative has a sign.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Adiabatic

variable {W Wd : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- **The field is bounded by the energy**, for a moving background. -/
theorem norm_kgFieldMildT_sq_le_energy (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMildT W (kgFreqInvOp g) h t‖ ^ (2 : ℕ) ≤ ‖kgFieldStateT W g h t‖ ^ (2 : ℕ) := by
  have hu : kgFieldMildT W (kgFreqInvOp g) h t = kgFreqInvOp (kgFieldGradT W g h t) :=
    (kgFreqInvOp_kgFieldGradT hb0 hWb hWs g h t).symm
  have hle : ‖kgFieldMildT W (kgFreqInvOp g) h t‖ ≤ ‖kgFieldGradT W g h t‖ := by
    rw [hu]
    have hc := (kgFreqInvOp (E := E)).le_of_opNorm_le norm_kgFreqInvOp_le (kgFieldGradT W g h t)
    rwa [one_mul] at hc
  have hsq : ‖kgFieldMildT W (kgFreqInvOp g) h t‖ ^ (2 : ℕ) ≤ ‖kgFieldGradT W g h t‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hstate : ‖kgFieldStateT W g h t‖ ^ (2 : ℕ)
      = ‖kgFieldGradT W g h t‖ ^ (2 : ℕ) + ‖kgFieldVelT W g h t‖ ^ (2 : ℕ) := by
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgFieldStateT, kgPair_fst, kgPair_snd]
  have hvel : (0 : ℝ) ≤ ‖kgFieldVelT W g h t‖ ^ (2 : ℕ) := sq_nonneg _
  rw [hstate]
  linarith

/-- The energy of the field in a moving background. -/
def kgAdiabaticEnergy (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : ℝ :=
  ‖kgFieldStateT W g h t‖ ^ (2 : ℕ)
    - RCLike.re (inner ℂ (W t (kgFieldMildT W (kgFreqInvOp g) h t))
        (kgFieldMildT W (kgFreqInvOp g) h t))

set_option maxHeartbeats 1000000 in
/-- **The work–energy identity.** The energy changes only at the rate at which the background does. -/
theorem hasDerivAt_kgAdiabaticEnergy (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (hsa : ∀ (r : ℝ) (x y : Lp ℂ 2 (volume : Measure E)),
      (inner ℂ (W r x) y : ℂ) = inner ℂ x (W r y))
    (hWd : ∀ r : ℝ, HasDerivAt W (Wd r) r)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgAdiabaticEnergy W g h)
      (-RCLike.re (inner ℂ (Wd t (kgFieldMildT W (kgFreqInvOp g) h t))
        (kgFieldMildT W (kgFreqInvOp g) h t))) t := by
  set u := kgFieldMildT W (kgFreqInvOp g) h with hu
  set u' := kgFieldVelT W g h t with hu'
  have hderiv : HasDerivAt u u' t := by
    rw [hu, hu', kgFieldVelT]
    exact hasDerivAt_kgFieldMildT hb0 hWb hWs g h t
  have hstateSq := hasDerivAt_normSq_kgFieldStateT hb0 hWb hWs g h t
  have hWr : HasDerivAt (fun s : ℝ => (W s).restrictScalars ℝ)
      ((Wd t).restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ (Lp ℂ 2 (volume : Measure E))
      (Lp ℂ 2 (volume : Measure E)) ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hWd t)
  have hWu : HasDerivAt (fun s : ℝ => W s (u s)) (Wd t (u t) + W t u') t := hWr.clm_apply hderiv
  have hprod := HasDerivAt.inner ℂ hWu hderiv
  have hprodRe : HasDerivAt (fun s : ℝ => RCLike.re (inner ℂ (W s (u s)) (u s) : ℂ))
      (RCLike.re (inner ℂ (W t (u t)) u' + inner ℂ (Wd t (u t) + W t u') (u t))) t :=
    (RCLike.reCLM (K := ℂ)).hasFDerivAt.comp_hasDerivAt t hprod
  have hdiff := hstateSq.sub hprodRe
  have hzero : RCLike.re (inner ℂ u' (W t (u t)) + inner ℂ (W t (u t)) u')
      - RCLike.re (inner ℂ (W t (u t)) u' + inner ℂ (Wd t (u t) + W t u') (u t))
      = -RCLike.re (inner ℂ (Wd t (u t)) (u t)) := by
    have hswap : (inner ℂ (W t u') (u t) : ℂ) = inner ℂ u' (W t (u t)) := hsa t u' (u t)
    rw [inner_add_left, hswap, map_add, map_add, map_add]
    ring
  rw [hzero] at hdiff
  exact hdiff

/-- The energy dominates the state when the background is small. -/
theorem kgAdiabaticEnergy_lower (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    (1 - b) * ‖kgFieldStateT W g h t‖ ^ (2 : ℕ) ≤ kgAdiabaticEnergy W g h t := by
  have hbd := abs_re_inner_potential_le (hWb t) (kgFieldMildT W (kgFreqInvOp g) h t)
  have hut := norm_kgFieldMildT_sq_le_energy hb0 hWb hWs g h t
  have h1 := (abs_le.mp hbd).2
  have h2 : b * ‖kgFieldMildT W (kgFreqInvOp g) h t‖ ^ (2 : ℕ) ≤ b * ‖kgFieldStateT W g h t‖ ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hut hb0
  rw [kgAdiabaticEnergy]
  linarith

theorem kgAdiabaticEnergy_nonneg (hb0 : 0 ≤ b) (hb1 : b < 1) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : 0 ≤ kgAdiabaticEnergy W g h t := by
  have hlow := kgAdiabaticEnergy_lower hb0 hWb hWs g h t
  have hnn : (0 : ℝ) ≤ (1 - b) * ‖kgFieldStateT W g h t‖ ^ (2 : ℕ) := by
    have : (0 : ℝ) ≤ 1 - b := by linarith
    positivity
  linarith

/-- The derivative of the energy is bounded by the energy itself. -/
theorem abs_deriv_kgAdiabaticEnergy_le (hb0 : 0 ≤ b) (hb1 : b < 1) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (hL0 : 0 ≤ L) (hWL : ∀ r : ℝ, ‖Wd r‖ ≤ L)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    |RCLike.re (inner ℂ (Wd t (kgFieldMildT W (kgFreqInvOp g) h t))
        (kgFieldMildT W (kgFreqInvOp g) h t))|
      ≤ L / (1 - b) * kgAdiabaticEnergy W g h t := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hbd := abs_re_inner_potential_le (hWL t) (kgFieldMildT W (kgFreqInvOp g) h t)
  have hut := norm_kgFieldMildT_sq_le_energy hb0 hWb hWs g h t
  have hlow := kgAdiabaticEnergy_lower hb0 hWb hWs g h t
  have h2 : L * ‖kgFieldMildT W (kgFreqInvOp g) h t‖ ^ (2 : ℕ) ≤ L * ‖kgFieldStateT W g h t‖ ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hut hL0
  have h3 : L * ‖kgFieldStateT W g h t‖ ^ (2 : ℕ) ≤ L / (1 - b) * kgAdiabaticEnergy W g h t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb1']
    nlinarith [mul_le_mul_of_nonneg_left hlow hL0]
  linarith

/-- **The adiabatic estimate.** The energy grows at most at the rate at which the background moves. -/
theorem kgAdiabaticEnergy_le (hb0 : 0 ≤ b) (hb1 : b < 1) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (hsa : ∀ (r : ℝ) (x y : Lp ℂ 2 (volume : Measure E)),
      (inner ℂ (W r x) y : ℂ) = inner ℂ x (W r y))
    (hWd : ∀ r : ℝ, HasDerivAt W (Wd r) r) (hL0 : 0 ≤ L) (hWL : ∀ r : ℝ, ‖Wd r‖ ≤ L)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgAdiabaticEnergy W g h t
      ≤ kgAdiabaticEnergy W g h 0 * Real.exp (L / (1 - b) * |t|) := by
  set K : ℝ := L / (1 - b) with hK
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hEd : ∀ x : ℝ, HasDerivAt (kgAdiabaticEnergy W g h)
      (-RCLike.re (inner ℂ (Wd x (kgFieldMildT W (kgFreqInvOp g) h x))
        (kgFieldMildT W (kgFreqInvOp g) h x))) x :=
    fun x => hasDerivAt_kgAdiabaticEnergy hb0 hWb hWs hsa hWd g h x
  have hbound : ∀ x : ℝ,
      |(-RCLike.re (inner ℂ (Wd x (kgFieldMildT W (kgFreqInvOp g) h x))
        (kgFieldMildT W (kgFreqInvOp g) h x)))| ≤ K * kgAdiabaticEnergy W g h x := by
    intro x
    rw [abs_neg]
    exact abs_deriv_kgAdiabaticEnergy_le hb0 hb1 hWb hWs hL0 hWL g h x
  rcases le_total (0 : ℝ) t with ht | ht
  · -- forward in time: `E(x)e^{-Kx}` is antitone
    have hFd : ∀ x : ℝ, HasDerivAt (fun s => kgAdiabaticEnergy W g h s * Real.exp (-(K * s)))
        ((-RCLike.re (inner ℂ (Wd x (kgFieldMildT W (kgFreqInvOp g) h x))
            (kgFieldMildT W (kgFreqInvOp g) h x))) * Real.exp (-(K * x))
          + kgAdiabaticEnergy W g h x * (Real.exp (-(K * x)) * (-K))) x := by
      intro x
      have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(K * s))) (Real.exp (-(K * x)) * (-K)) x := by
        have hlin : HasDerivAt (fun s : ℝ => -(K * s)) (-K) x := by
          have h1 : HasDerivAt (fun s : ℝ => (-K) * s) ((-K) * 1) x :=
            (hasDerivAt_id x).const_mul (-K)
          rw [mul_one] at h1
          exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by ring)
        simpa using hlin.exp
      exact (hEd x).mul hexp
    have hFnp : ∀ x : ℝ, deriv (fun s => kgAdiabaticEnergy W g h s * Real.exp (-(K * s))) x ≤ 0 := by
      intro x
      rw [(hFd x).deriv]
      have h1 := (abs_le.mp (hbound x)).2
      have hexp0 : (0 : ℝ) < Real.exp (-(K * x)) := Real.exp_pos _
      nlinarith [h1, hexp0]
    have hFanti : Antitone fun s => kgAdiabaticEnergy W g h s * Real.exp (-(K * s)) :=
      antitone_of_deriv_nonpos (fun x => (hFd x).differentiableAt) hFnp
    have hle := hFanti ht
    rw [abs_of_nonneg ht]
    have hexpt : (0 : ℝ) < Real.exp (K * t) := Real.exp_pos _
    have hmul : kgAdiabaticEnergy W g h t * Real.exp (-(K * t)) * Real.exp (K * t)
        ≤ kgAdiabaticEnergy W g h 0 * Real.exp (-(K * 0)) * Real.exp (K * t) :=
      mul_le_mul_of_nonneg_right hle hexpt.le
    have hcancel : Real.exp (-(K * t)) * Real.exp (K * t) = 1 := by
      rw [← Real.exp_add]
      simp
    calc kgAdiabaticEnergy W g h t
        = kgAdiabaticEnergy W g h t * Real.exp (-(K * t)) * Real.exp (K * t) := by
          rw [mul_assoc, hcancel, mul_one]
      _ ≤ kgAdiabaticEnergy W g h 0 * Real.exp (-(K * 0)) * Real.exp (K * t) := hmul
      _ = kgAdiabaticEnergy W g h 0 * Real.exp (K * t) := by norm_num
  · -- backward in time: `E(x)e^{Kx}` is monotone
    have hGd : ∀ x : ℝ, HasDerivAt (fun s => kgAdiabaticEnergy W g h s * Real.exp (K * s))
        ((-RCLike.re (inner ℂ (Wd x (kgFieldMildT W (kgFreqInvOp g) h x))
            (kgFieldMildT W (kgFreqInvOp g) h x))) * Real.exp (K * x)
          + kgAdiabaticEnergy W g h x * (Real.exp (K * x) * K)) x := by
      intro x
      have hexp : HasDerivAt (fun s : ℝ => Real.exp (K * s)) (Real.exp (K * x) * K) x := by
        have hlin : HasDerivAt (fun s : ℝ => K * s) K x := by
          simpa using (hasDerivAt_id x).const_mul K
        simpa using hlin.exp
      exact (hEd x).mul hexp
    have hGnn : ∀ x : ℝ, 0 ≤ deriv (fun s => kgAdiabaticEnergy W g h s * Real.exp (K * s)) x := by
      intro x
      rw [(hGd x).deriv]
      have h1 := (abs_le.mp (hbound x)).1
      have hexp0 : (0 : ℝ) < Real.exp (K * x) := Real.exp_pos _
      nlinarith [h1, hexp0]
    have hGmono : Monotone fun s => kgAdiabaticEnergy W g h s * Real.exp (K * s) :=
      monotone_of_deriv_nonneg (fun x => (hGd x).differentiableAt) hGnn
    have hle := hGmono ht
    rw [abs_of_nonpos ht]
    have hexpt : (0 : ℝ) < Real.exp (-(K * t)) := Real.exp_pos _
    have hmul : kgAdiabaticEnergy W g h t * Real.exp (K * t) * Real.exp (-(K * t))
        ≤ kgAdiabaticEnergy W g h 0 * Real.exp (K * 0) * Real.exp (-(K * t)) :=
      mul_le_mul_of_nonneg_right hle hexpt.le
    have hcancel : Real.exp (K * t) * Real.exp (-(K * t)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hrw : K * -t = -(K * t) := by ring
    rw [hrw]
    calc kgAdiabaticEnergy W g h t
        = kgAdiabaticEnergy W g h t * Real.exp (K * t) * Real.exp (-(K * t)) := by
          rw [mul_assoc, hcancel, mul_one]
      _ ≤ kgAdiabaticEnergy W g h 0 * Real.exp (K * 0) * Real.exp (-(K * t)) := hmul
      _ = kgAdiabaticEnergy W g h 0 * Real.exp (-(K * t)) := by norm_num

/-- **The state is bounded by the adiabatic estimate**: a slowly moving background heats the field
slowly. -/
theorem kgFieldEnergyT_le_adiabatic (hb0 : 0 ≤ b) (hb1 : b < 1) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (hsa : ∀ (r : ℝ) (x y : Lp ℂ 2 (volume : Measure E)),
      (inner ℂ (W r x) y : ℂ) = inner ℂ x (W r y))
    (hWd : ∀ r : ℝ, HasDerivAt W (Wd r) r) (hL0 : 0 ≤ L) (hWL : ∀ r : ℝ, ‖Wd r‖ ≤ L)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGradT W g h t‖ ^ (2 : ℕ) + ‖kgFieldVelT W g h t‖ ^ (2 : ℕ)
      ≤ kgAdiabaticEnergy W g h 0 * Real.exp (L / (1 - b) * |t|) / (1 - b) := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hlow := kgAdiabaticEnergy_lower hb0 hWb hWs g h t
  have hupp := kgAdiabaticEnergy_le hb0 hb1 hWb hWs hsa hWd hL0 hWL g h t
  have hstate : ‖kgFieldStateT W g h t‖ ^ (2 : ℕ)
      = ‖kgFieldGradT W g h t‖ ^ (2 : ℕ) + ‖kgFieldVelT W g h t‖ ^ (2 : ℕ) := by
    rw [← kgEnergy_eq_norm_sq, kgEnergy, kgFieldStateT, kgPair_fst, kgPair_snd]
  rw [le_div_iff₀ hb1', ← hstate]
  linarith

end Adiabatic

end GaloisForLFunctions.HTGeometry
