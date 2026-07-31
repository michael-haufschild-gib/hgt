import GaloisForLFunctions.RHTower.SuzukiCriticalEntryWallQuarterShiftGreenLaw

/-!
# Explicit integral Green representation at the entry wall

In entry depth the near/far gap is the causal convolution of the endpoint trace against the
twice-vanishing kernel `exp (-I z x) - 1 + I z x`. Because that kernel splits as
`exp (-I z s) * exp (I z r)` plus an affine term, the convolution is an elementary combination of
three primitives of the trace, so all three delay jets are ordinary calculus.

The representation solves the third-order causal Green equation
`(d/ds + I z) Φ'' = -z ^ 2 * u` with vanishing value, slope and curvature at the wall, and those
three initial conditions determine it uniquely.
-/

open Complex intervalIntegral

namespace RHTower

noncomputable section

/-- Twice-vanishing causal kernel of the entry Green equation. -/
def entryGreenKernel (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * z * x)) - 1 + Complex.I * z * x

/-- Zeroth primitive of the endpoint trace. -/
def entryTracePrimitive (u : ℝ → ℂ) (s : ℝ) : ℂ := ∫ r in (0 : ℝ)..s, u r

/-- First moment primitive of the endpoint trace. -/
def entryTraceMoment (u : ℝ → ℂ) (s : ℝ) : ℂ := ∫ r in (0 : ℝ)..s, (r : ℂ) * u r

/-- Exponentially weighted primitive of the endpoint trace. -/
def entryTraceExpMoment (z : ℂ) (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ r in (0 : ℝ)..s, Complex.exp (Complex.I * z * r) * u r

/-- Causal Green representation of the near/far gap in entry depth. -/
def entryGreenIntegral (z : ℂ) (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ r in (0 : ℝ)..s, entryGreenKernel z (s - r) * u r

theorem entryGreenKernel_zero (z : ℂ) : entryGreenKernel z 0 = 0 := by
  simp [entryGreenKernel]

/-- **Elementary form of the Green convolution.**  The kernel separates, so the convolution is a
combination of three primitives of the trace with explicit coefficients. -/
theorem entryGreenIntegral_eq (z : ℂ) {u : ℝ → ℂ} (hu : Continuous u) (s : ℝ) :
    entryGreenIntegral z u s =
      Complex.exp (-(Complex.I * z * s)) * entryTraceExpMoment z u s +
        ((Complex.I * z * s - 1) * entryTracePrimitive u s -
          Complex.I * z * entryTraceMoment u s) := by
  have hA : Continuous fun r : ℝ => Complex.exp (Complex.I * z * (r : ℂ)) * u r := by fun_prop
  have hB : Continuous fun r : ℝ => (r : ℂ) * u r := Complex.continuous_ofReal.mul hu
  have hcongr : entryGreenIntegral z u s =
      ∫ r in (0 : ℝ)..s,
        (Complex.exp (-(Complex.I * z * (s : ℂ))) *
            (Complex.exp (Complex.I * z * (r : ℂ)) * u r) +
          ((Complex.I * z * (s : ℂ) - 1) * u r - Complex.I * z * ((r : ℂ) * u r))) := by
    rw [entryGreenIntegral]
    refine intervalIntegral.integral_congr (fun r _ => ?_)
    have hexp : Complex.exp (-(Complex.I * z * ((s - r : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * z * (s : ℂ))) * Complex.exp (Complex.I * z * (r : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [entryGreenKernel, hexp]
    push_cast
    ring
  have hf1 : IntervalIntegrable
      (fun r : ℝ => Complex.exp (-(Complex.I * z * (s : ℂ))) *
        (Complex.exp (Complex.I * z * (r : ℂ)) * u r)) MeasureTheory.volume 0 s :=
    (hA.const_mul _).intervalIntegrable 0 s
  have hg1 : IntervalIntegrable
      (fun r : ℝ => (Complex.I * z * (s : ℂ) - 1) * u r) MeasureTheory.volume 0 s :=
    (hu.const_mul _).intervalIntegrable 0 s
  have hg2 : IntervalIntegrable
      (fun r : ℝ => Complex.I * z * ((r : ℂ) * u r)) MeasureTheory.volume 0 s :=
    (hB.const_mul _).intervalIntegrable 0 s
  have hf2 : IntervalIntegrable
      (fun r : ℝ => (Complex.I * z * (s : ℂ) - 1) * u r - Complex.I * z * ((r : ℂ) * u r))
      MeasureTheory.volume 0 s := hg1.sub hg2
  rw [hcongr, intervalIntegral.integral_add hf1 hf2,
    intervalIntegral.integral_sub hg1 hg2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rfl

theorem hasDerivAt_entryTracePrimitive {u : ℝ → ℂ} (hu : Continuous u) (s : ℝ) :
    HasDerivAt (entryTracePrimitive u) (u s) s :=
  intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable 0 s)
    (hu.stronglyMeasurableAtFilter _ _) hu.continuousAt

theorem hasDerivAt_entryTraceMoment {u : ℝ → ℂ} (hu : Continuous u) (s : ℝ) :
    HasDerivAt (entryTraceMoment u) ((s : ℂ) * u s) s := by
  have hc : Continuous fun r : ℝ => (r : ℂ) * u r := Complex.continuous_ofReal.mul hu
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem hasDerivAt_entryTraceExpMoment (z : ℂ) {u : ℝ → ℂ} (hu : Continuous u) (s : ℝ) :
    HasDerivAt (entryTraceExpMoment z u) (Complex.exp (Complex.I * z * s) * u s) s := by
  have hc : Continuous fun r : ℝ => Complex.exp (Complex.I * z * r) * u r := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

/-! ## The three delay jets -/

/-- First delay jet of the Green representation. -/
def entryGreenJet1 (z : ℂ) (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  -(Complex.I * z) * Complex.exp (-(Complex.I * z * s)) * entryTraceExpMoment z u s +
    Complex.I * z * entryTracePrimitive u s

/-- Second delay jet of the Green representation. -/
def entryGreenJet2 (z : ℂ) (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  -(z ^ 2) * Complex.exp (-(Complex.I * z * s)) * entryTraceExpMoment z u s

/-- Third delay jet of the Green representation. -/
def entryGreenJet3 (z : ℂ) (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  Complex.I * z ^ 3 * Complex.exp (-(Complex.I * z * s)) * entryTraceExpMoment z u s -
    z ^ 2 * u s

private theorem hasDerivAt_negExp (z : ℂ) (s : ℝ) :
    HasDerivAt (fun σ : ℝ => Complex.exp (-(Complex.I * z * (σ : ℂ))))
      (Complex.exp (-(Complex.I * z * (s : ℂ))) * -(Complex.I * z)) s := by
  have h0 : HasDerivAt (fun σ : ℝ => Complex.I * z * (σ : ℂ)) (Complex.I * z) s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I * z)
  exact h0.neg.cexp

private theorem exp_cancel (z : ℂ) (s : ℝ) :
    Complex.exp (-(Complex.I * z * (s : ℂ))) * Complex.exp (Complex.I * z * (s : ℂ)) = 1 := by
  rw [← Complex.exp_add]
  simp

theorem hasDerivAt_entryGreenIntegral (z : ℂ) {u : ℝ → ℂ} (hu : Continuous u) (s : ℝ) :
    HasDerivAt (entryGreenIntegral z u) (entryGreenJet1 z u s) s := by
  have hfun : entryGreenIntegral z u = fun σ : ℝ =>
      Complex.exp (-(Complex.I * z * (σ : ℂ))) * entryTraceExpMoment z u σ +
        ((Complex.I * z * (σ : ℂ) - 1) * entryTracePrimitive u σ -
          Complex.I * z * entryTraceMoment u σ) :=
    funext (entryGreenIntegral_eq z hu)
  have hlin : HasDerivAt (fun σ : ℝ => Complex.I * z * (σ : ℂ) - 1) (Complex.I * z) s := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I * z)).sub_const 1
  have hmain :=
    ((hasDerivAt_negExp z s).mul (hasDerivAt_entryTraceExpMoment z hu s)).add
      ((hlin.mul (hasDerivAt_entryTracePrimitive hu s)).sub
        ((hasDerivAt_entryTraceMoment hu s).const_mul (Complex.I * z)))
  have hval :
      Complex.exp (-(Complex.I * z * (s : ℂ))) * -(Complex.I * z) *
            entryTraceExpMoment z u s +
          Complex.exp (-(Complex.I * z * (s : ℂ))) *
            (Complex.exp (Complex.I * z * (s : ℂ)) * u s) +
        (Complex.I * z * entryTracePrimitive u s +
            (Complex.I * z * (s : ℂ) - 1) * u s -
          Complex.I * z * ((s : ℂ) * u s)) =
        entryGreenJet1 z u s := by
    rw [entryGreenJet1]
    have hc := exp_cancel z s
    have hrw : Complex.exp (-(Complex.I * z * (s : ℂ))) *
        (Complex.exp (Complex.I * z * (s : ℂ)) * u s) = u s := by
      rw [← mul_assoc, hc, one_mul]
    rw [hrw]
    ring
  rw [hfun, ← hval]
  exact hmain

theorem hasDerivAt_entryGreenJet1 (z : ℂ) {u : ℝ → ℂ} (hu : Continuous u) (s : ℝ) :
    HasDerivAt (entryGreenJet1 z u) (entryGreenJet2 z u s) s := by
  have hmain :=
    ((((hasDerivAt_negExp z s).mul (hasDerivAt_entryTraceExpMoment z hu s)).const_mul
      (-(Complex.I * z))).add
      ((hasDerivAt_entryTracePrimitive hu s).const_mul (Complex.I * z)))
  have hval :
      -(Complex.I * z) *
          (Complex.exp (-(Complex.I * z * (s : ℂ))) * -(Complex.I * z) *
              entryTraceExpMoment z u s +
            Complex.exp (-(Complex.I * z * (s : ℂ))) *
              (Complex.exp (Complex.I * z * (s : ℂ)) * u s)) +
        Complex.I * z * u s = entryGreenJet2 z u s := by
    rw [entryGreenJet2]
    have hrw : Complex.exp (-(Complex.I * z * (s : ℂ))) *
        (Complex.exp (Complex.I * z * (s : ℂ)) * u s) = u s := by
      rw [← mul_assoc, exp_cancel z s, one_mul]
    rw [hrw]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (Complex.exp (-(Complex.I * z * (s : ℂ))) *
      entryTraceExpMoment z u s * z ^ 2) * hI
  have hfun : entryGreenJet1 z u = fun σ : ℝ =>
      -(Complex.I * z) *
        (Complex.exp (-(Complex.I * z * (σ : ℂ))) * entryTraceExpMoment z u σ) +
        Complex.I * z * entryTracePrimitive u σ := by
    funext σ
    rw [entryGreenJet1]
    ring
  rw [hfun, ← hval]
  exact hmain

theorem hasDerivAt_entryGreenJet2 (z : ℂ) {u : ℝ → ℂ} (hu : Continuous u) (s : ℝ) :
    HasDerivAt (entryGreenJet2 z u) (entryGreenJet3 z u s) s := by
  have hmain :=
    (((hasDerivAt_negExp z s).mul (hasDerivAt_entryTraceExpMoment z hu s)).const_mul (-(z ^ 2)))
  have hval :
      -(z ^ 2) *
        (Complex.exp (-(Complex.I * z * (s : ℂ))) * -(Complex.I * z) *
            entryTraceExpMoment z u s +
          Complex.exp (-(Complex.I * z * (s : ℂ))) *
            (Complex.exp (Complex.I * z * (s : ℂ)) * u s)) = entryGreenJet3 z u s := by
    rw [entryGreenJet3]
    have hrw : Complex.exp (-(Complex.I * z * (s : ℂ))) *
        (Complex.exp (Complex.I * z * (s : ℂ)) * u s) = u s := by
      rw [← mul_assoc, exp_cancel z s, one_mul]
    rw [hrw]
    ring
  have hfun : entryGreenJet2 z u = fun σ : ℝ =>
      -(z ^ 2) * (Complex.exp (-(Complex.I * z * (σ : ℂ))) * entryTraceExpMoment z u σ) := by
    funext σ
    rw [entryGreenJet2]
    ring
  rw [hfun, ← hval]
  exact hmain

/-! ## The causal Green equation and its initial data -/

/-- **Exact third-order causal Green equation.**  The Green representation satisfies
`(d/ds + I z) Φ'' = -z ^ 2 * u` at every entry depth. -/
theorem entryGreen_causal_equation (z : ℂ) (u : ℝ → ℂ) (s : ℝ) :
    entryGreenJet3 z u s + Complex.I * z * entryGreenJet2 z u s = -(z ^ 2) * u s := by
  rw [entryGreenJet3, entryGreenJet2]
  ring

@[simp]
theorem entryTracePrimitive_zero (u : ℝ → ℂ) : entryTracePrimitive u 0 = 0 := by
  simp [entryTracePrimitive]

@[simp]
theorem entryTraceMoment_zero (u : ℝ → ℂ) : entryTraceMoment u 0 = 0 := by
  simp [entryTraceMoment]

@[simp]
theorem entryTraceExpMoment_zero (z : ℂ) (u : ℝ → ℂ) : entryTraceExpMoment z u 0 = 0 := by
  simp [entryTraceExpMoment]

@[simp]
theorem entryGreenIntegral_zero (z : ℂ) (u : ℝ → ℂ) : entryGreenIntegral z u 0 = 0 := by
  simp [entryGreenIntegral]

@[simp]
theorem entryGreenJet1_zero (z : ℂ) (u : ℝ → ℂ) : entryGreenJet1 z u 0 = 0 := by
  simp [entryGreenJet1]

@[simp]
theorem entryGreenJet2_zero (z : ℂ) (u : ℝ → ℂ) : entryGreenJet2 z u 0 = 0 := by
  simp [entryGreenJet2]

/-! ## Uniqueness from the three wall conditions -/

private theorem const_of_hasDerivAt_zero {D : ℝ → ℂ} (hD : ∀ s : ℝ, HasDerivAt D 0 s)
    (h0 : D 0 = 0) (s : ℝ) : D s = 0 := by
  have hdiff : Differentiable ℝ D := fun x => (hD x).differentiableAt
  have hderiv : ∀ x : ℝ, deriv D x = 0 := fun x => (hD x).deriv
  have := is_const_of_deriv_eq_zero hdiff hderiv s 0
  rw [this, h0]

/-- **Uniqueness of the Green representation.**  Any third-order causal solution vanishing to
second order at the entry wall is the Green convolution. -/
theorem entryGreenIntegral_unique (z : ℂ) {u : ℝ → ℂ} (hu : Continuous u)
    {Psi Psi1 Psi2 Psi3 : ℝ → ℂ}
    (hd0 : ∀ s : ℝ, HasDerivAt Psi (Psi1 s) s)
    (hd1 : ∀ s : ℝ, HasDerivAt Psi1 (Psi2 s) s)
    (hd2 : ∀ s : ℝ, HasDerivAt Psi2 (Psi3 s) s)
    (heq : ∀ s : ℝ, Psi3 s + Complex.I * z * Psi2 s = -(z ^ 2) * u s)
    (h0 : Psi 0 = 0) (h1 : Psi1 0 = 0) (h2 : Psi2 0 = 0) :
    Psi = entryGreenIntegral z u := by
  -- second jet
  have hD2deriv : ∀ s : ℝ,
      HasDerivAt (fun σ : ℝ => Psi2 σ - entryGreenJet2 z u σ)
        (-(Complex.I * z) * (Psi2 s - entryGreenJet2 z u s)) s := by
    intro s
    have hval : Psi3 s - entryGreenJet3 z u s =
        -(Complex.I * z) * (Psi2 s - entryGreenJet2 z u s) := by
      have e1 := heq s
      have e2 := entryGreen_causal_equation z u s
      linear_combination e1 - e2
    rw [← hval]
    exact (hd2 s).sub (hasDerivAt_entryGreenJet2 z hu s)
  have hD2 : ∀ s : ℝ, Psi2 s - entryGreenJet2 z u s = 0 := by
    have hg : ∀ s : ℝ, HasDerivAt
        (fun σ : ℝ => Complex.exp (Complex.I * z * (σ : ℂ)) *
          (Psi2 σ - entryGreenJet2 z u σ)) 0 s := by
      intro s
      have hexp : HasDerivAt (fun σ : ℝ => Complex.exp (Complex.I * z * (σ : ℂ)))
          (Complex.exp (Complex.I * z * (s : ℂ)) * (Complex.I * z)) s := by
        have h0' : HasDerivAt (fun σ : ℝ => Complex.I * z * (σ : ℂ)) (Complex.I * z) s := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I * z)
        exact h0'.cexp
      have hmain := hexp.mul (hD2deriv s)
      have hzero : Complex.exp (Complex.I * z * (s : ℂ)) * (Complex.I * z) *
            (Psi2 s - entryGreenJet2 z u s) +
          Complex.exp (Complex.I * z * (s : ℂ)) *
            (-(Complex.I * z) * (Psi2 s - entryGreenJet2 z u s)) = 0 := by
        ring
      rw [← hzero]
      exact hmain
    have hgzero : ∀ s : ℝ,
        Complex.exp (Complex.I * z * (s : ℂ)) * (Psi2 s - entryGreenJet2 z u s) = 0 := by
      refine const_of_hasDerivAt_zero hg ?_
      simp [h2]
    intro s
    have hexpne : Complex.exp (Complex.I * z * (s : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    exact (mul_eq_zero.mp (hgzero s)).resolve_left hexpne
  -- first jet
  have hD1 : ∀ s : ℝ, Psi1 s - entryGreenJet1 z u s = 0 := by
    refine const_of_hasDerivAt_zero (fun s => ?_) (by simp [h1])
    have := (hd1 s).sub (hasDerivAt_entryGreenJet1 z hu s)
    rwa [hD2 s] at this
  -- the function itself
  funext s
  have hzero : Psi s - entryGreenIntegral z u s = 0 := by
    refine const_of_hasDerivAt_zero (D := fun σ : ℝ => Psi σ - entryGreenIntegral z u σ)
      (fun σ => ?_) ?_ s
    · have hsub := (hd0 σ).sub (hasDerivAt_entryGreenIntegral z hu σ)
      rwa [hD1 σ] at hsub
    · show Psi 0 - entryGreenIntegral z u 0 = 0
      rw [h0, entryGreenIntegral_zero, sub_zero]
  exact sub_eq_zero.mp hzero

end

end RHTower
