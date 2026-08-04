import GaloisForLFunctions.HTGeometry.ClockRealKernels
import GaloisForLFunctions.HTGeometry.ClockNullTransverseLift

/-!
# The real field of the clock construction and its two derivatives

The field of the clock probe is the real part of the solution along the real transverse axis. Taking
the real part costs nothing: it is a continuous linear map, so it commutes with every derivative
taken so far, and the real axis lies inside every strip, so the transverse variable is a genuine
real variable there.

This file records the twelve real functions the chart calculus consumes — the field, its three first
derivatives and its nine second derivatives — and assembles them into the four continuity-and-
differentiability records that the d'Alembertian of the previous chapter asks for.

The two mixed pairs coincide, as they must: the transverse derivative of a null derivative is the
null derivative of the transverse one.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- The real part of a derivative is the derivative of the real part. -/
theorem hasDerivAt_re {f : ℝ → ℂ} {c : ℂ} {x : ℝ} (h : HasDerivAt f c x) :
    HasDerivAt (fun y : ℝ => (f y).re) c.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

/-- The same along the real axis of a holomorphic function. -/
theorem hasDerivAt_re_ofReal {g : ℂ → ℂ} {c : ℂ} {w : ℝ} (h : HasDerivAt g c ((w : ℝ) : ℂ)) :
    HasDerivAt (fun y : ℝ => (g ((y : ℝ) : ℂ)).re) c.re w :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt w h.comp_ofReal

/-! ## The twelve real functions -/

/-- The field of the clock probe: the real part of the solution on the real transverse axis. -/
noncomputable def probeU (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (clockSolution V (boxClamp T s) (boxClamp T t) ((w : ℝ) : ℂ)).re

/-- Its derivative along the first null coordinate. -/
noncomputable def probeA (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..t, clampedStep V T ((w : ℝ) : ℂ) s r).re

/-- Its derivative along the second null coordinate. -/
noncomputable def probeB (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..s, clampedStep V T ((w : ℝ) : ℂ) r t).re

/-- Its transverse derivative. -/
noncomputable def probeC (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (deriv (clampedSolution V T (s, t)) ((w : ℝ) : ℂ)).re

/-- The pure second derivative along the first null coordinate. -/
noncomputable def probeAa (V Vs : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..t, clampedStepFst V Vs T ((w : ℝ) : ℂ) s r).re

/-- The mixed null second derivative, which is the step operator itself. -/
noncomputable def probeAb (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (clampedStep V T ((w : ℝ) : ℂ) s t).re

/-- The mixed derivative along the first null coordinate and the transverse one. -/
noncomputable def probeAc (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..t, dClampedStep V T ((w : ℝ) : ℂ) s r).re

/-- The pure second derivative along the second null coordinate. -/
noncomputable def probeBb (V Vt : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..s, clampedStepSnd V Vt T ((w : ℝ) : ℂ) r t).re

/-- The mixed derivative along the second null coordinate and the transverse one. -/
noncomputable def probeBc (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..s, dClampedStep V T ((w : ℝ) : ℂ) r t).re

/-- The pure second transverse derivative. -/
noncomputable def probeCc (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (s t w : ℝ) : ℝ :=
  (deriv (deriv (clampedSolution V T (s, t))) ((w : ℝ) : ℂ)).re

/-- The open rectangle of null coordinates, with the transverse axis unrestricted. -/
def clockBox (T : ℝ) : Set ((ℝ × ℝ) × ℝ) := {q | |q.1.1| < T ∧ |q.1.2| < T}

theorem isOpen_clockBox (T : ℝ) : IsOpen (clockBox T) := by
  have h1 : IsOpen {q : (ℝ × ℝ) × ℝ | |q.1.1| < T} :=
    isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_fst)) continuous_const
  have h2 : IsOpen {q : (ℝ × ℝ) × ℝ | |q.1.2| < T} :=
    isOpen_lt (continuous_abs.comp (continuous_snd.comp continuous_fst)) continuous_const
  simpa [clockBox, Set.setOf_and] using h1.inter h2

theorem mem_clockBox {T : ℝ} {q : (ℝ × ℝ) × ℝ} :
    q ∈ clockBox T ↔ |q.1.1| < T ∧ |q.1.2| < T := Iff.rfl

namespace ClockDatum

variable {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

/-! ## Continuity of the twelve functions -/

theorem continuous_probeU :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeU V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp hD.continuous_solReal

theorem continuous_probeA :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeA V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_innerReal (K := fun z s t => clampedStep V T z s t) hD.continuous_stepReal)

theorem continuous_probeB :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeB V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_outerReal (K := fun z s t => clampedStep V T z s t) hD.continuous_stepReal)

theorem continuous_probeC :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeC V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp hD.continuous_dSolReal

theorem continuous_probeAa :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeAa V Vs T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_innerReal (K := fun z s t => clampedStepFst V Vs T z s t)
      hD.continuous_stepFstReal)

theorem continuous_probeAb :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeAb V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp hD.continuous_stepReal

theorem continuous_probeAc :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeAc V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_innerReal (K := fun z s t => dClampedStep V T z s t) hD.continuous_dStepReal)

theorem continuous_probeBb :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeBb V Vt T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_outerReal (K := fun z s t => clampedStepSnd V Vt T z s t)
      hD.continuous_stepSndReal)

theorem continuous_probeBc :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeBc V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp
    (continuous_outerReal (K := fun z s t => dClampedStep V T z s t) hD.continuous_dStepReal)

theorem continuous_probeCc :
    Continuous fun q : (ℝ × ℝ) × ℝ => probeCc V T q.1.1 q.1.2 q.2 :=
  Complex.continuous_re.comp hD.continuous_d2SolReal

/-! ## The four differentiability records -/

/-- **The field of the probe is continuously differentiable in all three variables.** -/
theorem isC1On3_probeU :
    IsC1On3 (probeU V T) (probeA V T) (probeB V T) (probeC V T) (clockBox T) where
  isOpen := isOpen_clockBox T
  hasDerivFst := by
    intro q hq
    have hcx := hasDerivAt_clockSolution_fst hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg
      hD.rad hD.sideNonneg hD.small hq.1 (le_of_lt hq.2) (hD.absIm q.2)
    refine (hasDerivAt_re hcx).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.1) fun x hx => ?_
    show probeU V T x q.1.2 q.2 = _
    rw [probeU, boxClamp_eq_self (le_of_lt hx), boxClamp_eq_self (le_of_lt hq.2)]
  hasDerivSnd := by
    intro q hq
    have hcx := hasDerivAt_clockSolution_snd hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg
      hD.rad hD.sideNonneg hD.small (le_of_lt hq.1) hq.2 (hD.absIm q.2)
    refine (hasDerivAt_re hcx).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.2) fun y hy => ?_
    show probeU V T q.1.1 y q.2 = _
    rw [probeU, boxClamp_eq_self (le_of_lt hq.1), boxClamp_eq_self (le_of_lt hy)]
  hasDerivThd := by
    intro q _
    have hdiff : DifferentiableAt ℂ (clampedSolution V T q.1) (((q.2 : ℝ)) : ℂ) :=
      (differentiableOn_clampedSolution hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg
        hD.rad hD.sideNonneg hD.small q.1).differentiableAt
        ((isOpen_imStrip ρ).mem_nhds (hD.memStrip q.2))
    exact hasDerivAt_re_ofReal hdiff.hasDerivAt
  contFst := hD.continuous_probeA
  contSnd := hD.continuous_probeB
  contThd := hD.continuous_probeC

/-- **The first null derivative is continuously differentiable in all three variables.** -/
theorem isC1On3_probeA :
    IsC1On3 (probeA V T) (probeAa V Vs T) (probeAb V T) (probeAc V T) (clockBox T) where
  isOpen := isOpen_clockBox T
  hasDerivFst := by
    intro q hq
    have hcx := hasDerivAt_deriv_clockSolution_fst_fst hD.pos hD.potC1 hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂Nonneg hD.rad₂
      hD.rad₃Nonneg hD.rad₃ hq.1 hq.2 (hD.memStrip₃ q.2)
    have hint : (fun x : ℝ => ∫ r in (0 : ℝ)..q.1.2, clampedStep V T (((q.2 : ℝ)) : ℂ) x r)
        =ᶠ[nhds q.1.1]
        fun x : ℝ => deriv (fun y : ℝ => clockSolution V y q.1.2 (((q.2 : ℝ)) : ℂ)) x := by
      refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.1) fun x hx => ?_
      exact (deriv_clockSolution_fst hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
        hD.sideNonneg hD.small hx (le_of_lt hq.2) (hD.absIm q.2)).symm
    exact hasDerivAt_re (hcx.congr_of_eventuallyEq hint)
  hasDerivSnd := by
    intro q _
    have hsl : Continuous fun r : ℝ => clampedStep V T (((q.2 : ℝ)) : ℂ) q.1.1 r :=
      (continuous_clampedStep hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
        hD.sideNonneg hD.small (hD.absIm q.2)).comp
        (f := fun r : ℝ => ((q.1.1, r) : ℝ × ℝ)) (continuous_const.prodMk continuous_id)
    exact hasDerivAt_re (hsl.integral_hasStrictDerivAt 0 q.1.2).hasDerivAt
  hasDerivThd := by
    intro q _
    have hcx := hasDerivAt_clampedInner_transverse hD.pos hD.pot hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂ q.1.1 q.1.2
      (hD.memStrip₂ q.2)
    exact hasDerivAt_re_ofReal hcx
  contFst := hD.continuous_probeAa
  contSnd := hD.continuous_probeAb
  contThd := hD.continuous_probeAc

/-- **The second null derivative is continuously differentiable in all three variables.** -/
theorem isC1On3_probeB :
    IsC1On3 (probeB V T) (probeAb V T) (probeBb V Vt T) (probeBc V T) (clockBox T) where
  isOpen := isOpen_clockBox T
  hasDerivFst := by
    intro q _
    have hsl : Continuous fun r : ℝ => clampedStep V T (((q.2 : ℝ)) : ℂ) r q.1.2 :=
      (continuous_clampedStep hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
        hD.sideNonneg hD.small (hD.absIm q.2)).comp
        (f := fun r : ℝ => ((r, q.1.2) : ℝ × ℝ)) (continuous_id.prodMk continuous_const)
    exact hasDerivAt_re (hsl.integral_hasStrictDerivAt 0 q.1.1).hasDerivAt
  hasDerivSnd := by
    intro q hq
    have hcx := hasDerivAt_deriv_clockSolution_snd_snd hD.pos hD.potC1 hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂Nonneg hD.rad₂
      hD.rad₃Nonneg hD.rad₃ hq.1 hq.2 (hD.memStrip₃ q.2)
    have hint : (fun y : ℝ => ∫ r in (0 : ℝ)..q.1.1, clampedStep V T (((q.2 : ℝ)) : ℂ) r y)
        =ᶠ[nhds q.1.2]
        fun y : ℝ => deriv (fun x : ℝ => clockSolution V q.1.1 x (((q.2 : ℝ)) : ℂ)) y := by
      refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.2) fun y hy => ?_
      exact (deriv_clockSolution_snd hD.pos hD.pot hD.massNonneg hD.mass hD.radNonneg hD.rad
        hD.sideNonneg hD.small (le_of_lt hq.1) hy (hD.absIm q.2)).symm
    exact hasDerivAt_re (hcx.congr_of_eventuallyEq hint)
  hasDerivThd := by
    intro q _
    have hcx := hasDerivAt_clampedOuter_transverse hD.pos hD.pot hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂ q.1.1 q.1.2
      (hD.memStrip₂ q.2)
    exact hasDerivAt_re_ofReal hcx
  contFst := hD.continuous_probeAb
  contSnd := hD.continuous_probeBb
  contThd := hD.continuous_probeBc

/-- **The transverse derivative is continuously differentiable in all three variables.** -/
theorem isC1On3_probeC :
    IsC1On3 (probeC V T) (probeAc V T) (probeBc V T) (probeCc V T) (clockBox T) where
  isOpen := isOpen_clockBox T
  hasDerivFst := by
    intro q hq
    have hcx := hasDerivAt_deriv_clockSolution_transverse_fst hD.pos hD.pot hD.massNonneg
      hD.mass hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂Nonneg
      hD.rad₂ hq.1 (le_of_lt hq.2) (hD.memStrip₂ q.2)
    refine (hasDerivAt_re hcx).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.1) fun x hx => ?_
    show probeC V T x q.1.2 q.2 = _
    rw [probeC, clampedSolution, boxClamp_eq_self (le_of_lt hx),
      boxClamp_eq_self (le_of_lt hq.2)]
  hasDerivSnd := by
    intro q hq
    have hcx := hasDerivAt_deriv_clockSolution_transverse_snd hD.pos hD.pot hD.massNonneg
      hD.mass hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂Nonneg
      hD.rad₂ (le_of_lt hq.1) hq.2 (hD.memStrip₂ q.2)
    refine (hasDerivAt_re hcx).congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hq.2) fun y hy => ?_
    show probeC V T q.1.1 y q.2 = _
    rw [probeC, clampedSolution, boxClamp_eq_self (le_of_lt hq.1),
      boxClamp_eq_self (le_of_lt hy)]
  hasDerivThd := by
    intro q _
    have hcx := hasDerivAt_deriv_clockSolution_transverse hD.pos hD.pot hD.massNonneg hD.mass
      hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁ (abs_boxClamp_le hD.sideNonneg q.1.1)
      (abs_boxClamp_le hD.sideNonneg q.1.2) (hD.memStrip₁ q.2)
    exact hasDerivAt_re_ofReal hcx
  contFst := hD.continuous_probeAc
  contSnd := hD.continuous_probeBc
  contThd := hD.continuous_probeCc

end ClockDatum

end GaloisForLFunctions.HTGeometry
