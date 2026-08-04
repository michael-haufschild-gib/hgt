import GaloisForLFunctions.HTGeometry.ClockSolutionPureSecondSnd

/-!
# The clock datum and its kernels along the real transverse axis

The construction is controlled by one potential, one strip of analyticity, one bound, one rectangle
and a decreasing chain of four inner radii, each losing a little of the strip to a Cauchy estimate.
This file bundles them into a single datum, so that the statements that follow carry one hypothesis
rather than fourteen.

Along the real transverse axis every kernel of the construction is continuous on the whole of `ℝ³`.
The reason is that the real axis lies in the interior of every strip: the transverse variable never
has to be clamped, only the two null coordinates do. So the kernels restricted to real transverse
values are global objects, and the parametric integrals built from them may be taken with variable
limits without any further hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- The data of a clock construction: an analytic potential with continuously differentiable
dependence on the null coordinates, a strip, a bound, a small rectangle, and the chain of inner
radii the Cauchy estimates consume. -/
structure ClockDatum (V Vs Vt : ℝ → ℝ → ℂ → ℂ) (ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ) : Prop where
  pos : 0 < ρ₀
  potC1 : StripPotentialC1 V Vs Vt ρ₀
  massNonneg : 0 ≤ Mv
  mass : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv
  radNonneg : 0 ≤ ρ
  rad : ρ < ρ₀
  sideNonneg : 0 ≤ T
  small : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1
  rad₁Nonneg : 0 ≤ ρ₁
  rad₁ : ρ₁ < ρ
  rad₂Nonneg : 0 ≤ ρ₂
  rad₂ : ρ₂ < ρ₁
  rad₃Pos : 0 < ρ₃
  rad₃ : ρ₃ < ρ₂

/-- The continuous embedding of the parameter space along the real transverse axis. -/
theorem continuous_realPoint :
    Continuous fun q : (ℝ × ℝ) × ℝ => ((q.1, (q.2 : ℂ)) : (ℝ × ℝ) × ℂ) :=
  continuous_fst.prodMk (Complex.continuous_ofReal.comp continuous_snd)

/-- The inner integral of a kernel along the second null coordinate. -/
theorem continuous_innerReal {K : ℂ → ℝ → ℝ → ℂ}
    (hK : Continuous fun q : (ℝ × ℝ) × ℝ => K ((q.2 : ℝ) : ℂ) q.1.1 q.1.2) :
    Continuous fun q : (ℝ × ℝ) × ℝ => ∫ r in (0 : ℝ)..q.1.2, K ((q.2 : ℝ) : ℂ) q.1.1 r := by
  have huncurry : Continuous fun p : ((ℝ × ℝ) × ℝ) × ℝ => K ((p.1.2 : ℝ) : ℂ) p.1.1.1 p.2 :=
    hK.comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
        ((((p.1.1.1, p.2) : ℝ × ℝ), p.1.2) : (ℝ × ℝ) × ℝ))
      (((continuous_fst.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd).prodMk
        (continuous_snd.comp continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (q : (ℝ × ℝ) × ℝ) (r : ℝ) => K ((q.2 : ℝ) : ℂ) q.1.1 r) huncurry
    (continuous_snd.comp continuous_fst)

/-- The outer integral of a kernel along the first null coordinate. -/
theorem continuous_outerReal {K : ℂ → ℝ → ℝ → ℂ}
    (hK : Continuous fun q : (ℝ × ℝ) × ℝ => K ((q.2 : ℝ) : ℂ) q.1.1 q.1.2) :
    Continuous fun q : (ℝ × ℝ) × ℝ => ∫ r in (0 : ℝ)..q.1.1, K ((q.2 : ℝ) : ℂ) r q.1.2 := by
  have huncurry : Continuous fun p : ((ℝ × ℝ) × ℝ) × ℝ => K ((p.1.2 : ℝ) : ℂ) p.2 p.1.1.2 :=
    hK.comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
        ((((p.2, p.1.1.2) : ℝ × ℝ), p.1.2) : (ℝ × ℝ) × ℝ))
      ((continuous_snd.prodMk (continuous_snd.comp (continuous_fst.comp continuous_fst))).prodMk
        (continuous_snd.comp continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (q : (ℝ × ℝ) × ℝ) (r : ℝ) => K ((q.2 : ℝ) : ℂ) r q.1.2) huncurry
    (continuous_fst.comp continuous_fst)

namespace ClockDatum

variable {V Vs Vt : ℝ → ℝ → ℂ → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

theorem pot : StripPotential V ρ₀ := hD.potC1.base

theorem rad₃Nonneg : 0 ≤ ρ₃ := hD.rad₃Pos.le

/-- The real transverse axis lies inside the innermost strip. -/
theorem memStrip₃ (w : ℝ) : ((w : ℝ) : ℂ) ∈ imStrip ρ₃ := by
  rw [mem_imStrip, Complex.ofReal_im, abs_zero]
  exact hD.rad₃Pos

theorem memStrip₂ (w : ℝ) : ((w : ℝ) : ℂ) ∈ imStrip ρ₂ := imStrip_mono hD.rad₃.le (hD.memStrip₃ w)

theorem memStrip₁ (w : ℝ) : ((w : ℝ) : ℂ) ∈ imStrip ρ₁ := imStrip_mono hD.rad₂.le (hD.memStrip₂ w)

theorem memStrip (w : ℝ) : ((w : ℝ) : ℂ) ∈ imStrip ρ := imStrip_mono hD.rad₁.le (hD.memStrip₁ w)

theorem memStrip₀ (w : ℝ) : ((w : ℝ) : ℂ) ∈ imStrip ρ₀ := imStrip_mono hD.rad.le (hD.memStrip w)

theorem absIm (w : ℝ) : |(((w : ℝ) : ℂ)).im| ≤ ρ := le_of_lt (mem_imStrip.mp (hD.memStrip w))

/-! ## The kernels -/

/-- **The step operator along the real transverse axis is continuous on the whole space.** -/
theorem continuous_stepReal :
    Continuous fun q : (ℝ × ℝ) × ℝ => clampedStep V T ((q.2 : ℝ) : ℂ) q.1.1 q.1.2 := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_clampedStep_joint hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁
    (q := ((q.1, ((q.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ)) (hD.memStrip₁ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × ℝ => ((q'.1, ((q'.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    continuous_realPoint.continuousAt

/-- **The transverse derivative of the step operator along the real axis.** -/
theorem continuous_dStepReal :
    Continuous fun q : (ℝ × ℝ) × ℝ => dClampedStep V T ((q.2 : ℝ) : ℂ) q.1.1 q.1.2 := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_dClampedStep_joint hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂Nonneg hD.rad₂
    (q := ((q.1, ((q.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ)) (hD.memStrip₂ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × ℝ => ((q'.1, ((q'.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    continuous_realPoint.continuousAt

/-- **The second transverse derivative of the step operator along the real axis.** -/
theorem continuous_d2StepReal :
    Continuous fun q : (ℝ × ℝ) × ℝ => d2ClampedStep V T ((q.2 : ℝ) : ℂ) q.1.1 q.1.2 := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_d2ClampedStep_joint hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂Nonneg hD.rad₂
    hD.rad₃Nonneg hD.rad₃
    (q := ((q.1, ((q.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ)) (hD.memStrip₃ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × ℝ => ((q'.1, ((q'.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    continuous_realPoint.continuousAt

/-- **The solution along the real transverse axis.** -/
theorem continuous_solReal :
    Continuous fun q : (ℝ × ℝ) × ℝ =>
      clockSolution V (boxClamp T q.1.1) (boxClamp T q.1.2) ((q.2 : ℝ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := (continuousOn_clockSolution_clamped hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small).continuousAt
    (x := ((q.1, ((q.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    ((isOpen_univ.prod (isOpen_imStrip ρ)).mem_nhds ⟨mem_univ _, hD.memStrip q.2⟩)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × ℝ => ((q'.1, ((q'.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    continuous_realPoint.continuousAt

/-- **The transverse derivative of the solution along the real axis.** -/
theorem continuous_dSolReal :
    Continuous fun q : (ℝ × ℝ) × ℝ => deriv (clampedSolution V T q.1) ((q.2 : ℝ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_deriv_clampedSolution hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁
    (q := ((q.1, ((q.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ)) (hD.memStrip₁ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × ℝ => ((q'.1, ((q'.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    continuous_realPoint.continuousAt

/-- **The second transverse derivative of the solution along the real axis.** -/
theorem continuous_d2SolReal :
    Continuous fun q : (ℝ × ℝ) × ℝ =>
      deriv (deriv (clampedSolution V T q.1)) ((q.2 : ℝ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_deriv_deriv_clampedSolution hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁
    (q := ((q.1, ((q.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ)) (hD.memStrip₁ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × ℝ => ((q'.1, ((q'.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    continuous_realPoint.continuousAt

/-- **The potential along the real transverse axis.** -/
theorem continuous_VReal :
    Continuous fun q : (ℝ × ℝ) × ℝ => V q.1.1 q.1.2 ((q.2 : ℝ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := hD.pot.cont.continuousAt (x := ((q.1, ((q.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    ((isOpen_univ.prod (isOpen_imStrip ρ₀)).mem_nhds ⟨mem_univ _, hD.memStrip₀ q.2⟩)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × ℝ => ((q'.1, ((q'.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    continuous_realPoint.continuousAt

theorem continuous_VsReal :
    Continuous fun q : (ℝ × ℝ) × ℝ => Vs q.1.1 q.1.2 ((q.2 : ℝ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := hD.potC1.contFst.continuousAt (x := ((q.1, ((q.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    ((isOpen_univ.prod (isOpen_imStrip ρ₀)).mem_nhds ⟨mem_univ _, hD.memStrip₀ q.2⟩)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × ℝ => ((q'.1, ((q'.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    continuous_realPoint.continuousAt

theorem continuous_VtReal :
    Continuous fun q : (ℝ × ℝ) × ℝ => Vt q.1.1 q.1.2 ((q.2 : ℝ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := hD.potC1.contSnd.continuousAt (x := ((q.1, ((q.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    ((isOpen_univ.prod (isOpen_imStrip ρ₀)).mem_nhds ⟨mem_univ _, hD.memStrip₀ q.2⟩)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × ℝ => ((q'.1, ((q'.2 : ℝ) : ℂ)) : (ℝ × ℝ) × ℂ))
    continuous_realPoint.continuousAt

/-! ## The parametric integrals

Every integral below has a variable upper limit, which costs nothing: along the real transverse axis
the integrands are continuous on the whole space.
-/

/-- **The derivative of the step operator along the first null coordinate, on the real axis.** -/
theorem continuous_stepFstReal :
    Continuous fun q : (ℝ × ℝ) × ℝ => clampedStepFst V Vs T ((q.2 : ℝ) : ℂ) q.1.1 q.1.2 := by
  have h1 := continuous_innerReal (K := fun z s t => d2ClampedStep V T z s t)
    hD.continuous_d2StepReal
  have h3 := continuous_innerReal (K := fun z s t => clampedStep V T z s t)
    hD.continuous_stepReal
  exact ((h1.add ((hD.continuous_VsReal.mul hD.continuous_solReal).add
    (hD.continuous_VReal.mul h3))).div_const 4)

/-- **The derivative of the step operator along the second null coordinate, on the real axis.** -/
theorem continuous_stepSndReal :
    Continuous fun q : (ℝ × ℝ) × ℝ => clampedStepSnd V Vt T ((q.2 : ℝ) : ℂ) q.1.1 q.1.2 := by
  have h1 := continuous_outerReal (K := fun z s t => d2ClampedStep V T z s t)
    hD.continuous_d2StepReal
  have h3 := continuous_outerReal (K := fun z s t => clampedStep V T z s t)
    hD.continuous_stepReal
  exact ((h1.add ((hD.continuous_VtReal.mul hD.continuous_solReal).add
    (hD.continuous_VReal.mul h3))).div_const 4)

end ClockDatum

end GaloisForLFunctions.HTGeometry
