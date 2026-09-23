import GaloisForLFunctions.HTGeometry.ClockTubePureSecondSnd

/-!
# The clock datum on a tube and its kernels along the real transverse points

The construction with several coupled transverse coordinates is controlled by the same data as in one
variable: one potential, one tube of analyticity, one bound, one rectangle and a decreasing chain of
four inner radii, each losing a little of the tube to a Cauchy estimate. This file bundles them and
records that, along *real* transverse points, every kernel of the construction is continuous on the
whole of `ℝ² × ℝᵏ`.

The reason is the same as in one variable: the real points lie in the interior of every tube, so the
transverse variables never have to be clamped, only the two null coordinates do.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- The data of a clock construction on a tube. -/
structure TubeDatum (V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ) (ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ) : Prop where
  pos : 0 < ρ₀
  potC1 : TubePotentialC1 V Vs Vt ρ₀
  massNonneg : 0 ≤ Mv
  mass : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv
  radNonneg : 0 ≤ ρ
  rad : ρ < ρ₀
  sideNonneg : 0 ≤ T
  small : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1
  rad₁Pos : 0 < ρ₁
  rad₁ : ρ₁ < ρ
  rad₂Pos : 0 < ρ₂
  rad₂ : ρ₂ < ρ₁
  rad₃Pos : 0 < ρ₃
  rad₃ : ρ₃ < ρ₂

/-- A real transverse point of the tube. -/
def realTube (y : Fin k → ℝ) : Fin k → ℂ := fun i => ((y i : ℝ) : ℂ)

theorem continuous_realTube : Continuous (realTube (k := k)) :=
  continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)

/-- The continuous embedding of the parameter space along the real transverse points. -/
theorem continuous_realTubePoint :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ)) :=
  continuous_fst.prodMk (continuous_realTube.comp continuous_snd)

/-- The inner integral of a kernel along the second null coordinate. -/
theorem continuous_innerRealTube {K : (Fin k → ℂ) → ℝ → ℝ → ℂ}
    (hK : Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => K (realTube q.2) q.1.1 q.1.2) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      ∫ r in (0 : ℝ)..q.1.2, K (realTube q.2) q.1.1 r := by
  have huncurry : Continuous fun p : ((ℝ × ℝ) × (Fin k → ℝ)) × ℝ =>
      K (realTube p.1.2) p.1.1.1 p.2 :=
    hK.comp (f := fun p : ((ℝ × ℝ) × (Fin k → ℝ)) × ℝ =>
        ((((p.1.1.1, p.2) : ℝ × ℝ), p.1.2) : (ℝ × ℝ) × (Fin k → ℝ)))
      (((continuous_fst.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd).prodMk
        (continuous_snd.comp continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (q : (ℝ × ℝ) × (Fin k → ℝ)) (r : ℝ) => K (realTube q.2) q.1.1 r) huncurry
    (continuous_snd.comp continuous_fst)

/-- The outer integral of a kernel along the first null coordinate. -/
theorem continuous_outerRealTube {K : (Fin k → ℂ) → ℝ → ℝ → ℂ}
    (hK : Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => K (realTube q.2) q.1.1 q.1.2) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      ∫ r in (0 : ℝ)..q.1.1, K (realTube q.2) r q.1.2 := by
  have huncurry : Continuous fun p : ((ℝ × ℝ) × (Fin k → ℝ)) × ℝ =>
      K (realTube p.1.2) p.2 p.1.1.2 :=
    hK.comp (f := fun p : ((ℝ × ℝ) × (Fin k → ℝ)) × ℝ =>
        ((((p.2, p.1.1.2) : ℝ × ℝ), p.1.2) : (ℝ × ℝ) × (Fin k → ℝ)))
      ((continuous_snd.prodMk (continuous_snd.comp (continuous_fst.comp continuous_fst))).prodMk
        (continuous_snd.comp continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (q : (ℝ × ℝ) × (Fin k → ℝ)) (r : ℝ) => K (realTube q.2) r q.1.2) huncurry
    (continuous_fst.comp continuous_fst)

namespace TubeDatum

variable {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
  (hD : TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T)

include hD

theorem pot : TubePotential V ρ₀ := hD.potC1.base

theorem rad₁Nonneg : 0 ≤ ρ₁ := hD.rad₁Pos.le

theorem rad₂Nonneg : 0 ≤ ρ₂ := hD.rad₂Pos.le

theorem rad₃Nonneg : 0 ≤ ρ₃ := hD.rad₃Pos.le

/-- The real transverse points lie inside the innermost tube. -/
theorem memTube₃ (y : Fin k → ℝ) : realTube y ∈ tube k ρ₃ := by
  intro i
  rw [realTube, Complex.ofReal_im, abs_zero]
  exact hD.rad₃Pos

theorem memTube₂ (y : Fin k → ℝ) : realTube y ∈ tube k ρ₂ := tube_mono hD.rad₃.le (hD.memTube₃ y)

theorem memTube₁ (y : Fin k → ℝ) : realTube y ∈ tube k ρ₁ := tube_mono hD.rad₂.le (hD.memTube₂ y)

theorem memTube (y : Fin k → ℝ) : realTube y ∈ tube k ρ := tube_mono hD.rad₁.le (hD.memTube₁ y)

theorem memTube₀ (y : Fin k → ℝ) : realTube y ∈ tube k ρ₀ := tube_mono hD.rad.le (hD.memTube y)

theorem absIm (y : Fin k → ℝ) : ∀ i, |(realTube y i).im| ≤ ρ := fun i => (hD.memTube y i).le

/-! ## The kernels -/

/-- **The step operator along the real transverse points is continuous on the whole space.** -/
theorem continuous_stepReal :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      clampedTubeStep V T (realTube q.2) q.1.1 q.1.2 := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_clampedTubeStep_joint hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁
    (q := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ))) (hD.memTube₁ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

/-- **A transverse derivative of the step operator along the real points.** -/
theorem continuous_dStepReal (i : Fin k) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      dClampedTubeStep V T i (realTube q.2) q.1.1 q.1.2 := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_dClampedTubeStep_joint hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂Nonneg hD.rad₂ i
    (q := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ))) (hD.memTube₂ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

/-- **A second transverse derivative of the step operator along the real points.** -/
theorem continuous_d2StepReal (i : Fin k) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      d2ClampedTubeStep V T i (realTube q.2) q.1.1 q.1.2 := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_d2ClampedTubeStep_joint hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ hD.rad₂Nonneg hD.rad₂
    hD.rad₃Nonneg hD.rad₃ i
    (q := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ))) (hD.memTube₃ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

/-- **The solution along the real transverse points.** -/
theorem continuous_solReal :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      tubeSolution V (boxClamp T q.1.1) (boxClamp T q.1.2) (realTube q.2) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := (continuousOn_tubeSolution_clamped hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small).continuousAt
    (x := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    ((isOpen_univ.prod (isOpen_tube k ρ)).mem_nhds ⟨mem_univ _, hD.memTube q.2⟩)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

/-- **A transverse derivative of the solution along the real points.** -/
theorem continuous_dSolReal (i : Fin k) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      cpartial i (clampedTubeSolution V T q.1) (realTube q.2) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_cpartial_clampedTubeSolution hD.pos hD.pot hD.massNonneg hD.mass
    hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ i
    (q := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ))) (hD.memTube₁ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

/-- **A second transverse derivative of the solution along the real points.** -/
theorem continuous_d2SolReal (i : Fin k) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      cpartial i (cpartial i (clampedTubeSolution V T q.1)) (realTube q.2) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := continuousAt_cpartial_cpartial_clampedTubeSolution hD.pos hD.pot hD.massNonneg
    hD.mass hD.radNonneg hD.rad hD.sideNonneg hD.small hD.rad₁Nonneg hD.rad₁ i
    (q := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ))) (hD.memTube₁ q.2)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

/-- **The potential along the real transverse points.** -/
theorem continuous_VReal :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => V q.1.1 q.1.2 (realTube q.2) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := hD.pot.cont.continuousAt (x := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    ((isOpen_univ.prod (isOpen_tube k ρ₀)).mem_nhds ⟨mem_univ _, hD.memTube₀ q.2⟩)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

theorem continuous_VsReal :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => Vs q.1.1 q.1.2 (realTube q.2) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := hD.potC1.contFst.continuousAt
    (x := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    ((isOpen_univ.prod (isOpen_tube k ρ₀)).mem_nhds ⟨mem_univ _, hD.memTube₀ q.2⟩)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

theorem continuous_VtReal :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => Vt q.1.1 q.1.2 (realTube q.2) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  have hbase := hD.potC1.contSnd.continuousAt
    (x := ((q.1, realTube q.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    ((isOpen_univ.prod (isOpen_tube k ρ₀)).mem_nhds ⟨mem_univ _, hD.memTube₀ q.2⟩)
  exact hbase.comp (x := q)
    (f := fun q' : (ℝ × ℝ) × (Fin k → ℝ) => ((q'.1, realTube q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    continuous_realTubePoint.continuousAt

/-! ## The parametric integrals -/

/-- **The derivative of the step operator along the first null coordinate, on the real points.** -/
theorem continuous_stepFstReal :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      clampedTubeStepFst V Vs T (realTube q.2) q.1.1 q.1.2 := by
  classical
  have h1 : Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      ∑ i : Fin k, ∫ r in (0 : ℝ)..q.1.2, d2ClampedTubeStep V T i (realTube q.2) q.1.1 r := by
    refine continuous_finsetSum Finset.univ fun i _ => ?_
    exact continuous_innerRealTube (K := fun z s t => d2ClampedTubeStep V T i z s t)
      (hD.continuous_d2StepReal i)
  have h3 := continuous_innerRealTube (K := fun z s t => clampedTubeStep V T z s t)
    hD.continuous_stepReal
  exact ((h1.add ((hD.continuous_VsReal.mul hD.continuous_solReal).add
    (hD.continuous_VReal.mul h3))).div_const 4)

/-- **The derivative of the step operator along the second null coordinate, on the real points.** -/
theorem continuous_stepSndReal :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      clampedTubeStepSnd V Vt T (realTube q.2) q.1.1 q.1.2 := by
  classical
  have h1 : Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) =>
      ∑ i : Fin k, ∫ r in (0 : ℝ)..q.1.1, d2ClampedTubeStep V T i (realTube q.2) r q.1.2 := by
    refine continuous_finsetSum Finset.univ fun i _ => ?_
    exact continuous_outerRealTube (K := fun z s t => d2ClampedTubeStep V T i z s t)
      (hD.continuous_d2StepReal i)
  have h3 := continuous_outerRealTube (K := fun z s t => clampedTubeStep V T z s t)
    hD.continuous_stepReal
  exact ((h1.add ((hD.continuous_VtReal.mul hD.continuous_solReal).add
    (hD.continuous_VReal.mul h3))).div_const 4)

end TubeDatum

end GaloisForLFunctions.HTGeometry
