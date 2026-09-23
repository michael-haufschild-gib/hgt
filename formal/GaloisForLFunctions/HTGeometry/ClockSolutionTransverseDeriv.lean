import GaloisForLFunctions.HTGeometry.ClockSolutionSecondNull

/-!
# The transverse derivatives of the solution, jointly in all three variables

The chart d'Alembertian reads the transverse second derivative of the field, and the two null
derivatives of the transverse one, so the transverse derivatives are needed as functions of all
three variables at once, not one null slice at a time.

They are supplied by the Cauchy representation on a disc of fixed radius about the point: for a
family holomorphic on a strip and jointly continuous there, every iterated derivative is again
jointly continuous. Applied to the clamped solution — clamped in the null coordinates only, since
the real axis lies in every strip — this gives the joint continuity of the solution's transverse
derivatives and hence of the step operator itself as a function of all three variables.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- The solution as a family indexed by the two null coordinates, clamped to the rectangle. -/
noncomputable def clampedSolution (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (p : ℝ × ℝ) : ℂ → ℂ :=
  clockSolution V (boxClamp T p.1) (boxClamp T p.2)

theorem continuousOn_clampedSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℂ => clampedSolution V T q.1 q.2) (univ ×ˢ imStrip ρ) :=
  continuousOn_clockSolution_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall

theorem differentiableOn_clampedSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (p : ℝ × ℝ) : DifferentiableOn ℂ (clampedSolution V T p) (imStrip ρ) :=
  differentiableOn_clockSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    (abs_boxClamp_le hT p.1) (abs_boxClamp_le hT p.2)

/-- **The transverse derivative of the solution is jointly continuous.** -/
theorem continuousAt_deriv_clampedSolution {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) {q : (ℝ × ℝ) × ℂ} (hq : q.2 ∈ imStrip ρ₁) :
    ContinuousAt (fun q' : (ℝ × ℝ) × ℂ => deriv (clampedSolution V T q'.1) q'.2) q :=
  continuousAt_deriv_of_strip hρ₁ hρ₁0
    (continuousOn_clampedSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall)
    (differentiableOn_clampedSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall) hq

/-- **The second transverse derivative of the solution is jointly continuous.** -/
theorem continuousAt_deriv_deriv_clampedSolution {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) {q : (ℝ × ℝ) × ℂ} (hq : q.2 ∈ imStrip ρ₁) :
    ContinuousAt (fun q' : (ℝ × ℝ) × ℂ => deriv (deriv (clampedSolution V T q'.1)) q'.2) q :=
  continuousAt_deriv_deriv_of_strip hρ₁ hρ₁0
    (continuousOn_clampedSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall)
    (differentiableOn_clampedSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall) hq

/-- **The step operator applied to the solution is jointly continuous in the two null coordinates
and the transverse point.** -/
theorem continuousAt_clampedStep_joint {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) {q : (ℝ × ℝ) × ℂ} (hq : q.2 ∈ imStrip ρ₁) :
    ContinuousAt (fun q' : (ℝ × ℝ) × ℂ => clampedStep V T q'.2 q'.1.1 q'.1.2) q := by
  have hopen : IsOpen ((univ : Set (ℝ × ℝ)) ×ˢ imStrip ρ) :=
    isOpen_univ.prod (isOpen_imStrip ρ)
  have hq2 : q.2 ∈ imStrip ρ := imStrip_mono hρ₁.le hq
  have hq0 : q.2 ∈ imStrip ρ₀ := imStrip_mono hρ.le hq2
  have hsecond := continuousAt_deriv_deriv_clampedSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    hρ₁0 hρ₁ hq
  have hclampmap : Continuous fun q' : (ℝ × ℝ) × ℂ =>
      (((boxClamp T q'.1.1, boxClamp T q'.1.2), q'.2) : (ℝ × ℝ) × ℂ) :=
    ((((continuous_boxClamp T).comp (continuous_fst.comp continuous_fst)).prodMk
      ((continuous_boxClamp T).comp (continuous_snd.comp continuous_fst))).prodMk
        continuous_snd)
  have hVat : ContinuousAt
      (fun q' : (ℝ × ℝ) × ℂ => V (boxClamp T q'.1.1) (boxClamp T q'.1.2) q'.2) q := by
    have hbase : ContinuousAt (fun r : (ℝ × ℝ) × ℂ => V r.1.1 r.1.2 r.2)
        (((boxClamp T q.1.1, boxClamp T q.1.2), q.2) : (ℝ × ℝ) × ℂ) :=
      hV.cont.continuousAt
        ((isOpen_univ.prod (isOpen_imStrip ρ₀)).mem_nhds ⟨mem_univ _, hq0⟩)
    exact hbase.comp (x := q)
      (f := fun q' : (ℝ × ℝ) × ℂ =>
        (((boxClamp T q'.1.1, boxClamp T q'.1.2), q'.2) : (ℝ × ℝ) × ℂ))
      hclampmap.continuousAt
  have hWat : ContinuousAt (fun q' : (ℝ × ℝ) × ℂ => clampedSolution V T q'.1 q'.2) q :=
    (continuousOn_clampedSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall).continuousAt
      (hopen.mem_nhds ⟨mem_univ _, hq2⟩)
  exact (hsecond.add (hVat.mul hWat)).div_const 4

end GaloisForLFunctions.HTGeometry
