import GaloisForLFunctions.HTGeometry.ClockTubeSolutionSecondNull

/-!
# The transverse derivatives of the solution on a tube, jointly in all variables

The chart d'Alembertian reads the transverse second derivatives of the field, and the null
derivatives of the transverse ones, so the transverse derivatives are needed as functions of all
variables at once, not one null slice at a time.

They are supplied by the Cauchy representation along each coordinate slice, on a disc of fixed radius
about the point: for a family slice holomorphic on a tube and jointly continuous there, every partial
derivative along a coordinate is again jointly continuous. Applied to the clamped solution — clamped
in the null coordinates only, since the real points lie in every tube — this gives the joint
continuity of the transverse partial derivatives and hence of the step operator itself as a function
of all variables.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- The solution as a family indexed by the two null coordinates, clamped to the rectangle. -/
noncomputable def clampedTubeSolution (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (p : ℝ × ℝ) :
    (Fin k → ℂ) → ℂ :=
  tubeSolution V (boxClamp T p.1) (boxClamp T p.2)

theorem continuousOn_clampedTubeSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1) :
    ContinuousOn (fun q : (ℝ × ℝ) × (Fin k → ℂ) => clampedTubeSolution V T q.1 q.2)
      (univ ×ˢ tube k ρ) :=
  continuousOn_tubeSolution_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall

theorem sliceHolo_clampedTubeSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (p : ℝ × ℝ) : SliceHolo (clampedTubeSolution V T p) ρ :=
  sliceHolo_tubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    (abs_boxClamp_le hT p.1) (abs_boxClamp_le hT p.2)

/-- **The transverse partial derivatives of the solution are jointly continuous.** -/
theorem continuousAt_cpartial_clampedTubeSolution {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (i : Fin k)
    {q : (ℝ × ℝ) × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ₁) :
    ContinuousAt (fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      cpartial i (clampedTubeSolution V T q'.1) q'.2) q :=
  continuousAt_cpartial_of_tube hρ₁ hρ₁0
    (continuousOn_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall)
    (sliceHolo_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall) i hq

/-- **The second transverse partial derivatives of the solution are jointly continuous.** -/
theorem continuousAt_cpartial_cpartial_clampedTubeSolution {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (i : Fin k)
    {q : (ℝ × ℝ) × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ₁) :
    ContinuousAt (fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      cpartial i (cpartial i (clampedTubeSolution V T q'.1)) q'.2) q :=
  continuousAt_cpartial_cpartial_of_tube hρ₁ hρ₁0
    (continuousOn_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall)
    (sliceHolo_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall) i hq

/-- **The step operator applied to the solution is jointly continuous in the two null coordinates
and the transverse point.** -/
theorem continuousAt_clampedTubeStep_joint {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) {q : (ℝ × ℝ) × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ₁) :
    ContinuousAt (fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      clampedTubeStep V T q'.2 q'.1.1 q'.1.2) q := by
  classical
  have hopen : IsOpen ((univ : Set ((ℝ : Type) × ℝ)) ×ˢ tube k ρ) :=
    isOpen_univ.prod (isOpen_tube k ρ)
  have hq2 : q.2 ∈ tube k ρ := tube_mono hρ₁.le hq
  have hq0 : q.2 ∈ tube k ρ₀ := tube_mono hρ.le hq2
  have hsecond : ∀ i : Fin k, ContinuousAt (fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      cpartial i (cpartial i (clampedTubeSolution V T q'.1)) q'.2) q := fun i =>
    continuousAt_cpartial_cpartial_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
      hρ₁0 hρ₁ i hq
  have hsum : ContinuousAt (fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      ∑ i, cpartial i (cpartial i (clampedTubeSolution V T q'.1)) q'.2) q :=
    tendsto_finsetSum (f := fun (i : Fin k) (q' : (ℝ × ℝ) × (Fin k → ℂ)) =>
      cpartial i (cpartial i (clampedTubeSolution V T q'.1)) q'.2)
      (a := fun i => cpartial i (cpartial i (clampedTubeSolution V T q.1)) q.2)
      Finset.univ fun i _ => hsecond i
  have hclampmap : Continuous fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      (((boxClamp T q'.1.1, boxClamp T q'.1.2), q'.2) : (ℝ × ℝ) × (Fin k → ℂ)) :=
    ((((continuous_boxClamp T).comp (g := boxClamp T)
      (continuous_fst.comp continuous_fst)).prodMk
      ((continuous_boxClamp T).comp (g := boxClamp T)
        (continuous_snd.comp continuous_fst))).prodMk continuous_snd)
  have hVat : ContinuousAt (fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      V (boxClamp T q'.1.1) (boxClamp T q'.1.2) q'.2) q := by
    have hbase : ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) => V r.1.1 r.1.2 r.2)
        (((boxClamp T q.1.1, boxClamp T q.1.2), q.2) : (ℝ × ℝ) × (Fin k → ℂ)) :=
      hV.cont.continuousAt
        ((isOpen_univ.prod (isOpen_tube k ρ₀)).mem_nhds ⟨mem_univ _, hq0⟩)
    exact hbase.comp (x := q)
      (f := fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
        (((boxClamp T q'.1.1, boxClamp T q'.1.2), q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
      hclampmap.continuousAt
  have hWat : ContinuousAt
      (fun q' : (ℝ × ℝ) × (Fin k → ℂ) => clampedTubeSolution V T q'.1 q'.2) q :=
    (continuousOn_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall).continuousAt
      (hopen.mem_nhds ⟨mem_univ _, hq2⟩)
  exact (hsum.add (hVat.mul hWat)).div_const 4

end GaloisForLFunctions.HTGeometry
