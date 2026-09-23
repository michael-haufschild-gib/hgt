import GaloisForLFunctions.HTGeometry.ClockTubeSecondTransverse

/-!
# The remaining second derivatives of the solution on a tube

Two derivatives are still needed before the probe data can be assembled: the transverse derivative of
the *outer* integral of the step operator, which is the mixed null–transverse derivative read in the
other order, and the mixed transverse–transverse derivative `∂_j ∂_i u` along two different
coordinates.

Both come from the same source as the others. The first is the transverse derivative passing through
a parametric integral; the second is the slice holomorphy of a single transverse partial derivative,
which the corpus already has.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- The slice of the step operator through a point of the tube, jointly with the *first* null
coordinate. -/
theorem continuousOn_clampedTubeStep_sliceOuter {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (t : ℝ) {z : Fin k → ℂ} (hz : z ∈ tube k ρ₁) (i : Fin k) :
    ContinuousOn (fun q : ℝ × ℂ => clampedTubeStep V T (Function.update z i q.2) q.1 t)
      (univ ×ˢ imStrip ρ₁) := by
  intro q hq
  have hmem : Function.update z i q.2 ∈ tube k ρ₁ := update_mem_tube hz i hq.2
  have hbase := continuousAt_clampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    (q := (((q.1, t) : ℝ × ℝ), Function.update z i q.2)) hmem
  have hmap : ContinuousAt (fun q' : ℝ × ℂ =>
      ((((q'.1, t) : ℝ × ℝ), Function.update z i q'.2) : (ℝ × ℝ) × (Fin k → ℂ))) q :=
    ((continuous_fst.prodMk continuous_const).prodMk
      ((differentiable_updateSlice z i).continuous.comp continuous_snd)).continuousAt
  exact (hbase.comp (x := q)
    (f := fun q' : ℝ × ℂ =>
      ((((q'.1, t) : ℝ × ℝ), Function.update z i q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    hmap).continuousWithinAt

/-- **The transverse partial derivative passes through the outer integration.** -/
theorem hasDerivAt_clampedTubeOuter_transverse {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂ : ρ₂ < ρ₁) (ξ η : ℝ)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) (i : Fin k) :
    HasDerivAt (fun ζ : ℂ => ∫ s in (0 : ℝ)..ξ, clampedTubeStep V T (Function.update z i ζ) s η)
      (∫ s in (0 : ℝ)..ξ, cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s η) z)
      (z i) := by
  have hz₁ : z ∈ tube k ρ₁ := tube_mono hρ₂.le hz
  exact hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₁) (ρ := ρ₂)
    (F := fun s ζ => clampedTubeStep V T (Function.update z i ζ) s η) hρ₂
    (continuousOn_clampedTubeStep_sliceOuter hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ η hz₁ i)
    (fun s => sliceHolo_mono
      (sliceHolo_clampedTubeStepFun hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall s η) hρ₁.le z hz₁ i)
    (mem_imStrip.mpr (hz i))

/-! ## The mixed transverse derivatives -/

/-- The solution at clamped null coordinates is continuous in the transverse point alone. -/
theorem continuousOn_clampedTubeSolution_fixed {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (p : ℝ × ℝ) : ContinuousOn (clampedTubeSolution V T p) (tube k ρ) := by
  have hopen : IsOpen ((univ : Set ((ℝ : Type) × ℝ)) ×ˢ tube k ρ) :=
    isOpen_univ.prod (isOpen_tube k ρ)
  have hjoint := continuousOn_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
  intro y hy
  have hbase := hjoint.continuousAt (x := ((p, y) : (ℝ × ℝ) × (Fin k → ℂ)))
    (hopen.mem_nhds ⟨mem_univ _, hy⟩)
  exact (hbase.comp (x := y)
    (f := fun y' : (Fin k → ℂ) => ((p, y') : (ℝ × ℝ) × (Fin k → ℂ)))
    (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt

/-- **A transverse partial derivative of the solution is slice holomorphic.** -/
theorem sliceHolo_cpartial_clampedTubeSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (i : Fin k) (p : ℝ × ℝ) : SliceHolo (cpartial i (clampedTubeSolution V T p)) ρ :=
  sliceHolo_cpartial (continuousOn_clampedTubeSolution_fixed hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall p)
    (sliceHolo_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall p) i

/-- **The mixed transverse partial derivative of the solution is jointly continuous.** -/
theorem continuousAt_cpartial_cpartial_mixed {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (i j : Fin k)
    {q : (ℝ × ℝ) × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ₂) :
    ContinuousAt (fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      cpartial j (cpartial i (clampedTubeSolution V T q'.1)) q'.2) q :=
  continuousAt_cpartial_of_tube (ρ' := ρ₁) (P := ℝ × ℝ)
    (W := fun p : ℝ × ℝ => cpartial i (clampedTubeSolution V T p)) hρ₂ hρ₂0
    (fun _ hr => (continuousAt_cpartial_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
      hρ₁0 hρ₁ i hr.2).continuousWithinAt)
    (fun p => sliceHolo_mono
      (sliceHolo_cpartial_clampedTubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall i p) hρ₁.le)
    j hq

end GaloisForLFunctions.HTGeometry
