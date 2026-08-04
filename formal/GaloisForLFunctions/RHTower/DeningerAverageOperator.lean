import GaloisForLFunctions.RHTower.DeningerPeriodAverage
import GaloisForLFunctions.RHTower.DeningerHomotopyC1

/-!
# The averaging operator over a period

Averaging a map over one period in a coordinate direction produces a map that is again periodic in
every coordinate and continuously differentiable, whose derivative is the average of the derivative.
Applied to a contraction this is what removes the derivative term of the Cartan formula.

* `deningerAverageOp` : the average over one period in a coordinate direction.
* `deningerAverageOp_periodic` : it preserves periodicity in every coordinate.
* `deningerAverageOp_hasFDerivAt` : its derivative is the average of the derivative.
-/

namespace RHTower

open Complex MeasureTheory

section AverageOperator

variable {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **The average of a map over one period** in a coordinate direction. -/
noncomputable def deningerAverageOp (β : (Fin r → ℂ) → X) (j : Fin r) (w : Fin r → ℂ) : X :=
  ∫ s in (0 : ℝ)..1, β (deningerPeriodCurve w j s)

theorem deningerPeriodCurve_add (w : Fin r → ℂ) (j : Fin r) (c : Fin r → ℂ) (s : ℝ) :
    deningerPeriodCurve (w + c) j s = deningerPeriodCurve w j s + c := by
  show w + c + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ) =
    (w + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) + c
  abel

omit [CompleteSpace X] in
/-- **The average preserves periodicity** in every coordinate. -/
theorem deningerAverageOp_periodic {β : (Fin r → ℂ) → X} (j : Fin r) {l : Fin r}
    (hper : ∀ w : Fin r → ℂ,
      β (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = β w)
    (w : Fin r → ℂ) :
    deningerAverageOp β j (w + (2 * Real.pi * Complex.I) •
        (Pi.single l (1 : ℂ) : Fin r → ℂ)) = deningerAverageOp β j w := by
  show (∫ s in (0 : ℝ)..1, β (deningerPeriodCurve (w + (2 * Real.pi * Complex.I) •
      (Pi.single l (1 : ℂ) : Fin r → ℂ)) j s)) = ∫ s in (0 : ℝ)..1, β (deningerPeriodCurve w j s)
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [deningerPeriodCurve_add, hper]

/-- The swept set of a period curve over a ball is compact. -/
theorem deningerPeriodCurve_image_isCompact (w₀ : Fin r → ℂ) (j : Fin r) :
    IsCompact ((fun p : ℝ × (Fin r → ℂ) => deningerPeriodCurve p.2 j p.1) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)) := by
  haveI : ProperSpace (Fin r → ℂ) := FiniteDimensional.proper ℂ (Fin r → ℂ)
  refine IsCompact.image ((isCompact_Icc).prod (isCompact_closedBall w₀ 1)) ?_
  show Continuous fun p : ℝ × (Fin r → ℂ) =>
    p.2 + ((p.1 : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
  fun_prop

theorem deningerPeriodCurve_mem_image {w₀ : Fin r → ℂ} {j : Fin r} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : Fin r → ℂ} (hx : x ∈ Metric.closedBall w₀ 1) :
    deningerPeriodCurve x j t ∈ (fun p : ℝ × (Fin r → ℂ) => deningerPeriodCurve p.2 j p.1) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1) :=
  ⟨(t, x), ⟨ht, hx⟩, rfl⟩

omit [CompleteSpace X] in
/-- **The derivative of the average is the average of the derivative.** -/
theorem deningerAverageOp_hasFDerivAt {β : (Fin r → ℂ) → X} (hdiff : Differentiable ℂ β)
    (hcont' : Continuous (fderiv ℂ β)) (j : Fin r) (w₀ : Fin r → ℂ) :
    HasFDerivAt (deningerAverageOp β j)
      (∫ s in (0 : ℝ)..1, fderiv ℂ β (deningerPeriodCurve w₀ j s)) w₀ := by
  have hcurvecont : ∀ x : Fin r → ℂ, Continuous (deningerPeriodCurve x j) := by
    intro x
    show Continuous fun s : ℝ =>
      x + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
    fun_prop
  have hKne : ((fun p : ℝ × (Fin r → ℂ) => deningerPeriodCurve p.2 j p.1) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)).Nonempty :=
    ⟨deningerPeriodCurve w₀ j 0, deningerPeriodCurve_mem_image
      ⟨le_refl 0, zero_le_one⟩ (Metric.mem_closedBall_self zero_le_one)⟩
  have hnorm : Continuous fun x : Fin r → ℂ => ‖fderiv ℂ β x‖ := by
    have h : Continuous fun A : (Fin r → ℂ) →L[ℂ] X => ‖A‖ := by
      exact continuous_norm (E := (Fin r → ℂ) →L[ℂ] X)
    exact h.comp hcont'
  obtain ⟨p₀, -, hp₀⟩ := IsCompact.exists_isMaxOn (deningerPeriodCurve_image_isCompact w₀ j) hKne
    (f := fun x => ‖fderiv ℂ β x‖) (Continuous.continuousOn hnorm)
  set C : ℝ := ‖fderiv ℂ β p₀‖ with hCdef
  have hCnonneg : 0 ≤ C := by
    rw [hCdef]
    exact ContinuousLinearMap.opNorm_nonneg _
  have hbound : ∀ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Metric.ball w₀ 1,
      ‖fderiv ℂ β (deningerPeriodCurve x j t)‖ ≤ C := by
    intro t ht x hx
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    exact hp₀ (deningerPeriodCurve_mem_image ht01 (Metric.ball_subset_closedBall hx))
  have htranslate : ∀ (t : ℝ) (x : Fin r → ℂ),
      HasFDerivAt (fun y : Fin r → ℂ => β (deningerPeriodCurve y j t))
        (fderiv ℂ β (deningerPeriodCurve x j t)) x := by
    intro t x
    have hshift : HasFDerivAt (fun y : Fin r → ℂ => deningerPeriodCurve y j t)
        (ContinuousLinearMap.id ℂ (Fin r → ℂ)) x := by
      have h := (hasFDerivAt_id (𝕜 := ℂ) x).add_const
        ((((t : ℂ) * (2 * Real.pi * Complex.I)) •
          (Pi.single j (1 : ℂ) : Fin r → ℂ) : Fin r → ℂ))
      exact h
    have h := ((hdiff (deningerPeriodCurve x j t)).hasFDerivAt).comp x hshift
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  refine _root_.intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (x : Fin r → ℂ) (t : ℝ) => β (deningerPeriodCurve x j t))
    (F' := fun (x : Fin r → ℂ) (t : ℝ) => fderiv ℂ β (deningerPeriodCurve x j t))
    (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hdiff.continuous.comp (hcurvecont x)).aestronglyMeasurable)
    ((hdiff.continuous.comp (hcurvecont w₀)).intervalIntegrable 0 1)
    ((hcont'.comp (hcurvecont w₀)).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun t _ x _ => htranslate t x)

end AverageOperator

end RHTower

namespace RHTower

section AverageC1

open ContinuousAlternatingMap

variable {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The average is differentiable. -/
theorem deningerAverageOp_differentiable {β : (Fin r → ℂ) → X} (hdiff : Differentiable ℂ β)
    (hcont' : Continuous (fderiv ℂ β)) (j : Fin r) :
    Differentiable ℂ (deningerAverageOp β j) :=
  fun w => (deningerAverageOp_hasFDerivAt hdiff hcont' j w).differentiableAt

omit [CompleteSpace X] in
/-- **The average is continuously differentiable.** -/
theorem deningerAverageOp_fderiv_continuous {β : (Fin r → ℂ) → X} (hdiff : Differentiable ℂ β)
    (hcont' : Continuous (fderiv ℂ β)) (j : Fin r) :
    Continuous (fderiv ℂ (deningerAverageOp β j)) := by
  have hfd : fderiv ℂ (deningerAverageOp β j) =
      fun w => ∫ s in (0 : ℝ)..1, fderiv ℂ β (deningerPeriodCurve w j s) := by
    funext w
    exact (deningerAverageOp_hasFDerivAt hdiff hcont' j w).fderiv
  rw [hfd]
  refine deningerContinuous_parametric_integral ?_
  have hcurve : Continuous fun p : (Fin r → ℂ) × ℝ => deningerPeriodCurve p.1 j p.2 := by
    show Continuous fun p : (Fin r → ℂ) × ℝ =>
      p.1 + ((p.2 : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
    fun_prop
  exact hcont'.comp hcurve

/-- **The average commutes with the exterior derivative.** -/
theorem deningerAverageOp_extDeriv {n : ℕ}
    {β : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ} (hdiff : Differentiable ℂ β)
    (hcont' : Continuous (fderiv ℂ β)) (j : Fin r) (w : Fin r → ℂ) :
    extDeriv (deningerAverageOp β j) w =
      ∫ s in (0 : ℝ)..1, extDeriv β (deningerPeriodCurve w j s) := by
  have hcurvecont : Continuous (deningerPeriodCurve w j) := by
    show Continuous fun s : ℝ =>
      w + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
    fun_prop
  have hcont : Continuous fun s : ℝ => fderiv ℂ β (deningerPeriodCurve w j s) :=
    hcont'.comp hcurvecont
  rw [extDeriv, (deningerAverageOp_hasFDerivAt hdiff hcont' j w).fderiv]
  exact deningerIntegral_comp_comm (alternatizeUncurryFinCLM ℂ (Fin r → ℂ) ℂ (n := n))
    (fun s => fderiv ℂ β (deningerPeriodCurve w j s)) hcont

end AverageC1

end RHTower
