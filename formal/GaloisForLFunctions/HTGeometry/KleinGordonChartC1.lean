import GaloisForLFunctions.HTGeometry.KleinGordonFlowJointContinuity
import GaloisForLFunctions.HTGeometry.ClockPiPartialC1
import GaloisForLFunctions.HTGeometry.ConformalMetricDalembertian

/-!
# The chart field has continuous partial derivatives

Each partial derivative of the chart field is the real part of a synthesis: the time partial
synthesises the time derivative of the frequency data, and a spatial partial synthesises the derived
density. Both families are dominated by the weight, uniformly on time intervals, so both syntheses
are continuous in the event — and therefore the chart field satisfies the corpus's condition for
being differentiable with the expected differential.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

variable (a : WienerFamily E N) (G₀ : E →ᵇ ℂ)

/-! ## The two syntheses are continuous in the event -/

theorem norm_kgFlowDensity_le_weight {T : ℝ} {t : ℝ} (ht : |t| ≤ T) (ξ : E) :
    ‖kgFlowDensity a G₀ t ξ‖ ≤ (kgFreq ξ ^ N)⁻¹ * kgFlowSize a G₀ T := by
  have hbound := norm_kgWeighted_le N (kgPotentialFlow a G₀ t) ξ
  have hflow : ‖kgPotentialFlow a G₀ t‖ ≤ kgFlowSize a G₀ T :=
    (norm_kgPotentialFlow_le a G₀ t).trans (kgFlowSize_mono a G₀ ht)
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_left hflow (inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le)

/-- **The synthesis of the time derivative is continuous in the event.** -/
theorem continuous_kgSynthesis_flowDensityDeriv (hN : (Module.finrank ℝ E : ℝ) + 2 < N) :
    Continuous fun p : ℝ × E => kgSynthesis (kgFlowDensityDeriv a G₀ p.1) p.2 := by
  have hdim : (Module.finrank ℝ E : ℝ) < N := by linarith
  refine continuous_kgSynthesis_param (N := N) hdim
    (continuous_kgFlowDensityDeriv_freq a G₀) (continuous_kgFlowDensityDeriv_time a G₀) ?_
  intro T
  refine ⟨‖G₀‖ + 2 * (kgFlowBoundConst a * kgFlowSize a G₀ T * T), fun t ht ξ => ?_⟩
  rw [norm_kgFlowDensityDeriv]
  exact mul_le_mul_of_nonneg_left (norm_deriv_kgPotentialFlow_apply_le_of_abs_le a G₀ ξ ht)
    (inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le)

/-- **The synthesis of a derived density is continuous in the event.** -/
theorem continuous_kgSynthesis_dirDensity (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (v : E) :
    Continuous fun p : ℝ × E => kgSynthesis (kgDirDensity v (kgFlowDensity a G₀ p.1)) p.2 := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := by
    have hpos : 0 < N := by
      have h0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) < N := by linarith
      exact_mod_cast this
    exact ⟨N - 1, by omega⟩
  have hdimM : (Module.finrank ℝ E : ℝ) < M := by
    push_cast at hN
    linarith
  refine continuous_kgSynthesis_param (N := M) hdimM
    (fun t => continuous_kgDirDensity (continuous_kgFlowDensity a G₀ t) v) ?_ ?_
  · intro ξ
    exact continuous_kgDirDensity_time v ξ (continuous_kgFlowDensity_time a G₀ ξ)
  · intro T
    refine ⟨2 * Real.pi * ‖v‖ * kgFlowSize a G₀ T, fun t ht ξ => ?_⟩
    exact norm_kgDirDensity_le_weight (N := M) v
      (fun ζ => norm_kgFlowDensity_le_weight a G₀ ht ζ) ξ

/-! ## The chart partials -/

section Chart

variable {d : ℕ} (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
  (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)

theorem continuous_kgSpatial (d : ℕ) : Continuous (kgSpatial d) := by
  have hcoord : Continuous fun y : Fin (d + 1) → ℝ => fun i : Fin d => y i.succ :=
    continuous_pi fun i => continuous_apply i.succ
  exact ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp hcoord).const_smul
    ((2 * Real.pi)⁻¹ : ℝ)

theorem continuous_chartPoint (d : ℕ) :
    Continuous fun y : Fin (d + 1) → ℝ => ((y 0, kgSpatial d y) :
      ℝ × EuclideanSpace ℝ (Fin d)) :=
  (continuous_apply 0).prodMk (continuous_kgSpatial d)

theorem kgChartTimePartial_eq
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (y : Fin (d + 1) → ℝ) :
    kgChartTimePartial a G₀ y
      = (kgSynthesis (kgFlowDensityDeriv a G₀ (y 0)) (kgSpatial d y)).re := by
  show deriv (fun r : ℝ => (kgFlowField a G₀ r (kgSpatial d y)).re) (y 0) = _
  rw [deriv_re_eq (fun t => differentiableAt_kgFlowField_time a G₀ hN (kgSpatial d y) t) (y 0),
    (hasDerivAt_kgFlowField hN a G₀ (kgSpatial d y) (y 0)).deriv]
  rfl

theorem kgChartSpacePartial_eq
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (i : Fin d)
    (y : Fin (d + 1) → ℝ) :
    kgChartSpacePartial a G₀ i y
      = (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
          (kgFlowDensity a G₀ (y 0))) (kgSpatial d y)).re := by
  show deriv (fun s : ℝ => (kgFlowField a G₀ (y 0)
      (kgSpatial d y + s • ((2 * Real.pi)⁻¹ • kgDir d i))).re) 0 = _
  rw [deriv_re_eq (fun s => differentiableAt_kgFlowField_dir a G₀ hN (y 0) (kgSpatial d y)
      ((2 * Real.pi)⁻¹ • kgDir d i) s) 0,
    deriv_kgFlowField_dir_eq a G₀ hN (y 0) (kgSpatial d y) ((2 * Real.pi)⁻¹ • kgDir d i) 0]
  simp

theorem continuous_kgChartTimePartial
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) :
    Continuous (kgChartTimePartial a G₀) := by
  have hfun : kgChartTimePartial a G₀
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
          (kgSynthesis (kgFlowDensityDeriv a G₀ p.1) p.2).re)
        ∘ (fun y : Fin (d + 1) → ℝ => (y 0, kgSpatial d y)) := by
    funext y
    exact kgChartTimePartial_eq a G₀ hN y
  rw [hfun]
  exact (Complex.continuous_re.comp (continuous_kgSynthesis_flowDensityDeriv a G₀ hN)).comp
    (continuous_chartPoint d)

theorem continuous_kgChartSpacePartial
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (i : Fin d) :
    Continuous (kgChartSpacePartial a G₀ i) := by
  have hfun : kgChartSpacePartial a G₀ i
      = (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
          (kgSynthesis (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
            (kgFlowDensity a G₀ p.1)) p.2).re)
        ∘ (fun y : Fin (d + 1) → ℝ => (y 0, kgSpatial d y)) := by
    funext y
    exact kgChartSpacePartial_eq a G₀ hN i y
  rw [hfun]
  exact (Complex.continuous_re.comp
    (continuous_kgSynthesis_dirDensity a G₀ hN ((2 * Real.pi)⁻¹ • kgDir d i))).comp
    (continuous_chartPoint d)

/-- **Every chart partial is continuous.** -/
theorem continuous_kgChartPartial
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (j : Fin (d + 1)) :
    Continuous (kgChartPartial a G₀ j) := by
  refine Fin.cases ?_ ?_ j
  · rw [kgChartPartial_zero]
    exact continuous_kgChartTimePartial a G₀ hN
  · intro i
    rw [kgChartPartial_succ]
    exact continuous_kgChartSpacePartial a G₀ hN i

/-! ## The chart field is differentiable -/

/-- **The chart field has continuous partial derivatives everywhere.** -/
theorem isC1OnPi_kgChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) :
    IsC1OnPi (kgChartField a G₀) (kgChartPartial a G₀) Set.univ where
  isOpen := isOpen_univ
  hasDeriv := fun y _ j => hasDerivAt_kgChartField_update hN a G₀ y j
  cont := fun j => continuous_kgChartPartial a G₀ hN j

/-- **Hence it is differentiable, with the expected differential.** -/
theorem hasFDerivAt_kgChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (y : Fin (d + 1) → ℝ) :
    HasFDerivAt (kgChartField a G₀) (piToCLM fun j => kgChartPartial a G₀ j y) y :=
  hasFDerivAt_of_isC1OnPi (d + 1) (kgChartField a G₀) (kgChartPartial a G₀) Set.univ
    (isC1OnPi_kgChartField a G₀ hN) y (Set.mem_univ y)

/-- **And its coordinate partials are the computed ones.** -/
theorem coordPartial_kgChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (j : Fin (d + 1))
    (y : Fin (d + 1) → ℝ) :
    coordPartial j (kgChartField a G₀) y = kgChartPartial a G₀ j y := by
  rw [coordPartial, (hasFDerivAt_kgChartField a G₀ hN y).fderiv, piToCLM_single]

end Chart

end GaloisForLFunctions.HTGeometry
