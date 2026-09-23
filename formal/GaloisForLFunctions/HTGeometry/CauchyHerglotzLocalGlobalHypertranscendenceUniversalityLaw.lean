import GaloisForLFunctions.HTGeometry.RegularizedTransformGauge

/-!
# Cauchy--Herglotz local/global hypertranscendence law

The local polynomial-gauge theorem transports upper-half-plane differential relation-freeness from
a Cauchy transform to every normalized Herglotz presentation.  Since any global algebraic
differential equation restricts to the upper half-plane, both local conclusions are literal global
hypertranscendence statements.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory

noncomputable section

/-- Failure of differential algebraicity on any set already rules out a global algebraic
differential equation. -/
theorem hypertranscendental_of_not_differentiallyAlgebraicOn
    {f : ℂ → ℂ} {U : Set ℂ} (hlocal : ¬ DifferentiallyAlgebraicOn f U) :
    Hypertranscendental f := by
  intro hglobal
  obtain ⟨n, P, hP, hall⟩ := hglobal
  exact hlocal ⟨n, P, hP, fun z _hz => hall z⟩

/-- **Cauchy--Herglotz local/global hypertranscendence universality law.**  For every finite real
measure, upper-half-plane differential relation-freeness of its Cauchy transform forces global
hypertranscendence of that transform and of every normalized Herglotz presentation. -/
theorem cauchyHerglotz_upperHalfPlane_globalHypertranscendence
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hC : ¬ DifferentiallyAlgebraicOn (cauchyTransform ν) upperHalfPlane) :
    Hypertranscendental (cauchyTransform ν) ∧
      ∀ M : ℂ, Hypertranscendental
        (fun z => z * M + (1 + z ^ (2 : ℕ)) * cauchyTransform ν z) := by
  refine ⟨hypertranscendental_of_not_differentiallyAlgebraicOn hC, ?_⟩
  intro M
  exact hypertranscendental_of_not_differentiallyAlgebraicOn
    (not_differentiallyAlgebraicOn_herglotzPresentation_upperHalfPlane ν M hC)

/-- **Lower-half-plane form of the Cauchy--Herglotz local/global law.**  The noncritical
projective row packets are placed in the lower half-plane, so relation-freeness there is the
hypothesis the packet argument supplies; the conclusion is the same global hypertranscendence. -/
theorem cauchyHerglotz_lowerHalfPlane_globalHypertranscendence
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hC : ¬ DifferentiallyAlgebraicOn (cauchyTransform ν) lowerHalfPlane) :
    Hypertranscendental (cauchyTransform ν) ∧
      ∀ M : ℂ, Hypertranscendental
        (fun z => z * M + (1 + z ^ (2 : ℕ)) * cauchyTransform ν z) := by
  refine ⟨hypertranscendental_of_not_differentiallyAlgebraicOn hC, ?_⟩
  intro M
  exact hypertranscendental_of_not_differentiallyAlgebraicOn
    (not_differentiallyAlgebraicOn_herglotzPresentation ν M isOpen_lowerHalfPlane
      (fun _ hz => im_ne_zero_of_mem_lowerHalfPlane hz) hC)

end

end GaloisForLFunctions.HTGeometry
