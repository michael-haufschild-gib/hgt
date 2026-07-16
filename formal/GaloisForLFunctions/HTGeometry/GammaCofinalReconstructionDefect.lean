import GaloisForLFunctions.HTGeometry.GammaFactorialObservabilitySpectrum

/-!
# Gamma's cofinal reconstruction defect

The source-normalized Gamma reporter is exactly invertible on every finite clock, with inverse
coefficient `(n + 1)!` in clock direction `n`.  Those coefficients diverge, and the completed
square-summable reporter admits no continuous left inverse.

Thus finite algebraic effectivity and completed analytic effectivity are genuinely different:
every finite reconstruction problem is solved, while reconstruction fails to commute with the
cofinal source completion.  This is the vertical seed for a cofinal-effectivity obstruction theory;
it is not a claim that finite-section instability is new operator theory.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The source-normalized factorial observation on the first `N` clock coordinates. -/
def gammaFactorialFiniteObservation (N : ℕ) (x : Fin N → ℂ) : Fin N → ℂ :=
  fun n => gammaPeriodicConormalCoefficient n * x n

/-- The exact algebraic inverse of the finite Gamma factorial observation. -/
def gammaFactorialFiniteReconstruction (N : ℕ) (y : Fin N → ℂ) : Fin N → ℂ :=
  fun n => (gammaPeriodicConormalCoefficient n)⁻¹ * y n

/-- Finite reconstruction is a left inverse at every resolution. -/
theorem gammaFactorialFiniteReconstruction_leftInverse (N : ℕ) :
    Function.LeftInverse (gammaFactorialFiniteReconstruction N)
      (gammaFactorialFiniteObservation N) := by
  intro x
  funext n
  simp [gammaFactorialFiniteObservation, gammaFactorialFiniteReconstruction,
    gammaPeriodicConormalCoefficient_ne_zero]

/-- Finite reconstruction is also a right inverse at every resolution. -/
theorem gammaFactorialFiniteReconstruction_rightInverse (N : ℕ) :
    Function.RightInverse (gammaFactorialFiniteReconstruction N)
      (gammaFactorialFiniteObservation N) := by
  intro y
  funext n
  simp [gammaFactorialFiniteObservation, gammaFactorialFiniteReconstruction,
    gammaPeriodicConormalCoefficient_ne_zero]

/-- Every finite Gamma factorial observation problem is exactly effective. -/
theorem gammaFactorialFiniteObservation_bijective (N : ℕ) :
    Function.Bijective (gammaFactorialFiniteObservation N) :=
  ⟨(gammaFactorialFiniteReconstruction_leftInverse N).injective,
    (gammaFactorialFiniteReconstruction_rightInverse N).surjective⟩

/-- The inverse coefficient in clock direction `n` is exactly `(n + 1)!`. -/
theorem gammaFactorialFiniteReconstruction_apply (N : ℕ)
    (y : Fin N → ℂ) (n : Fin N) :
    gammaFactorialFiniteReconstruction N y n =
      ((n.val + 1).factorial : ℂ) * y n := by
  simp [gammaFactorialFiniteReconstruction, gammaPeriodicConormalCoefficient]

/-- The exact finite reconstruction amplification diverges factorially along the clock. -/
theorem gammaFactorialFiniteReconstruction_amplification_tendsto_atTop :
    Tendsto (fun n : ℕ => (((n + 1).factorial : ℕ) : ℝ)) atTop atTop := by
  exact ((tendsto_natCast_atTop_atTop (R := ℝ)).comp factorial_tendsto_atTop).comp
    (tendsto_add_atTop_nat 1)

/-- The completed Hilbert reporter is coordinatewise the restriction of the already formalized
raw-stream factorial equivalence.  The strictness jump therefore belongs to the source rigging,
not to a change of algebraic normalization. -/
theorem gammaFactorialObservabilityOperator_eq_streamEquiv_apply
    (x : lp (fun _ : ℕ ↦ ℂ) 2) (n : ℕ) :
    gammaFactorialObservabilityOperator x n =
      gammaFactorialStreamEquiv (fun k => x k) n := by
  simp [gammaFactorialObservabilityOperator_apply, gammaFactorialStreamEquiv]

/-- The completed Gamma reporter is not an independently chosen diagonal: its coefficient in
clock direction `n` is the oriented rank-one curvature exposed between the adjacent finite
translation shadows at levels `n + 1` and `n + 2`.  Hence the completed strictness defect is
forced coordinatewise by the finite source action. -/
theorem gammaFactorialObservabilityOperator_apply_eq_clockCurvature
    (x : lp (fun _ : ℕ ↦ ℂ) 2) (n : ℕ) :
    gammaFactorialObservabilityOperator x n =
      gammaClockCurvature (n + 1) (Pi.single (Fin.last (n + 1)) 1)
          (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) * x n := by
  rw [gammaFactorialObservabilityOperator_apply, gammaClockCurvature_apply]
  simp [gammaPeriodicConormalCoefficient]

/-- The completed Gamma reporter has no bounded reconstruction map, even on its range. -/
theorem gammaFactorialObservabilityOperator_no_continuousLeftInverse :
    ¬ ∃ B : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2,
      Function.LeftInverse B gammaFactorialObservabilityOperator := by
  rintro ⟨B, hB⟩
  apply gammaFactorialObservabilityOperator_not_stablyConservative
  refine ⟨⟨‖B‖, B.opNorm_nonneg⟩, AntilipschitzWith.of_le_mul_dist ?_⟩
  intro x y
  calc
    dist x y = dist (B (gammaFactorialObservabilityOperator x))
        (B (gammaFactorialObservabilityOperator y)) := by rw [hB x, hB y]
    _ ≤ ‖B‖ * dist (gammaFactorialObservabilityOperator x)
        (gammaFactorialObservabilityOperator y) :=
      B.lipschitz.dist_le_mul _ _

/-- The completed reporter has dense range: every finite-support clock observation is attained. -/
theorem gammaFactorialObservabilityOperator_denseRange :
    DenseRange gammaFactorialObservabilityOperator := by
  have hle : Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ)) ≤
      gammaFactorialObservabilityOperator.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    rw [HilbertSchmidt.lpBasis_apply]
    refine ⟨(gammaPeriodicConormalCoefficient n)⁻¹ • lp.single 2 n 1, ?_⟩
    apply lp.ext
    funext j
    change gammaFactorialObservabilityOperator
      ((gammaPeriodicConormalCoefficient n)⁻¹ • lp.single 2 n 1) j =
        (lp.single 2 n (1 : ℂ) : lp (fun _ : ℕ ↦ ℂ) 2) j
    rw [gammaFactorialObservabilityOperator_apply]
    by_cases h : j = n
    · subst j
      simp [gammaPeriodicConormalCoefficient_ne_zero]
    · simp [h]
  apply (Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (HilbertSchmidt.lpBasis ℕ).dense_span).mono
  intro x hx
  rcases hle hx with ⟨y, hy⟩
  exact ⟨y, hy⟩

/-- Dense completed observability is not exact observability: the reporter is not onto. -/
theorem gammaFactorialObservabilityOperator_not_surjective :
    ¬ Function.Surjective gammaFactorialObservabilityOperator := by
  intro hsurj
  apply gammaFactorialObservabilityOperator_not_isClosed_range
  rw [hsurj.range_eq]
  exact isClosed_univ

/-- The same factorial normalization is an algebraic equivalence on raw streams but is not
continuously left-split on the source-rigged square-summable completion. -/
theorem gammaFactorial_rawEquiv_completed_nonsplit :
    Function.Bijective gammaFactorialStreamEquiv ∧
      ¬ ∃ B : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2,
        Function.LeftInverse B gammaFactorialObservabilityOperator := by
  exact ⟨gammaFactorialStreamEquiv.bijective,
    gammaFactorialObservabilityOperator_no_continuousLeftInverse⟩

/-- **Gamma cofinal reconstruction defect.** Every finite source-normalized clock is exactly
reconstructible. The completed reporter has dense proper range and no continuous left inverse. -/
theorem gammaFactorial_finite_effective_completed_nonsplit :
    (∀ N : ℕ, Function.Bijective (gammaFactorialFiniteObservation N)) ∧
      DenseRange gammaFactorialObservabilityOperator ∧
      ¬ Function.Surjective gammaFactorialObservabilityOperator ∧
      ¬ ∃ B : lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2,
        Function.LeftInverse B gammaFactorialObservabilityOperator := by
  exact ⟨gammaFactorialFiniteObservation_bijective,
    gammaFactorialObservabilityOperator_denseRange,
    gammaFactorialObservabilityOperator_not_surjective,
    gammaFactorialObservabilityOperator_no_continuousLeftInverse⟩

end

end GaloisForLFunctions.HTGeometry
