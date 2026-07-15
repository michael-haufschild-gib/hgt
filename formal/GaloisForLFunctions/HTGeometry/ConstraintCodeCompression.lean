import GaloisForLFunctions.HTGeometry.FiniteClockOrthogonalObservability

/-!
# Constraint ideals compressed to a physical code subspace

If a projection-like operator `P` is annihilated on both sides by a constraint `C`, then every
operator in the two-sided constraint ideal has zero `P`-compression.  Consequently observables
which differ by a constraint-ideal term have identical compressed representatives.

For a finite-period isometric clock, the cyclic gauge average supplies `P`.  The left and right
annihilation laws follow from the two geometric-series telescopes, so matrix-element representative
independence no longer requires the clock constraint `U - 1` itself to be self-adjoint.

This is the static operator identity underlying code-subspace observability and constraint
reduction.  It is not a dynamical error-correction procedure.
-/

namespace HTGeometry

noncomputable section

section Algebra

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every two-sided constraint-ideal term vanishes after compression by an operator annihilating
the constraint on both sides. -/
theorem constraintTwoSidedIdeal_compression_eq_zero
    (P C L R : E →L[𝕜] E) (hPC : P * C = 0) (hCP : C * P = 0) :
    P * (C * L + R * C) * P = 0 := by
  calc
    P * (C * L + R * C) * P =
        (P * C) * L * P + P * R * (C * P) := by noncomm_ring
    _ = 0 := by rw [hPC, hCP]; simp

/-- Operators equal modulo the two-sided constraint ideal have exactly the same compressed
operator, not merely the same value on one chosen pair of physical vectors. -/
theorem compression_congr_mod_constraintTwoSidedIdeal
    (P C A B L R : E →L[𝕜] E)
    (hPC : P * C = 0) (hCP : C * P = 0)
    (hmod : B = A + (C * L + R * C)) :
    P * B * P = P * A * P := by
  rw [hmod]
  have hzero := constraintTwoSidedIdeal_compression_eq_zero P C L R hPC hCP
  calc
    P * (A + (C * L + R * C)) * P =
        P * A * P + P * (C * L + R * C) * P := by noncomm_ring
    _ = P * A * P := by rw [hzero, add_zero]

/-- The finite cyclic gauge average is annihilated on the left by its clock constraint. -/
theorem constraint_mul_finiteCyclicGaugeAverage_eq_zero
    (U : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) :
    (U - 1) * finiteCyclicGaugeAverage U N = 0 := by
  rw [finiteCyclicGaugeAverage, mul_smul_comm,
    finiteCyclicGaugeSum_telescope, hperiod, sub_self, smul_zero]

/-- The right geometric telescope gives the missing opposite annihilation law. -/
theorem finiteCyclicGaugeAverage_mul_constraint_eq_zero
    (U : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1) :
    finiteCyclicGaugeAverage U N * (U - 1) = 0 := by
  rw [finiteCyclicGaugeAverage, smul_mul_assoc]
  change ((N : 𝕜)⁻¹) •
    ((∑ k ∈ Finset.range N, U ^ k) * (U - 1)) = 0
  rw [geom_sum_mul, hperiod, sub_self, smul_zero]

/-- Constraint-ideal equivalence becomes literal operator equality after finite-clock averaging.
No self-adjointness premise on `U - 1` is needed. -/
theorem finiteCyclicGaugeAverage_compression_congr_mod_constraintTwoSidedIdeal
    (U A B L R : E →L[𝕜] E) (N : ℕ) (hperiod : U ^ N = 1)
    (hmod : B = A + ((U - 1) * L + R * (U - 1))) :
    finiteCyclicGaugeAverage U N * B * finiteCyclicGaugeAverage U N =
      finiteCyclicGaugeAverage U N * A * finiteCyclicGaugeAverage U N := by
  exact compression_congr_mod_constraintTwoSidedIdeal
    (finiteCyclicGaugeAverage U N) (U - 1) A B L R
    (finiteCyclicGaugeAverage_mul_constraint_eq_zero U N hperiod)
    (constraint_mul_finiteCyclicGaugeAverage_eq_zero U N hperiod) hmod

end Algebra

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Finite-clock physical code representative independence.**  Averaging the bra and ket by a
finite-period isometric clock makes every two-sided constraint-ideal representative invisible.
Unlike the earlier generic Ward theorem, this result does not assume `IsSelfAdjoint (U - 1)`. -/
theorem finiteClock_matrixElement_congr_mod_constraintTwoSidedIdeal
    (U A B L R : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    (hmod : B = A + ((U - 1) * L + R * (U - 1))) (φ ψ : E) :
    inner 𝕜 (finiteCyclicGaugeAverage U N φ)
        (B (finiteCyclicGaugeAverage U N ψ)) =
      inner 𝕜 (finiteCyclicGaugeAverage U N φ)
        (A (finiteCyclicGaugeAverage U N ψ)) := by
  let P : E →L[𝕜] E := finiteCyclicGaugeAverage U N
  have hPadj : P.adjoint = P := by
    simpa only [P, ContinuousLinearMap.star_eq_adjoint] using
      (finiteCyclicGaugeAverage_isSelfAdjoint_of_periodic_isometry
        U N hN hadjoint_mul hperiod).star_eq
  have hcompress : P * B * P = P * A * P :=
    finiteCyclicGaugeAverage_compression_congr_mod_constraintTwoSidedIdeal
      U A B L R N hperiod hmod
  calc
    inner 𝕜 (P φ) (B (P ψ)) = inner 𝕜 φ (P.adjoint (B (P ψ))) :=
      (P.adjoint_inner_right φ (B (P ψ))).symm
    _ = inner 𝕜 φ (P (B (P ψ))) := by rw [hPadj]
    _ = inner 𝕜 φ ((P * B * P) ψ) := by
      simp only [ContinuousLinearMap.mul_apply]
    _ = inner 𝕜 φ ((P * A * P) ψ) := by rw [hcompress]
    _ = inner 𝕜 φ (P (A (P ψ))) := by
      simp only [ContinuousLinearMap.mul_apply]
    _ = inner 𝕜 (P φ) (A (P ψ)) := by
      simpa only [hPadj] using P.adjoint_inner_right φ (A (P ψ))

end Hilbert

end


end HTGeometry
