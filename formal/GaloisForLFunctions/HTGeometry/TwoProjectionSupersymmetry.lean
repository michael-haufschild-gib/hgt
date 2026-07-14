import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage

/-!
# The anticommutative Pythagorean theorem for two quantum projections

For idempotents `P,Q`, put `A = P - Q` and `B = 1 - P - Q`.  The exact relations

`A * A + B * B = 1`,

`A * B + B * A = 0`

are the two-projection supersymmetry used in quantum spectral-subspace comparison.  When the
idempotents are self-adjoint bounded operators, the first relation is a master-constraint
partition of the identity.  Every state therefore obeys the exact value law

`‖(P-Q) psi‖^2 + ‖(1-P-Q) psi‖^2 = ‖psi‖^2`.

In particular, both operators are contractions.  This is a static constraint relation; it does
not introduce a flow.
-/

namespace HTGeometry

noncomputable section

section Algebra

variable {R : Type*} [Ring R]

/-- **Anticommutative Pythagorean square law.**  The difference and formal complement of two
idempotents have squares summing exactly to the identity. -/
theorem twoProjection_difference_sq_add_complement_sq
    {P Q : R} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    (P - Q) * (P - Q) + (1 - P - Q) * (1 - P - Q) = 1 := by
  have hPP : P * P = P := hP
  have hQQ : Q * Q = Q := hQ
  noncomm_ring [hPP, hQQ]

/-- **Two-projection supersymmetry.**  The projection difference anticommutes with the formal
complement. -/
theorem twoProjection_difference_anticommutes_complement
    {P Q : R} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    (P - Q) * (1 - P - Q) + (1 - P - Q) * (P - Q) = 0 := by
  have hPP : P * P = P := hP
  have hQQ : Q * Q = Q := hQ
  noncomm_ring [hPP, hQQ]

end Algebra

section HilbertSpace

variable {k E : Type*} [RCLike k]
  [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]

private theorem adjoint_sub_twoProjection
    (S T : E →L[k] E) :
    ContinuousLinearMap.adjoint (S - T) =
      ContinuousLinearMap.adjoint S - ContinuousLinearMap.adjoint T := by
  let adj : (E →L[k] E) ≃ₗᵢ⋆[k] (E →L[k] E) :=
    ContinuousLinearMap.adjoint
  exact adj.map_sub S T

/-- The anticommutative Pythagorean law is exactly a partition of the identity by the two
positive quantum master constraints. -/
theorem quantumMasterConstraint_twoProjection_partition
    (P Q : E →L[k] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hQadj : ContinuousLinearMap.adjoint Q = Q) :
    quantumMasterConstraint (P - Q) +
        quantumMasterConstraint (1 - P - Q) = 1 := by
  have hAadj : ContinuousLinearMap.adjoint (P - Q) = P - Q := by
    rw [adjoint_sub_twoProjection, hPadj, hQadj]
  have hBadj : ContinuousLinearMap.adjoint (1 - P - Q) = 1 - P - Q := by
    rw [adjoint_sub_twoProjection, adjoint_sub_twoProjection,
      ContinuousLinearMap.adjoint_one, hPadj, hQadj]
  simpa only [quantumMasterConstraint, ContinuousLinearMap.mul_def, hAadj, hBadj] using
    (twoProjection_difference_sq_add_complement_sq hP hQ)

/-- **Statewise two-projection value law.**  The difference energy and the formal-complement
energy exhaust the norm of every state, with no commutativity premise on the projections. -/
theorem norm_twoProjection_difference_sq_add_complement_sq
    (P Q : E →L[k] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hQadj : ContinuousLinearMap.adjoint Q = Q) (psi : E) :
    ‖(P - Q) psi‖ ^ 2 + ‖(1 - P - Q) psi‖ ^ 2 = ‖psi‖ ^ 2 := by
  have hmaster := quantumMasterConstraint_twoProjection_partition
    P Q hP hQ hPadj hQadj
  calc
    ‖(P - Q) psi‖ ^ 2 + ‖(1 - P - Q) psi‖ ^ 2 =
        RCLike.re (inner k psi (quantumMasterConstraint (P - Q) psi)) +
          RCLike.re (inner k psi
            (quantumMasterConstraint (1 - P - Q) psi)) := by
      rw [re_inner_quantumMasterConstraint_eq_normSq,
        re_inner_quantumMasterConstraint_eq_normSq]
    _ = RCLike.re (inner k psi
        ((quantumMasterConstraint (P - Q) +
          quantumMasterConstraint (1 - P - Q)) psi)) := by
      simp only [ContinuousLinearMap.add_apply, inner_add_right, map_add]
    _ = RCLike.re (inner k psi psi) := by rw [hmaster]; simp
    _ = ‖psi‖ ^ 2 := inner_self_eq_norm_sq psi

/-- The formal complement `1-P-Q` of two self-adjoint idempotents is a contraction.  This sharp
bound replaces the triangle estimate `1 + ‖P‖ + ‖Q‖`. -/
theorem norm_twoProjection_complement_le_one
    (P Q : E →L[k] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hQadj : ContinuousLinearMap.adjoint Q = Q) :
    ‖1 - P - Q‖ ≤ 1 := by
  apply (1 - P - Q).opNorm_le_bound zero_le_one
  intro psi
  have henergy := norm_twoProjection_difference_sq_add_complement_sq
    P Q hP hQ hPadj hQadj psi
  have hsquares : ‖(1 - P - Q) psi‖ ^ 2 ≤ ‖psi‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(P - Q) psi‖]
  have hnorm : ‖(1 - P - Q) psi‖ ≤ ‖psi‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares
  simpa using hnorm

/-- The difference of two self-adjoint idempotents is also a contraction, by the same exact
energy partition. -/
theorem norm_twoProjection_difference_le_one
    (P Q : E →L[k] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hQadj : ContinuousLinearMap.adjoint Q = Q) :
    ‖P - Q‖ ≤ 1 := by
  apply (P - Q).opNorm_le_bound zero_le_one
  intro psi
  have henergy := norm_twoProjection_difference_sq_add_complement_sq
    P Q hP hQ hPadj hQadj psi
  have hsquares : ‖(P - Q) psi‖ ^ 2 ≤ ‖psi‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(1 - P - Q) psi‖]
  have hnorm : ‖(P - Q) psi‖ ≤ ‖psi‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares
  simpa using hnorm

end HilbertSpace

end

end HTGeometry
