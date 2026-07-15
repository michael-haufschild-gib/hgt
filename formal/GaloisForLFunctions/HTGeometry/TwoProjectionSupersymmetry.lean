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

/-- The formal complement of two idempotents is itself idempotent exactly when their Jordan
overlap vanishes.  This is the ring-level sharpness criterion for the complement of two quantum
effects. -/
theorem twoProjection_complement_isIdempotentElem_iff_anticommutator_eq_zero
    {P Q : R} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    IsIdempotentElem (1 - P - Q) ↔ P * Q + Q * P = 0 := by
  have hPP : P * P = P := hP
  have hQQ : Q * Q = Q := hQ
  constructor
  · intro hB
    have hBB : (1 - P - Q) * (1 - P - Q) = 1 - P - Q := hB
    noncomm_ring [hPP, hQQ, hBB]
  · intro hanti
    show (1 - P - Q) * (1 - P - Q) = 1 - P - Q
    noncomm_ring [hPP, hQQ, hanti]

/-- **Zero-mode-subtracted two-projection partition.**  Suppose `Z` is an idempotent annihilated
on both sides by the two idempotents `P,Q`.  Replacing the formal complement `1-P-Q` by its
`Z`-corrected version `Z-(1-P-Q)` removes exactly the `Z` zero-mode energy:

`(P-Q)^2 + (Z-(1-P-Q))^2 = 1-Z`.

This is the algebraic form needed when `Z` projects onto the common kernel of two quantum
constraints. -/
theorem twoProjection_difference_sq_add_corrected_complement_sq
    {P Q Z : R} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hZ : IsIdempotentElem Z)
    (hPZ : P * Z = 0) (hZP : Z * P = 0)
    (hQZ : Q * Z = 0) (hZQ : Z * Q = 0) :
    (P - Q) * (P - Q) +
        (Z - (1 - P - Q)) * (Z - (1 - P - Q)) = 1 - Z := by
  have hPP : P * P = P := hP
  have hQQ : Q * Q = Q := hQ
  have hZZ : Z * Z = Z := hZ
  noncomm_ring [hPP, hQQ, hZZ, hPZ, hZP, hQZ, hZQ]

/-- The zero-mode-corrected complement remains the supersymmetric partner of the projection
difference: removing a joint zero-mode does not change the anticommutation law. -/
theorem twoProjection_difference_anticommutes_corrected_complement
    {P Q Z : R} (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPZ : P * Z = 0) (hZP : Z * P = 0)
    (hQZ : Q * Z = 0) (hZQ : Z * Q = 0) :
    (P - Q) * (Z - (1 - P - Q)) +
        (Z - (1 - P - Q)) * (P - Q) = 0 := by
  have hPP : P * P = P := hP
  have hQQ : Q * Q = Q := hQ
  noncomm_ring [hPP, hQQ, hPZ, hZP, hQZ, hZQ]

end Algebra

section HilbertSpace

variable {k E : Type*} [RCLike k]
  [NormedAddCommGroup E] [InnerProductSpace k E] [CompleteSpace E]

/-- Two self-adjoint idempotents have zero anticommutator exactly when their ranges are
orthogonal.  Equivalently, a pair of sharp quantum effects has no Jordan overlap exactly when
one ordered transition channel vanishes. -/
theorem twoProjection_anticommutator_eq_zero_iff_mul_eq_zero
    (P Q : E →L[k] E) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hQadj : ContinuousLinearMap.adjoint Q = Q) :
    P * Q + Q * P = 0 ↔ Q * P = 0 := by
  have hPP : P * P = P := hP
  have hQQ : Q * Q = Q := hQ
  constructor
  · intro hanti
    have hcompress := congrArg (fun T : E →L[k] E => P * T * P) hanti
    have htwice : P * Q * P + P * Q * P = 0 := by
      simpa [mul_add, add_mul, ← mul_assoc, hPP] using hcompress
    have hPQP : P * Q * P = 0 := add_self_eq_zero.mp htwice
    let T : E →L[k] E := Q * P
    have hTadj : ContinuousLinearMap.adjoint T = P * Q := by
      change ContinuousLinearMap.adjoint (Q ∘L P) = P ∘L Q
      rw [ContinuousLinearMap.adjoint_comp, hPadj, hQadj]
    have hmaster : quantumMasterConstraint T = 0 := by
      rw [quantumMasterConstraint, hTadj]
      change (P * Q) * (Q * P) = 0
      calc
        (P * Q) * (Q * P) = P * (Q * Q) * P := by
          simp only [mul_assoc]
        _ = P * Q * P := by rw [hQQ]
        _ = 0 := hPQP
    exact (quantumMasterConstraint_eq_zero_iff T).mp hmaster
  · intro hQP
    have hPQ : P * Q = 0 := by
      have h := congrArg ContinuousLinearMap.adjoint hQP
      change ContinuousLinearMap.adjoint (Q ∘L P) =
        ContinuousLinearMap.adjoint 0 at h
      simpa [ContinuousLinearMap.adjoint_comp, hPadj, hQadj] using h
    simp [hPQ, hQP]

/-- Nonzero Jordan overlap and nonzero transition amplitude are therefore equivalent for sharp
quantum effects. -/
theorem twoProjection_anticommutator_ne_zero_iff_mul_ne_zero
    (P Q : E →L[k] E) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hQadj : ContinuousLinearMap.adjoint Q = Q) :
    P * Q + Q * P ≠ 0 ↔ Q * P ≠ 0 :=
  not_congr
    (twoProjection_anticommutator_eq_zero_iff_mul_eq_zero P Q hP hQ hPadj hQadj)

/-- For sharp effects on a Hilbert space, the formal complement is sharp exactly when there is
no transition amplitude between the two effects. -/
theorem twoProjection_complement_isIdempotentElem_iff_mul_eq_zero
    (P Q : E →L[k] E) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hQadj : ContinuousLinearMap.adjoint Q = Q) :
    IsIdempotentElem (1 - P - Q) ↔ Q * P = 0 := by
  rw [twoProjection_complement_isIdempotentElem_iff_anticommutator_eq_zero hP hQ,
    twoProjection_anticommutator_eq_zero_iff_mul_eq_zero P Q hP hQ hPadj hQadj]

/-- Equivalently, any nonzero sharp-effect transition forces the formal complement to remain an
unsharp contraction rather than a projection. -/
theorem twoProjection_complement_not_isIdempotentElem_iff_mul_ne_zero
    (P Q : E →L[k] E) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hQadj : ContinuousLinearMap.adjoint Q = Q) :
    (¬ IsIdempotentElem (1 - P - Q)) ↔ Q * P ≠ 0 :=
  not_congr
    (twoProjection_complement_isIdempotentElem_iff_mul_eq_zero
      P Q hP hQ hPadj hQadj)

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

/-- **Active-space energy conservation.**  If `Z` is the orthogonal projection onto a joint
zero-mode sector for the orthogonal projections `P,Q`, then the projection mismatch and the
zero-mode-corrected complement exhaust exactly the norm outside `Z`:

`||(P-Q) psi||^2 + ||(Z-(1-P-Q)) psi||^2 = ||(1-Z) psi||^2`.

The identity is the statewise value form of the zero-mode-subtracted supersymmetric partition. -/
theorem norm_twoProjection_difference_sq_add_corrected_complement_sq
    (P Q Z : E →L[k] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hZ : IsIdempotentElem Z)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hQadj : ContinuousLinearMap.adjoint Q = Q)
    (hZadj : ContinuousLinearMap.adjoint Z = Z)
    (hPZ : P * Z = 0) (hZP : Z * P = 0)
    (hQZ : Q * Z = 0) (hZQ : Z * Q = 0) (psi : E) :
    ‖(P - Q) psi‖ ^ 2 + ‖(Z - (1 - P - Q)) psi‖ ^ 2 =
      ‖(1 - Z) psi‖ ^ 2 := by
  have hAadj : ContinuousLinearMap.adjoint (P - Q) = P - Q := by
    rw [adjoint_sub_twoProjection, hPadj, hQadj]
  have hBadj : ContinuousLinearMap.adjoint (1 - P - Q) = 1 - P - Q := by
    rw [adjoint_sub_twoProjection, adjoint_sub_twoProjection,
      ContinuousLinearMap.adjoint_one, hPadj, hQadj]
  have hCadj : ContinuousLinearMap.adjoint (Z - (1 - P - Q)) =
      Z - (1 - P - Q) := by
    rw [adjoint_sub_twoProjection, hZadj, hBadj]
  have hpartition :
      quantumMasterConstraint (P - Q) +
          quantumMasterConstraint (Z - (1 - P - Q)) = 1 - Z := by
    simpa only [quantumMasterConstraint, ContinuousLinearMap.mul_def, hAadj, hCadj] using
      (twoProjection_difference_sq_add_corrected_complement_sq
        hP hQ hZ hPZ hZP hQZ hZQ)
  have hIZadj : ContinuousLinearMap.adjoint (1 - Z) = 1 - Z := by
    rw [adjoint_sub_twoProjection, ContinuousLinearMap.adjoint_one, hZadj]
  have hZZ : Z * Z = Z := hZ
  have hIZsq : (1 - Z) * (1 - Z) = 1 - Z := by
    noncomm_ring [hZZ]
  have hIZmaster : quantumMasterConstraint (1 - Z) = 1 - Z := by
    simp only [quantumMasterConstraint, ContinuousLinearMap.mul_def, hIZadj, hIZsq]
  calc
    ‖(P - Q) psi‖ ^ 2 + ‖(Z - (1 - P - Q)) psi‖ ^ 2 =
        RCLike.re (inner k psi (quantumMasterConstraint (P - Q) psi)) +
          RCLike.re (inner k psi
            (quantumMasterConstraint (Z - (1 - P - Q)) psi)) := by
      rw [re_inner_quantumMasterConstraint_eq_normSq,
        re_inner_quantumMasterConstraint_eq_normSq]
    _ = RCLike.re (inner k psi
        ((quantumMasterConstraint (P - Q) +
          quantumMasterConstraint (Z - (1 - P - Q))) psi)) := by
      simp only [ContinuousLinearMap.add_apply, inner_add_right, map_add]
    _ = RCLike.re (inner k psi ((1 - Z) psi)) := by rw [hpartition]
    _ = RCLike.re (inner k psi (quantumMasterConstraint (1 - Z) psi)) := by
      rw [hIZmaster]
    _ = ‖(1 - Z) psi‖ ^ 2 := re_inner_quantumMasterConstraint_eq_normSq (1 - Z) psi

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
