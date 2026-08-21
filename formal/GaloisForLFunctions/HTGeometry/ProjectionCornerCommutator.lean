import GaloisForLFunctions.HTGeometry.CompactAdjoint

/-!
# Projection corners and commutators

For an orthogonal projection `Q` and a self-adjoint bounded operator `A`, the cross-boundary corner
`(1-Q) A Q` and the commutator `[Q, A]` are compact together:

```text
[Q, A] = Q A (1-Q) - (1-Q) A Q,   (1-Q) A Q = -(1-Q) [Q, A] Q,
```

and the two off-diagonal blocks are adjoints of one another, so Schauder's theorem closes the
remaining direction.  Corner compactness therefore transfers along every algebraic operation that
preserves compactness of the commutator:

* `[Q, A⁻¹] = -A⁻¹ [Q, A] A⁻¹`, so the `A` and `A⁻¹` corners are compact together;
* `[Q, C·D] = [Q,C]·D + C·[Q,D]`, so a compact `C`-corner forces a compact `C²`-corner.

In particular a *noncompact* corner for `A` propagates to `A⁻¹`, and rules out a compact corner for
any square root of `A`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The lower cross-boundary corner `(1-Q) A Q`. -/
def crossCorner (Q A : H →L[ℂ] H) : H →L[ℂ] H := (1 - Q) * A * Q

/-- The upper cross-boundary corner `Q A (1-Q)`. -/
def upperCorner (Q A : H →L[ℂ] H) : H →L[ℂ] H := Q * A * (1 - Q)

/-- The commutator `[Q, A]`. -/
def projCommutator (Q A : H →L[ℂ] H) : H →L[ℂ] H := Q * A - A * Q

omit [CompleteSpace H] in
/-- The commutator of a projection with an operator is the difference of the two cross corners. -/
theorem projCommutator_eq_corners (Q A : H →L[ℂ] H) :
    projCommutator Q A = upperCorner Q A - crossCorner Q A := by
  unfold projCommutator upperCorner crossCorner
  noncomm_ring

omit [CompleteSpace H] in
/-- The lower cross corner is a two-sided compression of the commutator. -/
theorem crossCorner_eq_neg_compression {Q A : H →L[ℂ] H} (hQ : Q * Q = Q) :
    crossCorner Q A = -((1 - Q) * projCommutator Q A * Q) := by
  unfold crossCorner projCommutator
  have h : -((1 - Q) * (Q * A - A * Q) * Q)
      = (1 - Q) * A * Q - (Q - Q * Q) * A * Q + (1 - Q) * A * (Q * Q - Q) := by
    noncomm_ring
  rw [h, hQ]
  simp

omit [CompleteSpace H] in
/-- A compact commutator gives a compact corner. -/
theorem isCompactOperator_crossCorner_of_commutator {Q A : H →L[ℂ] H} (hQ : Q * Q = Q)
    (h : IsCompactOperator (projCommutator Q A)) :
    IsCompactOperator (crossCorner Q A) := by
  rw [crossCorner_eq_neg_compression hQ]
  exact ((h.clm_comp (1 - Q)).comp_clm Q).neg

/-- The upper cross corner is the adjoint of the lower one. -/
theorem upperCorner_eq_adjoint {Q A : H →L[ℂ] H} (hQ : IsSelfAdjoint Q) (hA : IsSelfAdjoint A) :
    upperCorner Q A = ContinuousLinearMap.adjoint (crossCorner Q A) := by
  have hstar : star (crossCorner Q A) = upperCorner Q A := by
    unfold crossCorner upperCorner
    rw [star_mul, star_mul, hQ.star_eq, hA.star_eq, star_sub, star_one, hQ.star_eq]
    noncomm_ring
  exact hstar.symm

/-- A compact corner gives a compact commutator (Schauder). -/
theorem isCompactOperator_commutator_of_crossCorner {Q A : H →L[ℂ] H}
    (hQsa : IsSelfAdjoint Q) (hAsa : IsSelfAdjoint A)
    (h : IsCompactOperator (crossCorner Q A)) :
    IsCompactOperator (projCommutator Q A) := by
  rw [projCommutator_eq_corners, upperCorner_eq_adjoint hQsa hAsa]
  exact (isCompactOperator_adjoint_rectangular _ h).sub h

/-- **Item 1.**  Corner and commutator are compact together. -/
theorem isCompactOperator_crossCorner_iff {Q A : H →L[ℂ] H} (hQ : Q * Q = Q)
    (hQsa : IsSelfAdjoint Q) (hAsa : IsSelfAdjoint A) :
    IsCompactOperator (crossCorner Q A) ↔ IsCompactOperator (projCommutator Q A) :=
  ⟨isCompactOperator_commutator_of_crossCorner hQsa hAsa,
    isCompactOperator_crossCorner_of_commutator hQ⟩

omit [CompleteSpace H] in
/-- **Item 2, the identity.**  `[Q, A⁻¹] = -A⁻¹ [Q, A] A⁻¹`. -/
theorem projCommutator_inv {Q A B : H →L[ℂ] H} (hAB : A * B = 1) (hBA : B * A = 1) :
    projCommutator Q B = -(B * projCommutator Q A * B) := by
  unfold projCommutator
  have h : -(B * (Q * A - A * Q) * B)
      = (B * A) * Q * B - B * Q * (A * B) := by
    noncomm_ring
  rw [h, hAB, hBA]
  noncomm_ring

omit [CompleteSpace H] in
/-- **Item 2.**  The `A` and `A⁻¹` commutators are compact together. -/
theorem isCompactOperator_projCommutator_inv_iff {Q A B : H →L[ℂ] H}
    (hAB : A * B = 1) (hBA : B * A = 1) :
    IsCompactOperator (projCommutator Q B) ↔ IsCompactOperator (projCommutator Q A) := by
  constructor
  · intro h
    rw [projCommutator_inv hBA hAB]
    exact ((h.clm_comp A).comp_clm A).neg
  · intro h
    rw [projCommutator_inv hAB hBA]
    exact ((h.clm_comp B).comp_clm B).neg

omit [CompleteSpace H] in
/-- The commutator is a derivation. -/
theorem projCommutator_mul (Q C D : H →L[ℂ] H) :
    projCommutator Q (C * D) = projCommutator Q C * D + C * projCommutator Q D := by
  unfold projCommutator
  noncomm_ring

omit [CompleteSpace H] in
/-- **Item 3.**  A compact commutator for a square root gives a compact commutator for the
square. -/
theorem isCompactOperator_projCommutator_sq {Q C : H →L[ℂ] H}
    (h : IsCompactOperator (projCommutator Q C)) :
    IsCompactOperator (projCommutator Q (C * C)) := by
  rw [projCommutator_mul]
  exact (h.comp_clm C).add (h.clm_comp C)

/-- **Items 3 and 4, corner form.**  If the corner of a square root is compact, so is the corner of
its square. -/
theorem isCompactOperator_crossCorner_sq {Q C : H →L[ℂ] H} (hQ : Q * Q = Q)
    (hQsa : IsSelfAdjoint Q) (hCsa : IsSelfAdjoint C)
    (h : IsCompactOperator (crossCorner Q C)) :
    IsCompactOperator (crossCorner Q (C * C)) :=
  isCompactOperator_crossCorner_of_commutator hQ
    (isCompactOperator_projCommutator_sq
      (isCompactOperator_commutator_of_crossCorner hQsa hCsa h))

/-- **The propagation theorem for the inverse.**  A noncompact corner for `A` forces a noncompact
corner for its inverse. -/
theorem not_isCompactOperator_crossCorner_inv {Q A B : H →L[ℂ] H} (hQ : Q * Q = Q)
    (hQsa : IsSelfAdjoint Q) (hBsa : IsSelfAdjoint B)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (h : ¬ IsCompactOperator (crossCorner Q A)) :
    ¬ IsCompactOperator (crossCorner Q B) := by
  intro hB
  exact h (isCompactOperator_crossCorner_of_commutator hQ
    ((isCompactOperator_projCommutator_inv_iff hAB hBA).1
      (isCompactOperator_commutator_of_crossCorner hQsa hBsa hB)))

/-- **The propagation theorem for square roots.**  A noncompact corner for `C * C` forces a
noncompact corner for `C`. -/
theorem not_isCompactOperator_crossCorner_sqrt {Q C : H →L[ℂ] H} (hQ : Q * Q = Q)
    (hQsa : IsSelfAdjoint Q) (hCsa : IsSelfAdjoint C)
    (h : ¬ IsCompactOperator (crossCorner Q (C * C))) :
    ¬ IsCompactOperator (crossCorner Q C) := by
  intro hC
  exact h (isCompactOperator_crossCorner_sq hQ hQsa hCsa hC)


/-! ## Transport along a bounded isomorphism of the two ranges

If `θ` is boundedly invertible and carries the range of `Q` onto the range of `P`, then the
rectangular corner `(1-P) θ A Q` is compact exactly when `(1-Q) A Q` is.  Only the two
range-containment identities are used, so no analytic input enters. -/

/-- The rectangular corner `(1-P) A Q` between two projections. -/
def mixedCorner (P Q A : H →L[ℂ] H) : H →L[ℂ] H := (1 - P) * A * Q

omit [CompleteSpace H] in
/-- If `θ` carries `ran Q` into `ran P`, the transported rectangular corner is the image of the
square corner. -/
theorem mixedCorner_eq_comp {P Q θ A : H →L[ℂ] H} (hθQ : P * (θ * Q) = θ * Q) :
    mixedCorner P Q (θ * A) = (1 - P) * θ * crossCorner Q A := by
  have hzero : (1 - P) * (θ * Q) = 0 := by rw [sub_mul, one_mul, hθQ, sub_self]
  have hdiff : mixedCorner P Q (θ * A) - (1 - P) * θ * crossCorner Q A
      = ((1 - P) * (θ * Q)) * (A * Q) := by
    unfold mixedCorner crossCorner
    noncomm_ring
  rw [hzero, zero_mul] at hdiff
  exact sub_eq_zero.mp hdiff

omit [CompleteSpace H] in
/-- If `θ'` carries `ran P` into `ran Q` and inverts `θ` on the left, the square corner is the image
of the transported rectangular corner. -/
theorem crossCorner_eq_comp {P Q θ θ' A : H →L[ℂ] H} (hθ'P : Q * (θ' * P) = θ' * P)
    (hinv : θ' * θ = 1) :
    crossCorner Q A = (1 - Q) * θ' * mixedCorner P Q (θ * A) := by
  have hzero : (1 - Q) * (θ' * P) = 0 := by rw [sub_mul, one_mul, hθ'P, sub_self]
  have hstep : (1 - Q) * ((θ' * θ) * A) * Q - (1 - Q) * θ' * mixedCorner P Q (θ * A)
      = ((1 - Q) * (θ' * P)) * (θ * A * Q) := by
    unfold mixedCorner
    noncomm_ring
  rw [hzero, zero_mul, sub_eq_zero] at hstep
  rw [crossCorner, ← hstep, hinv]
  noncomm_ring

omit [CompleteSpace H] in
/-- **Transport of corner compactness along a range isomorphism.** -/
theorem isCompactOperator_mixedCorner_iff {P Q θ θ' A : H →L[ℂ] H}
    (hθQ : P * (θ * Q) = θ * Q) (hθ'P : Q * (θ' * P) = θ' * P) (hinv : θ' * θ = 1) :
    IsCompactOperator (mixedCorner P Q (θ * A)) ↔ IsCompactOperator (crossCorner Q A) := by
  constructor
  · intro h
    rw [crossCorner_eq_comp hθ'P hinv]
    exact h.clm_comp ((1 - Q) * θ')
  · intro h
    rw [mixedCorner_eq_comp hθQ]
    exact h.clm_comp ((1 - P) * θ)

end

end GaloisForLFunctions.HTGeometry

