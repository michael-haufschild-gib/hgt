import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianJetDerivatives
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

/-!
# The Schwarzian coordinate system is algebraically independent

Indexed by the natural numbers, the Schwarzian coordinate system is the first three jets of the base
coordinate followed by the jets of the Schwarzian.  Against the coordinate derivations of the same
index the Jacobian is upper triangular: below the diagonal an entry either differentiates a jet
along a different coordinate, or differentiates a Schwarzian jet beyond its reach.  The diagonal is
`1` on the first three entries and `1/x'` afterwards, so the determinant is a unit and the Jacobian
criterion applies.

Every finite subfamily sits inside such a block, so the whole system is algebraically independent.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

/-- The Schwarzian coordinate system indexed by the natural numbers. -/
def schwarzianSystem (C : Type*) [Field C] : ℕ → FreeScalarJetField C := fun m =>
  if m < 3 then freeCoordinate C ℕ m else differentialJet (m - 3) (freeJetSchwarzian C)

omit [CharZero C] in
theorem schwarzianSystem_of_lt {m : ℕ} (hm : m < 3) :
    schwarzianSystem C m = freeCoordinate C ℕ m := if_pos hm

omit [CharZero C] in
theorem schwarzianSystem_of_ge {m : ℕ} (hm : 3 ≤ m) :
    schwarzianSystem C m = differentialJet (m - 3) (freeJetSchwarzian C) :=
  if_neg (by omega)

/-! ## The Jacobian of a finite block -/

/-- The Jacobian of the first `3 + N` Schwarzian coordinates against the coordinate derivations of
the same indices. -/
def schwarzianJacobian (C : Type*) [Field C] (N : ℕ) :
    Matrix (Fin (3 + N)) (Fin (3 + N)) (FreeScalarJetField C) :=
  Matrix.of fun i j => freeCoordinateDerivation C ℕ (i : ℕ) (schwarzianSystem C (j : ℕ))

omit [CharZero C] in
theorem schwarzianJacobian_upperTriangular (N : ℕ) {i j : Fin (3 + N)} (hji : j < i) :
    schwarzianJacobian C N i j = 0 := by
  rw [schwarzianJacobian, Matrix.of_apply]
  have hlt : (j : ℕ) < (i : ℕ) := hji
  by_cases hj : (j : ℕ) < 3
  · rw [schwarzianSystem_of_lt hj]
    exact freeCoordinateDerivation_freeCoordinate_of_ne (by omega)
  · rw [schwarzianSystem_of_ge (by omega)]
    exact freeCoordinateDerivation_schwarzianJet_of_gt _ _ (by omega)

theorem schwarzianJacobian_diag (N : ℕ) (i : Fin (3 + N)) :
    schwarzianJacobian C N i i =
      if (i : ℕ) < 3 then 1 else (freeCoordinate C ℕ 1)⁻¹ := by
  rw [schwarzianJacobian, Matrix.of_apply]
  by_cases hi : (i : ℕ) < 3
  · rw [schwarzianSystem_of_lt hi, if_pos hi]
    exact freeCoordinateDerivation_freeCoordinate_self _
  · rw [schwarzianSystem_of_ge (by omega), if_neg hi]
    have h := freeCoordinateDerivation_schwarzianJet_top (C := C) ((i : ℕ) - 3)
    rwa [show (i : ℕ) - 3 + 3 = (i : ℕ) from by omega] at h

theorem schwarzianJacobian_det_ne_zero (N : ℕ) : (schwarzianJacobian C N).det ≠ 0 := by
  have htri : (schwarzianJacobian C N).BlockTriangular id := fun i j hji =>
    schwarzianJacobian_upperTriangular N hji
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [schwarzianJacobian_diag]
  by_cases hi : (i : ℕ) < 3
  · rw [if_pos hi]
    exact one_ne_zero
  · rw [if_neg hi]
    exact inv_ne_zero (freeScalarJetCoordinate_ne_zero 1)

/-! ## Independence -/

theorem algebraicIndependent_schwarzianBlock (N : ℕ) :
    AlgebraicIndependent C (fun i : Fin (3 + N) => schwarzianSystem C (i : ℕ)) := by
  classical
  refine algebraicIndependent_of_domain_jacobian
    (K := C) (R := FreeScalarJetField C)
    (fun i : Fin (3 + N) => schwarzianSystem C (i : ℕ))
    (fun i f => freeCoordinateDerivation C ℕ (i : ℕ) f)
    (fun i a b => map_add _ a b)
    (fun i a b => by
      rw [Derivation.leibniz]
      simp only [smul_eq_mul])
    (fun i c => Derivation.map_algebraMap _ c)
    (schwarzianJacobian C N) (schwarzianJacobian_det_ne_zero N)
    (fun i j => rfl)

/-- **The Schwarzian coordinate system is algebraically independent.** -/
theorem algebraicIndependent_schwarzianSystem :
    AlgebraicIndependent C (schwarzianSystem C) := by
  classical
  refine algebraicIndependent_of_finite_type fun t ht => ?_
  obtain ⟨b, hb⟩ := ht.bddAbove
  set N := b + 1 with hN
  have hlt : ∀ m : t, (m : ℕ) < 3 + N := by
    intro m
    have := hb m.2
    omega
  have hinj : Function.Injective (fun m : t => (⟨(m : ℕ), hlt m⟩ : Fin (3 + N))) := by
    intro a b hab
    exact Subtype.ext (congrArg Fin.val hab)
  have h := (algebraicIndependent_schwarzianBlock (C := C) N).comp _ hinj
  exact h

omit [CharZero C] in
theorem range_schwarzianSystem :
    Set.range (schwarzianSystem C) = Set.range (schwarzianCoordinates C) := by
  ext z
  constructor
  · rintro ⟨m, rfl⟩
    by_cases hm : m < 3
    · exact ⟨Sum.inl ⟨m, hm⟩, by rw [schwarzianSystem_of_lt hm]; rfl⟩
    · exact ⟨Sum.inr (m - 3), by rw [schwarzianSystem_of_ge (by omega)]; rfl⟩
  · rintro ⟨(k | k), rfl⟩
    · exact ⟨(k : ℕ), by rw [schwarzianSystem_of_lt k.2]; rfl⟩
    · refine ⟨k + 3, ?_⟩
      rw [schwarzianSystem_of_ge (by omega), show k + 3 - 3 = k from by omega]
      rfl

/-- **The Schwarzian coordinate system generates the free scalar jet field.** -/
theorem schwarzianSystem_adjoin_eq_top :
    IntermediateField.adjoin C (Set.range (schwarzianSystem C)) = ⊤ := by
  rw [range_schwarzianSystem]
  exact schwarzianCoordinates_adjoin_eq_top

end

end GaloisForLFunctions.HTGeometry
