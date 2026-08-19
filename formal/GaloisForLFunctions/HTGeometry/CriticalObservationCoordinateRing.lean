import GaloisForLFunctions.HTGeometry.CriticalSchurCoordinateAdjoin
import GaloisForLFunctions.HTGeometry.CriticalSourceChartIntegrality

/-!
# The observation coordinate ring

The observation coordinates are algebraically independent, so the observation field is the fraction
field of a polynomial ring in them.  This module installs that polynomial ring, its structure maps
into the observation and source fields, the images of the variables, and the marked product whose
inversion defines the chart.

The positivity hypotheses are carried as `Fact` instances so that the algebra structures can be
instances.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)]

/-- Coordinate ring of the observation chart. -/
abbrev criticalObservationRing (K : Type*) [Field K] (m n : ℕ) :=
  MvPolynomial (Fin n ⊕ Fin m) K

/-- Structure map of the observation coordinate ring into the observation field. -/
noncomputable def criticalObservationRingToField :
    criticalObservationRing K m n →ₐ[K] criticalObservationField K m n :=
  (criticalObservationFieldEquiv K (Fact.out : 0 < m) (Fact.out : 0 < n)).toAlgHom.comp
    (IsScalarTower.toAlgHom K (criticalObservationRing K m n)
      (FractionRing (criticalObservationRing K m n)))

noncomputable instance criticalObservationRingAlgebra :
    Algebra (criticalObservationRing K m n) (criticalObservationField K m n) :=
  (criticalObservationRingToField K).toRingHom.toAlgebra

instance criticalObservationRingTower :
    IsScalarTower K (criticalObservationRing K m n) (criticalObservationField K m n) :=
  IsScalarTower.of_algebraMap_eq fun c => ((criticalObservationRingToField K).commutes c).symm

/-- The fraction-field equivalence, as an equivalence of coordinate-ring algebras. -/
noncomputable def criticalObservationFracEquiv :
    FractionRing (criticalObservationRing K m n) ≃ₐ[criticalObservationRing K m n]
      criticalObservationField K m n :=
  { criticalObservationFieldEquiv K (Fact.out : 0 < m) (Fact.out : 0 < n) with
    commutes' := fun _ => rfl }

/-- **The observation field is the fraction field of the observation coordinate ring.** -/
instance criticalObservationRing_isFractionRing :
    IsFractionRing (criticalObservationRing K m n) (criticalObservationField K m n) :=
  IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (criticalObservationRing K m n))
    (criticalObservationFracEquiv K)

/-- The observation coordinates, as elements of the observation field. -/
noncomputable def criticalObservationCoord :
    Fin n ⊕ Fin m → criticalObservationField K m n
  | Sum.inl i => criticalObservationRaw K m n i
  | Sum.inr j => criticalObservationRecip K m n j

omit [CharZero K] [IsAlgClosed K] [Fact (0 < m)] [Fact (0 < n)] in
theorem coe_aeval_criticalObservationCoord (p : criticalObservationRing K m n) :
    ((MvPolynomial.aeval (criticalObservationCoord K) p : criticalObservationField K m n) :
      genericJetField K (m + n))
      = MvPolynomial.aeval (criticalFieldObservation K m n) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      rw [map_add, map_add]
      push_cast
      rw [hp, hq]
  | mul_X p s hp =>
      rw [map_mul, map_mul]
      push_cast
      rw [hp]
      congr 1
      rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      cases s with
      | inl i => rfl
      | inr j => rfl

theorem criticalObservationRingToField_apply (p : criticalObservationRing K m n) :
    criticalObservationRingToField K p = MvPolynomial.aeval (criticalObservationCoord K) p := by
  have hAI := algebraicIndependent_criticalFieldObservation K
    (Fact.out : 0 < m) (Fact.out : 0 < n)
  have h := hAI.aevalEquivField_algebraMap_apply_coe p
  show criticalObservationFieldEquiv K (Fact.out : 0 < m) (Fact.out : 0 < n)
      (algebraMap (criticalObservationRing K m n)
        (FractionRing (criticalObservationRing K m n)) p) = _
  rw [criticalObservationFieldEquiv, AlgEquiv.trans_apply]
  apply Subtype.ext
  change ((hAI.aevalEquivField
      (algebraMap _ (FractionRing (criticalObservationRing K m n)) p) :
        IntermediateField.adjoin K (Set.range (criticalFieldObservation K m n))) :
      genericJetField K (m + n)) = _
  rw [h, ← coe_aeval_criticalObservationCoord K p]

/-- The observation coordinate ring acts on the source field. -/
noncomputable instance criticalObservationRingSourceAlgebra :
    Algebra (criticalObservationRing K m n) (criticalSourceField K m n) :=
  ((algebraMap (criticalObservationField K m n) (criticalSourceField K m n)).comp
    (algebraMap (criticalObservationRing K m n) (criticalObservationField K m n))).toAlgebra

instance criticalObservationRingSourceTower :
    IsScalarTower (criticalObservationRing K m n) (criticalObservationField K m n)
      (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem algebraMap_criticalObservationRing_X_inl (i : Fin n) :
    algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
        (MvPolynomial.X (Sum.inl i))
      = criticalSourceRaw K m n ⟨m + (i : ℕ), by omega⟩ := by
  rw [IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
    (criticalObservationField K m n) (criticalSourceField K m n)]
  show algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
    (criticalObservationRingToField K (MvPolynomial.X (Sum.inl i))) = _
  rw [criticalObservationRingToField_apply, MvPolynomial.aeval_X]
  exact algebraMap_criticalObservationRaw K i

theorem algebraMap_criticalObservationRing_X_inr (j : Fin m) :
    algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
        (MvPolynomial.X (Sum.inr j))
      = criticalSourceRecip K m n ⟨n + (j : ℕ), by omega⟩ := by
  rw [IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
    (criticalObservationField K m n) (criticalSourceField K m n)]
  show algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
    (criticalObservationRingToField K (MvPolynomial.X (Sum.inr j))) = _
  rw [criticalObservationRingToField_apply, MvPolynomial.aeval_X]
  exact algebraMap_criticalObservationRecip K j

/-- The marked product of the two distinguished observation coordinates. -/
noncomputable def criticalObservationMarked : criticalObservationRing K m n :=
  MvPolynomial.X (Sum.inl (⟨0, Fact.out⟩ : Fin n)) *
    MvPolynomial.X (Sum.inr (⟨0, Fact.out⟩ : Fin m))

theorem algebraMap_criticalObservationMarked :
    algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
        (criticalObservationMarked K)
      = criticalSourceRaw K m n ⟨m, by have := (Fact.out : 0 < n); omega⟩ *
          criticalSourceRecip K m n ⟨n, by have := (Fact.out : 0 < m); omega⟩ := by
  rw [criticalObservationMarked, map_mul, algebraMap_criticalObservationRing_X_inl,
    algebraMap_criticalObservationRing_X_inr]
  congr 2

end

end GaloisForLFunctions.HTGeometry
