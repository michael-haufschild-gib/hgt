import GaloisForLFunctions.HTGeometry.CriticalGeometricSheetFibre
import GaloisForLFunctions.HTGeometry.PowerSeriesCommonScaleIndependence
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A common-scale generic arc in the critical observation field

All critical observation coordinates are sent to one Laurent uniformizer times independent
direction constants.  The resulting family remains algebraically independent, hence defines an
embedding of the actual rational observation field.  Pulling back the Laurent valuation along this
embedding supplies the common-scale discrete place used to bound geometric sheets.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped LaurentSeries

noncomputable section

/-- Rational function field on generic critical direction constants. -/
abbrev CriticalArcDirectionField
    (K : Type*) [Field K] (m n : ℕ) :=
  FreeCoordinateRationalField K (Fin n ⊕ Fin m)

/-- Algebraically closed field containing all generic direction constants. -/
abbrev CriticalArcConstants
    (K : Type*) [Field K] (m n : ℕ) :=
  AlgebraicClosure (CriticalArcDirectionField K m n)

/-- Independent critical direction constants in the chosen algebraic closure. -/
noncomputable def criticalArcDirection
    (K : Type*) [Field K] (m n : ℕ) :
    Fin n ⊕ Fin m → CriticalArcConstants K m n := fun i =>
  algebraMap (CriticalArcDirectionField K m n) (CriticalArcConstants K m n)
    (freeCoordinate K (Fin n ⊕ Fin m) i)

noncomputable def criticalArcRawDirection
    (K : Type*) [Field K] (m n : ℕ) :
    Fin n → CriticalArcConstants K m n := fun i =>
  criticalArcDirection K m n (Sum.inl i)

noncomputable def criticalArcReciprocalDirection
    (K : Type*) [Field K] (m n : ℕ) :
    Fin m → CriticalArcConstants K m n := fun j =>
  criticalArcDirection K m n (Sum.inr j)

theorem algebraicIndependent_criticalArcDirection
    (K : Type*) [Field K] (m n : ℕ) :
    AlgebraicIndependent K (criticalArcDirection K m n) := by
  let f : CriticalArcDirectionField K m n →ₐ[K] CriticalArcConstants K m n :=
    IsScalarTower.toAlgHom K (CriticalArcDirectionField K m n)
      (CriticalArcConstants K m n)
  have h := (algebraicIndependent_freeCoordinate K (Fin n ⊕ Fin m)).map' f.injective
  change AlgebraicIndependent K
    (fun i => algebraMap (CriticalArcDirectionField K m n) (CriticalArcConstants K m n)
      (freeCoordinate K (Fin n ⊕ Fin m) i))
  exact h

theorem criticalArcDirectionConstants_eq
    (K : Type*) [Field K] (m n : ℕ) :
    criticalDirectionConstants (criticalArcRawDirection K m n)
      (criticalArcReciprocalDirection K m n) = criticalArcDirection K m n := by
  funext i
  rcases i with i | j <;> rfl

/-- Common-scale Laurent observation on the actual critical index set. -/
noncomputable def criticalArcObservation
    (K : Type*) [Field K] (m n : ℕ) :
    Fin n ⊕ Fin m → (CriticalArcConstants K m n)⸨X⸩ :=
  laurentCriticalObservation K (CriticalArcConstants K m n)
    (criticalArcRawDirection K m n) (criticalArcReciprocalDirection K m n)

theorem algebraicIndependent_criticalArcObservation
    (K : Type*) [Field K] (m n : ℕ) :
    AlgebraicIndependent K (criticalArcObservation K m n) := by
  apply algebraicIndependent_laurentCriticalObservation
  rw [criticalArcDirectionConstants_eq]
  exact algebraicIndependent_criticalArcDirection K m n

/-- Embedding of the actual critical observation field along the common-scale Laurent arc. -/
noncomputable def criticalObservationArcEmbedding
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalObservationField K m n →ₐ[K]
      (CriticalArcConstants K m n)⸨X⸩ :=
  (IntermediateField.adjoin K (Set.range (criticalArcObservation K m n))).val.comp
    ((algebraicIndependent_criticalArcObservation K m n).aevalEquivField.toAlgHom.comp
      (criticalObservationFieldEquiv K hm hn).symm.toAlgHom)

theorem criticalObservationFieldEquiv_symm_raw
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    (criticalObservationFieldEquiv K hm hn).symm
        (criticalObservationRaw K m n i) =
      algebraMap (MvPolynomial (Fin n ⊕ Fin m) K)
        (FractionRing (MvPolynomial (Fin n ⊕ Fin m) K))
        (MvPolynomial.X (Sum.inl i)) := by
  apply (criticalObservationFieldEquiv K hm hn).injective
  simp only [AlgEquiv.apply_symm_apply]
  change criticalObservationRaw K m n i = _
  apply Subtype.ext
  simp [criticalObservationFieldEquiv, criticalObservationRaw,
    criticalFieldObservation]

theorem criticalObservationFieldEquiv_symm_recip
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    (criticalObservationFieldEquiv K hm hn).symm
        (criticalObservationRecip K m n j) =
      algebraMap (MvPolynomial (Fin n ⊕ Fin m) K)
        (FractionRing (MvPolynomial (Fin n ⊕ Fin m) K))
        (MvPolynomial.X (Sum.inr j)) := by
  apply (criticalObservationFieldEquiv K hm hn).injective
  simp only [AlgEquiv.apply_symm_apply]
  change criticalObservationRecip K m n j = _
  apply Subtype.ext
  simp [criticalObservationFieldEquiv, criticalObservationRecip,
    criticalFieldObservation]

@[simp] theorem criticalObservationArcEmbedding_raw
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin n) :
    criticalObservationArcEmbedding K hm hn (criticalObservationRaw K m n i) =
      criticalArcObservation K m n (Sum.inl i) := by
  rw [criticalObservationArcEmbedding, criticalObservationFieldEquiv_symm_raw K hm hn]
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

@[simp] theorem criticalObservationArcEmbedding_recip
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (j : Fin m) :
    criticalObservationArcEmbedding K hm hn (criticalObservationRecip K m n j) =
      criticalArcObservation K m n (Sum.inr j) := by
  rw [criticalObservationArcEmbedding, criticalObservationFieldEquiv_symm_recip K hm hn]
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

end

end GaloisForLFunctions.HTGeometry
