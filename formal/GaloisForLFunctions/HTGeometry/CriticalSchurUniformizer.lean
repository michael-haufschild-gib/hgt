import GaloisForLFunctions.HTGeometry.CriticalSchurValuationDVR
import GaloisForLFunctions.HTGeometry.CriticalSchurJacobianDivisor
import GaloisForLFunctions.HTGeometry.CriticalSchurMarkedUnits

/-!
# The actual Schur uniformizer

The irreducible Schur polynomial is transported from the height-one localization, through its
valuation-subring presentation, and finally into the actual critical source valuation ring.  Its
underlying source-field element is exactly the evaluated Schur ramification equation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsDiscreteValuationRing

set_option maxHeartbeats 1000000

/-- Schur uniformizer in the coordinate valuation-subring presentation. -/
noncomputable def criticalSchurCoordinateUniformizer
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurCoordinateValuationSubring K hm hn := by
  let R := criticalSchurSourceRing K m n
  let P := criticalSchurPrimeDivisor K hm hn
  let A := Localization.AtPrime P.1
  let π : A := algebraMap R A (criticalSourceSchurRamificationPolynomial K m n)
  unfold criticalSchurCoordinateValuationSubring
  exact IsDiscreteValuationRing.equivValuationSubring π

/-- The coordinate Schur element is a uniformizer. -/
theorem irreducible_criticalSchurCoordinateUniformizer
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Irreducible (criticalSchurCoordinateUniformizer K hm hn) := by
  let R := criticalSchurSourceRing K m n
  let P := criticalSchurPrimeDivisor K hm hn
  let A := Localization.AtPrime P.1
  let π : A := algebraMap R A (criticalSourceSchurRamificationPolynomial K m n)
  change Irreducible (IsDiscreteValuationRing.equivValuationSubring π)
  exact (irreducible_algebraMap_criticalSourceSchurRamificationPolynomial K hm hn).map
    (IsDiscreteValuationRing.equivValuationSubring (A := A)
      (K := FractionRing R))

/-- Underlying coordinate fraction-field element of the Schur uniformizer. -/
theorem coe_criticalSchurCoordinateUniformizer
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurCoordinateUniformizer K hm hn :
      FractionRing (criticalSchurSourceRing K m n)) =
      algebraMap (criticalSchurSourceRing K m n)
        (FractionRing (criticalSchurSourceRing K m n))
        (criticalSourceSchurRamificationPolynomial K m n) := by
  change algebraMap
      (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1)
      (FractionRing (criticalSchurSourceRing K m n))
      (algebraMap (criticalSchurSourceRing K m n)
        (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1)
        (criticalSourceSchurRamificationPolynomial K m n)) = _
  exact IsScalarTower.algebraMap_apply
    (criticalSchurSourceRing K m n)
    (Localization.AtPrime (criticalSchurPrimeDivisor K hm hn).1)
    (FractionRing (criticalSchurSourceRing K m n))
    (criticalSourceSchurRamificationPolynomial K m n) |>.symm

/-- Actual Schur uniformizer in the source valuation ring. -/
noncomputable def criticalSchurSourceUniformizer
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurSourceValuationSubring K hm hn :=
  (criticalSchurSourceValuationRingEquiv K hm hn).symm
    (criticalSchurCoordinateUniformizer K hm hn)

/-- The actual source Schur element is a uniformizer. -/
theorem irreducible_criticalSchurSourceUniformizer
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Irreducible (criticalSchurSourceUniformizer K hm hn) :=
  (irreducible_criticalSchurCoordinateUniformizer K hm hn).map
    (criticalSchurSourceValuationRingEquiv K hm hn).symm

/-- The underlying actual source-field element is exactly the evaluated Schur polynomial. -/
theorem coe_criticalSchurSourceUniformizer
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurSourceUniformizer K hm hn : criticalSourceField K m n) =
      MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn)
        (criticalSourceSchurRamificationPolynomial K m n) := by
  change criticalSourceSchurFieldEquiv K hm hn
      (criticalSchurCoordinateUniformizer K hm hn :
        FractionRing (criticalSchurSourceRing K m n)) = _
  rw [coe_criticalSchurCoordinateUniformizer K hm hn]
  exact criticalSourceSchurFieldEquiv_algebraMap_apply K hm hn _

/-- The actual Schur equation has source divisorial order exactly one. -/
theorem addVal_criticalSchurSourceUniformizer_eq_one
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    addVal (criticalSchurSourceValuationSubring K hm hn)
      (criticalSchurSourceUniformizer K hm hn) = 1 :=
  addVal_uniformizer (irreducible_criticalSchurSourceUniformizer K hm hn)

/-! ## The concrete Jacobian determinant -/

/-- The source scale, as an element of the Schur valuation ring. -/
noncomputable def criticalSchurSourceScaleElement
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurSourceValuationSubring K hm hn :=
  ⟨criticalSourceScale K hm hn, by
    rw [criticalSourceScale_eq_schurCoordinate_zero K hm hn]
    exact criticalSourceSchurCoordinates_mem_sourceValuationSubring K hm hn 0⟩

/-- In genuinely two-sided rank, the source scale is transverse to the Schur divisor and hence is
a unit of the source Schur valuation ring. -/
theorem isUnit_criticalSchurSourceScaleElement
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    IsUnit (criticalSchurSourceScaleElement K (by omega : 0 < m) (by omega : 0 < n)) := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  apply isUnit_criticalSchurSourceValuationSubring_of_mem_transverseField K hm hn
  · rw [criticalSourceScale_eq_schurCoordinate_zero K hm0 hn0]
    apply criticalSourceSchurCoordinate_mem_transverseField K hm0 hn0
    intro h
    have := congrArg Fin.val h
    simp [criticalSchurRamificationCoordinateIndex] at this
  · exact criticalSourceScale_ne_zero K hm0 hn0

/-- Inverse source scale, explicitly lifted to the source Schur valuation ring. -/
noncomputable def criticalSchurSourceScaleInvElement
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurSourceValuationSubring K hm hn :=
  ⟨(criticalSourceScale K hm hn)⁻¹,
    criticalSourceScale_inv_mem_sourceValuationSubring K hm hn⟩

/-- In two-sided rank, the explicitly lifted inverse scale is a unit. -/
theorem isUnit_criticalSchurSourceScaleInvElement
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    IsUnit (criticalSchurSourceScaleInvElement K (by omega : 0 < m)
      (by omega : 0 < n)) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨criticalSchurSourceScaleElement K (by omega : 0 < m) (by omega : 0 < n),
    Subtype.ext ?_⟩
  exact inv_mul_cancel₀ (criticalSourceScale_ne_zero K (by omega) (by omega))

/-- Concrete reciprocal Jacobian determinant lifted to the actual source Schur valuation ring. -/
noncomputable def criticalSchurJacobianDetElement
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurSourceValuationSubring K hm hn :=
  (-1) ^ m * (criticalSchurSourceScaleInvElement K hm hn ^ 2) ^ m *
    criticalSchurSourceUniformizer K hm hn

/-- The lifted element is exactly the determinant of the concrete reciprocal Jacobian. -/
theorem coe_criticalSchurJacobianDetElement
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurJacobianDetElement K hm hn : criticalSourceField K m n) =
      (criticalReciprocalJacobian
        (criticalSourceReciprocalPolynomial K m n) n m).det := by
  rw [criticalSourceReciprocalJacobian_det_eq_schurRamification K hm hn]
  change (-1 : criticalSourceField K m n) ^ m *
      (((criticalSourceScale K hm hn)⁻¹) ^ 2) ^ m *
        (criticalSchurSourceUniformizer K hm hn : criticalSourceField K m n) = _
  rw [coe_criticalSchurSourceUniformizer K hm hn]
  simp only [inv_pow]

/-- In two-sided rank, the explicit scalar multiplying the Schur equation in the Jacobian is a
unit of the source valuation ring. -/
theorem isUnit_criticalSchurJacobianUnitFactor
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    IsUnit (((-1 : criticalSchurSourceValuationSubring K (by omega : 0 < m)
        (by omega : 0 < n))) ^ m *
      (criticalSchurSourceScaleInvElement K (by omega : 0 < m)
        (by omega : 0 < n) ^ 2) ^ m) := by
  exact (isUnit_neg_one.pow m).mul
    ((isUnit_criticalSchurSourceScaleInvElement K hm hn).pow 2 |>.pow m)

/-- The actual reciprocal Jacobian determinant is a source-DVR uniformizer in two-sided rank. -/
theorem irreducible_criticalSchurJacobianDetElement
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    Irreducible (criticalSchurJacobianDetElement K (by omega : 0 < m) (by omega : 0 < n)) := by
  exact (irreducible_isUnit_mul (isUnit_criticalSchurJacobianUnitFactor K hm hn)).mpr
    (irreducible_criticalSchurSourceUniformizer K (by omega : 0 < m) (by omega : 0 < n))

/-- The concrete reciprocal Jacobian determinant has source divisorial order exactly one. -/
theorem addVal_criticalSchurJacobianDetElement_eq_one
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    addVal (criticalSchurSourceValuationSubring K (by omega : 0 < m) (by omega : 0 < n))
      (criticalSchurJacobianDetElement K (by omega : 0 < m) (by omega : 0 < n)) = 1 :=
  addVal_uniformizer (irreducible_criticalSchurJacobianDetElement K hm hn)

end

end GaloisForLFunctions.HTGeometry
