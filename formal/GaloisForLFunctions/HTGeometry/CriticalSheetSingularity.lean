import GaloisForLFunctions.HTGeometry.CriticalSheetReducedJacobian
import GaloisForLFunctions.HTGeometry.HorizonJacobianDeterminant
import GaloisForLFunctions.HTGeometry.CriticalSchurJacobianDivisor

/-!
# A degenerate reduced Jacobian makes a sheet singular

The caustic determinant of a sheet's reduced reciprocal jet is the reduction of the sheet image of
the source caustic determinant, and the ramification element is a unit multiple of that
determinant inside the chart algebra.  So a sheet whose reduced Jacobian degenerates lands the
ramification element in the maximal ideal — exactly the singularity hypothesis that `(D-1)` needs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial IsLocalRing

set_option maxHeartbeats 40000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The reduced reciprocal jet of a sheet at the Schur place. -/
noncomputable def criticalSheetReducedRecipPolynomial (σ : criticalGeometricSheet K m n) :
    (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))[X] :=
  ((criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2
    + criticalNormalClosureSchurReciprocalTailIntegral K (Fact.out : 0 < m)
        (Fact.out : 0 < n)).map
    (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))

/-- The integral reduced reciprocal jet of a sheet maps to the sheet image of the source jet. -/
theorem criticalSheetFibre_recipPolynomial_map (σ : criticalGeometricSheet K m n) :
    ((criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2
        + criticalNormalClosureSchurReciprocalTailIntegral K (Fact.out : 0 < m)
          (Fact.out : 0 < n)).map
        ((criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)).subtype)
      = (criticalSourceReciprocalPolynomial K m n).map σ.toRingHom := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  rw [Polynomial.map_add, map_criticalNormalClosureSchurReciprocalTailIntegral]
  have hfibre : ((criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m)
      (Fact.out : 1 < n) σ).1.2).map
      ((criticalNormalClosureSchurValuationSubring K hfm
        hfn).subtype)
      = (criticalSourceReciprocalLow K m n).map σ.toRingHom :=
    congrArg (fun p => p.1.2)
      (criticalFibreMap_criticalGeometricSheetToSchurFibre K
        (Fact.out : 1 < m) (Fact.out : 1 < n) σ)
  rw [hfibre, criticalSourceReciprocalPolynomial_eq_low_add_tail K m n,
    Polynomial.map_add, Polynomial.map_map,
    show (σ.toRingHom).comp (algebraMap (criticalObservationField K m n)
        (criticalSourceField K m n)) = criticalObservationNormalClosureMap K m n from
      RingHom.ext fun x => σ.commutes x]

/-- The caustic determinant of a sheet's reduced jet is the reduction of the sheet image. -/
theorem det_criticalReciprocalJacobian_criticalSheetReducedRecipPolynomial
    (σ : criticalGeometricSheet K m n) :
    (criticalReciprocalJacobian (criticalSheetReducedRecipPolynomial K σ) n m).det
      = IsLocalRing.residue _
        ((criticalReciprocalJacobian
          ((criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2
            + criticalNormalClosureSchurReciprocalTailIntegral K (Fact.out : 0 < m)
              (Fact.out : 0 < n)) n m).det) := by
  rw [criticalSheetReducedRecipPolynomial, ← criticalReciprocalJacobian_map,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]

/-- The sheet image of the source caustic determinant. -/
theorem subtype_det_criticalReciprocalJacobian_sheet (σ : criticalGeometricSheet K m n) :
    ((criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)).subtype)
        ((criticalReciprocalJacobian
          ((criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2
            + criticalNormalClosureSchurReciprocalTailIntegral K (Fact.out : 0 < m)
              (Fact.out : 0 < n)) n m).det)
      = σ ((criticalReciprocalJacobian (criticalSourceReciprocalPolynomial K m n) n m).det) := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, criticalReciprocalJacobian_map,
    criticalSheetFibre_recipPolynomial_map K σ, ← criticalReciprocalJacobian_map,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/-- The source caustic determinant lies in the chart algebra. -/
theorem det_criticalReciprocalJacobian_mem_chartAlgebra :
    (criticalReciprocalJacobian (criticalSourceReciprocalPolynomial K m n) n m).det
      ∈ criticalSourceChartAlgebra K (m := m) (n := n) := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  rw [criticalSourceReciprocalJacobian_det_eq_schurRamification K
    hfm hfn]
  refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
  · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
  · refine Subalgebra.pow_mem _ ?_ _
    rw [← inv_pow]
    exact Subalgebra.pow_mem _ (criticalSourceScale_inv_mem_chartAlgebra K) _
  · exact criticalSchurAeval_mem K _

/-- The source caustic determinant as an element of the chart algebra. -/
noncomputable def criticalSourceJacobianDetChart :
    criticalSourceChartAlgebra K (m := m) (n := n) :=
  ⟨(criticalReciprocalJacobian (criticalSourceReciprocalPolynomial K m n) n m).det,
    det_criticalReciprocalJacobian_mem_chartAlgebra K⟩

/-- The ramification element is a multiple of the caustic determinant in the chart algebra. -/
theorem criticalSchurRamificationChartElement_dvd :
    criticalSourceJacobianDetChart K (m := m) (n := n)
      ∣ criticalSchurRamificationChartElement K (m := m) (n := n) := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  refine ⟨⟨(-1 : criticalSourceField K m n) ^ m *
    (criticalSourceScale K hfm hfn ^ 2) ^ m, ?_⟩, ?_⟩
  · refine Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) ?_
    refine Subalgebra.pow_mem _ (Subalgebra.pow_mem _ ?_ _) _
    rw [criticalSourceScale]
    exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
  · apply Subtype.ext
    show MvPolynomial.aeval (criticalSourceSchurCoordinates K hfm
        hfn) (criticalSourceSchurRamificationPolynomial K m n)
      = (criticalReciprocalJacobian (criticalSourceReciprocalPolynomial K m n) n m).det *
        ((-1 : criticalSourceField K m n) ^ m *
          (criticalSourceScale K hfm hfn ^ 2) ^ m)
    rw [criticalSourceReciprocalJacobian_det_eq_schurRamification K
      hfm hfn]
    have hs : (criticalSourceScale K hfm hfn ^ 2) ≠ 0 :=
      pow_ne_zero 2 (criticalSourceScale_ne_zero K _ _)
    field_simp
    have hall : ((-1 : criticalSourceField K m n) ^ m) ^ 2 *
        ((1 / criticalSourceScale K hfm hfn ^ 2) ^ m *
          (criticalSourceScale K hfm hfn ^ 2) ^ m) = 1 := by
      rw [← mul_pow, one_div, inv_mul_cancel₀ hs, one_pow, mul_one, ← pow_mul, mul_comm m 2,
        pow_mul, neg_one_sq, one_pow]
    rw [mul_assoc, mul_assoc, hall, mul_one]

/-- **A degenerate reduced Jacobian makes the sheet singular.** -/
theorem criticalSheet_singular_of_det_eq_zero (σ : criticalGeometricSheet K m n)
    (hdet : (criticalReciprocalJacobian (criticalSheetReducedRecipPolynomial K σ) n m).det = 0) :
    criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)) := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  have hdetmem : criticalSheetChartToNormalSchur K σ
      (criticalSourceJacobianDetChart K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K hfm
        hfn) := by
    refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
    have hval : criticalSheetChartToNormalSchur K σ
        (criticalSourceJacobianDetChart K (m := m) (n := n))
        = (criticalReciprocalJacobian
            ((criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2
              + criticalNormalClosureSchurReciprocalTailIntegral K hfm
                hfn) n m).det := by
      apply Subtype.ext
      exact (subtype_det_criticalReciprocalJacobian_sheet K σ).symm
    rw [hval, ← det_criticalReciprocalJacobian_criticalSheetReducedRecipPolynomial K σ]
    exact hdet
  obtain ⟨u, hu⟩ := criticalSchurRamificationChartElement_dvd K (m := m) (n := n)
  rw [hu, map_mul]
  exact Ideal.mul_mem_right _ _ hdetmem

end

end GaloisForLFunctions.HTGeometry
