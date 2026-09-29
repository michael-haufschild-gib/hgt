import GaloisForLFunctions.HTGeometry.CriticalCoefficientBaseChange
import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromy

/-!
# The critical horizon over arbitrary characteristic-zero constants

The critical observation coordinates are algebraically independent over every characteristic-zero
field.  Coefficient extension to an algebraic closure carries them to the observation over
algebraically closed constants, which is independent, and independence descends along the
coefficient-extension homomorphism.  Consequently the critical source field is a finite separable
extension of the critical observation field over every characteristic-zero field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- **The critical observation is algebraically independent over every characteristic-zero
field.** -/
theorem algebraicIndependent_criticalFieldObservation_charZero
    (F : Type*) [Field F] [CharZero F] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    AlgebraicIndependent F (criticalFieldObservation F m n) := by
  let K := AlgebraicClosure F
  have hKF : AlgebraicIndependent F (criticalFieldObservation K m n) :=
    (algebraicIndependent_criticalFieldObservation K hm hn).restrictScalars
      (algebraMap F K).injective
  have hcomp : (genericJetFieldBaseChangeAlgHom (k := F) (K := K) (m + n)) ∘
      criticalFieldObservation F m n = criticalFieldObservation K m n := by
    funext s
    rcases s with i | j
    · exact genericJetFieldBaseChange_genericRaw _ (by omega)
    · exact genericJetFieldBaseChange_genericRecip _ _
  rw [← hcomp] at hKF
  exact AlgebraicIndependent.of_comp _ hKF

/-- Rational presentation of the critical observation field over characteristic-zero constants. -/
noncomputable def criticalObservationFieldEquivCharZero
    (F : Type*) [Field F] [CharZero F] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    FractionRing (MvPolynomial (Fin n ⊕ Fin m) F) ≃ₐ[F]
      criticalObservationField F m n :=
  (algebraicIndependent_criticalFieldObservation_charZero F hm hn).aevalEquivField.trans
    (IntermediateField.equivOfEq (by rfl))

/-- The critical observation field has transcendence degree `m+n` over every characteristic-zero
field. -/
theorem trdeg_criticalObservationField_charZero
    (F : Type u) [Field F] [CharZero F] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Algebra.trdeg F (criticalObservationField F m n) = (m + n : Cardinal) := by
  calc
    Algebra.trdeg F (criticalObservationField F m n) =
        Algebra.trdeg F (FractionRing (MvPolynomial (Fin n ⊕ Fin m) F)) :=
      (criticalObservationFieldEquivCharZero F hm hn).trdeg_eq.symm
    _ = Cardinal.lift.{u} (Cardinal.mk (Fin n ⊕ Fin m)) :=
      trdeg_fractionRing_mvPolynomial F _
    _ = (m + n : Cardinal) := by simp [add_comm]

/-- The critical source field is algebraic over the critical observation field over every
characteristic-zero field: both have transcendence degree `m+n`. -/
theorem criticalSourceField_isAlgebraic_criticalObservationField_charZero
    (F : Type*) [Field F] [CharZero F] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Algebra.IsAlgebraic (criticalObservationField F m n) (criticalSourceField F m n) := by
  haveI : FaithfulSMul F (criticalObservationField F m n) :=
    (faithfulSMul_iff_algebraMap_injective F _).mpr (algebraMap F _).injective
  haveI : FaithfulSMul (criticalObservationField F m n) (criticalSourceField F m n) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (criticalObservationField F m n) (criticalSourceField F m n)).injective
  have hsum := trdeg_add_eq F (criticalObservationField F m n)
    (A := criticalSourceField F m n)
  rw [trdeg_criticalObservationField_charZero F hm hn, trdeg_criticalSourceField F m n] at hsum
  have hzero : Algebra.trdeg (criticalObservationField F m n)
      (criticalSourceField F m n) = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hsum with hlarge | hzero
    · have hfinite : (m : Cardinal) + (n : Cardinal) < Cardinal.aleph0 := by
        simpa using (Cardinal.natCast_lt_aleph0 (n := m + n))
      exact False.elim ((not_le_of_gt hfinite)
        (le_trans (le_max_left Cardinal.aleph0
          (Algebra.trdeg (criticalObservationField F m n) (criticalSourceField F m n))) hlarge))
    · exact hzero
  exact trdeg_eq_zero_iff.mp hzero

/-- **The critical source is a finite extension of the critical observation field over every
characteristic-zero field.** -/
theorem criticalSourceField_finiteDimensional_criticalObservationField_charZero
    (F : Type*) [Field F] [CharZero F] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    FiniteDimensional (criticalObservationField F m n) (criticalSourceField F m n) := by
  letI : Algebra.IsAlgebraic (criticalObservationField F m n) (criticalSourceField F m n) :=
    criticalSourceField_isAlgebraic_criticalObservationField_charZero F hm hn
  have hfg : (⊤ : IntermediateField (criticalObservationField F m n)
      (criticalSourceField F m n)).FG := by
    rw [← criticalSourceRaw_adjoin_eq_top F m n]
    exact IntermediateField.fg_adjoin_of_finite (Set.finite_range _)
  letI : Algebra.EssFiniteType (criticalObservationField F m n)
      (criticalSourceField F m n) := IntermediateField.fg_top_iff.mp hfg
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end

end GaloisForLFunctions.HTGeometry
