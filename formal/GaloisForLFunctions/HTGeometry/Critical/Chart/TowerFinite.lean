import GaloisForLFunctions.HTGeometry.Critical.Schur.ChartHeight
import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
# Finiteness and Noetherian structure of the chart tower

The structure maps of the observation coordinate ring and of the chart ring into the source field
are injective, the chart algebra is a finite module over the chart ring, and both are Noetherian.
The chart ring also has the observation field as its fraction field.  These are the standing
hypotheses of the going-down theorem and of the height formula.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing

set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem algebraMap_observationRing_injective :
    Function.Injective (algebraMap (criticalObservationRing K m n)
      (criticalSourceField K m n)) := by
  have h1 : Function.Injective (algebraMap (criticalObservationRing K m n)
      (criticalObservationField K m n)) := IsFractionRing.injective _ _
  have h2 : Function.Injective
      ((algebraMap (criticalObservationField K m n) (criticalSourceField K m n) :
        criticalObservationField K m n →+* criticalSourceField K m n)) := RingHom.injective _
  intro x y hxy
  apply h1
  apply h2
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at *
  exact hxy

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem algebraMap_chartRing_injective :
    Function.Injective (algebraMap (criticalObservationChartRing K m n)
      (criticalSourceField K m n)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨p, s⟩, hp⟩ := IsLocalization.surj
    (M := Submonoid.powers (criticalObservationMarked K (m := m) (n := n))) x
  have hE := congrArg (algebraMap (criticalObservationChartRing K m n)
    (criticalSourceField K m n)) hp
  rw [map_mul, hx, zero_mul, ← IsScalarTower.algebraMap_apply] at hE
  have hp0 : p = 0 := by
    apply algebraMap_observationRing_injective K
    rw [map_zero, ← hE]
  rw [hp0, map_zero] at hp
  exact (IsLocalization.map_units
    (M := Submonoid.powers (criticalObservationMarked K (m := m) (n := n)))
    (criticalObservationChartRing K m n) s).mul_left_eq_zero.mp hp

instance chartAlgebra_faithfulSMul :
    FaithfulSMul (criticalObservationChartRing K m n)
      (criticalSourceChartAlgebra K (m := m) (n := n)) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply algebraMap_chartRing_injective K
  exact congrArg (Subtype.val (p := fun z : criticalSourceField K m n =>
    z ∈ criticalSourceChartAlgebra K (m := m) (n := n))) hxy

omit [CharZero K] [IsAlgClosed K] [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)] in
theorem criticalSourceCoordinateSet_finite : (criticalSourceCoordinateSet K m n).Finite :=
  (Set.finite_range _).union (Set.finite_range _)

instance chartAlgebra_module_finite :
    Module.Finite (criticalObservationChartRing K m n)
      (criticalSourceChartAlgebra K (m := m) (n := n)) := by
  exact Module.Finite.iff_fg.mpr (fg_adjoin_of_finite (criticalSourceCoordinateSet_finite K)
    (criticalSourceCoordinate_isIntegral_chartRing K))

instance chartRing_isNoetherianRing :
    IsNoetherianRing (criticalObservationChartRing K m n) :=
  IsLocalization.isNoetherianRing
    (Submonoid.powers (criticalObservationMarked K (m := m) (n := n))) _ inferInstance

instance chartAlgebra_isNoetherianRing :
    IsNoetherianRing (criticalSourceChartAlgebra K (m := m) (n := n)) :=
  IsNoetherianRing.of_finite (criticalObservationChartRing K m n) _

noncomputable instance chartRingObservationFieldAlgebra :
    Algebra (criticalObservationChartRing K m n) (criticalObservationField K m n) :=
  (IsLocalization.Away.lift (S := criticalObservationChartRing K m n)
    (criticalObservationMarked K)
    (by
      refine (Ne.isUnit ?_)
      intro h
      exact criticalObservationMarked_ne_zero K
        ((IsFractionRing.injective (criticalObservationRing K m n)
          (criticalObservationField K m n)) (by rw [h, map_zero]))) ).toAlgebra

instance chartRingObservationFieldTower :
    IsScalarTower (criticalObservationRing K m n) (criticalObservationChartRing K m n)
      (criticalObservationField K m n) :=
  IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp _ _).symm

instance chartRing_isFractionRing :
    IsFractionRing (criticalObservationChartRing K m n) (criticalObservationField K m n) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (criticalObservationMarked K (m := m) (n := n))) _ _

end

end GaloisForLFunctions.HTGeometry
