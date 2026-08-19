import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphicIsomonodromy
import GaloisForLFunctions.HTGeometry.IsomonodromyGaugeInvariance
import GaloisForLFunctions.HTGeometry.BesselOrderJetModule

/-!
# The unit shift is a differential automorphism of `ℂ(X)`, and the Bessel obstruction is intrinsic

Transporting through the faithful embedding of `ℂ(X)` into the global meromorphic field, where
translation is already known to commute with differentiation, shows that the unit shift commutes
with the rational coordinate derivation.  With gauge invariance of the integrability equation this
upgrades the Bessel obstruction: **no system gauge equivalent to the Bessel order companion over
`ℂ(ν)` admits a connection**, so the obstruction belongs to the difference module and not to the
companion basis.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- **The unit shift commutes with the rational coordinate derivation.** -/
theorem ratShift_deriv (r : RatFunc ℂ) :
    ratShift (Differential.deriv r) = Differential.deriv (ratShift r) := by
  have hinj : Function.Injective
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) :=
    (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective
  apply hinj
  calc algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (ratShift (Differential.deriv r))
      = addTranslationMeroEquiv (1 : ℂ)
          (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (Differential.deriv r)) := by
        rw [addTranslationMeroEquiv_one_algebraMap]
    _ = addTranslationMeroEquiv (1 : ℂ)
          (Differential.deriv
            (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r)) := by
        rw [deriv_algebraMap (A := RatFunc ℂ) (B := meroField (Set.univ : Set ℂ))]
    _ = Differential.deriv (addTranslationMeroEquiv (1 : ℂ)
          (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r)) :=
        addTranslationMeroEquiv_deriv 1 _
    _ = Differential.deriv
          (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (ratShift r)) := by
        rw [addTranslationMeroEquiv_one_algebraMap]
    _ = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
          (Differential.deriv (ratShift r)) :=
        (deriv_algebraMap (A := RatFunc ℂ) (B := meroField (Set.univ : Set ℂ)) _)

/-- The entrywise derivative of the Bessel order companion. -/
theorem matrixDeriv_besselOrderCompanion (c : ℂ) :
    matrixDeriv (besselOrderCompanion c) = besselOrderCompanionDeriv c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixDeriv, besselOrderCompanion, besselOrderCompanionDeriv]
  exact deriv_orderShiftCoeff c

/-- **The Bessel obstruction is intrinsic to the difference module.**  No system gauge equivalent
to the Bessel order companion over `ℂ(ν)` admits a connection. -/
theorem besselOrder_no_gauge_delta_structure {c : ℂ} (hc : c ≠ 0)
    (T A' B' : Matrix (Fin 2) (Fin 2) (RatFunc ℂ)) [Invertible T]
    (hgauge : T.map ratShift * besselOrderCompanion c = A' * T)
    (hiso : B'.map ratShift * A' = matrixDeriv A' + A' * B') : False := by
  letI : Invertible (T.map ratShift) := invertibleMapRingHom ratShift T
  have hmapinv : (⅟T).map ratShift = ⅟(T.map ratShift) := rfl
  obtain ⟨B, hB⟩ := isomonodromy_of_gauge ratShift ratShift_deriv
    (besselOrderCompanion c) A' B' T hmapinv hgauge hiso
  refine besselOrder_no_matrix_delta_structure hc B ?_
  rw [hB, matrixDeriv_besselOrderCompanion]
  abel

end

end GaloisForLFunctions.HTGeometry
