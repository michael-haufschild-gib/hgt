import GaloisForLFunctions.HTGeometry.PowerSeriesCommonScaleIndependence
import GaloisForLFunctions.HTGeometry.FreeJetTranslationFixedField
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Explicit generic critical fibre

An algebraic closure of a rational function field supplies `m+n` independent constants.  Multiplying
them by one Laurent uniformizer and adding the two leading `1` coefficients gives an explicitly
algebraically independent critical observation.  The valuative theorem then computes its fibre
without any genericity, separability, or intersection-theory premise.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped LaurentSeries

/-- Fixed characteristic-zero base field for the closed generic construction. -/
abbrev CriticalGenericBase := RatFunc ℚ

/-- Rational function field on all critical observation directions. -/
abbrev CriticalGenericDirectionField (m n : ℕ) :=
  FreeCoordinateRationalField CriticalGenericBase (Fin n ⊕ Fin m)

/-- Algebraically closed constant field containing the generic directions. -/
abbrev CriticalGenericConstants (m n : ℕ) :=
  AlgebraicClosure (CriticalGenericDirectionField m n)

/-- Generic direction constants embedded in the algebraic closure. -/
noncomputable def criticalGenericDirection (m n : ℕ) :
    Fin n ⊕ Fin m → CriticalGenericConstants m n := fun i =>
  algebraMap (CriticalGenericDirectionField m n) (CriticalGenericConstants m n)
    (freeCoordinate CriticalGenericBase (Fin n ⊕ Fin m) i)

noncomputable def criticalGenericRawDirection (m n : ℕ) :
    Fin n → CriticalGenericConstants m n := fun i => criticalGenericDirection m n (Sum.inl i)

noncomputable def criticalGenericReciprocalDirection (m n : ℕ) :
    Fin m → CriticalGenericConstants m n := fun j => criticalGenericDirection m n (Sum.inr j)

/-- The generic direction constants are algebraically independent over the fixed base. -/
theorem algebraicIndependent_criticalGenericDirection (m n : ℕ) :
    AlgebraicIndependent CriticalGenericBase (criticalGenericDirection m n) := by
  let f : CriticalGenericDirectionField m n →ₐ[CriticalGenericBase]
      CriticalGenericConstants m n :=
    IsScalarTower.toAlgHom CriticalGenericBase (CriticalGenericDirectionField m n)
      (CriticalGenericConstants m n)
  have h := (algebraicIndependent_freeCoordinate CriticalGenericBase (Fin n ⊕ Fin m)).map'
    f.injective
  change AlgebraicIndependent CriticalGenericBase
    (fun i => algebraMap (CriticalGenericDirectionField m n) (CriticalGenericConstants m n)
      (freeCoordinate CriticalGenericBase (Fin n ⊕ Fin m) i))
  exact h

theorem criticalDirectionConstants_generic (m n : ℕ) :
    criticalDirectionConstants (criticalGenericRawDirection m n)
      (criticalGenericReciprocalDirection m n) = criticalGenericDirection m n := by
  funext i
  rcases i with i | j <;> rfl

/-- The explicit critical observation is genuinely generic: its coordinates are algebraically
independent. -/
theorem algebraicIndependent_criticalGenericLaurentObservation (m n : ℕ) :
    AlgebraicIndependent CriticalGenericBase
      (laurentCriticalObservation CriticalGenericBase (CriticalGenericConstants m n)
        (criticalGenericRawDirection m n) (criticalGenericReciprocalDirection m n)) := by
  apply algebraicIndependent_laurentCriticalObservation
  rw [criticalDirectionConstants_generic]
  exact algebraicIndependent_criticalGenericDirection m n

/-- Raw tail of the explicit generic critical observation. -/
noncomputable def criticalGenericLaurentRawTail (m n : ℕ) :
    (CriticalGenericConstants m n)⸨X⸩[X] :=
  (X ^ m + powerSeriesRawDeformation (CriticalGenericConstants m n) m n
    (criticalGenericRawDirection m n)).map
      (algebraMap (PowerSeries (CriticalGenericConstants m n))
        (CriticalGenericConstants m n)⸨X⸩)

/-- Reciprocal tail of the explicit generic critical observation. -/
noncomputable def criticalGenericLaurentReciprocalTail (m n : ℕ) :
    (CriticalGenericConstants m n)⸨X⸩[X] :=
  (X ^ n + powerSeriesReciprocalDeformation (CriticalGenericConstants m n) m n
    (criticalGenericReciprocalDirection m n)).map
      (algebraMap (PowerSeries (CriticalGenericConstants m n))
        (CriticalGenericConstants m n)⸨X⸩)

theorem coeff_powerSeriesRawDeformation
    (E : Type*) [Field E] (m : ℕ) {n : ℕ} (u : Fin n → E) (i : Fin n) :
    (powerSeriesRawDeformation E m n u).coeff (m + (i : ℕ)) =
      powerSeriesDeformParam (u i) := by
  classical
  rw [powerSeriesRawDeformation, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hji (Fin.ext (by omega))
  · exact fun h => absurd (Finset.mem_univ i) h

theorem coeff_powerSeriesReciprocalDeformation
    (E : Type*) [Field E] (n : ℕ) {m : ℕ} (v : Fin m → E) (j : Fin m) :
    (powerSeriesReciprocalDeformation E m n v).coeff (n + (j : ℕ)) =
      powerSeriesDeformParam (v j) := by
  classical
  rw [powerSeriesReciprocalDeformation, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hij (Fin.ext (by omega))
  · exact fun h => absurd (Finset.mem_univ j) h

/-- Raw observed coefficients of the explicit tails are exactly the generic observation
coordinates. -/
theorem criticalGenericLaurentRawTail_coeff (m n : ℕ) (i : Fin n) :
    (criticalGenericLaurentRawTail m n).coeff (m + (i : ℕ)) =
      laurentCriticalObservation CriticalGenericBase (CriticalGenericConstants m n)
        (criticalGenericRawDirection m n) (criticalGenericReciprocalDirection m n) (Sum.inl i) := by
  rw [criticalGenericLaurentRawTail, Polynomial.coeff_map, Polynomial.coeff_add,
    coeff_powerSeriesRawDeformation]
  by_cases hi : (i : ℕ) = 0
  · simp [hi, laurentCriticalObservation, powerSeriesCriticalObservation,
      criticalObservationShift, criticalDirectionConstants, add_comm]
  · simp [hi, laurentCriticalObservation, powerSeriesCriticalObservation,
      criticalObservationShift, criticalDirectionConstants]

/-- Reciprocal observed coefficients of the explicit tails are exactly the generic observation
coordinates. -/
theorem criticalGenericLaurentReciprocalTail_coeff (m n : ℕ) (j : Fin m) :
    (criticalGenericLaurentReciprocalTail m n).coeff (n + (j : ℕ)) =
      laurentCriticalObservation CriticalGenericBase (CriticalGenericConstants m n)
        (criticalGenericRawDirection m n) (criticalGenericReciprocalDirection m n) (Sum.inr j) := by
  rw [criticalGenericLaurentReciprocalTail, Polynomial.coeff_map, Polynomial.coeff_add,
    coeff_powerSeriesReciprocalDeformation]
  by_cases hj : (j : ℕ) = 0
  · simp [hj, laurentCriticalObservation, powerSeriesCriticalObservation,
      criticalObservationShift, criticalDirectionConstants, add_comm]
  · simp [hj, laurentCriticalObservation, powerSeriesCriticalObservation,
      criticalObservationShift, criticalDirectionConstants]

/-- **Closed generic critical multiplicity theorem.**  For every positive pair of depths, the
explicit algebraically independent critical observation has exactly `choose (m+n) m` compatible
jets. -/
theorem nat_card_criticalGenericLaurentFibre
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalFibre (CriticalGenericConstants m n)⸨X⸩ m n
      (criticalGenericLaurentRawTail m n)
      (criticalGenericLaurentReciprocalTail m n)) =
      criticalHorizonMultiplicity m n := by
  exact nat_card_laurentSeriesCriticalFibre (CriticalGenericConstants m n) hm hn
    (criticalGenericRawDirection m n) (criticalGenericReciprocalDirection m n)

end GaloisForLFunctions.HTGeometry
