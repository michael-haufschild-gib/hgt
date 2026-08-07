import GaloisForLFunctions.HTGeometry.CriticalNormalClosureArcPlace

/-!
# Geometric sheets as critical-fibre points in the normal closure

The earlier ambient construction placed sheet values in a chosen algebraic closure.  For the
valuative degree bound we need the sharper codomain: the actual finite normal closure itself.
Every geometric sheet gives a compatible critical-fibre point there, and the map is injective.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

/-- Actual observation-field map into the actual normal closure. -/
noncomputable def criticalObservationNormalClosureMap
    (K : Type*) [Field K] (m n : ℕ) :
    criticalObservationField K m n →+* criticalNormalClosure K m n :=
  algebraMap (criticalObservationField K m n) (criticalNormalClosure K m n)

theorem X_pow_dvd_criticalObservationRawTail_map_normalClosure
    (K : Type*) [Field K] (m n : ℕ) :
    (X : (criticalNormalClosure K m n)[X]) ^ m ∣
      (criticalObservationRawTail K m n).map
        (criticalObservationNormalClosureMap K m n) := by
  simpa using Polynomial.map_dvd
    (criticalObservationNormalClosureMap K m n)
    (X_pow_dvd_criticalObservationRawTail K m n)

theorem X_pow_dvd_criticalObservationReciprocalTail_map_normalClosure
    (K : Type*) [Field K] (m n : ℕ) :
    (X : (criticalNormalClosure K m n)[X]) ^ n ∣
      (criticalObservationReciprocalTail K m n).map
        (criticalObservationNormalClosureMap K m n) := by
  simpa using Polynomial.map_dvd
    (criticalObservationNormalClosureMap K m n)
    (X_pow_dvd_criticalObservationReciprocalTail K m n)

/-- Mapping the actual generic inverse identity along a geometric sheet gives inverse coefficient
blocks inside the actual normal closure. -/
theorem criticalGeometricSheet_mapped_inverse_normalClosure
    (K : Type*) [Field K] (m n : ℕ) (σ : criticalGeometricSheet K m n) :
    (X : (criticalNormalClosure K m n)[X]) ^ (m + n) ∣
      ((criticalSourceRawLow K m n).map σ.toRingHom +
        (criticalObservationRawTail K m n).map
          (criticalObservationNormalClosureMap K m n)) *
      ((criticalSourceReciprocalLow K m n).map σ.toRingHom +
        (criticalObservationReciprocalTail K m n).map
          (criticalObservationNormalClosureMap K m n)) - 1 := by
  have h := Polynomial.map_dvd σ.toRingHom
    (X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one K m n)
  rw [criticalSourceRawPolynomial_eq_low_add_tail,
    criticalSourceReciprocalPolynomial_eq_low_add_tail] at h
  have hcomp : σ.toRingHom.comp
      (algebraMap (criticalObservationField K m n) (criticalSourceField K m n)) =
      criticalObservationNormalClosureMap K m n := by
    apply RingHom.ext
    intro z
    exact σ.commutes z
  simpa only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_map, Polynomial.map_pow, Polynomial.map_X,
    hcomp] using h

/-- A geometric sheet evaluated on low coefficient blocks is an actual critical-fibre point in
the normal closure. -/
noncomputable def criticalGeometricSheetToNormalFibre
    (K : Type*) [Field K] (m n : ℕ) :
    criticalGeometricSheet K m n →
      criticalFibre (criticalNormalClosure K m n) m n
        ((criticalObservationRawTail K m n).map
          (criticalObservationNormalClosureMap K m n))
        ((criticalObservationReciprocalTail K m n).map
          (criticalObservationNormalClosureMap K m n)) := by
  intro σ
  let A := (criticalSourceRawLow K m n).map σ.toRingHom
  let B := (criticalSourceReciprocalLow K m n).map σ.toRingHom
  refine ⟨(A, B), ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _)
  · exact lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _)
  · apply (dvd_criticalLowProduct_sub_one_iff_mul_sub_one
      (X_pow_dvd_criticalObservationRawTail_map_normalClosure K m n)
      (X_pow_dvd_criticalObservationReciprocalTail_map_normalClosure K m n) A B).2
    exact criticalGeometricSheet_mapped_inverse_normalClosure K m n σ

/-- Distinct geometric sheets give distinct critical states already in the normal closure. -/
theorem criticalGeometricSheetToNormalFibre_injective
    (K : Type*) [Field K] (m n : ℕ) :
    Function.Injective (criticalGeometricSheetToNormalFibre K m n) := by
  intro σ τ hστ
  have hA : (criticalSourceRawLow K m n).map σ.toRingHom =
      (criticalSourceRawLow K m n).map τ.toRingHom :=
    congrArg (fun p => p.1.1) hστ
  apply AlgHom.ext
  intro x
  have hx : x ∈ IntermediateField.adjoin (criticalObservationField K m n)
      (Set.range (criticalSourceRaw K m n)) := by
    rw [criticalSourceRaw_adjoin_eq_top K m n]
    trivial
  exact IntermediateField.adjoin_induction
    (criticalObservationField K m n)
    (p := fun z _ => σ z = τ z)
    (fun z hz => by
      obtain ⟨j, rfl⟩ := hz
      by_cases hj : (j : ℕ) < m
      · have hc := congrArg (fun P : (criticalNormalClosure K m n)[X] =>
            P.coeff (j : ℕ)) hA
        simpa [criticalSourceRawLow, lowPolynomial_coeff, hj] using hc
      · have hjm : m ≤ (j : ℕ) := Nat.le_of_not_gt hj
        have hjn : (j : ℕ) - m < n := by omega
        let i : Fin n := ⟨(j : ℕ) - m, hjn⟩
        have hcoord : criticalSourceRaw K m n j =
            algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
              (criticalObservationRaw K m n i) := by
          apply Subtype.ext
          change criticalAmbientRaw K m n (j : ℕ) =
            criticalAmbientRaw K m n (m + (i : ℕ))
          congr 1
          dsimp [i]
          omega
        rw [hcoord, σ.commutes, τ.commutes])
    (fun z => by rw [σ.commutes, τ.commutes])
    (fun _ _ _ _ hz hw => by rw [map_add, map_add, hz, hw])
    (fun _ _ hz => by rw [map_inv₀, map_inv₀, hz])
    (fun _ _ _ _ hz hw => by rw [map_mul, map_mul, hz, hw]) hx

end

end GaloisForLFunctions.HTGeometry
