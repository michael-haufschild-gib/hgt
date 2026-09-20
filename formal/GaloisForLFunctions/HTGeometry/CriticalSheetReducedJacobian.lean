import GaloisForLFunctions.HTGeometry.CriticalSheetConormalVector
import GaloisForLFunctions.HTGeometry.HorizonConormalJacobianKernel
import GaloisForLFunctions.HTGeometry.CriticalSchurIntegralJacobian
import GaloisForLFunctions.HTGeometry.CriticalSchurCollisionSingular

/-!
# The reduced Jacobian of a singular sheet

The observation Jacobian of the corpus is literally the horizon Jacobian of the integral
reciprocal jet, and the horizon Jacobian is functorial in the coefficient ring.  So the reduced
observation Jacobian along a singular sheet is the horizon Jacobian of that sheet's reduced
reciprocal jet — the matrix whose kernel the collision tangents live in.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial IsLocalRing

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

/-- The horizon observation Jacobian is functorial in the coefficient ring. -/
theorem horizonObservationJacobian_map {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (Y : F[X]) (n m : ℕ) :
    (horizonObservationJacobian Y n m).map f
      = horizonObservationJacobian (Y.map f) n m := by
  classical
  refine Matrix.ext fun t s => ?_
  rcases s with s' | s'
  · show f (if _ then _ else _) = if _ then _ else _
    by_cases hle : ((finSumFinEquiv t : Fin (m + n)) : ℕ) ≤ n + (s' : ℕ)
    · rw [if_pos hle, if_pos hle, map_neg, ← Polynomial.map_mul, Polynomial.coeff_map]
    · rw [if_neg hle, if_neg hle, map_zero]
  · show f (if _ then _ else _) = if _ then _ else _
    by_cases ht : t = Sum.inr s'
    · rw [if_pos ht, if_pos ht, map_one]
    · rw [if_neg ht, if_neg ht, map_zero]

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The observation Jacobian is the horizon Jacobian of the integral reciprocal jet. -/
theorem criticalObservationJacobian_eq_horizon :
    criticalObservationJacobian K (m := m) (n := n)
      = horizonObservationJacobian (criticalSourceRecipPolynomialIntegral K
          (Fact.out : 0 < m) (Fact.out : 0 < n)) n m := by
  refine Matrix.ext fun t s => ?_
  rcases s with s' | s' <;> rfl

/-- The reduced reciprocal jet of a singular sheet is the image of the integral one. -/
theorem criticalSheet_recipPolynomialIntegral_map (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) :
    (criticalSourceRecipPolynomialIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n)).map
        (criticalSheetSourceSchurLift K σ hsing)
      = (criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2
        + criticalNormalClosureSchurReciprocalTailIntegral K (Fact.out : 0 < m)
            (Fact.out : 0 < n) := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  refine Polynomial.map_injective
    ((criticalNormalClosureSchurValuationSubring K hfm
      hfn).subtype) Subtype.val_injective ?_
  rw [Polynomial.map_map, criticalSheetSourceSchurLift_comp, ← Polynomial.map_map,
    map_criticalSourceRecipPolynomialIntegral, Polynomial.map_add,
    map_criticalNormalClosureSchurReciprocalTailIntegral]
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

/-- **The reduced observation Jacobian at a singular sheet is the horizon Jacobian of its reduced
reciprocal jet.** -/
theorem criticalSheet_jacobian_eq_horizon (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))) :
    (criticalObservationJacobian K (m := m) (n := n)).map
        ((IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))).comp (criticalSheetSourceSchurLift K σ hsing))
      = horizonObservationJacobian
          (((criticalGeometricSheetToSchurFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ).1.2
            + criticalNormalClosureSchurReciprocalTailIntegral K (Fact.out : 0 < m)
              (Fact.out : 0 < n)).map
            (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K
              (Fact.out : 0 < m) (Fact.out : 0 < n)))) n m := by
  simp only [RingHom.coe_comp, ← Matrix.map_map, criticalObservationJacobian_eq_horizon K,
    horizonObservationJacobian_map, horizonObservationJacobian_map,
    criticalSheet_recipPolynomialIntegral_map K σ hsing]


end

end GaloisForLFunctions.HTGeometry
