import GaloisForLFunctions.RHTower.IntegralCurvedTateFormationPropernessIndex
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceShellReplicaWardDoubleProperness
import GaloisForLFunctions.HTGeometry.BoundedFormationRecoveryRigidity

/-!
# Integral curved Tate coherent-primitive index

Finite exactness becomes substantive only when the boundary primitives themselves form one
compatible history. For the literal fixed-tail Roos tower, such a history is unique when it exists:
after forgetting summability it must be the negative family of arithmetic tails. Its existence is
equivalent to vanishing of the pre-divisor derived class, the integral curved Tate determinant, and
the formation-completion anomaly.

Thus the evaluated Laurent determinant is the obstruction index of a proof-carrying completion,
not merely of Boolean boundary membership. No RH, critical-line, positivity, compactness, or
integral-landing premise is used.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

open PreDivisorReflectionDefectStabilization
open HedenmalmThetaSource

/-- Proof-carrying completion fibre of the pre-divisor transverse boundary. -/
def PreDivisorTransverseCoherentPrimitive (s : ℂ) : Type :=
  {h : ∀ _n : ℕ, routeRSummableSequenceIdeal //
    inverseDifference (fun _ : ℕ => routeRSummableSequenceIdeal)
        routeRTailRoosRestrictedBond h =
      routeRDiagonalMismatchInIdeal
        (routeRPrimeGammaCriticalWallSequence (preDivisorCenteredRate s))}

/-- Any coherent primitive is the literal negative-tail family after forgetting summability. -/
theorem preDivisorTransverseCoherentPrimitive_coe_eq
    (s : ℂ) (h : PreDivisorTransverseCoherentPrimitive s) :
    (fun n => (h.1 n : RouteRTraceSequence)) =
      fun n => -routeRTail
        (routeRPrimeGammaCriticalWallSequence (preDivisorCenteredRate s)) n := by
  apply routeRTailRoos_primitive_unique
  funext n
  exact congrArg Subtype.val (congrFun h.2 n)

/-- The proof-carrying completion fibre has at most one point. -/
theorem preDivisorTransverseCoherentPrimitive_subsingleton (s : ℂ) :
    Subsingleton (PreDivisorTransverseCoherentPrimitive s) := by
  constructor
  intro x y
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact congrFun (preDivisorTransverseCoherentPrimitive_coe_eq s x) n |>.trans
    (congrFun (preDivisorTransverseCoherentPrimitive_coe_eq s y) n).symm

/-- The proof-carrying completion fibre is inhabited exactly when the Roos class vanishes. -/
theorem nonempty_preDivisorTransverseCoherentPrimitive_iff
    (s : ℂ) :
    Nonempty (PreDivisorTransverseCoherentPrimitive s) ↔
      preDivisorTransverseDerivedCompletionClass s = 0 := by
  rw [preDivisorTransverseDerivedCompletionClass_eq_criticalWall,
    routeRDiagonalTailRoosClass, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨h⟩
    exact ⟨h.1, h.2⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨h, hh⟩⟩

/-- On an Xi fibre, coherent primitive existence is the zero integral-index phase. -/
theorem nonempty_preDivisorTransverseCoherentPrimitive_iff_index_zero
    (q : XiZeroCopy) :
    Nonempty (PreDivisorTransverseCoherentPrimitive (q.1 : ℂ)) ↔
      deningerXiIntegralCofinalFormationIndex q = 0 := by
  rw [nonempty_preDivisorTransverseCoherentPrimitive_iff,
    preDivisorTransverseDerivedCompletionClass_eq_zero_iff,
    deningerXiIntegralCofinalFormationIndex_eq_zero_iff]

/-- Actual primitive coherence, marked convergence, and compact recurrence are one phase. -/
theorem deningerXiCoherentPrimitiveCompletion_fusion
    (q : XiZeroCopy) :
    (Nonempty (PreDivisorTransverseCoherentPrimitive (q.1 : ℂ)) ↔
      deningerXiIntegralCofinalFormationIndex q = 0) ∧
    (Nonempty (PreDivisorTransverseCoherentPrimitive (q.1 : ℂ)) ↔
      Tendsto (fun n => deningerGammaSixXiFiniteFormationState q n) atTop
        (nhds (deningerGammaSixXiPhysicalFormationState q))) ∧
    (Nonempty (PreDivisorTransverseCoherentPrimitive (q.1 : ℂ)) ↔
      ThetaXiPrimeModularCompactRecurrenceDescent q) := by
  constructor
  · exact nonempty_preDivisorTransverseCoherentPrimitive_iff_index_zero q
  constructor
  · rw [deningerGammaSixXiFiniteFormationState_tendsto_iff_index_zero]
    exact nonempty_preDivisorTransverseCoherentPrimitive_iff_index_zero q
  · rw [thetaXiPrimeModularCompactRecurrenceDescent_iff_index_zero]
    exact nonempty_preDivisorTransverseCoherentPrimitive_iff_index_zero q

/-- Coherent completion is exactly closability of the orthogonally replicated theta recovery. -/
theorem nonempty_preDivisorTransverseCoherentPrimitive_iff_shellReplica_closable
    (q : XiZeroCopy) :
    Nonempty (PreDivisorTransverseCoherentPrimitive (q.1 : ℂ)) ↔
      ThetaXiQuadraticGhostOrbitClosable q.1 := by
  rw [nonempty_preDivisorTransverseCoherentPrimitive_iff_index_zero,
    deningerXiIntegralCofinalFormationIndex_eq_zero_iff,
    thetaXiQuadraticGhostOrbitClosable_iff]

/-- Any common two-sided bounded realization of shell recovery supplies the unique coherent
completion primitive. -/
theorem nonempty_preDivisorTransverseCoherentPrimitive_of_bounded_shell_factorization
    (q : XiZeroCopy)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (load : lp (fun _ : ℕ => Lp ℂ 2 unitIntervalMeasure) 2 →L[ℝ] F)
    (recover : F →L[ℝ] Lp ℂ 2 unitIntervalMeasure)
    (hfactor : ∀ x : ℕ →₀ Lp ℂ 2 unitIntervalMeasure,
      recover (load ((codiagEmbed (H := Lp ℂ 2 unitIntervalMeasure)).restrictScalars ℝ x)) =
        ((codiag (H := Lp ℂ 2 unitIntervalMeasure)
          (thetaXiQuadraticGhostOrbitWeight q.1)).restrictScalars ℝ) x) :
    Nonempty (PreDivisorTransverseCoherentPrimitive (q.1 : ℂ)) := by
  apply (nonempty_preDivisorTransverseCoherentPrimitive_iff_shellReplica_closable q).2
  exact GaloisForLFunctions.HTGeometry.isSequentiallyClosableBetween_of_bounded_factorization
    ((codiag (H := Lp ℂ 2 unitIntervalMeasure)
      (thetaXiQuadraticGhostOrbitWeight q.1)).restrictScalars ℝ)
    ((codiagEmbed (H := Lp ℂ 2 unitIntervalMeasure)).restrictScalars ℝ)
    load recover hfactor

/-- Universal contractibility of the actual primitive fibres is exactly RH. -/
theorem forall_nonempty_preDivisorTransverseCoherentPrimitive_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      Nonempty (PreDivisorTransverseCoherentPrimitive (q.1 : ℂ))) ↔
      RiemannHypothesis := by
  rw [← forall_deningerXiIntegralCofinalFormationIndex_eq_zero_iff_riemannHypothesis]
  exact forall_congr' fun q =>
    nonempty_preDivisorTransverseCoherentPrimitive_iff_index_zero q

end

end RHTower
