import GaloisForLFunctions.RHTower.RouteRSummableHadamardConstitutiveCoronaEmbedding
import GaloisForLFunctions.RHTower.RouteRCompletionMigrationDefect

/-!
# Summable Hadamard corona inside fixed-tail Roos homology

The bounded-tail summable corona and Route R's diagonal tail--Roos obstruction use the same
coefficient equivalence relation: two bounded sequences agree precisely when their difference is
absolutely summable.  This file makes that identification coefficient-faithful.

The resulting map is linear and injective.  It sends the universal nonzero square-zero harmonic
class to the universal nonzero diagonal tail--Roos class, and sends every oriented critical-wall
corona class to the corresponding explicit critical-wall tail obstruction.  Multiplicative
nilpotence and additive completion escape are therefore two structures on one carrier, not merely
two tests with the same vanishing locus.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.BoundaryMigration

/-- Forget boundedness while retaining every enumerated coefficient. -/
def routeRBoundedTraceToTraceSequence :
    RouteRBoundedTraceSequence →ₗ[ℂ] RouteRTraceSequence where
  toFun a n := a n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Additivity of the diagonal class, inherited from the canonical mismatch linear map. -/
theorem routeRDiagonalTailRoosClass_add
    (a b : RouteRTraceSequence) :
    routeRDiagonalTailRoosClass (a + b) =
      routeRDiagonalTailRoosClass a + routeRDiagonalTailRoosClass b := by
  change Submodule.Quotient.mk (routeRDiagonalMismatchLinear (a + b)) =
    Submodule.Quotient.mk (routeRDiagonalMismatchLinear a) +
      Submodule.Quotient.mk (routeRDiagonalMismatchLinear b)
  simp

/-- Complex linearity of the diagonal class, inherited from the canonical mismatch linear map. -/
theorem routeRDiagonalTailRoosClass_smul
    (c : ℂ) (a : RouteRTraceSequence) :
    routeRDiagonalTailRoosClass (c • a) =
      c • routeRDiagonalTailRoosClass a := by
  change Submodule.Quotient.mk (routeRDiagonalMismatchLinear (c • a)) =
    c • Submodule.Quotient.mk (routeRDiagonalMismatchLinear a)
  simp

/-- Raw quotient map from bounded tails modulo `ell^(1 : ℕ)` to fixed-tail Roos homology. -/
private def routeRSummableHadamardToTailRoosFun
    (x : RouteRSummableHadamardCorona) :
    DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
      routeRTailRoosRestrictedBond :=
  Quotient.map
    (fun a => routeRDiagonalMismatchLinear (routeRBoundedTraceToTraceSequence a))
    (by
      intro a b hab
      apply Quotient.exact
      apply (routeRDiagonalTailRoosClass_eq_iff_summable_sub _ _).2
      have hmem : a - b ∈ routeRSummableBoundedTailIdeal :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 (Quotient.sound' hab)
      change Summable (fun n : ℕ => ‖(a - b) n‖) at hmem
      have hnorm : Summable (fun n : ℕ =>
          ‖routeRBoundedTraceToTraceSequence a n -
            routeRBoundedTraceToTraceSequence b n‖) := by
        simpa [routeRBoundedTraceToTraceSequence] using hmem
      exact summable_norm_iff.mp hnorm) x

/-- Coefficient-faithful linear realization of the summable Hadamard corona in the diagonal
fixed-tail derived obstruction space. -/
def routeRSummableHadamardToTailRoos :
    RouteRSummableHadamardCorona →ₗ[ℂ]
      DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
        routeRTailRoosRestrictedBond where
  toFun := routeRSummableHadamardToTailRoosFun
  map_add' x y := by
    induction x using Quotient.inductionOn' with
    | _ a =>
      induction y using Quotient.inductionOn' with
      | _ b =>
        exact routeRDiagonalTailRoosClass_add _ _
  map_smul' c x := by
    induction x using Quotient.inductionOn' with
    | _ a =>
      exact routeRDiagonalTailRoosClass_smul c _

@[simp]
theorem routeRSummableHadamardToTailRoos_mk
    (a : RouteRBoundedTraceSequence) :
    routeRSummableHadamardToTailRoos
        (Quotient.mk'' a : RouteRSummableHadamardCorona) =
      routeRDiagonalTailRoosClass (routeRBoundedTraceToTraceSequence a) := by
  rfl

/-- Passing from the bounded summable corona to tail homology loses no coefficient class. -/
theorem routeRSummableHadamardToTailRoos_injective :
    Function.Injective routeRSummableHadamardToTailRoos := by
  have hker : ∀ x : RouteRSummableHadamardCorona,
      routeRSummableHadamardToTailRoos x = 0 → x = 0 := by
    intro x
    induction x using Quotient.inductionOn' with
    | _ a =>
      intro hzero
      rw [routeRSummableHadamardToTailRoos_mk] at hzero
      have hsum : Summable (routeRBoundedTraceToTraceSequence a) :=
        (routeRDiagonalTailRoosClass_eq_zero_iff_summable _).1 hzero
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change Summable (fun n : ℕ => ‖a n‖)
      exact summable_norm_iff.mpr hsum
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker (x - y)
  rw [map_sub, hxy, sub_self]

/-- The universal square-zero harmonic corona carrier is exactly the universal nonzero tail--Roos
carrier after forgetting multiplication. -/
theorem routeRSummableHadamardToTailRoos_harmonic :
    routeRSummableHadamardToTailRoos
        (routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence) =
      routeRDiagonalTailRoosClass routeRPrimeHarmonicTraceSequence := by
  change routeRSummableHadamardToTailRoos
    (Quotient.mk'' routeRPrimeHarmonicBoundedTraceSequence) = _
  rw [routeRSummableHadamardToTailRoos_mk]
  rfl

/-- The oriented multiplicative critical-wall class maps coefficient-for-coefficient to the
explicit additive critical-wall completion obstruction. -/
theorem routeRSummableHadamardToTailRoos_criticalWall (t : ℝ) :
    routeRSummableHadamardToTailRoos
        (routeRPrimeGammaCriticalWallSummableHadamardClass t) =
      routeRDiagonalTailRoosClass (routeRPrimeGammaCriticalWallSequence t) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [routeRPrimeGammaCriticalWallSummableHadamardClass, if_neg (not_lt.mpr (le_of_lt ht)),
      if_pos ht, routeRSummableHadamardToTailRoos_harmonic,
      routeRPrimeGammaCriticalWallTailRoosClass_eq_harmonic_of_neg ht]
  · simpa [routeRPrimeGammaCriticalWallSummableHadamardClass] using
      routeRPrimeGammaCriticalWallTailRoosClass_eq_zero.symm
  · rw [routeRPrimeGammaCriticalWallSummableHadamardClass, if_pos ht, map_neg,
      routeRSummableHadamardToTailRoos_harmonic,
      routeRPrimeGammaCriticalWallTailRoosClass_eq_neg_harmonic_of_pos ht]

end

end RHTower
