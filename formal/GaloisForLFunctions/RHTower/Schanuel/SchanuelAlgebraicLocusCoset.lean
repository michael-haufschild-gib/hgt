import GaloisForLFunctions.HTGeometry.AffineExponentialAlgebraicLocusKaehler
import GaloisForLFunctions.RHTower.Schanuel.SchanuelInvariantKaehlerForm

/-!
# Algebraic coset supplied by a numerical Schanuel-defect relation

A numerical algebraic-coefficient relation among Schanuel defects determines a genuine mixed
invariant Kähler form.  Principal-open generic propagation supplies a coordinatewise algebraic
point on the exact algebraic locus such that the form vanishes both there and at the translated
original exponential point.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open AffineExponentialPointEvaluation
open AffineExponentialPointClosure
open AffineExponentialInvariantKaehler
open AffineExponentialAlgebraicLocusSubgroup
open AffineExponentialAlgebraicLocusKaehler

noncomputable section

theorem exists_schanuel_algebraic_coset_subgroup_pullback_eq_zero
    {n : ℕ} (x : Fin n → ℂ) (c : Fin n → algebraicClosure ℚ ℂ)
    (hrelation : ∑ i, (c i : ℂ) • schanuelDefect (x i) = 0) :
    ∃ q : Point ℂ n,
      (∀ i, IsAlgebraic ℚ (additivePart q i)) ∧
      (∀ i, IsAlgebraic ℚ (torusPart q i : ℂ)) ∧
      q ∈ algebraicLocus (schanuelExponentialPoint x) ∧
      pointKaehlerMap (algebraicClosure ℚ ℂ) q
        (mixedInvariantKaehlerVector (algebraicClosure ℚ ℂ)
          c (fun i => -c i)) = 0 ∧
      pointKaehlerMap (algebraicClosure ℚ ℂ)
        (schanuelExponentialPoint x * q⁻¹)
        (mixedInvariantKaehlerVector (algebraicClosure ℚ ℂ)
          c (fun i => -c i)) = 0 ∧
      schanuelExponentialPoint x * q⁻¹ ∈
        zeroLocus (algebraicLocusSubgroupIdeal (schanuelExponentialPoint x) q) := by
  exact exists_algebraic_coset_subgroup_mixedInvariant_pullback_eq_zero
    (schanuelExponentialPoint x) c (fun i => -c i)
    (pointKaehlerMap_schanuelInvariantVector_eq_zero_of_relation x c hrelation)

end

end GaloisForLFunctions.RHTower
