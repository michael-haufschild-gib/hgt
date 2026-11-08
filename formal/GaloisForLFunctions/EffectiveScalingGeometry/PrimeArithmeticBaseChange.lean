import GaloisForLFunctions.EffectiveScalingGeometry.PrimeHomologyBaseChange
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeArithmeticPersistence

/-!
# Coefficient compatibility of the arithmetic prime barcode

The natural odd-squarefree barcode of actual augmented homology commutes with
canonical integer coefficient extension. Every coefficient at an interval
label is the image of its integer coefficient in the target ring. This follows
from the canonical tensor comparison and the coefficient-preserving arithmetic
reindexing, including the empty interval.
-/

noncomputable section
open CategoryTheory RHTower
open scoped TensorProduct
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Canonical coefficient extension preserves every surviving integral coordinate. -/
theorem primeIntegralHomologyMap_coordinate (k N : ℕ)
    (x : (primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N)
    (s : primeCriticalFaces k N) :
    primeHomologyCoordinateEquiv R k N (primeIntegralHomologyMap R k N x) s =
      (primeHomologyCoordinateEquiv ℤ k N x s : R) := by
  rw [← primeHomologyBaseChange_one_tmul]
  rw [primeHomologyCoordinateBaseChange_tmul]
  simp only [zsmul_eq_mul,mul_one]

/-- The original barcode comparison commutes with canonical coefficient extension. -/
theorem primeHomologyCriticalIso_integral (k N : ℕ)
    (x : (primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N)
    (s : Set.powersetCard Nat.Primes k) :
    (((primeHomologyCriticalIso R k).app N).hom (primeIntegralHomologyMap R k N x)).val s =
      ((((primeHomologyCriticalIso ℤ k).app N).hom x).val s : R) := by
  by_cases hs : s ∈ primeCriticalFaces k N
  · change primeHomologyCoordinateEquiv R k N (primeIntegralHomologyMap R k N x) ⟨s,hs⟩ =
      (primeHomologyCoordinateEquiv ℤ k N x ⟨s,hs⟩ : R)
    exact primeIntegralHomologyMap_coordinate R k N x ⟨s,hs⟩
  · have hR := (Finsupp.mem_supported' R _).mp
      (((primeHomologyCriticalIso R k).app N).hom (primeIntegralHomologyMap R k N x)).property s hs
    have hZ := (Finsupp.mem_supported' ℤ _).mp
      (((primeHomologyCriticalIso ℤ k).app N).hom x).property s hs
    rw [hR,hZ,Int.cast_zero]

/-- Each odd-squarefree interval carries the canonical image of its integer coefficient. -/
theorem primeHomologySquarefreeIntervalIso_integral (k N : ℕ)
    (x : (primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N)
    (m : SquarefreeDegree k) :
    (((primeHomologySquarefreeIntervalIso R k).app N).hom (primeIntegralHomologyMap R k N x)).val m =
      ((((primeHomologySquarefreeIntervalIso ℤ k).app N).hom x).val m : R) := by
  change (primeCriticalArithmeticEquiv R k N
    (((primeHomologyCriticalIso R k).app N).hom (primeIntegralHomologyMap R k N x))).val m =
      ((primeCriticalArithmeticEquiv ℤ k N (((primeHomologyCriticalIso ℤ k).app N).hom x)).val m : R)
  rw [primeCriticalArithmeticEquiv_apply,primeCriticalArithmeticEquiv_apply]
  exact primeHomologyCriticalIso_integral R k N x ((primeFaceSquarefreeEquiv k).symm m)

#print axioms primeHomologySquarefreeIntervalIso_integral
end GaloisForLFunctions.EffectiveScalingGeometry
