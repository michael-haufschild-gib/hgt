import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.EllipticStableSubsets
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.TupleOrientationCounts

/-!
# Square-root discrepancy of actual elliptic orientation quotients

The two counts are Frobenius-stable orbits of actual elliptic point tuples,
with and without an orientation label. Signed transporter counting reduces
their difference to the intrinsic signs of stable point configurations.
The actual divisor comparison and curve root bound then give square-root
scale discrepancy. Collisions and both low-degree labels are retained.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset Equiv MulAction
open GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

variable (E : Type*) [Field E] [Algebra Constants E] [Fintype E]

/-- Arithmetic stability is exactly invariance under the actual point permutation. -/
theorem ellipticPointSubsetInvariant_iff (T : Finset (Points E)) :
    PointSubsetInvariant (ellipticPointFrobenius E) T ↔ EllipticPointStable E T := by
  constructor
  · intro h p hp
    rw [← ellipticPointFrobenius_apply]
    exact (h p).mpr hp
  · intro h
    exact ellipticPointStable_mem_iff E h

/-- The general subset orientation agrees with the actual geometric Frobenius sign. -/
theorem elliptic_pointSubsetOrientation (T : Finset (Points E)) (hT : EllipticPointStable E T) :
    pointSubsetOrientation (ellipticPointFrobenius E) T =
      (Perm.sign (ellipticStablePointPerm E T hT) : ℤ) := by
  rw [pointSubsetOrientation, dif_pos ((ellipticPointSubsetInvariant_iff E T).mpr hT)]
  congr 3
  exact Subsingleton.elim _ _

private def stableCardSubsetEquiv (n : ℕ) :
    {T : {T : Finset (Points E) // T.card = n} // EllipticPointStable E T.val} ≃
      {T : Finset (Points E) // EllipticPointStable E T ∧ T.card = n} where
  toFun T := ⟨T.val.val, T.property, T.val.property⟩
  invFun T := ⟨⟨T.val, T.property.2⟩, T.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Moving supports contribute zero; stable supports contribute their actual orientation sign. -/
theorem elliptic_sum_pointSubsetOrientation (n : ℕ) :
    (∑ T : {T : Finset (Points E) // T.card = n},
      pointSubsetOrientation (ellipticPointFrobenius E) T.val) =
      ∑ T : {T : Finset (Points E) // EllipticPointStable E T ∧ T.card = n},
        (Perm.sign (ellipticStablePointPerm E T.val T.property.1) : ℤ) := by
  let w := fun T : {T : Finset (Points E) // T.card = n} =>
    pointSubsetOrientation (ellipticPointFrobenius E) T.val
  calc
    _ = ∑ T ∈ univ.filter (fun T : {T : Finset (Points E) // T.card = n} =>
        EllipticPointStable E T.val), w T := by
      symm
      apply sum_subset (filter_subset _ _)
      intro T _ hT
      have hn : ¬EllipticPointStable E T.val := by
        simpa only [mem_filter, mem_univ, true_and] using hT
      change pointSubsetOrientation (ellipticPointFrobenius E) T.val = 0
      exact dif_neg (fun h => hn ((ellipticPointSubsetInvariant_iff E T.val).mp h))
    _ = ∑ T : {T : {T : Finset (Points E) // T.card = n} // EllipticPointStable E T.val},
        w T.val := sum_subtype _ (fun _ => by simp) _
    _ = _ := Fintype.sum_equiv (stableCardSubsetEquiv E n) _ _
      (fun T => elliptic_pointSubsetOrientation E T.val.val T.property)

/-- Actual Frobenius-stable orbits in the orientation cover of point tuples. -/
def arithmeticEllipticOrientationCoverCount (n : ℕ) : ℕ :=
  let E := FiniteField.Extension Constants 3 (Fintype.card (Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  letI : MulAction (Perm (Fin n)) (Fin n → Points E) :=
    permutationTupleAction (Points E) (Perm (Fin n)) (Fin n)
  orientationFixedOrbitCount Perm.sign (pointTupleMap n (ellipticPointFrobenius E))

/-- Actual ordinary Frobenius-stable orbits of point tuples, retaining collisions. -/
def arithmeticEllipticTupleOrbitCount (n : ℕ) : ℕ :=
  let E := FiniteField.Extension Constants 3 (Fintype.card (Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  letI : MulAction (Perm (Fin n)) (Fin n → Points E) :=
    permutationTupleAction (Points E) (Perm (Fin n)) (Fin n)
  (equivariantFixedOrbits (pointTupleMap n (ellipticPointFrobenius E))).card

/-- The two original arithmetic quotient counts differ by the actual geometric orientation sum. -/
theorem arithmeticEllipticOrientationCover_sub (n : ℕ) :
    (arithmeticEllipticOrientationCoverCount n : ℤ) - arithmeticEllipticTupleOrbitCount n =
      arithmeticEllipticStableOrientationSum n := by
  let E := FiniteField.Extension Constants 3 (Fintype.card (Perm (Fin n)))
  letI : Fintype E := Fintype.ofFinite E
  letI : MulAction (Perm (Fin n)) (Fin n → Points E) :=
    permutationTupleAction (Points E) (Perm (Fin n)) (Fin n)
  change (orientationFixedOrbitCount Perm.sign (pointTupleMap n (ellipticPointFrobenius E)) : ℤ) -
    (equivariantFixedOrbits (pointTupleMap n (ellipticPointFrobenius E))).card = _
  rw [pointTuple_orientationCount_sub, elliptic_sum_pointSubsetOrientation]
  rfl

/-- The arithmetic quotient discrepancy has the exact signed divisor coefficient, with its degree sign. -/
theorem arithmeticEllipticOrientationCover_eq_signedDivisors (n : ℕ) :
    (arithmeticEllipticOrientationCoverCount n : ℤ) - arithmeticEllipticTupleOrbitCount n =
      (-1 : ℤ) ^ n * ((ellipticEvenDivisorCount n : ℤ) - ellipticOddDivisorCount n) :=
  (arithmeticEllipticOrientationCover_sub n).trans (arithmeticEllipticStableOrientationSum_eq n)

/-- Actual orientation-cover counts have square-root-scale discrepancy, with all curve inputs proved. -/
theorem arithmeticEllipticOrientationCover_bound (n : ℕ) :
    |(arithmeticEllipticOrientationCoverCount n : ℝ) - arithmeticEllipticTupleOrbitCount n| ≤
      8 * ((n : ℝ) + 1) ^ 2 * (Real.sqrt 3) ^ n := by
  have he := congrArg (fun z : ℤ => (z : ℝ)) (arithmeticEllipticOrientationCover_sub n)
  push_cast at he
  rw [he]
  exact arithmeticEllipticStableOrientationSum_bound n

#print axioms ellipticPointSubsetInvariant_iff
#print axioms elliptic_sum_pointSubsetOrientation
#print axioms arithmeticEllipticOrientationCover_sub
#print axioms arithmeticEllipticOrientationCover_eq_signedDivisors
#print axioms arithmeticEllipticOrientationCover_bound
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
