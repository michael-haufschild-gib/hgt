import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.HyperellipticFixedPoints
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.OrientationDeterminant
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.TruncatedTraceComparison

/-!
# Square-root cancellation of actual hyperelliptic orientation counts

The two independent counts are stable orbits of actual curve point tuples,
with and without an orientation label. Their discrepancy is a coefficient
of the actual Frobenius permutation determinant. Fixed-field descent and
finite-degree Newton comparison identify it with the signed reciprocal
curve-zeta coefficient. The derived Stepanov theorem supplies the root
bound, so no trace formula or cancellation bound remains as an input.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset Equiv Matrix Polynomial MulAction
open GaloisForLFunctions.RHTower.Hyperelliptic
open GaloisForLFunctions.ArithmeticCompensationTheory

/-- The actual integral orientation determinant maps to the complex permutation determinant. -/
theorem matrixOrientationPolynomial_perm {I : Type*} [Fintype I] (φ : Perm I) :
    letI : DecidableEq I := Classical.decEq I
    matrixOrientationPolynomial (φ.permMatrix ℂ) =
      (pointOrientationPolynomial φ).map (Int.castRingHom ℂ) := by
  classical
  unfold matrixOrientationPolynomial pointOrientationPolynomial
  change Matrix.det _ = (Polynomial.mapRingHom (Int.castRingHom ℂ)) (Matrix.det _)
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    by_cases hφ : φ i = i <;>
      simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Equiv.toPEquiv_apply, hφ]
  · by_cases hφ : φ i = j <;>
      simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Equiv.toPEquiv_apply, hij, hφ]

variable (F : Type*) [Field F] [Fintype F]

/-- Actual stable orbits of hyperelliptic point tuples with the sign orientation label. -/
def hyperellipticOrientationCoverCount (f : F[X]) (n : ℕ) : ℕ :=
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  letI : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  let E := FiniteField.Extension F (ringChar F) n.factorial
  letI : Fintype E := Fintype.ofFinite E
  letI : MulAction (Perm (Fin n)) (Fin n → HyperellipticPoints f E) :=
    permutationTupleAction (HyperellipticPoints f E) (Perm (Fin n)) (Fin n)
  orientationFixedOrbitCount Perm.sign (pointTupleMap n (hyperellipticFrobenius F E f))

/-- Actual ordinary stable tuple-orbit count, retaining all collisions. -/
def hyperellipticTupleOrbitCount (f : F[X]) (n : ℕ) : ℕ :=
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  letI : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  let E := FiniteField.Extension F (ringChar F) n.factorial
  letI : Fintype E := Fintype.ofFinite E
  letI : MulAction (Perm (Fin n)) (Fin n → HyperellipticPoints f E) :=
    permutationTupleAction (HyperellipticPoints f E) (Perm (Fin n)) (Fin n)
  (equivariantFixedOrbits (pointTupleMap n (hyperellipticFrobenius F E f))).card

/-- The independent count discrepancy is the signed reciprocal coefficient of the actual curve. -/
theorem hyperellipticOrientationCover_sub (hF : ringChar F ≠ 2) {f : F[X]}
    (hodd : Odd f.natDegree) (n : ℕ) :
    (hyperellipticOrientationCoverCount F f n : ℂ) - hyperellipticTupleOrbitCount F f n =
      PowerSeries.coeff n (PowerSeries.rescale (-1)
        (curveZinv (Fintype.card F) (rootEnum (lRoots f)))) := by
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  letI : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  let E := FiniteField.Extension F (ringChar F) n.factorial
  letI : Fintype E := Fintype.ofFinite E
  let φ := hyperellipticFrobenius F E f
  letI : DecidableEq (HyperellipticPoints f E) := Classical.decEq _
  letI : MulAction (Perm (Fin n)) (Fin n → HyperellipticPoints f E) :=
    permutationTupleAction (HyperellipticPoints f E) (Perm (Fin n)) (Fin n)
  have htr (d : ℕ) (hd : 0 < d) (hdn : d ≤ n) :
      ((φ.permMatrix ℂ) ^ d).trace = (Fintype.card F : ℂ) ^ d + 1 -
        ∑ i, rootEnum (lRoots f) i ^ d := by
    letI : NeZero d := ⟨hd.ne'⟩
    rw [permutation_power_trace]
    have h := hyperelliptic_factorial_fixed_count hF hodd n d hdn
    rw [← univ_map_rootEnum (lRoots f), Multiset.map_map,
      ← Finset.sum_eq_multiset_sum] at h
    exact h
  have he := matrixOrientationPolynomial_coeff_curveZinv (φ.permMatrix ℂ)
    (rootEnum (lRoots f)) (Fintype.card F) n htr
  rw [matrixOrientationPolynomial_perm, Polynomial.coeff_map] at he
  have hc := congrArg (fun z : ℤ => (z : ℂ)) (pointTuple_orientationCount_eq_coeff φ n)
  push_cast at hc
  change (orientationFixedOrbitCount Perm.sign (pointTupleMap n φ) : ℂ) -
    (equivariantFixedOrbits (pointTupleMap n φ)).card = _
  exact hc.trans he

/-- Actual hyperelliptic orientation counts cancel at the square-root scale with a degree loss. -/
theorem hyperellipticOrientationCover_bound (hF : ringChar F ≠ 2) {f : F[X]}
    (hsq : Squarefree f) (hodd : Odd f.natDegree) (n : ℕ) :
    |(hyperellipticOrientationCoverCount F f n : ℝ) - hyperellipticTupleOrbitCount F f n| ≤
      (2 * (Fintype.card F : ℝ) + 2) * ((n : ℝ) + 1) ^ (f.natDegree - 1) *
        (Real.sqrt (Fintype.card F)) ^ n := by
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card F))
  have ht : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr (by simpa only [one_pow] using hq)
  have hbound := norm_coeff_signed_curveZinv_le (Fintype.card F) (rootEnum (lRoots f)) ht
    (norm_rootEnum_le (p := ringChar F) hF hsq hodd) n
  have hm : (lRoots f).toList.length = f.natDegree - 1 := by
    rw [Multiset.length_toList, card_lRoots f hodd.pos]
  have hC : ‖(hyperellipticOrientationCoverCount F f n : ℂ) -
      hyperellipticTupleOrbitCount F f n‖ =
      |(hyperellipticOrientationCoverCount F f n : ℝ) - hyperellipticTupleOrbitCount F f n| := by
    rw [show (hyperellipticOrientationCoverCount F f n : ℂ) - hyperellipticTupleOrbitCount F f n =
      (((hyperellipticOrientationCoverCount F f n : ℝ) - hyperellipticTupleOrbitCount F f n : ℝ) : ℂ)
      by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
  rw [← hC, hyperellipticOrientationCover_sub F hF hodd]
  calc
    _ ≤ _ := hbound
    _ = _ := by rw [hm]

#print axioms matrixOrientationPolynomial_perm
#print axioms hyperellipticOrientationCover_sub
#print axioms hyperellipticOrientationCover_bound
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
