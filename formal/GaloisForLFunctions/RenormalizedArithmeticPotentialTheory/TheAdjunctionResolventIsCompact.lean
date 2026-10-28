import GaloisForLFunctions.HTGeometry.ClosedEigenbasisPositiveInverse
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveOperatorHasTheAdjunctionEigenbasis

/-!
# The shifted arithmetic adjunction operator has a compact inverse

Adding one minus Euler's constant makes the actual operator strictly positive.
Its inverse multiplies each arithmetic excitation by the reciprocal of one plus
logarithmic degree and tame different; these reciprocals vanish off finite sets.
-/

noncomputable section

open scoped Classical InnerProductSpace LinearPMap

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry ArithmeticIntersectionTheory

/-- The positive shift of the actual finite-sieve operator. -/
def shiftedSieveAdjunctionOperator (Q : Finset Nat.Primes) :
    SieveClassL2 Q →ₗ.[ℂ] SieveClassL2 Q :=
  (((1 - Real.eulerMascheroniConstant : ℝ) : ℂ) •
    (1 : SieveClassL2 Q →L[ℂ] SieveClassL2 Q)).toLinearMap +ᵥ sieveAdjunctionOperator Q

theorem shiftedSieveAdjunctionOperator_isClosed (Q : Finset Nat.Primes) :
    (shiftedSieveAdjunctionOperator Q).IsClosed :=
  LinearPMap.IsClosed.continuousLinearMap_vadd (sieveAdjunctionOperator_isClosed Q) _

theorem shiftedSieveAdjunctionOperator_formalSelfAdjoint (Q : Finset Nat.Primes) :
    (shiftedSieveAdjunctionOperator Q).IsFormalAdjoint (shiftedSieveAdjunctionOperator Q) := by
  intro x y
  let xA : (sieveAdjunctionOperator Q).domain := ⟨(x : SieveClassL2 Q), x.property⟩
  let yA : (sieveAdjunctionOperator Q).domain := ⟨(y : SieveClassL2 Q), y.property⟩
  change inner ℂ ((((1 - Real.eulerMascheroniConstant : ℝ) : ℂ) • (x : SieveClassL2 Q)) +
      sieveAdjunctionOperator Q xA) (y : SieveClassL2 Q) =
    inner ℂ (x : SieveClassL2 Q)
      ((((1 - Real.eulerMascheroniConstant : ℝ) : ℂ) • (y : SieveClassL2 Q)) +
        sieveAdjunctionOperator Q yA)
  rw [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => ((1 - Real.eulerMascheroniConstant : ℝ) : ℂ) *
    inner ℂ (x : SieveClassL2 Q) (y : SieveClassL2 Q) + z)
      (sieveAdjunctionOperator_formalSelfAdjoint Q xA yA)

theorem sieveAdjunctionBasis_mem_shifted_domain (Q : Finset Nat.Primes) (m : SieveClass Q) :
    sieveAdjunctionBasis Q m ∈ (shiftedSieveAdjunctionOperator Q).domain :=
  sieveAdjunctionBasis_mem_domain Q m

theorem shiftedSieveAdjunctionOperator_basis (Q : Finset Nat.Primes) (m : SieveClass Q) :
    shiftedSieveAdjunctionOperator Q
      ⟨sieveAdjunctionBasis Q m, sieveAdjunctionBasis_mem_shifted_domain Q m⟩ =
        ((1 + Real.log (m : ℕ) + tameDifferent (m : ℕ) : ℝ) : ℂ) • sieveAdjunctionBasis Q m := by
  change ((1 - Real.eulerMascheroniConstant : ℝ) : ℂ) • sieveAdjunctionBasis Q m +
    sieveAdjunctionOperator Q ⟨sieveAdjunctionBasis Q m, sieveAdjunctionBasis_mem_domain Q m⟩ = _
  rw [sieveAdjunctionOperator_basis, ← add_smul]
  congr 1
  simp only [matchedSieveEnergy, ← Complex.ofReal_add]
  congr 1
  ring

/-- The inverse, defined on the entire actual Hilbert space. -/
def sieveAdjunctionInverse (Q : Finset Nat.Primes) : SieveClassL2 Q →L[ℂ] SieveClassL2 Q :=
  positiveBasisInverse (sieveAdjunctionBasis Q)
    (fun m => 1 + Real.log (m : ℕ) + tameDifferent (m : ℕ)) (one_le_sieveAdjunctionEnergy Q)

/-- Every inverse output belongs to the original maximal operator domain. -/
theorem sieveAdjunctionInverse_mem_domain (Q : Finset Nat.Primes) (x : SieveClassL2 Q) :
    sieveAdjunctionInverse Q x ∈ (shiftedSieveAdjunctionOperator Q).domain :=
  positiveBasisInverse_mem_domain _ _ _ _ (shiftedSieveAdjunctionOperator_isClosed Q)
    (sieveAdjunctionBasis_mem_shifted_domain Q) (shiftedSieveAdjunctionOperator_basis Q) x

theorem shiftedSieveAdjunctionOperator_inverse (Q : Finset Nat.Primes) (x : SieveClassL2 Q) :
    shiftedSieveAdjunctionOperator Q
      ⟨sieveAdjunctionInverse Q x, sieveAdjunctionInverse_mem_domain Q x⟩ = x :=
  apply_positiveBasisInverse _ _ _ _ (shiftedSieveAdjunctionOperator_isClosed Q)
    (sieveAdjunctionBasis_mem_shifted_domain Q) (shiftedSieveAdjunctionOperator_basis Q) x

theorem sieveAdjunctionInverse_shiftedOperator (Q : Finset Nat.Primes)
    (x : (shiftedSieveAdjunctionOperator Q).domain) :
    sieveAdjunctionInverse Q (shiftedSieveAdjunctionOperator Q x) = (x : SieveClassL2 Q) :=
  positiveBasisInverse_apply _ _ _ _ (shiftedSieveAdjunctionOperator_formalSelfAdjoint Q)
    (sieveAdjunctionBasis_mem_shifted_domain Q) (shiftedSieveAdjunctionOperator_basis Q) x

theorem sieveAdjunctionInverse_basis (Q : Finset Nat.Primes) (m : SieveClass Q) :
    sieveAdjunctionInverse Q (sieveAdjunctionBasis Q m) =
      ((1 + Real.log (m : ℕ) + tameDifferent (m : ℕ) : ℝ) : ℂ)⁻¹ • sieveAdjunctionBasis Q m :=
  positiveBasisInverse_basis _ _ _ _

/-- The actual shifted inverse is compact because arithmetic energies escape every finite bound. -/
theorem sieveAdjunctionInverse_isCompact (Q : Finset Nat.Primes) :
    IsCompactOperator (sieveAdjunctionInverse Q) :=
  positiveBasisInverse_isCompact _ _ _ (tendsto_sieveAdjunctionEnergy_cofinite Q)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

