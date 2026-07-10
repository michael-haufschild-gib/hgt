/-
# The coupled all-prime Sonin column and Gram operators

The block-diagonal all-prime operator separates prime powers and therefore deletes all mixed
prime words.  The canonical coupled assembly instead stacks every weighted residual over the
same Sonin source space.  Its Gram operator is positive and retains cross-prime overlaps.
-/
import GaloisForLFunctions.HilbertSchmidtRectangular
import GaloisForLFunctions.RHTower.SoninAllPrimeResidualKernel

noncomputable section

open scoped BigOperators

namespace RHTower

/-- Rectangular matrix of the canonical column operator.  Rows are indexed by a prime power and
an output Sonin coordinate; columns use the single common Sonin input coordinate. -/
def soninAllPrimeColumnKernel (a : ℝ) :
    SoninAllPrimeIndex × SoninHilbertIndex → ℂ := fun z =>
  inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 z.1.2)
    (centralSoninWeightedPrimePowerResidual a z.1.1
      (ContinuousLinearMap.hsBasis ℂ SoninL2 z.2))

private def soninAllPrimeColumnEquiv :
    (Nat.Primes × ℕ) × (SoninHilbertIndex × SoninHilbertIndex) ≃
      SoninAllPrimeIndex × SoninHilbertIndex where
  toFun pji := ((pji.1, pji.2.2), pji.2.1)
  invFun z := (z.1.1, (z.2, z.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The existing all-prime Hilbert--Schmidt energy sum proves convergence of the coupled column
without any additional hypothesis. -/
theorem soninAllPrimeColumnKernel_isHSRect (a : ℝ) (ha : 0 < a) :
    HilbertSchmidt.IsHSRect (soninAllPrimeColumnKernel a) := by
  apply (soninAllPrimeColumnEquiv.summable_iff).mp
  refine (summable_all_prime_residual_matrix_entries a ha).congr (fun pji => ?_)
  rfl

/-- Coordinate version of the all-prime column operator. -/
def soninAllPrimeColumnCoordinateOperator (a : ℝ) (ha : 0 < a) :
    lp (fun _ : SoninHilbertIndex => ℂ) 2 →L[ℂ] SoninAllPrimeL2 :=
  HilbertSchmidt.toOperatorRect (soninAllPrimeColumnKernel_isHSRect a ha)

/-- The canonical column operator on the actual common Sonin space. -/
def soninAllPrimeColumnOperator (a : ℝ) (ha : 0 < a) :
    SoninL2 →L[ℂ] SoninAllPrimeL2 :=
  soninAllPrimeColumnCoordinateOperator a ha ∘L
    (ContinuousLinearMap.hsBasis ℂ SoninL2).repr.toContinuousLinearEquiv.toContinuousLinearMap

/-- The coupled column is genuinely Hilbert--Schmidt. -/
theorem soninAllPrimeColumnOperator_isHilbertSchmidt (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt (soninAllPrimeColumnOperator a ha) := by
  exact (HilbertSchmidt.isHilbertSchmidt_toOperatorRect
    (soninAllPrimeColumnKernel_isHSRect a ha)).comp_right
      (ContinuousLinearMap.hsBasis ℂ SoninL2).repr.toContinuousLinearEquiv.toContinuousLinearMap

/-- Evaluation of the column at a prime-power/output-basis row. -/
theorem soninAllPrimeColumnOperator_apply (a : ℝ) (ha : 0 < a) (x : SoninL2)
    (pk : Nat.Primes × ℕ) (i : SoninHilbertIndex) :
    soninAllPrimeColumnOperator a ha x (pk, i) =
      inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 i)
        (centralSoninWeightedPrimePowerResidual a pk x) := by
  let b := ContinuousLinearMap.hsBasis ℂ SoninL2
  let A := centralSoninWeightedPrimePowerResidual a pk
  rw [soninAllPrimeColumnOperator, ContinuousLinearMap.comp_apply,
    soninAllPrimeColumnCoordinateOperator, HilbertSchmidt.toOperatorRect_apply]
  change (∑' j, inner ℂ (b i) (A (b j)) * b.repr x j) = inner ℂ (b i) (A x)
  simp_rw [b.repr_apply_apply]
  calc
    (∑' j, inner ℂ (b i) (A (b j)) * inner ℂ (b j) x) =
        ∑' j, inner ℂ (ContinuousLinearMap.adjoint A (b i)) (b j) *
          inner ℂ (b j) x := by
      apply tsum_congr
      intro j
      rw [ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ (ContinuousLinearMap.adjoint A (b i)) x :=
      b.tsum_inner_mul_inner _ _
    _ = inner ℂ (b i) (A x) := ContinuousLinearMap.adjoint_inner_left A x (b i)

/-- The coupled positive energy on the single Sonin space. -/
def soninAllPrimeMixedEnergyOperator (a : ℝ) (ha : 0 < a) :
    SoninL2 →L[ℂ] SoninL2 :=
  ContinuousLinearMap.adjoint (soninAllPrimeColumnOperator a ha) ∘L
    soninAllPrimeColumnOperator a ha

/-- Explicit trace-class factorization through the all-prime column Hilbert space. -/
theorem soninAllPrimeMixedEnergyOperator_traceClassFactorization (a : ℝ) (ha : 0 < a) :
    ∃ S : SoninAllPrimeL2 →L[ℂ] SoninL2, ∃ U : SoninL2 →L[ℂ] SoninAllPrimeL2,
      ContinuousLinearMap.IsHilbertSchmidt S ∧
      ContinuousLinearMap.IsHilbertSchmidt U ∧
      soninAllPrimeMixedEnergyOperator a ha = S ∘L U := by
  refine ⟨ContinuousLinearMap.adjoint (soninAllPrimeColumnOperator a ha),
    soninAllPrimeColumnOperator a ha, ?_, ?_, rfl⟩
  · exact (soninAllPrimeColumnOperator_isHilbertSchmidt a ha).adjoint
  · exact soninAllPrimeColumnOperator_isHilbertSchmidt a ha

/-- The coupled energy is self-adjoint. -/
theorem soninAllPrimeMixedEnergyOperator_isSelfAdjoint (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.adjoint (soninAllPrimeMixedEnergyOperator a ha) =
      soninAllPrimeMixedEnergyOperator a ha := by
  rw [soninAllPrimeMixedEnergyOperator, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- The coupled energy has a nonnegative quadratic form. -/
theorem soninAllPrimeMixedEnergyOperator_nonnegative (a : ℝ) (ha : 0 < a) (x : SoninL2) :
    0 ≤ (inner ℂ x (soninAllPrimeMixedEnergyOperator a ha x)).re := by
  change 0 ≤ Complex.re
    (inner ℂ x
      (ContinuousLinearMap.adjoint (soninAllPrimeColumnOperator a ha)
        (soninAllPrimeColumnOperator a ha x)))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (E := SoninAllPrimeL2)

/-- A mixed prime-power overlap.  Its Hilbert--Schmidt energy is the cross term retained by the
coupled Gram and erased by the block-diagonal assembly. -/
def soninPrimePowerCrossOverlap (a : ℝ) (α β : Nat.Primes × ℕ) :
    SoninL2 →L[ℂ] SoninL2 :=
  centralSoninWeightedPrimePowerResidual a α ∘L
    ContinuousLinearMap.adjoint (centralSoninWeightedPrimePowerResidual a β)

theorem soninPrimePowerCrossOverlap_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (α β : Nat.Primes × ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt (soninPrimePowerCrossOverlap a α β) := by
  exact (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha β).adjoint.comp_left
    (centralSoninWeightedPrimePowerResidual a α)

theorem soninPrimePowerCrossOverlap_hsNormSq_nonneg
    (a : ℝ) (α β : Nat.Primes × ℕ) :
    0 ≤ ContinuousLinearMap.hsNormSq (soninPrimePowerCrossOverlap a α β) :=
  ContinuousLinearMap.hsNormSq_nonneg _

end RHTower
