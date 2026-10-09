import GaloisForLFunctions.HTGeometry.PaperOriginalDegreeMultiplication
import GaloisForLFunctions.HTGeometry.FreeCoordinateField
import Mathlib.Algebra.Order.Monoid.ToMulBot
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!+# The paper's degeneration as a valuation of the native rational field

The domain theorem for the actual associated graded ring makes the original
signed degree multiplicative. Its multiplicative reindexing is a valuation
with zero support, so it extends to the existing free rational coordinate
field. The paper's polynomial has value corresponding to integer `-1`;
its integral powers and reciprocals realize the full integer value group.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

/-- The literal four-variable filtration defines a multiplicative valuation. -/
def paperOriginalValuation : Valuation (R 4) (WithZero (Multiplicative ℤ)) where
  toFun p := WithZero.toMulBot.symm (Multiplicative.ofAdd (paperOriginalSignedDegree p))
  map_zero' := paperOriginalSignedDegree_zero
  map_one' := paperOriginalSignedDegree_one
  map_mul' := paperOriginalSignedDegree_mul
  map_add_le_max' := paperOriginalSignedDegree_add_le

/-- The valuation has no nonzero element in its support. -/
@[simp] theorem paperOriginalValuation_eq_zero_iff (p : R 4) :
    paperOriginalValuation p = 0 ↔ p = 0 := by
  change paperOriginalSignedDegree p = ⊥ ↔ p = 0
  simp [paperOriginalSignedDegree]

theorem paperOriginalValuation_supp : paperOriginalValuation.supp = ⊥ := by
  ext p
  simp [Valuation.mem_supp_iff]

private theorem denominators_outside_support :
    nonZeroDivisors (R 4) ≤ paperOriginalValuation.supp.primeCompl := by
  intro p hp
  change paperOriginalValuation p ≠ 0
  intro hz
  exact nonZeroDivisors.ne_zero hp ((paperOriginalValuation_eq_zero_iff p).mp hz)

/-- Extension to the corpus's literal rational function field in four variables. -/
def paperRationalValuation :
    Valuation (FreeCoordinateRationalField ℂ (Fin 4)) (WithZero (Multiplicative ℤ)) :=
  paperOriginalValuation.extendToLocalization denominators_outside_support _

@[simp] theorem paperRationalValuation_algebraMap (p : R 4) :
    paperRationalValuation
      (algebraMap (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) p) =
      paperOriginalValuation p :=
  paperOriginalValuation.extendToLocalization_apply_map_apply denominators_outside_support _ p

/-- A rational quotient has exactly the quotient of its polynomial values. -/
theorem paperRationalValuation_div (p q : R 4) :
    paperRationalValuation
      (algebraMap (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) p /
        algebraMap (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) q) =
      paperOriginalValuation p / paperOriginalValuation q := by
  rw [map_div₀, paperRationalValuation_algebraMap, paperRationalValuation_algebraMap]

/-- The source polynomial gives a generator of the integer value group. -/
theorem paperOriginalValuation_f :
    paperOriginalValuation f = (↑(Multiplicative.ofAdd (-1 : ℤ)) : WithZero (Multiplicative ℤ)) := by
  change paperOriginalSignedDegree f = ((-1 : ℤ) : WithBot ℤ)
  exact paperOriginalSignedDegree_f

/-- Every integer value is attained by an integral power of the actual source polynomial. -/
theorem paperRationalValuation_f_zpow (n : ℤ) :
    paperRationalValuation
      ((algebraMap (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) f) ^ n) =
      (↑(Multiplicative.ofAdd (-n)) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, paperRationalValuation_algebraMap, paperOriginalValuation_f,
    ← WithZero.coe_zpow, ← ofAdd_zsmul]
  simp

/-- The field valuation realizes zero and every value of its integer value group. -/
theorem paperRationalValuation_surjective : Function.Surjective paperRationalValuation := by
  intro v
  induction v using WithZero.recZeroCoe with
  | zero => exact ⟨0, map_zero _⟩
  | coe n =>
    refine ⟨(algebraMap (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) f) ^ (-n.toAdd), ?_⟩
    simpa only [neg_neg, ofAdd_toAdd] using paperRationalValuation_f_zpow (-n.toAdd)

/-- The actual local valuation ring inside the native rational function field. -/
def paperRationalValuationRing : ValuationSubring (FreeCoordinateRationalField ℂ (Fin 4)) :=
  paperRationalValuation.valuationSubring

/-- The polynomial part of the valuation ring is exactly the zeroth filtration layer. -/
theorem paperRationalValuationRing_algebraMap_iff (p : R 4) :
    algebraMap (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) p ∈
      paperRationalValuationRing ↔ p ∈ paperOriginalFiltration 0 := by
  rw [paperRationalValuationRing, Valuation.mem_valuationSubring_iff,
    paperRationalValuation_algebraMap, paperOriginalFiltration_mem_iff]
  change paperOriginalSignedDegree p ≤ (0 : WithBot ℤ) ↔ p = 0 ∨ paperOriginalDegree p ≤ 0
  by_cases hp : p = 0 <;> simp [paperOriginalSignedDegree, hp]

/-- Integral powers of the source polynomial lie in the valuation ring exactly at nonnegative exponents. -/
theorem paperRationalValuationRing_f_zpow_iff (n : ℤ) :
    (algebraMap (R 4) (FreeCoordinateRationalField ℂ (Fin 4)) f) ^ n ∈
      paperRationalValuationRing ↔ 0 ≤ n := by
  rw [paperRationalValuationRing, Valuation.mem_valuationSubring_iff,
    paperRationalValuation_f_zpow, WithZero.coe_le_one]
  change -n ≤ 0 ↔ 0 ≤ n
  exact neg_nonpos

end

end GaloisForLFunctions.HTGeometry
