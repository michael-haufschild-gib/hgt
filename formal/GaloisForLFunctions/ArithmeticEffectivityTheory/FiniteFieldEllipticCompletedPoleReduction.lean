import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticInfinityApproximation
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticPoleSemigroup
import Mathlib.Data.Int.WithZero

/-!
# Pole reduction in the completed elliptic infinity field

Affine monomials remove every pole order at least two. The simple-pole gap
leaves one constant-field coefficient; subtraction of the remaining residue
then gives a representative in `F₃ (x/y)⁻¹ + m∞`.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open scoped WithZero WithZeroMulInt
noncomputable section

/-- The affine coordinate ring inside the completed infinity field. -/
def affineInfinityEmbedding : A →+* InfinityCompletion :=
  infinityEmbedding.comp (algebraMap A K)

theorem affineInfinityEmbedding_constant (c : Constants) :
    affineInfinityEmbedding (algebraMap Constants A c) =
      infinityEmbedding (algebraMap Constants K c) := by
  rw [IsScalarTower.algebraMap_apply Constants A K]
  rfl

private theorem completedInfinity_cancel_leading_coefficient
    (z u : InfinityCompletion) (n : ℤ)
    (hu : Valued.v u = WithZero.exp n) (hz : Valued.v z ≤ WithZero.exp n) :
    ∃ c : Constants,
      Valued.v (z - infinityEmbedding (algebraMap Constants K c) * u) < WithZero.exp n := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  have hquot : Valued.v (z / u) ≤ 1 := by
    rw [map_div₀, hu, div_le_one₀ WithZero.exp_pos]
    exact hz
  obtain ⟨c, hc⟩ := completedInfinity_sub_constant (z / u) hquot
  refine ⟨c, ?_⟩
  have heq : z - infinityEmbedding (algebraMap Constants K c) * u =
      (z / u - infinityEmbedding (algebraMap Constants K c)) * u := by
    rw [sub_mul, div_mul_cancel₀ _ hu0]
  rw [heq, map_mul]
  have hp : 0 < Valued.v u := by rw [hu]; exact WithZero.exp_pos
  simpa only [one_mul, hu] using mul_lt_mul_of_pos_right hc hp

private theorem completedInfinity_reduce_poles_bounded (n : ℕ)
    (z : InfinityCompletion) (hz : Valued.v z ≤ WithZero.exp (n : ℤ)) :
    ∃ a : A, Valued.v (z - affineInfinityEmbedding a) ≤ WithZero.exp (1 : ℤ) := by
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
    by_cases hn : n ≤ 1
    · refine ⟨0, ?_⟩
      rw [map_zero, sub_zero]
      exact hz.trans (WithZero.exp_le_exp.mpr (by exact_mod_cast hn))
    obtain ⟨a, ha⟩ := exists_affine_infinity_valuation n (by omega)
    have hva : Valued.v (affineInfinityEmbedding a) = WithZero.exp (n : ℤ) := by
      change Valued.v (infinityEmbedding (algebraMap A K a)) = _
      rw [infinityEmbedding_valuation, ha]
    obtain ⟨c, hc⟩ := completedInfinity_cancel_leading_coefficient z
      (affineInfinityEmbedding a) n hva hz
    have hstep : Valued.v (z - affineInfinityEmbedding (algebraMap Constants A c * a)) ≤
        WithZero.exp ((n - 1 : ℕ) : ℤ) := by
      apply (WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).mp
      rw [← WithZero.exp_add,
        show ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) by omega,
        map_mul, affineInfinityEmbedding_constant]
      exact hc
    obtain ⟨b, hb⟩ := ih (n - 1) (by omega)
      (z - affineInfinityEmbedding (algebraMap Constants A c * a)) hstep
    refine ⟨algebraMap Constants A c * a + b, ?_⟩
    rw [map_add]
    simpa only [sub_sub] using hb

/-- Subtracting an affine function leaves at most the unique simple-pole gap. -/
theorem completedInfinity_reduce_poles (z : InfinityCompletion) :
    ∃ a : A, Valued.v (z - affineInfinityEmbedding a) ≤ WithZero.exp (1 : ℤ) := by
  exact completedInfinity_reduce_poles_bounded (Valued.v z).log.toNat z
    (WithZero.le_exp_of_log_le (Int.self_le_toNat _))

/-- Every completed infinity element has an affine part, a simple-pole coefficient,
and a remainder in the maximal ideal. -/
theorem completedInfinity_affine_simplePole_remainder (z : InfinityCompletion) :
    ∃ (a : A) (c : Constants),
      Valued.v (z - affineInfinityEmbedding a -
        infinityEmbedding (algebraMap Constants K c) *
          infinityEmbedding ((x / y) ^ (-1 : ℤ))) < 1 := by
  obtain ⟨a, ha⟩ := completedInfinity_reduce_poles z
  let u := infinityEmbedding ((x / y) ^ (-1 : ℤ))
  have hu : Valued.v u = WithZero.exp (1 : ℤ) := by
    dsimp only [u]
    rw [infinityEmbedding_valuation, infinityValuation_parameter_zpow]
    rfl
  obtain ⟨c, hc⟩ := completedInfinity_cancel_leading_coefficient
    (z - affineInfinityEmbedding a) u 1 hu ha
  have hregular : Valued.v
      (z - affineInfinityEmbedding a - infinityEmbedding (algebraMap Constants K c) * u) ≤ 1 := by
    apply (WithZero.lt_mul_exp_iff_le (by exact one_ne_zero)).mp
    simpa only [one_mul] using hc
  obtain ⟨d, hd⟩ := completedInfinity_sub_constant _ hregular
  refine ⟨a + algebraMap Constants A d, c, ?_⟩
  rw [map_add, affineInfinityEmbedding_constant]
  have heq : z - (affineInfinityEmbedding a + infinityEmbedding (algebraMap Constants K d)) -
      infinityEmbedding (algebraMap Constants K c) * u =
      z - affineInfinityEmbedding a - infinityEmbedding (algebraMap Constants K c) * u -
        infinityEmbedding (algebraMap Constants K d) := by abel
  change Valued.v (z - (affineInfinityEmbedding a + infinityEmbedding (algebraMap Constants K d)) -
    infinityEmbedding (algebraMap Constants K c) * u) < 1
  rw [heq]
  exact hd

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.completedInfinity_reduce_poles
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.completedInfinity_affine_simplePole_remainder
