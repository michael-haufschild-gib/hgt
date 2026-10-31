import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticIdealNorm
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticInfinityValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Data.Int.WithZero

/-!
# Product formula on the actual elliptic function field over F₃

Finite places are normalized by their residue cardinalities; the omitted
degree-one infinity place is normalized by three. Ideal factorization and the
proved principal ideal norm identify their products, first on affine functions
and then on every nonzero fraction.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open Polynomial IsDedekindDomain Function
open scoped nonZeroDivisors NNReal WithZero WithZeroMulInt
noncomputable section

theorem affineIdealNorm_pos (I : Ideal CoordinateRing) (hI : I ≠ ⊥) :
    0 < affineIdealNorm I := by
  letI := affine_quotient_finite I hI
  exact Nat.card_pos

private theorem finiteNormBase_ne_zero (v : HeightOneSpectrum CoordinateRing) :
    (affineIdealNorm v.asIdeal : ℝ≥0) ≠ 0 := by
  exact_mod_cast (affineIdealNorm_pos v.asIdeal v.ne_bot).ne'

/-- The finite-place magnitude with its actual residue-cardinality normalization. -/
def affinePlaceMagnitude (v : HeightOneSpectrum CoordinateRing) : FunctionField →*₀ ℝ≥0 :=
  (WithZeroMulInt.toNNReal (finiteNormBase_ne_zero v)).comp
    (v.valuation FunctionField).toMonoidWithZeroHom

/-- The magnitude at the proved degree-one infinity place. -/
def infinityMagnitude : FunctionField →*₀ ℝ≥0 :=
  (WithZeroMulInt.toNNReal (by norm_num : (3 : ℝ≥0) ≠ 0)).comp
    infinityValuation.toMonoidWithZeroHom

theorem affinePlaceMagnitude_algebraMap (v : HeightOneSpectrum CoordinateRing)
    {a : CoordinateRing} (ha : a ≠ 0) :
    affinePlaceMagnitude v (algebraMap CoordinateRing FunctionField a) =
      (affineIdealNorm (v.maxPowDividing (Ideal.span {a})) : ℝ≥0)⁻¹ := by
  change WithZeroMulInt.toNNReal (finiteNormBase_ne_zero v)
    (v.valuation FunctionField (algebraMap CoordinateRing FunctionField a)) = _
  rw [v.valuation_of_algebraMap, v.intValuation_if_neg ha,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_natCast,
    HeightOneSpectrum.maxPowDividing, map_pow, Nat.cast_pow]

/-- Only the prime ideal divisors of a nonzero affine function can contribute. -/
theorem affinePlaceMagnitude_hasFiniteMulSupport_algebraMap
    {a : CoordinateRing} (ha : a ≠ 0) :
    HasFiniteMulSupport fun v =>
      affinePlaceMagnitude v (algebraMap CoordinateRing FunctionField a) := by
  have hI : Ideal.span {a} ≠ (0 : Ideal CoordinateRing) :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  apply (Ideal.hasFiniteMulSupport hI).subset
  intro v hv
  rw [mem_mulSupport] at hv ⊢
  intro heq
  apply hv
  rw [affinePlaceMagnitude_algebraMap v ha, heq, map_one, Nat.cast_one, inv_one]

/-- Finite place magnitudes multiply to the inverse actual principal ideal norm. -/
theorem finprod_affinePlaceMagnitude_algebraMap
    {a : CoordinateRing} (ha : a ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum CoordinateRing,
      affinePlaceMagnitude v (algebraMap CoordinateRing FunctionField a)) =
        (affineIdealNorm (Ideal.span {a}) : ℝ≥0)⁻¹ := by
  have hI : Ideal.span {a} ≠ (0 : Ideal CoordinateRing) :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  let N : Ideal CoordinateRing →* ℝ≥0 :=
    (Nat.castRingHom ℝ≥0).toMonoidHom.comp affineIdealNorm.toMonoidHom
  have hmap := N.map_finprod (Ideal.hasFiniteMulSupport hI)
  rw [Ideal.finprod_heightOneSpectrum_factorization hI] at hmap
  simp only [affinePlaceMagnitude_algebraMap _ ha, finprod_inv_distrib]
  exact congrArg Inv.inv hmap.symm

/-- The infinity magnitude equals the actual principal ideal norm. -/
theorem infinityMagnitude_algebraMap {a : CoordinateRing} (ha : a ≠ 0) :
    infinityMagnitude (algebraMap CoordinateRing FunctionField a) =
      (affineIdealNorm (Ideal.span {a}) : ℝ≥0) := by
  have hv : infinityValuation (algebraMap CoordinateRing FunctionField a) =
      WithZero.exp ((Algebra.norm Constants[X] a).natDegree : ℤ) := by
    rw [infinityValuation_algebraMap]
    change (poleDegree a).map (Nat.castAddMonoidHom ℤ) =
      (((Algebra.norm Constants[X] a).natDegree : ℤ) : WithBot ℤ)
    rw [affine_principal_norm_exponent a ha]
    rfl
  change WithZeroMulInt.toNNReal (by norm_num : (3 : ℝ≥0) ≠ 0)
    (infinityValuation (algebraMap CoordinateRing FunctionField a)) = _
  rw [hv, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    affineIdealNorm_principal a ha]
  simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd, zpow_natCast, Nat.cast_pow,
    Nat.cast_ofNat]

theorem product_formula_algebraMap {a : CoordinateRing} (ha : a ≠ 0) :
    infinityMagnitude (algebraMap CoordinateRing FunctionField a) *
      (∏ᶠ v : HeightOneSpectrum CoordinateRing,
        affinePlaceMagnitude v (algebraMap CoordinateRing FunctionField a)) = 1 := by
  rw [infinityMagnitude_algebraMap ha, finprod_affinePlaceMagnitude_algebraMap ha]
  apply mul_inv_cancel₀
  exact_mod_cast (affineIdealNorm_pos (Ideal.span {a})
    (Ideal.span_singleton_eq_bot.not.mpr ha)).ne'

/-- Every nonzero rational function has finite support among the normalized finite places. -/
theorem affinePlaceMagnitude_hasFiniteMulSupport {z : FunctionField} (hz : z ≠ 0) :
    HasFiniteMulSupport fun v => affinePlaceMagnitude v z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective CoordinateRing z
  have hb0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by
    intro heq
    apply hz
    rw [heq, map_zero, zero_div]
  simp only [map_div₀]
  exact (affinePlaceMagnitude_hasFiniteMulSupport_algebraMap ha).div
    (affinePlaceMagnitude_hasFiniteMulSupport_algebraMap hb0)

/-- The normalized product formula for every nonzero function on `y²=x³−x` over F₃. -/
theorem product_formula {z : FunctionField} (hz : z ≠ 0) :
    infinityMagnitude z *
      (∏ᶠ v : HeightOneSpectrum CoordinateRing, affinePlaceMagnitude v z) = 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective CoordinateRing z
  have hb0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by
    intro heq
    apply hz
    rw [heq, map_zero, zero_div]
  simp only [map_div₀]
  rw [finprod_div_distrib (affinePlaceMagnitude_hasFiniteMulSupport_algebraMap ha)
    (affinePlaceMagnitude_hasFiniteMulSupport_algebraMap hb0), div_mul_div_comm,
    product_formula_algebraMap ha, product_formula_algebraMap hb0, div_self one_ne_zero]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.affinePlaceMagnitude_hasFiniteMulSupport
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.product_formula
