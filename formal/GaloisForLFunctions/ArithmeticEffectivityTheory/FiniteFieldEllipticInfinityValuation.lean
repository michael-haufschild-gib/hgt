import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticCharts
import Mathlib.Algebra.Order.Monoid.ToMulBot
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# The infinity valuation of the elliptic curve over the three-element field

The actual norm degree extends from the coordinate ring to its fraction field.
The coordinate ratio `x/y` has valuation exponent minus one, so the valuation
is discrete and its local ring is a DVR with that explicit uniformizer.
-/

open Polynomial
open scoped nonZeroDivisors

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

private def integerPoleDegree (a : CoordinateRing) : WithBot ℤ :=
  (poleDegree a).map (Nat.castAddMonoidHom ℤ)

private lemma map_natDegree_le_iff (a b : WithBot ℕ) :
    a.map (Nat.castAddMonoidHom ℤ) ≤ b.map (Nat.castAddMonoidHom ℤ) ↔ a ≤ b := by
  cases a with
  | bot =>
    change (⊥ : WithBot ℤ) ≤ _ ↔ (⊥ : WithBot ℕ) ≤ _
    simp
  | coe n =>
    cases b with
    | bot =>
      change (↑(n : ℤ) : WithBot ℤ) ≤ ⊥ ↔ (↑n : WithBot ℕ) ≤ ⊥
      simp
    | coe m =>
      change (↑(n : ℤ) : WithBot ℤ) ≤ ↑(m : ℤ) ↔ (↑n : WithBot ℕ) ≤ ↑m
      simp

private lemma map_natDegree_le {a b : WithBot ℕ} (h : a ≤ b) :
    a.map (Nat.castAddMonoidHom ℤ) ≤ b.map (Nat.castAddMonoidHom ℤ) :=
  (map_natDegree_le_iff a b).mpr h

private lemma integerPoleDegree_mul (a b : CoordinateRing) :
    integerPoleDegree (a * b) = integerPoleDegree a + integerPoleDegree b := by
  unfold integerPoleDegree
  rw [poleDegree_mul, WithBot.map_add]

private lemma integerPoleDegree_add_le (a b : CoordinateRing) :
    integerPoleDegree (a + b) ≤ max (integerPoleDegree a) (integerPoleDegree b) := by
  have h := poleDegree_add a b
  rcases le_total (poleDegree a) (poleDegree b) with hab | hba
  · rw [max_eq_right hab] at h
    exact (map_natDegree_le h).trans (le_max_right _ _)
  · rw [max_eq_left hba] at h
    exact (map_natDegree_le h).trans (le_max_left _ _)

/-- The valuation on the affine coordinate ring obtained from pole degree at infinity. -/
def infinityCoordinateValuation : Valuation CoordinateRing (WithZero (Multiplicative ℤ)) where
  toFun a := WithZero.toMulBot.symm (Multiplicative.ofAdd (integerPoleDegree a))
  map_zero' := by
    change integerPoleDegree 0 = ⊥
    simp only [integerPoleDegree, poleDegree_zero, WithBot.map_bot]
  map_one' := by
    change integerPoleDegree 1 = 0
    simp [integerPoleDegree, poleDegree_one]
  map_mul' := integerPoleDegree_mul
  map_add_le_max' := integerPoleDegree_add_le

@[simp] lemma infinityCoordinateValuation_eq_zero_iff (a : CoordinateRing) :
    infinityCoordinateValuation a = 0 ↔ a = 0 := by
  change (poleDegree a).map (Nat.castAddMonoidHom ℤ) = ⊥ ↔ a = 0
  rw [WithBot.map_eq_bot_iff, poleDegree_eq_bot_iff]

private lemma infinity_denominators_outside_support :
    CoordinateRing⁰ ≤ infinityCoordinateValuation.supp.primeCompl := by
  intro a ha
  change infinityCoordinateValuation a ≠ 0
  exact fun hz => nonZeroDivisors.ne_zero ha
    ((infinityCoordinateValuation_eq_zero_iff a).mp hz)

/-- The actual infinity valuation on the function field of `y²=x³−x`. -/
def infinityValuation : Valuation FunctionField (WithZero (Multiplicative ℤ)) :=
  infinityCoordinateValuation.extendToLocalization infinity_denominators_outside_support _

@[simp] lemma infinityValuation_algebraMap (a : CoordinateRing) :
    infinityValuation (algebraMap CoordinateRing FunctionField a) =
      infinityCoordinateValuation a :=
  infinityCoordinateValuation.extendToLocalization_apply_map_apply
    infinity_denominators_outside_support _ a

lemma infinityValuation_x :
    infinityValuation x = (↑(Multiplicative.ofAdd (2 : ℤ)) : WithZero (Multiplicative ℤ)) := by
  rw [x, infinityValuation_algebraMap]
  change (poleDegree xA).map (Nat.castAddMonoidHom ℤ) = (2 : WithBot ℤ)
  rw [poleDegree_xA]
  rfl

lemma infinityValuation_y :
    infinityValuation y = (↑(Multiplicative.ofAdd (3 : ℤ)) : WithZero (Multiplicative ℤ)) := by
  rw [y, infinityValuation_algebraMap]
  change (poleDegree yA).map (Nat.castAddMonoidHom ℤ) = (3 : WithBot ℤ)
  rw [poleDegree_yA]
  rfl

/-- The projective parameter `x/y` has a simple zero at infinity. -/
lemma infinityValuation_parameter :
    infinityValuation (x / y) =
      (↑(Multiplicative.ofAdd (-1 : ℤ)) : WithZero (Multiplicative ℤ)) := by
  rw [map_div₀, infinityValuation_x, infinityValuation_y, ← WithZero.coe_div]
  rfl

lemma infinityValuation_parameter_zpow (n : ℤ) :
    infinityValuation ((x / y) ^ n) =
      (↑(Multiplicative.ofAdd (-n)) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, infinityValuation_parameter, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  simp

theorem infinityValuation_surjective : Function.Surjective infinityValuation := by
  intro v
  induction v using WithZero.recZeroCoe with
  | zero => exact ⟨0, map_zero _⟩
  | coe n =>
    refine ⟨(x / y) ^ (-n.toAdd), ?_⟩
    simpa only [neg_neg, ofAdd_toAdd] using infinityValuation_parameter_zpow (-n.toAdd)

instance infinityValuationNontrivial : infinityValuation.IsNontrivial := by
  refine ⟨x / y, ?_, ?_⟩
  · rw [infinityValuation_parameter]
    exact WithZero.coe_ne_zero
  · rw [infinityValuation_parameter]
    intro h
    have hm : Multiplicative.ofAdd (-1 : ℤ) = (1 : Multiplicative ℤ) :=
      WithZero.coe_injective h
    exact (neg_ne_zero.mpr one_ne_zero : (-1 : ℤ) ≠ 0) (ofAdd_eq_one.mp hm)

instance infinityValuationDiscrete : infinityValuation.IsRankOneDiscrete := inferInstance

/-- The local ring at the actual infinity valuation. -/
def InfinityRing : ValuationSubring FunctionField := infinityValuation.valuationSubring

instance : IsDiscreteValuationRing InfinityRing := by
  change IsDiscreteValuationRing infinityValuation.valuationSubring
  infer_instance

/-- The chosen projective parameter is a genuine uniformizer. -/
theorem infinityParameter_isUniformizer : infinityValuation.IsUniformizer (x / y) := by
  rw [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      infinityValuation_surjective, infinityValuation_parameter]
  rfl

lemma infinityCoordinateValuation_le_iff (a b : CoordinateRing) :
    infinityCoordinateValuation a ≤ infinityCoordinateValuation b ↔
      poleDegree a ≤ poleDegree b := by
  change (poleDegree a).map (Nat.castAddMonoidHom ℤ) ≤
    (poleDegree b).map (Nat.castAddMonoidHom ℤ) ↔ _
  exact map_natDegree_le_iff _ _

lemma infinityValuation_div_le_one_iff (a b : CoordinateRing) (hb : b ≠ 0) :
    infinityValuation (algebraMap CoordinateRing FunctionField a /
      algebraMap CoordinateRing FunctionField b) ≤ 1 ↔ poleDegree a ≤ poleDegree b := by
  rw [map_div₀, infinityValuation_algebraMap, infinityValuation_algebraMap,
    div_le_one₀ (pos_iff_ne_zero.mpr
      ((infinityCoordinateValuation_eq_zero_iff b).not.mpr hb))]
  exact infinityCoordinateValuation_le_iff a b

lemma infinityCoordinateValuation_lt_iff (a b : CoordinateRing) :
    infinityCoordinateValuation a < infinityCoordinateValuation b ↔
      poleDegree a < poleDegree b := by
  simp only [lt_iff_le_not_ge, infinityCoordinateValuation_le_iff]

lemma infinityValuation_div_lt_one_iff (a b : CoordinateRing) (hb : b ≠ 0) :
    infinityValuation (algebraMap CoordinateRing FunctionField a /
      algebraMap CoordinateRing FunctionField b) < 1 ↔ poleDegree a < poleDegree b := by
  rw [map_div₀, infinityValuation_algebraMap, infinityValuation_algebraMap,
    div_lt_one₀ (pos_iff_ne_zero.mpr
      ((infinityCoordinateValuation_eq_zero_iff b).not.mpr hb))]
  exact infinityCoordinateValuation_lt_iff a b

/-- The valuation local ring is precisely the previously constructed infinity chart regularity ring. -/
theorem mem_infinityRing_iff (z : FunctionField) :
    z ∈ InfinityRing ↔ z ∈ infinityRegular := by
  change infinityValuation z ≤ 1 ↔
    ∃ a b : CoordinateRing, b ≠ 0 ∧
      z = algebraMap CoordinateRing FunctionField a / algebraMap CoordinateRing FunctionField b ∧
      poleDegree a ≤ poleDegree b
  constructor
  · intro hz
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective CoordinateRing z
    have hb0 := nonZeroDivisors.ne_zero hb
    exact ⟨a, b, hb0, rfl, (infinityValuation_div_le_one_iff a b hb0).mp hz⟩
  · rintro ⟨a, b, hb, rfl, hab⟩
    exact (infinityValuation_div_le_one_iff a b hb).mpr hab

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
