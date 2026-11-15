import GaloisForLFunctions.HTGeometry.MilnorKTheory.PolylogSymbolCollapse
import GaloisForLFunctions.HTGeometry.SmoothRationalUnits
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Valuation detectors for classical symbols modulo shuffle

Two prime valuations give the alternating pairing
`v_p(a)v_q(b) - v_q(a)v_p(b)` on rational units. It descends through the degree-two
shuffle relation, but not through Steinberg relations. For every prime `p`, a prime
divisor `q` of `p+1` detects the classical symbol at `-p`. Consequently this symbol
has infinite order modulo shuffle while its Milnor image is zero.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

/-- The additive form of the rational unit group. -/
abbrev RationalUnitLattice := Additive ℚˣ

/-- Prime valuation as an integral linear functional on units. -/
def rationalUnitValuation (p : Nat.Primes) : RationalUnitLattice →ₗ[ℤ] ℤ := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  exact AddMonoidHom.toIntLinearMap
    { toFun := fun a => Multiplicative.toAdd (ratPadicValHom p.val a.toMul)
      map_zero' := congrArg Multiplicative.toAdd (map_one (ratPadicValHom p.val))
      map_add' := fun a b => congrArg Multiplicative.toAdd
        (map_mul (ratPadicValHom p.val) a.toMul b.toMul) }

@[simp]
theorem rationalUnitValuation_apply (p : Nat.Primes) (a : ℚˣ) :
    rationalUnitValuation p (Additive.ofMul a) = padicValRat p.val (a : ℚ) := rfl

/-- Determinant of two valuation coordinates, as a bilinear form. -/
def valuationAlternatingForm (p q : Nat.Primes) :
    RationalUnitLattice →ₗ[ℤ] RationalUnitLattice →ₗ[ℤ] ℤ where
  toFun a := rationalUnitValuation p a • rationalUnitValuation q -
    rationalUnitValuation q a • rationalUnitValuation p
  map_add' a b := by
    ext c
    simp only [map_add, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  map_smul' r a := by
    ext b
    simp only [map_smul, RingHom.id_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
    ring

/-- The corresponding linear detector on degree-two tensors. -/
def valuationTensorDetector (p q : Nat.Primes) :
    RationalUnitLattice ⊗[ℤ] RationalUnitLattice →ₗ[ℤ] ℤ :=
  TensorProduct.lift (valuationAlternatingForm p q)

/-- Pure tensors are detected by the determinant of their two prime valuations. -/
theorem valuationTensorDetector_tmul (p q : Nat.Primes) (a b : RationalUnitLattice) :
    valuationTensorDetector p q (a ⊗ₜ[ℤ] b) =
      rationalUnitValuation p a * rationalUnitValuation q b -
        rationalUnitValuation q a * rationalUnitValuation p b := rfl

/-- Degree-two shuffle relations. -/
def rationalUnitShuffleRelations : Submodule ℤ (RationalUnitLattice ⊗[ℤ] RationalUnitLattice) :=
  Submodule.span ℤ (Set.range fun ab : RationalUnitLattice × RationalUnitLattice =>
    ab.1 ⊗ₜ[ℤ] ab.2 + ab.2 ⊗ₜ[ℤ] ab.1)

/-- Alternating valuation detectors kill every degree-two shuffle. -/
theorem rationalUnitShuffleRelations_le_detector_ker (p q : Nat.Primes) :
    rationalUnitShuffleRelations ≤ (valuationTensorDetector p q).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, b⟩, rfl⟩
  change valuationTensorDetector p q (a ⊗ₜ[ℤ] b + b ⊗ₜ[ℤ] a) = 0
  rw [map_add, valuationTensorDetector_tmul, valuationTensorDetector_tmul]
  ring

/-- Degree-two rational-unit symbols modulo shuffle, before Steinberg relations. -/
abbrev RationalUnitShuffleSymbols :=
  (RationalUnitLattice ⊗[ℤ] RationalUnitLattice) ⧸ rationalUnitShuffleRelations

/-- A prime-pair detector on the shuffle quotient. -/
def valuationShuffleDetector (p q : Nat.Primes) : RationalUnitShuffleSymbols →ₗ[ℤ] ℤ :=
  rationalUnitShuffleRelations.liftQ (valuationTensorDetector p q)
    (rationalUnitShuffleRelations_le_detector_ker p q)

/-- The weight-two classical symbol, retaining the tensor sign convention. -/
def classicalPolylogTensorTwo (a : PolylogArgument ℚ) :
    RationalUnitLattice ⊗[ℤ] RationalUnitLattice :=
  -(Additive.ofMul (oneSubUnit a.2) ⊗ₜ[ℤ] Additive.ofMul a.1)

/-- The same classical symbol in the shuffle quotient. -/
def classicalPolylogShuffleClass (a : PolylogArgument ℚ) : RationalUnitShuffleSymbols :=
  Submodule.Quotient.mk (classicalPolylogTensorTwo a)

/-- Negative primes are admissible polylogarithm arguments. -/
def primePolylogArgument (p : Nat.Primes) : PolylogArgument ℚ :=
  ⟨-natRatUnit p.property.ne_zero, by
    change -(p.val : ℚ) ≠ 1
    have hp : 0 < (p.val : ℚ) := Nat.cast_pos.mpr p.property.pos
    exact ne_of_lt (lt_trans (neg_neg_of_pos hp) zero_lt_one)⟩

theorem primePolylogArgument_val (p : Nat.Primes) :
    ((primePolylogArgument p).1 : ℚ) = -(p.val : ℚ) := rfl

theorem primePolylogArgument_complement (p : Nat.Primes) :
    (oneSubUnit (primePolylogArgument p).2 : ℚ) = ((p.val + 1 : ℕ) : ℚ) := by
  change 1 - -(p.val : ℚ) = ((p.val + 1 : ℕ) : ℚ)
  push_cast
  ring

/-- Every negative-prime classical symbol has a positive alternating valuation detector. -/
theorem exists_primePolylog_positive_detector (p : Nat.Primes) :
    ∃ q : Nat.Primes, q ≠ p ∧
      0 < valuationShuffleDetector p q (classicalPolylogShuffleClass (primePolylogArgument p)) := by
  have hpnot : ¬ p.val ∣ p.val + 1 := by
    intro h
    have h1 : p.val ∣ 1 := (Nat.dvd_add_iff_right (dvd_refl p.val)).mpr h
    exact p.property.ne_one (Nat.dvd_one.mp h1)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show p.val + 1 ≠ 1 from by omega)
  have hqp : q ≠ p.val := by
    rintro rfl
    exact hpnot hqd
  letI : Fact p.val.Prime := ⟨p.property⟩
  letI : Fact q.Prime := ⟨hq⟩
  refine ⟨⟨q, hq⟩, fun h => hqp (congrArg Subtype.val h), ?_⟩
  change 0 < valuationTensorDetector p ⟨q, hq⟩ (classicalPolylogTensorTwo (primePolylogArgument p))
  rw [classicalPolylogTensorTwo, map_neg, valuationTensorDetector_tmul]
  simp only [rationalUnitValuation_apply, primePolylogArgument_val,
    primePolylogArgument_complement, padicValRat.neg]
  rw [padicValRat.self p.property.one_lt, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hpnot]
  have hqa : padicValRat q (p.val : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat_primes hqp, Int.natCast_zero]
  rw [hqa, Int.natCast_zero, zero_mul, mul_one, zero_sub, neg_neg, padicValRat.of_nat]
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
    (one_le_padicValNat_of_dvd (Nat.succ_ne_zero p.val) hqd))

/-- These classes have infinite order modulo shuffle, although their Milnor images vanish. -/
theorem primePolylogShuffleClass_infinite_order (p : Nat.Primes) :
    Function.Injective (fun m : ℤ => m • classicalPolylogShuffleClass (primePolylogArgument p)) := by
  obtain ⟨q, _, hpos⟩ := exists_primePolylog_positive_detector p
  intro m n hmn
  have h := congrArg (valuationShuffleDetector p q) hmn
  simp only [map_smul, smul_eq_mul, RingHom.id_apply] at h
  have hz : (m - n) * valuationShuffleDetector p q
      (classicalPolylogShuffleClass (primePolylogArgument p)) = 0 := by
    rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp hz with hzero | hzero
  · exact sub_eq_zero.mp hzero
  · exact (ne_of_gt hpos hzero).elim

/-- A concrete family separates shuffle symbols from their Milnor images. -/
theorem primePolylog_symbol_separation (p : Nat.Primes) :
    classicalPolylogMilnorImage ℚ 0 (primePolylogArgument p) = 0 ∧
      Function.Injective (fun m : ℤ => m • classicalPolylogShuffleClass (primePolylogArgument p)) :=
  ⟨classicalPolylogMilnorImage_eq_zero ℚ 0 _, primePolylogShuffleClass_infinite_order p⟩

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.primePolylog_symbol_separation
