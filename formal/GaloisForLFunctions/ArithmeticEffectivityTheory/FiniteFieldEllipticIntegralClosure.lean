import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticGlobalField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral functions on the affine elliptic curve

Quadratic conjugation extracts the two rational-function coordinates of an
integral element. Squarefreeness of `x³−x` excludes a nonconstant denominator
in the second coordinate, so the affine coordinate ring is integrally closed.
-/

open Polynomial

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

private lemma negative_y_root :
    curve.toAffine.polynomial.eval₂ (algebraMap Constants[X] A) (-yA) = 0 := by
  simp only [curve_polynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, neg_sq]
  rw [cubic, map_sub, map_pow]
  exact sub_eq_zero.mpr relationA

/-- The involution fixing `x` and negating `y` on the actual coordinate ring. -/
def coordinateConjugation : A →ₐ[Constants[X]] A :=
  AdjoinRoot.liftAlgHom curve.toAffine.polynomial (Algebra.ofId _ _) (-yA) negative_y_root

@[simp] lemma coordinateConjugation_y : coordinateConjugation yA = -yA :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma coordinateConjugation_involutive : Function.Involutive coordinateConjugation := by
  intro a
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  simp only [← yA_eq, map_add, map_smul, map_one, coordinateConjugation_y, map_neg, neg_neg]

/-- Quadratic conjugation on the actual fraction field. -/
def fieldConjugation : K →ₐ[Constants[X]] K :=
  IsFractionRing.liftAlgHom
    (g := (IsScalarTower.toAlgHom Constants[X] A K).comp coordinateConjugation)
    ((IsFractionRing.injective A K).comp coordinateConjugation_involutive.injective)

@[simp] lemma fieldConjugation_algebraMap (a : A) :
    fieldConjugation (algebraMap A K a) = algebraMap A K (coordinateConjugation a) :=
  IsFractionRing.lift_algebraMap
    (K := K) (g := ((IsScalarTower.toAlgHom Constants[X] A K).comp coordinateConjugation).toRingHom)
    ((IsFractionRing.injective A K).comp coordinateConjugation_involutive.injective) a

@[simp] lemma fieldConjugation_y : fieldConjugation y = -y := by
  rw [y, fieldConjugation_algebraMap, coordinateConjugation_y, map_neg]

@[simp] lemma fieldConjugation_ratFunc (r : RatFunc Constants) :
    fieldConjugation (algebraMap (RatFunc Constants) K r) =
      algebraMap (RatFunc Constants) K r := by
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective Constants[X] r
  simp only [map_div₀, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]

@[simp] lemma rationalFunctionBasis_zero : rationalFunctionBasis 0 = (1 : K) := by
  rw [rationalFunctionBasis, Module.Basis.mk_apply]
  change algebraMap A K (WeierstrassCurve.Affine.CoordinateRing.basis curve.toAffine 0) = 1
  rw [WeierstrassCurve.Affine.CoordinateRing.basis_zero, map_one]

@[simp] lemma rationalFunctionBasis_one : rationalFunctionBasis 1 = y := by
  rw [rationalFunctionBasis, Module.Basis.mk_apply]
  change algebraMap A K (WeierstrassCurve.Affine.CoordinateRing.basis curve.toAffine 1) = y
  rw [WeierstrassCurve.Affine.CoordinateRing.basis_one]
  rfl

/-- Every function is uniquely expressible in the rational basis `(1,y)`. -/
lemma exists_ratFunc_coordinates (z : K) :
    ∃ p q : RatFunc Constants,
      z = algebraMap (RatFunc Constants) K p + algebraMap (RatFunc Constants) K q * y := by
  have h := rationalFunctionBasis.sum_repr z
  rw [Fin.sum_univ_two, rationalFunctionBasis_zero, rationalFunctionBasis_one,
    Algebra.smul_def, Algebra.smul_def, mul_one] at h
  exact ⟨_, _, h.symm⟩

lemma fieldConjugation_coordinates (p q : RatFunc Constants) :
    fieldConjugation (algebraMap (RatFunc Constants) K p +
      algebraMap (RatFunc Constants) K q * y) =
      algebraMap (RatFunc Constants) K p - algebraMap (RatFunc Constants) K q * y := by
  simp only [map_add, map_mul, fieldConjugation_ratFunc, fieldConjugation_y, mul_neg,
    sub_eq_add_neg]

private lemma rational_cubic_relation :
    y ^ 2 = algebraMap (RatFunc Constants) K (algebraMap Constants[X] (RatFunc Constants) cubic) := by
  rw [← IsScalarTower.algebraMap_apply, cubic, map_sub, map_pow]
  exact relation

lemma coordinates_trace (p q : RatFunc Constants) :
    let z := algebraMap (RatFunc Constants) K p + algebraMap (RatFunc Constants) K q * y
    z + fieldConjugation z = algebraMap (RatFunc Constants) K (2 * p) := by
  dsimp only
  rw [fieldConjugation_coordinates, map_mul, map_ofNat]
  ring

lemma coordinates_norm (p q : RatFunc Constants) :
    let z := algebraMap (RatFunc Constants) K p + algebraMap (RatFunc Constants) K q * y
    z * fieldConjugation z = algebraMap (RatFunc Constants) K
      (p ^ 2 - algebraMap Constants[X] (RatFunc Constants) cubic * q ^ 2) := by
  dsimp only
  rw [fieldConjugation_coordinates, map_sub, map_mul, map_pow, map_pow]
  calc
    _ = (algebraMap (RatFunc Constants) K p) ^ 2 -
        (algebraMap (RatFunc Constants) K q) ^ 2 * y ^ 2 := by ring
    _ = _ := by rw [rational_cubic_relation]; ring

lemma integral_ratFunc_image_iff (p : RatFunc Constants) :
    IsIntegral Constants[X] (algebraMap (RatFunc Constants) K p) ↔
      ∃ a : Constants[X], algebraMap Constants[X] (RatFunc Constants) a = p := by
  rw [isIntegral_algebraMap_iff (algebraMap (RatFunc Constants) K).injective]
  exact IsIntegrallyClosedIn.isIntegral_iff

lemma integral_coordinates_trace_norm (p q : RatFunc Constants)
    (hz : IsIntegral Constants[X]
      (algebraMap (RatFunc Constants) K p + algebraMap (RatFunc Constants) K q * y)) :
    (∃ a : Constants[X], algebraMap Constants[X] (RatFunc Constants) a = 2 * p) ∧
    ∃ b : Constants[X], algebraMap Constants[X] (RatFunc Constants) b =
      p ^ 2 - algebraMap Constants[X] (RatFunc Constants) cubic * q ^ 2 := by
  constructor
  · apply (integral_ratFunc_image_iff _).mp
    rw [← coordinates_trace]
    exact hz.add (hz.map fieldConjugation)
  · apply (integral_ratFunc_image_iff _).mp
    rw [← coordinates_norm]
    exact hz.mul (hz.map fieldConjugation)

/-- A squarefree polynomial cannot absorb a squared rational-function denominator. -/
lemma exists_polynomial_of_squarefree_mul_sq (g : Constants[X]) (hg : Squarefree g)
    (q : RatFunc Constants)
    (hq : ∃ b : Constants[X], algebraMap Constants[X] (RatFunc Constants) b =
      algebraMap Constants[X] (RatFunc Constants) g * q ^ 2) :
    ∃ a : Constants[X], algebraMap Constants[X] (RatFunc Constants) a = q := by
  obtain ⟨b, hb⟩ := hq
  have hd : algebraMap Constants[X] (RatFunc Constants) q.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero q)
  have he : g * q.num ^ 2 = b * q.denom ^ 2 := by
    apply RatFunc.algebraMap_injective Constants
    simp only [map_mul, map_pow]
    rw [← RatFunc.num_div_denom q] at hb
    field_simp [hd] at hb
    exact hb.symm
  have hdiv : q.denom ^ 2 ∣ g * q.num ^ 2 := ⟨b, by rw [he]; ring⟩
  have hcop : IsCoprime (q.denom ^ 2) (q.num ^ 2) :=
    (RatFunc.isCoprime_num_denom q).symm.pow
  have hu : IsUnit q.denom := hg q.denom
    (by simpa only [pow_two] using hcop.dvd_of_dvd_mul_right hdiv)
  have hd1 : q.denom ∣ 1 := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact ⟨↑u⁻¹, by simp⟩
  obtain ⟨a, ha⟩ := (RatFunc.denom_dvd (x := q) (q := 1) one_ne_zero).mp hd1
  exact ⟨a, by simpa using ha.symm⟩

private lemma two_mul_two_ratFunc : (2 : RatFunc Constants) * 2 = 1 := by
  have h := congrArg (algebraMap Constants (RatFunc Constants))
    (show (2 : Constants) * 2 = 1 by decide)
  simpa only [map_mul, map_ofNat, map_one] using h

/-- Integrality forces both rational-function coordinates to be polynomials. -/
theorem integral_coordinates_are_polynomial (p q : RatFunc Constants)
    (hz : IsIntegral Constants[X]
      (algebraMap (RatFunc Constants) K p + algebraMap (RatFunc Constants) K q * y)) :
    (∃ a : Constants[X], algebraMap Constants[X] (RatFunc Constants) a = p) ∧
      ∃ b : Constants[X], algebraMap Constants[X] (RatFunc Constants) b = q := by
  obtain ⟨⟨a, ha⟩, b, hb⟩ := integral_coordinates_trace_norm p q hz
  have hp : algebraMap Constants[X] (RatFunc Constants) (2 * a) = p := by
    rw [map_mul, map_ofNat, ha, ← mul_assoc, two_mul_two_ratFunc, one_mul]
  refine ⟨⟨2 * a, hp⟩, exists_polynomial_of_squarefree_mul_sq cubic cubic_squarefree q ?_⟩
  refine ⟨(2 * a) ^ 2 - b, ?_⟩
  rw [map_sub, map_pow, hp, hb]
  ring

/-- The integral closure of `𝔽₃[x]` consists exactly of the actual affine functions. -/
theorem isIntegral_iff_coordinateRing_image (z : K) :
    IsIntegral Constants[X] z ↔ ∃ a : A, algebraMap A K a = z := by
  constructor
  · intro hz
    obtain ⟨p, q, rfl⟩ := exists_ratFunc_coordinates z
    obtain ⟨⟨a, ha⟩, b, hb⟩ := integral_coordinates_are_polynomial p q hz
    refine ⟨a • (1 : A) + b • yA, ?_⟩
    simp only [map_add, Algebra.smul_def, map_mul, mul_one,
      ← IsScalarTower.algebraMap_apply, y]
    rw [← ha, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · rintro ⟨a, rfl⟩
    exact (Algebra.IsIntegral.isIntegral a).algebraMap

instance coordinateRing_isIntegralClosure : IsIntegralClosure A Constants[X] K :=
  ⟨IsFractionRing.injective A K, isIntegral_iff_coordinateRing_image _⟩

/-- The affine ring of the actual nonsingular elliptic curve is Dedekind. -/
instance coordinateRing_isDedekindDomain : IsDedekindDomain A :=
  IsIntegralClosure.isDedekindDomain Constants[X] (RatFunc Constants) K A

/-- The abstract integral closure and the actual affine coordinate ring agree canonically. -/
def coordinateRingEquivRingOfIntegers : A ≃ₐ[Constants[X]] RingOfIntegers :=
  IsIntegralClosure.equiv Constants[X] A K RingOfIntegers

@[simp] lemma coordinateRingEquivRingOfIntegers_algebraMap (a : A) :
    algebraMap RingOfIntegers K (coordinateRingEquivRingOfIntegers a) = algebraMap A K a :=
  IsIntegralClosure.algebraMap_equiv Constants[X] A K RingOfIntegers a

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
