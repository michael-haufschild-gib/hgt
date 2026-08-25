import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEThirdOrderSourceCohomology

/-!
# Quadratic field-redefinition invariance of the third-order Teukolsky source

Let the gauge-fixed Einstein operator have Taylor data `(L,B,C)`, and change perturbation
coordinates by

`u = v + (1/2) K(v,v)`.

For symmetric `K`, the physical quadratic coefficients are

`u₊₊ = v₊₊ + (1/2) K(h₊,h₊)` and `u₊₋ = v₊₋ + K(h₊,h₋)`.

The Hessian changes by `Bᴷ(x,y) = B(x,y) + L(K(x,y))`; the third variation acquires the
polarized insertion of `B` against `K`. Exact expansion in the `++-` grade proves that the
transformed source and original physical source differ only by

`L(K(h₊,v₊₋) + K(h₋,v₊₊))`.

Every left resonant state annihilates this difference. Thus the total on-shell cokernel class is
coordinate invariant, but its cascade/direct decomposition is not. The scalar specialization at
the end gives an explicit redistribution: a zero original direct vertex becomes `3/2` after a
quadratic change of variables.
-/

open Complex

namespace RHTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Value of the Hessian after `u = v + K(v,v)/2`. -/
def d4EinsteinQuadraticFieldRedefinedHessianValue
    (L : V →ₗ[ℂ] V) (B K : V →ₗ[ℂ] V →ₗ[ℂ] V) (x y : V) : V :=
  B x y + L (K x y)

/-- Polarized third variation induced by a quadratic field redefinition. -/
def d4EinsteinQuadraticFieldRedefinedThirdVariationValue
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (K : V →ₗ[ℂ] V →ₗ[ℂ] V) (x y z : V) : V :=
  C x y z + B x (K y z) + B y (K x z) + B z (K x y)

/-- Transformed direct third-variation contribution in the `++-` grade. -/
def d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (K : V →ₗ[ℂ] V →ₗ[ℂ] V) (hPlus hMinus : V) : V :=
  (1 / 6 : ℂ) •
    (d4EinsteinQuadraticFieldRedefinedThirdVariationValue B C K hPlus hPlus hMinus +
      d4EinsteinQuadraticFieldRedefinedThirdVariationValue B C K hPlus hMinus hPlus +
      d4EinsteinQuadraticFieldRedefinedThirdVariationValue B C K hMinus hPlus hPlus)

/-- The direct vertex absorbs exactly the displayed part of the old quadratic cascade. -/
theorem d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus_eq
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (K : V →ₗ[ℂ] V →ₗ[ℂ] V) (hPlus hMinus : V)
    (hK : ∀ x y, K x y = K y x) :
    d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus B C K hPlus hMinus =
      d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus +
        B hPlus (K hPlus hMinus) + (1 / 2 : ℂ) • B hMinus (K hPlus hPlus) := by
  simp [d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus,
    d4EinsteinQuadraticFieldRedefinedThirdVariationValue,
    d4EinsteinDirectThirdVariationPlusPlusMinus, hK]
  module

/-- Direct-channel projection is coordinate invariant exactly when the resonant state annihilates
the quadratic insertion transferred from the cascade. -/
theorem d4TeukolskyQuadraticFieldRedefinedDirectProjection_eq_iff
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (K : V →ₗ[ℂ] V →ₗ[ℂ] V) (hPlus hMinus : V)
    (hK : ∀ x y, K x y = K y x) :
    ell (d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus B C K hPlus hMinus) =
        ell (d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus) ↔
      ell (B hPlus (K hPlus hMinus) +
        (1 / 2 : ℂ) • B hMinus (K hPlus hPlus)) = 0 := by
  rw [d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus_eq B C K hPlus hMinus hK]
  simp only [map_add, map_smul]
  constructor <;> intro h <;> linear_combination h

/-- Physical `++` coefficient expressed in the new quadratic coordinate. -/
def d4EinsteinQuadraticFieldRedefinedPhysicalPlusPlus
    (K : V →ₗ[ℂ] V →ₗ[ℂ] V) (hPlus vPlusPlus : V) : V :=
  vPlusPlus + (1 / 2 : ℂ) • K hPlus hPlus

/-- Physical `+-` coefficient expressed in the new quadratic coordinate. -/
def d4EinsteinQuadraticFieldRedefinedPhysicalPlusMinus
    (K : V →ₗ[ℂ] V →ₗ[ℂ] V) (hPlus hMinus vPlusMinus : V) : V :=
  vPlusMinus + K hPlus hMinus

/-- Complete transformed `++-` source in the new perturbation coordinate. -/
def d4EinsteinQuadraticFieldRedefinedPlusPlusMinusSource
    (L : V →ₗ[ℂ] V)
    (B K : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus vPlusPlus vPlusMinus : V) : V :=
  d4EinsteinQuadraticFieldRedefinedHessianValue L B K hPlus vPlusMinus +
    d4EinsteinQuadraticFieldRedefinedHessianValue L B K hMinus vPlusPlus +
    d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus B C K hPlus hMinus

/-- Exact grade-resolved equivalence theorem. The full transformed source changes by one
linearized-operator-exact term. -/
theorem d4EinsteinQuadraticFieldRedefinedPlusPlusMinusSource_eq
    (L : V →ₗ[ℂ] V)
    (B K : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus vPlusPlus vPlusMinus : V)
    (hK : ∀ x y, K x y = K y x) :
    d4EinsteinQuadraticFieldRedefinedPlusPlusMinusSource
        L B K C hPlus hMinus vPlusPlus vPlusMinus =
      d4EinsteinThirdOrderPlusPlusMinusSource B C hPlus hMinus
        (d4EinsteinQuadraticFieldRedefinedPhysicalPlusPlus K hPlus vPlusPlus)
        (d4EinsteinQuadraticFieldRedefinedPhysicalPlusMinus K hPlus hMinus vPlusMinus) +
      L (K hPlus vPlusMinus + K hMinus vPlusPlus) := by
  rw [d4EinsteinQuadraticFieldRedefinedPlusPlusMinusSource,
    d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus_eq B C K hPlus hMinus hK]
  simp [d4EinsteinQuadraticFieldRedefinedHessianValue,
    d4EinsteinQuadraticFieldRedefinedPhysicalPlusPlus,
    d4EinsteinQuadraticFieldRedefinedPhysicalPlusMinus,
    d4EinsteinThirdOrderPlusPlusMinusSource, map_add, map_smul]
  module

/-- A left QNM state sees the same total `++-` source in every quadratic perturbation
coordinate. -/
theorem d4TeukolskyQuadraticFieldRedefinition_resonantProjection_eq
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (B K : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (hPlus hMinus vPlusPlus vPlusMinus : V)
    (hK : ∀ x y, K x y = K y x)
    (hleft : ∀ v, ell (L v) = 0) :
    ell (d4EinsteinQuadraticFieldRedefinedPlusPlusMinusSource
        L B K C hPlus hMinus vPlusPlus vPlusMinus) =
      ell (d4EinsteinThirdOrderPlusPlusMinusSource B C hPlus hMinus
        (d4EinsteinQuadraticFieldRedefinedPhysicalPlusPlus K hPlus vPlusPlus)
        (d4EinsteinQuadraticFieldRedefinedPhysicalPlusMinus K hPlus hMinus vPlusMinus)) := by
  rw [d4EinsteinQuadraticFieldRedefinedPlusPlusMinusSource_eq
    L B K C hPlus hMinus vPlusPlus vPlusMinus hK]
  simp [map_add, hleft]

/-- Scalar countermodel to invariance of the direct/cascade split: the original direct vertex is
zero. -/
theorem d4EinsteinQuadraticFieldRedefinition_scalarOriginalDirect_eq_zero :
    d4EinsteinDirectThirdVariationPlusPlusMinus
        (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ) 1 1 = 0 := by
  simp [d4EinsteinDirectThirdVariationPlusPlusMinus]

/-- In the same scalar model, multiplication used as quadratic coordinate change creates direct
vertex `3/2`. -/
theorem d4EinsteinQuadraticFieldRedefinition_scalarRedefinedDirect_eq_threeHalves :
    d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus
        (LinearMap.lsmul ℂ ℂ)
        (0 : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ)
        (LinearMap.lsmul ℂ ℂ) 1 1 = (3 / 2 : ℂ) := by
  norm_num [d4EinsteinQuadraticFieldRedefinedDirectPlusPlusMinus,
    d4EinsteinQuadraticFieldRedefinedThirdVariationValue]

end

end RHTower
