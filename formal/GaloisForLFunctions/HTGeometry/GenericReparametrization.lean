import GaloisForLFunctions.HTGeometry.CoefficientDerivation
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The generic reparametrisation of a differential field

Composing the functions of a differential field `K` with a completely free reparametrisation `u` of
the variable produces a new differential field: the jets `u′, u″, …` are new free coordinates, and
the chain rule makes the derivation act on `K` by `a ↦ (δ a) · u′`.

`ReparamField K` is the field of rational functions in those jet coordinates over `K`, with that
derivation.  In it the elements of `K` are no longer differentially algebraic over the constants of
`K`: their derivatives carry the free velocity.  This is the carrier on which a point of an
algebraic group with coordinates in `K` becomes a *differential-generic* point, while every
derivation-preserving automorphism of `K` still acts, fixing the jet coordinates.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

universe u

/-- The polynomial ring of reparametrisation jets over a differential field. -/
abbrev ReparamPoly (K : Type u) [Field K] [Differential K] : Type u := MvPolynomial ℕ K

/-- The generic reparametrisation of a differential field. -/
def ReparamField (K : Type u) [Field K] [Differential K] : Type u :=
  FractionRing (ReparamPoly K)

namespace ReparamField

variable {K : Type u} [Field K] [Differential K]

noncomputable instance : Field (ReparamField K) :=
  inferInstanceAs (Field (FractionRing (ReparamPoly K)))

noncomputable instance : Algebra (ReparamPoly K) (ReparamField K) :=
  inferInstanceAs (Algebra (ReparamPoly K) (FractionRing (ReparamPoly K)))

instance : IsFractionRing (ReparamPoly K) (ReparamField K) :=
  inferInstanceAs (IsFractionRing (ReparamPoly K) (FractionRing (ReparamPoly K)))

noncomputable instance : Algebra K (ReparamField K) :=
  inferInstanceAs (Algebra K (FractionRing (ReparamPoly K)))

instance : IsScalarTower K (ReparamPoly K) (ReparamField K) :=
  inferInstanceAs (IsScalarTower K (ReparamPoly K) (FractionRing (ReparamPoly K)))

instance [CharZero K] : CharZero (ReparamPoly K) :=
  charZero_of_injective_algebraMap (MvPolynomial.C_injective ℕ K)

instance [CharZero K] : CharZero (ReparamField K) :=
  charZero_of_injective_algebraMap
    (IsFractionRing.injective (ReparamPoly K) (ReparamField K))

/-- The `i`-th jet of the reparametrisation. -/
noncomputable def jet (i : ℕ) : ReparamField K :=
  algebraMap (ReparamPoly K) (ReparamField K) (MvPolynomial.X i)

/-- The chain-rule derivation on the polynomial ring: it advances the jets and multiplies the
coefficient derivative by the velocity. -/
noncomputable def polyDerivation (K : Type u) [Field K] [Differential K] :
    Derivation ℤ (ReparamPoly K) (ReparamPoly K) :=
  (MvPolynomial.X 0 : ReparamPoly K) • coeffDerivation K ℕ
    + Derivation.restrictScalars ℤ
        (MvPolynomial.mkDerivation K fun i : ℕ => (MvPolynomial.X (i + 1) : ReparamPoly K))

theorem polyDerivation_C (a : K) :
    polyDerivation K (MvPolynomial.C a) =
      MvPolynomial.C (Differential.deriv a) * MvPolynomial.X 0 := by
  show (MvPolynomial.X 0 : ReparamPoly K) • coeffDerivation K ℕ (MvPolynomial.C a)
      + (MvPolynomial.mkDerivation K fun i : ℕ => (MvPolynomial.X (i + 1) : ReparamPoly K))
          (MvPolynomial.C a) = _
  have hC : (MvPolynomial.C a : ReparamPoly K) = algebraMap K (ReparamPoly K) a := rfl
  rw [coeffDerivation_apply, coeffDerivFun_C, hC, Derivation.map_algebraMap]
  simp only [smul_eq_mul, add_zero]
  ring

theorem polyDerivation_X (i : ℕ) :
    polyDerivation K (MvPolynomial.X i) = MvPolynomial.X (i + 1) := by
  show (MvPolynomial.X 0 : ReparamPoly K) • coeffDerivation K ℕ (MvPolynomial.X i)
      + (MvPolynomial.mkDerivation K fun i : ℕ => (MvPolynomial.X (i + 1) : ReparamPoly K))
          (MvPolynomial.X i) = _
  rw [coeffDerivation_apply, coeffDerivFun_X, MvPolynomial.mkDerivation_X]
  simp

/-- The chain-rule derivation, valued in the reparametrisation field. -/
noncomputable def fieldDerivationPoly (K : Type u) [Field K] [Differential K] :
    Derivation ℤ (ReparamPoly K) (ReparamField K) :=
  (Algebra.linearMap (ReparamPoly K) (ReparamField K)).compDer (polyDerivation K)

/-- **The derivation of the generic reparametrisation.** -/
noncomputable def fieldDerivation (K : Type u) [Field K] [Differential K] :
    Derivation ℤ (ReparamField K) (ReparamField K) :=
  fractionRingDerivation (fieldDerivationPoly K)

noncomputable instance : Differential (ReparamField K) := ⟨fieldDerivation K⟩

theorem deriv_eq (z : ReparamField K) : z′ = fieldDerivation K z := rfl

@[simp] theorem deriv_jet (i : ℕ) : (jet i : ReparamField K)′ = jet (i + 1) := by
  rw [deriv_eq, fieldDerivation, jet, fractionRingDerivation_algebraMap]
  show (Algebra.linearMap (ReparamPoly K) (ReparamField K))
      (polyDerivation K (MvPolynomial.X i)) = _
  rw [polyDerivation_X]
  rfl

/-- **The chain rule.**  The derivative of a function of `K` is its own derivative times the
velocity of the reparametrisation. -/
@[simp] theorem deriv_algebraMap (a : K) :
    ((algebraMap K (ReparamField K) a))′
      = algebraMap K (ReparamField K) (Differential.deriv a) * jet 0 := by
  have hbase : (algebraMap K (ReparamField K) a)
      = algebraMap (ReparamPoly K) (ReparamField K) (MvPolynomial.C a) := by
    rw [IsScalarTower.algebraMap_apply K (ReparamPoly K) (ReparamField K)]
    rfl
  rw [deriv_eq, fieldDerivation, hbase, fractionRingDerivation_algebraMap]
  show (Algebra.linearMap (ReparamPoly K) (ReparamField K))
      (polyDerivation K (MvPolynomial.C a)) = _
  rw [polyDerivation_C]
  rw [IsScalarTower.algebraMap_apply K (ReparamPoly K) (ReparamField K)]
  show algebraMap (ReparamPoly K) (ReparamField K)
      (MvPolynomial.C (Differential.deriv a) * MvPolynomial.X 0) = _
  rw [map_mul]
  rfl

end ReparamField

end GaloisForLFunctions.HTGeometry
