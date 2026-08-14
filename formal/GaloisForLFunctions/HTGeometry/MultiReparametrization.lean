import GaloisForLFunctions.HTGeometry.GeneralCoefficientDerivation
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# The generic reparametrisation of a differential field with several directions

A field carrying finitely many commuting derivations — for instance the functions of a complex space
with its partial derivatives — acquires a generic reparametrisation: the jets of the
reparametrisation become free coordinates, and the chain rule makes the derivation act on the base
by

`a ↦ ∑ⱼ (∂ⱼ a) · uⱼ′`.

`MultiReparamField` is the field of rational functions in those jets, with that derivation.  In it a
point of an algebraic group whose coordinates lie in the base becomes a differential-generic point,
while every automorphism of the base commuting with all the `∂ⱼ` still acts, fixing the jets.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- The polynomial ring of reparametrisation jets in `n` directions. -/
abbrev MultiReparamPoly (K : Type u) [Field K] (n : ℕ) : Type u := MvPolynomial (Fin n × ℕ) K

/-- The generic reparametrisation of a field with `n` prescribed derivations. -/
def MultiReparamField (K : Type u) [Field K] (n : ℕ) : Type u :=
  FractionRing (MultiReparamPoly K n)

namespace MultiReparamField

noncomputable instance : Field (MultiReparamField K n) :=
  inferInstanceAs (Field (FractionRing (MultiReparamPoly K n)))

noncomputable instance : Algebra (MultiReparamPoly K n) (MultiReparamField K n) :=
  inferInstanceAs (Algebra (MultiReparamPoly K n) (FractionRing (MultiReparamPoly K n)))

instance : IsFractionRing (MultiReparamPoly K n) (MultiReparamField K n) :=
  inferInstanceAs (IsFractionRing (MultiReparamPoly K n) (FractionRing (MultiReparamPoly K n)))

noncomputable instance : Algebra K (MultiReparamField K n) :=
  inferInstanceAs (Algebra K (FractionRing (MultiReparamPoly K n)))

instance : IsScalarTower K (MultiReparamPoly K n) (MultiReparamField K n) :=
  inferInstanceAs (IsScalarTower K (MultiReparamPoly K n) (FractionRing (MultiReparamPoly K n)))

instance [CharZero K] : CharZero (MultiReparamPoly K n) :=
  charZero_of_injective_algebraMap (MvPolynomial.C_injective (Fin n × ℕ) K)

instance [CharZero K] : CharZero (MultiReparamField K n) :=
  charZero_of_injective_algebraMap
    (IsFractionRing.injective (MultiReparamPoly K n) (MultiReparamField K n))

/-- The `i`-th jet of the `j`-th direction of the reparametrisation. -/
noncomputable def jet (p : Fin n × ℕ) : MultiReparamField K n :=
  algebraMap (MultiReparamPoly K n) (MultiReparamField K n) (MvPolynomial.X p)

section

variable (d : Fin n → Derivation ℤ K K)

/-- The chain-rule coefficient map: the derivative of a base element picks up the velocities. -/
noncomputable def chainCoeff : K →+ MultiReparamPoly K n where
  toFun a := ∑ j : Fin n, MvPolynomial.C (d j a) * MvPolynomial.X (j, 0)
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, add_mul]
    rw [Finset.sum_add_distrib]

theorem chainCoeff_apply (a : K) :
    chainCoeff d a = ∑ j : Fin n, MvPolynomial.C (d j a) * MvPolynomial.X (j, 0) := rfl

theorem chainCoeff_leibniz (a b : K) :
    chainCoeff d (a * b)
      = MvPolynomial.C a * chainCoeff d b + MvPolynomial.C b * chainCoeff d a := by
  rw [chainCoeff_apply, chainCoeff_apply, chainCoeff_apply, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz]
  simp only [smul_eq_mul, MvPolynomial.C_add, MvPolynomial.C_mul]
  ring

theorem chainCoeff_one : chainCoeff d (1 : K) = 0 := by
  rw [chainCoeff_apply]
  simp

/-- The chain-rule derivation on the jet polynomial ring. -/
noncomputable def polyDerivation :
    Derivation ℤ (MultiReparamPoly K n) (MultiReparamPoly K n) :=
  generalCoeffDerivation (chainCoeff d) (chainCoeff_leibniz d) (chainCoeff_one d)
    + Derivation.restrictScalars ℤ
        (MvPolynomial.mkDerivation K fun p : Fin n × ℕ =>
          (MvPolynomial.X (p.1, p.2 + 1) : MultiReparamPoly K n))

theorem polyDerivation_C (a : K) :
    polyDerivation d (MvPolynomial.C a) = chainCoeff d a := by
  show generalCoeffDerivation (chainCoeff d) (chainCoeff_leibniz d) (chainCoeff_one d)
      (MvPolynomial.C a)
      + (MvPolynomial.mkDerivation K fun p : Fin n × ℕ =>
          (MvPolynomial.X (p.1, p.2 + 1) : MultiReparamPoly K n)) (MvPolynomial.C a) = _
  have hC : (MvPolynomial.C a : MultiReparamPoly K n) = algebraMap K (MultiReparamPoly K n) a := rfl
  rw [generalCoeffDerivation_apply, generalCoeffDerivFun_C, hC, Derivation.map_algebraMap, add_zero]

theorem polyDerivation_X (p : Fin n × ℕ) :
    polyDerivation d (MvPolynomial.X p) = MvPolynomial.X (p.1, p.2 + 1) := by
  show generalCoeffDerivation (chainCoeff d) (chainCoeff_leibniz d) (chainCoeff_one d)
      (MvPolynomial.X p)
      + (MvPolynomial.mkDerivation K fun p : Fin n × ℕ =>
          (MvPolynomial.X (p.1, p.2 + 1) : MultiReparamPoly K n)) (MvPolynomial.X p) = _
  rw [generalCoeffDerivation_apply, generalCoeffDerivFun_X, MvPolynomial.mkDerivation_X, zero_add]

/-- The chain-rule derivation, valued in the reparametrisation field. -/
noncomputable def fieldDerivationPoly :
    Derivation ℤ (MultiReparamPoly K n) (MultiReparamField K n) :=
  (Algebra.linearMap (MultiReparamPoly K n) (MultiReparamField K n)).compDer (polyDerivation d)

/-- **The derivation of the generic reparametrisation with several directions.** -/
noncomputable def fieldDerivation :
    Derivation ℤ (MultiReparamField K n) (MultiReparamField K n) :=
  GaloisForLFunctions.fractionRingDerivation (fieldDerivationPoly d)

@[simp] theorem fieldDerivation_jet (p : Fin n × ℕ) :
    fieldDerivation d (jet p : MultiReparamField K n) = jet (p.1, p.2 + 1) := by
  rw [fieldDerivation, jet, GaloisForLFunctions.fractionRingDerivation_algebraMap]
  show (Algebra.linearMap (MultiReparamPoly K n) (MultiReparamField K n))
      (polyDerivation d (MvPolynomial.X p)) = _
  rw [polyDerivation_X]
  rfl

/-- **The chain rule.**  The derivative of a base element is the sum of its partial derivatives
against the velocities. -/
theorem fieldDerivation_algebraMap (a : K) :
    fieldDerivation d (algebraMap K (MultiReparamField K n) a)
      = ∑ j : Fin n, algebraMap K (MultiReparamField K n) (d j a) * jet (j, 0) := by
  have hbase : (algebraMap K (MultiReparamField K n) a)
      = algebraMap (MultiReparamPoly K n) (MultiReparamField K n) (MvPolynomial.C a) := by
    rw [IsScalarTower.algebraMap_apply K (MultiReparamPoly K n) (MultiReparamField K n)]
    rfl
  rw [fieldDerivation, hbase, GaloisForLFunctions.fractionRingDerivation_algebraMap]
  show (Algebra.linearMap (MultiReparamPoly K n) (MultiReparamField K n))
      (polyDerivation d (MvPolynomial.C a)) = _
  rw [polyDerivation_C, chainCoeff_apply]
  show algebraMap (MultiReparamPoly K n) (MultiReparamField K n)
      (∑ j : Fin n, MvPolynomial.C (d j a) * MvPolynomial.X (j, 0)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  congr 1

end

end MultiReparamField

end GaloisForLFunctions.HTGeometry
