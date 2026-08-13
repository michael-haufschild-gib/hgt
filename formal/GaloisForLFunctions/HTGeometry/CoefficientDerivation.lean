import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# Differentiating the coefficients of a multivariate polynomial

A derivation of a coefficient field extends to the polynomial ring by acting on coefficients and
killing the variables.  The construction is the dual-number graph: a derivation of `K` is the same
as a ring homomorphism `K → K[ε]`, `a ↦ a + (δ a) ε`, and evaluating a polynomial through that
homomorphism with the variables sent to `ε`-free values produces the pair `(p, δ-of-coefficients p)`.
The Leibniz rule is then the multiplicativity of that evaluation, read off in the `ε` component.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [Differential K] {σ : Type*}

/-- The dual-number graph of the coefficient derivation. -/
noncomputable def coeffGraphHom (K : Type*) [Field K] [Differential K] (σ : Type*) :
    K →+* DualNumber (MvPolynomial σ K) where
  toFun a := (MvPolynomial.C a, MvPolynomial.C (Differential.deriv a))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.fst_mul]
    · rw [TrivSqZeroExt.snd_mul]
      simp only [Differential.deriv.leibniz, smul_eq_mul, MvPolynomial.C_mul, MvPolynomial.C_add,
        TrivSqZeroExt.snd_mk, TrivSqZeroExt.fst_mk, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      ring
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp

@[simp] theorem coeffGraphHom_fst (a : K) :
    (coeffGraphHom K σ a).fst = MvPolynomial.C a := rfl

@[simp] theorem coeffGraphHom_snd (a : K) :
    (coeffGraphHom K σ a).snd = MvPolynomial.C (Differential.deriv a) := rfl

/-- Evaluation of a polynomial through the dual-number graph of the coefficient derivation. -/
noncomputable def coeffEval (K : Type*) [Field K] [Differential K] (σ : Type*) :
    MvPolynomial σ K →+* DualNumber (MvPolynomial σ K) :=
  MvPolynomial.eval₂Hom (coeffGraphHom K σ) fun i => TrivSqZeroExt.inl (MvPolynomial.X i)

theorem coeffEval_fst (p : MvPolynomial σ K) : (coeffEval K σ p).fst = p := by
  have hcomp : ((TrivSqZeroExt.fstHom ℤ (MvPolynomial σ K) (MvPolynomial σ K)).toRingHom.comp
      (coeffEval K σ)) = RingHom.id (MvPolynomial σ K) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      simp [coeffEval]
    · intro i
      simp [coeffEval]
  exact RingHom.congr_fun hcomp p

/-- Differentiation of the coefficients of a multivariate polynomial. -/
noncomputable def coeffDerivFun (p : MvPolynomial σ K) : MvPolynomial σ K := (coeffEval K σ p).snd

@[simp] theorem coeffDerivFun_C (a : K) :
    coeffDerivFun (MvPolynomial.C a : MvPolynomial σ K) = MvPolynomial.C (Differential.deriv a) := by
  simp [coeffDerivFun, coeffEval]

@[simp] theorem coeffDerivFun_X (i : σ) :
    coeffDerivFun (MvPolynomial.X i : MvPolynomial σ K) = 0 := by
  simp [coeffDerivFun, coeffEval]

theorem coeffDerivFun_zero : coeffDerivFun (0 : MvPolynomial σ K) = 0 := by
  simp [coeffDerivFun]

theorem coeffDerivFun_add (p q : MvPolynomial σ K) :
    coeffDerivFun (p + q) = coeffDerivFun p + coeffDerivFun q := by
  simp [coeffDerivFun]

theorem coeffDerivFun_mul (p q : MvPolynomial σ K) :
    coeffDerivFun (p * q) = p • coeffDerivFun q + q • coeffDerivFun p := by
  have hmul := map_mul (coeffEval K σ) p q
  have hsnd := congrArg TrivSqZeroExt.snd hmul
  rw [TrivSqZeroExt.snd_mul, coeffEval_fst, coeffEval_fst] at hsnd
  simpa [coeffDerivFun, smul_eq_mul, mul_comm] using hsnd

/-- **The coefficient derivation of a polynomial ring.** -/
noncomputable def coeffDerivation (K : Type*) [Field K] [Differential K] (σ : Type*) :
    Derivation ℤ (MvPolynomial σ K) (MvPolynomial σ K) := by
  let D : MvPolynomial σ K →+ MvPolynomial σ K :=
    { toFun := coeffDerivFun
      map_zero' := coeffDerivFun_zero
      map_add' := coeffDerivFun_add }
  exact Derivation.mk' D.toIntLinearMap coeffDerivFun_mul

@[simp] theorem coeffDerivation_apply (p : MvPolynomial σ K) :
    coeffDerivation K σ p = coeffDerivFun p := rfl

end GaloisForLFunctions.HTGeometry
