import GaloisForLFunctions.HTGeometry.GammaPoleFormalGermFreeness

/-!
# Gamma pole logarithmic jets are free over the rational pole-position field

The existing factorial--harmonic theorem proves freeness over `ℂ`.  The moving-base Gamma jet
groupoid needs a stronger statement: rational functions of the pole index must be allowed as
coefficients.  Otherwise the reciprocal base points `1 / n` could conceivably absorb a clock
relation.

This file proves the relative theorem.  The generalized harmonic jets are already algebraically
independent over `ℂ(n)`, and the reciprocal signed factorial is transcendental over their complete
finite polynomial ring.  A weighted affine substitution identifies these source coordinates with
the exact logarithmic derivatives of the normalized Gamma pole units.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions

noncomputable section

abbrev GammaPoleRationalBase := RatFunc ℂ

local instance gammaPoleRationalNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm :=
  ratNatEval.toAlgebra

local instance gammaPoleRelativeComplexNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- Coordinatewise affine substitution over an arbitrary commutative base ring. -/
def affineCoordinateMapOver
    {R : Type*} [CommRing R] (m : ℕ) (α β : Fin m → R) :
    MvPolynomial (Fin m) R →+* MvPolynomial (Fin m) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j =>
    MvPolynomial.C (α j) * MvPolynomial.X j + MvPolynomial.C (β j)

def affineCoordinateMapOverInv
    {K : Type*} [Field K] (m : ℕ) (α β : Fin m → K) :
    MvPolynomial (Fin m) K →+* MvPolynomial (Fin m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j =>
    MvPolynomial.C (α j)⁻¹ *
      (MvPolynomial.X j - MvPolynomial.C (β j))

theorem affineCoordinateMapOver_injective
    {K : Type*} [Field K] (m : ℕ) {α β : Fin m → K}
    (hα : ∀ j, α j ≠ 0) :
    Function.Injective (affineCoordinateMapOver m α β) := by
  have hcomp :
      (affineCoordinateMapOverInv m α β).comp
          (affineCoordinateMapOver m α β) =
        RingHom.id (MvPolynomial (Fin m) K) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineCoordinateMapOver, affineCoordinateMapOverInv]
    · intro j
      simp [affineCoordinateMapOver, affineCoordinateMapOverInv]
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      simp [hα j]
  apply Function.LeftInverse.injective
  intro P
  change affineCoordinateMapOverInv m α β
      (affineCoordinateMapOver m α β P) = P
  exact RingHom.congr_fun hcomp P

/-- Send coordinate `j` to its affine harmonic form times the reciprocal-factorial variable to
power `j+1`, now with rational functions of the pole index as ground coefficients. -/
def rationalWeightedAffineEmbedding
    (m : ℕ) (α β : Fin m → GammaPoleRationalBase) :
    MvPolynomial (Fin m) GammaPoleRationalBase →+*
      Polynomial (MvPolynomial (Fin m) GammaPoleRationalBase) :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp
      (MvPolynomial.C : GammaPoleRationalBase →+*
        MvPolynomial (Fin m) GammaPoleRationalBase)) fun j =>
    Polynomial.C
      (MvPolynomial.C (α j) * MvPolynomial.X j + MvPolynomial.C (β j)) *
      Polynomial.X ^ ((j : ℕ) + 1)

theorem rationalWeightedAffineEmbedding_injective
    (m : ℕ) {α β : Fin m → GammaPoleRationalBase}
    (hα : ∀ j, α j ≠ 0) :
    Function.Injective (rationalWeightedAffineEmbedding m α β) := by
  let atOne :
      Polynomial (MvPolynomial (Fin m) GammaPoleRationalBase) →+*
        MvPolynomial (Fin m) GammaPoleRationalBase :=
    Polynomial.evalRingHom 1
  have hcomp :
      atOne.comp (rationalWeightedAffineEmbedding m α β) =
        affineCoordinateMapOver m α β := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [atOne, rationalWeightedAffineEmbedding, affineCoordinateMapOver]
    · intro j
      simp [atOne, rationalWeightedAffineEmbedding, affineCoordinateMapOver]
  intro P Q hPQ
  apply affineCoordinateMapOver_injective m hα
  have h := congrArg atOne hPQ
  change (atOne.comp (rationalWeightedAffineEmbedding m α β)) P =
    (atOne.comp (rationalWeightedAffineEmbedding m α β)) Q at h
  rwa [hcomp] at h

def gammaPoleLogDerivativeRationalSlope
    (_j : ℕ) : GammaPoleRationalBase := -1

def gammaPoleLogDerivativeRationalConstant
    (j : ℕ) : GammaPoleRationalBase :=
  RatFunc.C (((j + 1).factorial : ℂ) * gammaPoleLogConstant j)

/-- Evaluation of a rational-coefficient polynomial at a finite prefix of the exact Gamma pole
logarithmic derivative germs. -/
def gammaPoleLogDerivativeRationalEval (m : ℕ) :
    MvPolynomial (Fin m) GammaPoleRationalBase →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval fun j =>
    gammaPoleLogDerivativeGerm (j : ℕ)

theorem gammaPoleLogDerivativeRationalEval_eq_comp (m : ℕ) :
    gammaPoleLogDerivativeRationalEval m =
      (reciprocalSignedFactorialEval m).comp
        (rationalWeightedAffineEmbedding m
          (fun j => gammaPoleLogDerivativeRationalSlope (j : ℕ))
          (fun j => gammaPoleLogDerivativeRationalConstant (j : ℕ))) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [gammaPoleLogDerivativeRationalEval,
      reciprocalSignedFactorialEval, rationalWeightedAffineEmbedding,
      harmonicJetEval]
  · intro j
    have hbase (c : ℂ) :
        algebraMap ℂ NatGerm c = ratNatEval (RatFunc.C c) := rfl
    simp [gammaPoleLogDerivativeRationalEval,
      reciprocalSignedFactorialEval, rationalWeightedAffineEmbedding,
      harmonicJetEval, gammaPoleLogDerivativeGerm,
      gammaPoleLogDerivativeRationalSlope,
      gammaPoleLogDerivativeRationalConstant, hbase]
    ring

theorem gammaPoleLogDerivativeRationalEval_injective (m : ℕ) :
    Function.Injective (gammaPoleLogDerivativeRationalEval m) := by
  rw [gammaPoleLogDerivativeRationalEval_eq_comp]
  exact (reciprocalSignedFactorialEval_injective m).comp
    (rationalWeightedAffineEmbedding_injective m fun _j => by
      simp [gammaPoleLogDerivativeRationalSlope])

/-- Every finite prefix of the exact Gamma pole logarithmic jets is algebraically independent over
the full rational pole-position field `ℂ(n)`. -/
theorem algebraicIndependent_gammaPoleLogDerivativeGerm_over_ratFunc_fin
    (m : ℕ) :
    AlgebraicIndependent GammaPoleRationalBase
      (fun j : Fin m => gammaPoleLogDerivativeGerm (j : ℕ)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleLogDerivativeRationalEval, MvPolynomial.aeval_def] using
    gammaPoleLogDerivativeRationalEval_injective m

/-- **Relative Gamma pole-log freeness.**  The complete logarithmic jet family is countably
algebraically independent even after adjoining every rational function of the pole index. -/
theorem algebraicIndependent_gammaPoleLogDerivativeGerm_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase gammaPoleLogDerivativeGerm := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  rcases ht.bddAbove with ⟨k, hk⟩
  let f : t → Fin (k + 1) := fun i => ⟨i, Nat.lt_succ_of_le (hk i.2)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext_iff.mp hij
  have hprefix :=
    algebraicIndependent_gammaPoleLogDerivativeGerm_over_ratFunc_fin (k + 1)
  have hsub := hprefix.comp f hf
  simpa [f, Function.comp_def] using hsub

end

end GaloisForLFunctions
