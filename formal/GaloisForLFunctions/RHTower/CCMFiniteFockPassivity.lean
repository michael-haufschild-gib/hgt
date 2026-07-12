/-
# Finite diagonal-Fock passivity

This file formalizes the unconditional finite-dimensional algebra behind the
Connes--Consani--Moscovici diagonal Fock lift.  A base Gram matrix `A` and a
transport Gram matrix `C` combine entrywise: the leakage Gram is `A ⊙ C`, and
the defect Gram is `A - A ⊙ C`.

The main theorem identifies nonnegativity of this defect with contractive
passivity of the diagonal lift.  A second theorem resolves the transport
kernel into Euler, boundary, and Mellin channels.  No zeta-zero statement is
assumed here: the genuinely RH-bearing assertion is precisely the resulting
source-resolved inequality.
-/
import GaloisForLFunctions.RHTower.SeamSpectralFlow
import Mathlib.LinearAlgebra.Matrix.Hadamard

open Complex Matrix

namespace RHTower

noncomputable section

variable {N : ℕ}

/-- Gram matrix of a finite family of features in a finite coordinate space. -/
def ccmFiniteFeatureGram {m : ℕ} {α : Type*} [Fintype α]
    (u : Fin m → α → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => ∑ a, u i a * star (u j a)

/-- The diagonal tensor feature sends the same sample index into both factors. -/
def ccmDiagonalTensorFeature {m k l : ℕ}
    (u : Fin m → Fin k → ℂ) (v : Fin m → Fin l → ℂ) :
    Fin m → (Fin k × Fin l) → ℂ :=
  fun i ab => u i ab.1 * v i ab.2

/-- Entrywise tensor leakage of a base Gram matrix through a transport Gram. -/
def ccmDiagonalLeakageGram
    (A C : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  A.hadamard C

/-- The finite diagonal-Fock defect `A - A ⊙ C`. -/
def ccmDiagonalDefectGram
    (A C : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  A - ccmDiagonalLeakageGram A C

/-- Exact Gram law for the diagonal tensor lift: the Gram matrix of diagonal
tensor features is the Hadamard product of the two factor Gram matrices. -/
theorem ccmFiniteFeatureGram_diagonalTensor {m k l : ℕ}
    (u : Fin m → Fin k → ℂ) (v : Fin m → Fin l → ℂ) :
    ccmFiniteFeatureGram (ccmDiagonalTensorFeature u v) =
      ccmDiagonalLeakageGram (ccmFiniteFeatureGram u) (ccmFiniteFeatureGram v) := by
  ext i j
  simp only [ccmFiniteFeatureGram, ccmDiagonalTensorFeature, Matrix.of_apply,
    ccmDiagonalLeakageGram, Matrix.hadamard_apply, map_mul]
  rw [Finset.sum_product]
  simp_rw [mul_assoc, mul_left_comm (v i _), mul_comm (v i _)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Contractive passivity of the diagonal tensor lift on every coefficient packet. -/
def CCMFiniteFockPassivity
    (A C : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ x : Fin N → ℂ,
    (star x ⬝ᵥ (ccmDiagonalLeakageGram A C).mulVec x).re ≤
      (star x ⬝ᵥ A.mulVec x).re

/-- A quadratic form converts matrix subtraction into subtraction of real energies. -/
theorem ccm_quadratic_sub
    (A B : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    (star x ⬝ᵥ (A - B).mulVec x).re =
      (star x ⬝ᵥ A.mulVec x).re - (star x ⬝ᵥ B.mulVec x).re := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

/-- Exact finite Fock law: defect nonnegativity is diagonal-lift passivity. -/
theorem ccmDiagonalDefect_kreinNonneg_iff_passivity
    (A C : Matrix (Fin N) (Fin N) ℂ) :
    KreinNonneg (ccmDiagonalDefectGram A C) ↔ CCMFiniteFockPassivity A C := by
  constructor
  · intro h x
    have hx := h x
    rw [ccmDiagonalDefectGram, ccm_quadratic_sub] at hx
    linarith
  · intro h x
    rw [ccmDiagonalDefectGram, ccm_quadratic_sub]
    linarith [h x]

/-- Hadamard multiplication transports an exact source decomposition without mixing channels. -/
theorem ccmDiagonalLeakage_incidence
    (A C E B M : Matrix (Fin N) (Fin N) ℂ)
    (hC : C = E - B + M) :
    ccmDiagonalLeakageGram A C =
      ccmDiagonalLeakageGram A E - ccmDiagonalLeakageGram A B +
        ccmDiagonalLeakageGram A M := by
  subst C
  ext i j
  simp [ccmDiagonalLeakageGram, Matrix.hadamard]
  ring

/-- The source-resolved passivity inequality.  In the intended Mellin incidence,
`E` is the Euler channel, `B` the elementary boundary channel, and `M` the
signed Mellin remainder.  Establishing this predicate cofinally for the actual
zeta data is the RH-bearing theorem; its algebraic meaning is unconditional. -/
def CCMSourceResolvedPassivity
    (A E B M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ x : Fin N → ℂ,
    (star x ⬝ᵥ (ccmDiagonalLeakageGram A E).mulVec x).re +
        (star x ⬝ᵥ (ccmDiagonalLeakageGram A M).mulVec x).re ≤
      (star x ⬝ᵥ A.mulVec x).re +
        (star x ⬝ᵥ (ccmDiagonalLeakageGram A B).mulVec x).re

/-- Exact four-channel incidence law.  Once `C = E - B + M`, diagonal Fock
passivity is equivalent to the Euler--Mellin energy being paid by the safe and
boundary energies. -/
theorem ccmFiniteFockPassivity_iff_sourceResolved
    (A C E B M : Matrix (Fin N) (Fin N) ℂ)
    (hC : C = E - B + M) :
    CCMFiniteFockPassivity A C ↔ CCMSourceResolvedPassivity A E B M := by
  rw [CCMFiniteFockPassivity, CCMSourceResolvedPassivity, hC,
    ccmDiagonalLeakage_incidence A (E - B + M) E B M rfl]
  apply forall_congr'
  intro x
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub]
  simp only [Complex.add_re, Complex.sub_re]
  constructor <;> intro h <;> linarith

/-- The complete finite algebraic reduction: the source-resolved inequality is
exactly nonnegativity of the diagonal-Fock defect. -/
theorem ccmDiagonalDefect_kreinNonneg_iff_sourceResolved
    (A C E B M : Matrix (Fin N) (Fin N) ℂ)
    (hC : C = E - B + M) :
    KreinNonneg (ccmDiagonalDefectGram A C) ↔
      CCMSourceResolvedPassivity A E B M := by
  rw [ccmDiagonalDefect_kreinNonneg_iff_passivity,
    ccmFiniteFockPassivity_iff_sourceResolved A C E B M hC]

end

end RHTower
