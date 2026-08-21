import GaloisForLFunctions.HTGeometry.CartierDualLieAlgebra
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# `α₂`: a finite free bialgebra with nonzero primitives

Over a commutative ring `R` of characteristic `2`, the dual numbers `R[ε]` carry a bialgebra
structure in which `ε` is **primitive**:

`Δ ε = ε ⊗ 1 + 1 ⊗ ε`,  `ε(ε) = 0`.

(The square-zero condition needs `2 = 0`: `(ε ⊗ 1 + 1 ⊗ ε)² = 2 (ε ⊗ ε)`.)  Geometrically
`Spec R[ε] = α₂`, the kernel of Frobenius on `𝔾ₐ`, the standard example of a finite flat group
scheme that is neither étale nor of multiplicative type, and the standard example of Cartier
self-duality.

The point of this file is **non-vacuity**: `α₂` is a finite free commutative bialgebra whose module
of primitive elements is nonzero, so `CartierDual.primitivesEquivCartierLie` — the isomorphism
`Lie (N^∨) ≅ Prim A` — is not a statement about zero modules.  For the group algebra `R[G]` of
`GroupAlgebraCoLieExample` the primitives vanish; here they do not.
-/

namespace GaloisForLFunctions.HTGeometry.AlphaTwo

open TensorProduct DualNumber Coalgebra

variable (R : Type*) [CommRing R] [CharP R 2]

theorem two_eq_zero : (2 : R) = 0 := by
  have h : ((2 : ℕ) : R) = 0 := CharP.cast_eq_zero R 2
  simpa using h

/-- The primitive element `ε ⊗ 1 + 1 ⊗ ε` of the tensor square. -/
noncomputable def epsTensor : DualNumber R ⊗[R] DualNumber R :=
  (ε : DualNumber R) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] (ε : DualNumber R)

theorem epsTensor_sq : epsTensor R * epsTensor R = 0 := by
  have h1 : ((ε : DualNumber R) ⊗ₜ[R] (1 : DualNumber R))
      * ((ε : DualNumber R) ⊗ₜ[R] (1 : DualNumber R)) = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, DualNumber.eps_mul_eps, TensorProduct.zero_tmul]
  have h2 : ((1 : DualNumber R) ⊗ₜ[R] (ε : DualNumber R))
      * ((1 : DualNumber R) ⊗ₜ[R] (ε : DualNumber R)) = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, DualNumber.eps_mul_eps, TensorProduct.tmul_zero]
  have h3 : ((ε : DualNumber R) ⊗ₜ[R] (1 : DualNumber R))
      * ((1 : DualNumber R) ⊗ₜ[R] (ε : DualNumber R))
      = (ε : DualNumber R) ⊗ₜ[R] (ε : DualNumber R) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hsum : epsTensor R * epsTensor R
      = ((ε : DualNumber R) ⊗ₜ[R] (1 : DualNumber R))
          * ((ε : DualNumber R) ⊗ₜ[R] (1 : DualNumber R))
        + (2 : R) • (((ε : DualNumber R) ⊗ₜ[R] (1 : DualNumber R))
          * ((1 : DualNumber R) ⊗ₜ[R] (ε : DualNumber R)))
        + ((1 : DualNumber R) ⊗ₜ[R] (ε : DualNumber R))
          * ((1 : DualNumber R) ⊗ₜ[R] (ε : DualNumber R)) := by
    rw [epsTensor, two_smul]
    ring
  rw [hsum, h1, h2, h3, two_eq_zero, zero_smul, zero_add, add_zero]

/-- The comultiplication of `α₂`, determined by `ε ↦ ε ⊗ 1 + 1 ⊗ ε`. -/
noncomputable def comulAlg : DualNumber R →ₐ[R] (DualNumber R ⊗[R] DualNumber R) :=
  DualNumber.lift ⟨(Algebra.ofId R _, epsTensor R), epsTensor_sq R,
    fun a => (Algebra.commutes a (epsTensor R)).symm⟩

/-- The counit of `α₂`, determined by `ε ↦ 0`. -/
noncomputable def counitAlg : DualNumber R →ₐ[R] R :=
  DualNumber.lift ⟨(AlgHom.id R R, 0), by simp, fun a => Commute.zero_left _⟩

@[simp] theorem comulAlg_eps : comulAlg R (ε : DualNumber R) = epsTensor R := by
  rw [comulAlg, DualNumber.lift_apply_eps]

@[simp] theorem counitAlg_eps : counitAlg R (ε : DualNumber R) = 0 := by
  rw [counitAlg, DualNumber.lift_apply_eps]


/-- **The bialgebra `α₂ = Spec R[ε]`** in characteristic `2`, with `ε` primitive. -/
noncomputable instance instBialgebraDualNumber : Bialgebra R (DualNumber R) :=
  Bialgebra.ofAlgHom (comulAlg R) (counitAlg R)
    (by
      apply DualNumber.algHom_ext
      simp [comulAlg_eps, epsTensor, Algebra.TensorProduct.map_tmul,
        TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel)
    (by
      apply DualNumber.algHom_ext
      simp [comulAlg_eps, counitAlg_eps, epsTensor, Algebra.TensorProduct.map_tmul,
        TensorProduct.add_tmul, TensorProduct.tmul_add])
    (by
      apply DualNumber.algHom_ext
      simp [comulAlg_eps, counitAlg_eps, epsTensor, Algebra.TensorProduct.map_tmul,
        TensorProduct.add_tmul, TensorProduct.tmul_add])

theorem comul_eps :
    Coalgebra.comul (R := R) (ε : DualNumber R)
      = (ε : DualNumber R) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] (ε : DualNumber R) := by
  show comulAlg R (ε : DualNumber R) = _
  rw [comulAlg_eps, epsTensor]

/-- `ε` is a primitive element of `α₂`. -/
theorem eps_mem_primitives :
    (ε : DualNumber R) ∈ AffineGroupScheme.primitives R (DualNumber R) := by
  rw [AffineGroupScheme.mem_primitives]
  exact comul_eps R

/-- **Non-vacuity of Cartier duality on Lie algebras.**  `α₂` is a finite free commutative
bialgebra whose primitive elements — the Lie algebra of its Cartier dual — are nonzero. -/
theorem primitives_ne_bot [Nontrivial R] :
    AffineGroupScheme.primitives R (DualNumber R) ≠ ⊥ := by
  intro h
  have hmem := eps_mem_primitives R
  rw [h, Submodule.mem_bot] at hmem
  have : (TrivSqZeroExt.snd (ε : DualNumber R) : R) = 0 := by rw [hmem]; simp
  rw [DualNumber.snd_eps] at this
  exact one_ne_zero this

example : Module.Free R (DualNumber R) := inferInstance
example : Module.Finite R (DualNumber R) := inferInstance

end GaloisForLFunctions.HTGeometry.AlphaTwo
