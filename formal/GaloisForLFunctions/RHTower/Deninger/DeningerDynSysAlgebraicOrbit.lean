import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Orbits of an algebraic element under the automorphism group are finite

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), the finiteness input for
Theorem 1.4 and Corollary 1.5(1).

An `F`-automorphism of `E` permutes the roots of the minimal polynomial of an algebraic element, so
the orbit of that element embeds into a finite set.  This is the elementary substitute for the
profinite topology on the automorphism group: it gives finiteness of orbits, hence integrality over
the invariants, with no topological hypothesis.
-/

namespace RHTower

open Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- An `F`-automorphism sends `x` to a root of its minimal polynomial. -/
theorem deningerAlgEquiv_isRoot_minpoly {x : E} (_hx : IsIntegral F x) (σ : E ≃ₐ[F] E) :
    ((minpoly F x).map (algebraMap F E)).IsRoot (σ x) := by
  have h0 : (Polynomial.aeval x) (minpoly F x) = 0 := minpoly.aeval F x
  have h1 : (Polynomial.aeval (σ x)) (minpoly F x) = 0 := by
    have h2 : (Polynomial.aeval (σ x)) (minpoly F x)
        = σ ((Polynomial.aeval x) (minpoly F x)) := by
      simp [Polynomial.aeval_algHom_apply]
    rw [h2, h0, map_zero]
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
  exact h1

/-- **The orbit of an algebraic element under the `F`-automorphisms is finite.** -/
theorem deningerAlgebraicOrbit_finite_of_isIntegral {x : E} (hx : IsIntegral F x) :
    (Set.range fun σ : E ≃ₐ[F] E => σ x).Finite := by
  classical
  have hne : (minpoly F x).map (algebraMap F E) ≠ 0 := by
    intro h
    have hm := minpoly.monic hx
    have : ((minpoly F x).map (algebraMap F E)).Monic := hm.map _
    rw [h] at this
    exact (Polynomial.not_monic_zero) this
  have hsub : (Set.range fun σ : E ≃ₐ[F] E => σ x)
      ⊆ ((minpoly F x).map (algebraMap F E)).roots.toFinset := by
    rintro _ ⟨σ, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne]
    exact deningerAlgEquiv_isRoot_minpoly hx σ
  exact Set.Finite.subset (Finset.finite_toSet _) hsub

/-- The orbit of an algebraic element is finite, as a `MulAction` orbit. -/
theorem deningerMulActionOrbit_finite_of_isIntegral {x : E} (hx : IsIntegral F x) :
    (MulAction.orbit (E ≃ₐ[F] E) x).Finite := by
  have : MulAction.orbit (E ≃ₐ[F] E) x = Set.range fun σ : E ≃ₐ[F] E => σ x := by
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨σ, rfl⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨σ, rfl⟩
  rw [this]
  exact deningerAlgebraicOrbit_finite_of_isIntegral hx

/-- Over an algebraic extension every orbit is finite. -/
theorem deningerAlgebraicOrbit_finite [Algebra.IsAlgebraic F E] (x : E) :
    (MulAction.orbit (E ≃ₐ[F] E) x).Finite :=
  deningerMulActionOrbit_finite_of_isIntegral (Algebra.IsIntegral.isIntegral x)

end RHTower
