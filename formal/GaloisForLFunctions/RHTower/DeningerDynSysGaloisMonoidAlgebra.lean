import GaloisForLFunctions.RHTower.DeningerDynSysInsepSubringAction
import GaloisForLFunctions.RHTower.DeningerDynSysAlgebraicOrbit
import GaloisForLFunctions.RHTower.DeningerDynSysFiniteOrbitIntegral

/-!
# The Galois action on `ℤ̲κ` and on `ℤ̲κ / κ₀`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(1).

Relabelling the atoms gives an action of `Aut_{κ₀} (κ)` on `ℤ̲κ` by ring automorphisms, which
restricts to Deninger's subring `ℤ̲κ / κ₀`.  Over an algebraic extension every orbit is finite: an
element has finite support and each atom has a finite orbit, so the orbit of the element is the
image of a finite set of relabellings.  Finiteness of orbits gives integrality over the invariants.
-/

namespace RHTower

open MonoidAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Relabelling of atoms by `F`-automorphisms of `E`. -/
noncomputable scoped instance deningerGaloisMonoidAlgebraAction :
    MulSemiringAction (E ≃ₐ[F] E) (MonoidAlgebra ℤ Eˣ) where
  smul σ ξ := deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E)) ξ
  one_smul ξ := by
    have h : ((deningerMonoidAlgebraMap (Units.map (((1 : E ≃ₐ[F] E) : E →+* E) : E →* E)) :
          MonoidAlgebra ℤ Eˣ →+* MonoidAlgebra ℤ Eˣ) :
          MonoidAlgebra ℤ Eˣ →+ MonoidAlgebra ℤ Eˣ)
        = AddMonoidHom.id _ := by
      refine MonoidAlgebra.addMonoidHom_ext ?_
      intro a n
      show deningerMonoidAlgebraMap (Units.map (((1 : E ≃ₐ[F] E) : E →+* E) : E →* E))
        (MonoidAlgebra.single a n) = MonoidAlgebra.single a n
      rw [deningerMonoidAlgebraMap_single]
      congr 1
    exact congrArg (fun F : MonoidAlgebra ℤ Eˣ →+ MonoidAlgebra ℤ Eˣ => F ξ) h
  mul_smul σ τ ξ := by
    have h : ((deningerMonoidAlgebraMap
          (Units.map ((((σ * τ : E ≃ₐ[F] E)) : E →+* E) : E →* E)) :
          MonoidAlgebra ℤ Eˣ →+* MonoidAlgebra ℤ Eˣ) :
          MonoidAlgebra ℤ Eˣ →+ MonoidAlgebra ℤ Eˣ)
        = ((deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E)) :
            MonoidAlgebra ℤ Eˣ →+* MonoidAlgebra ℤ Eˣ) :
            MonoidAlgebra ℤ Eˣ →+ MonoidAlgebra ℤ Eˣ).comp
          ((deningerMonoidAlgebraMap (Units.map ((τ : E →+* E) : E →* E)) :
            MonoidAlgebra ℤ Eˣ →+* MonoidAlgebra ℤ Eˣ) :
            MonoidAlgebra ℤ Eˣ →+ MonoidAlgebra ℤ Eˣ) := by
      refine MonoidAlgebra.addMonoidHom_ext ?_
      intro a n
      show deningerMonoidAlgebraMap (Units.map ((((σ * τ : E ≃ₐ[F] E)) : E →+* E) : E →* E))
          (MonoidAlgebra.single a n)
        = deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E))
          (deningerMonoidAlgebraMap (Units.map ((τ : E →+* E) : E →* E))
            (MonoidAlgebra.single a n))
      rw [deningerMonoidAlgebraMap_single, deningerMonoidAlgebraMap_single,
        deningerMonoidAlgebraMap_single]
      congr 1
    exact congrArg (fun F : MonoidAlgebra ℤ Eˣ →+ MonoidAlgebra ℤ Eˣ => F ξ) h
  smul_zero σ := map_zero (deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E)))
  smul_add σ x y := map_add (deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E))) x y
  smul_one σ := map_one (deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E)))
  smul_mul σ x y := map_mul (deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E))) x y

theorem deningerGaloisMonoidAlgebra_smul_def (σ : E ≃ₐ[F] E) (ξ : MonoidAlgebra ℤ Eˣ) :
    σ • ξ = deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E)) ξ := rfl

@[simp] theorem deningerGaloisMonoidAlgebra_smul_single (σ : E ≃ₐ[F] E) (a : Eˣ) (n : ℤ) :
    σ • (MonoidAlgebra.single a n : MonoidAlgebra ℤ Eˣ)
      = MonoidAlgebra.single (Units.map ((σ : E →+* E) : E →* E) a) n := by
  rw [deningerGaloisMonoidAlgebra_smul_def, deningerMonoidAlgebraMap_single]

end RHTower
