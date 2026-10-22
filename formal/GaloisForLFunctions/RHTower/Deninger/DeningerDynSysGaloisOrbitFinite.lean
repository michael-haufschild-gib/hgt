import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysGaloisMonoidAlgebra

/-!
# Finiteness of the Galois orbits on `ℤ̲κ`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(1).

An element of `ℤ̲κ` has finite support, and each atom in that support has a finite orbit because
the extension is algebraic.  The class is determined by the images of the atoms in its support, so
its orbit is the image of a finite set of relabellings, hence finite.  With the orbit-polynomial
argument this makes `ℤ̲κ` — and its stable subring `ℤ̲κ / κ₀` — integral over the invariants.
-/

namespace RHTower

open MonoidAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A class in `ℤ̲κ` is the sum of its atoms. -/
theorem deningerMonoidAlgebra_sum_single (ξ : MonoidAlgebra ℤ Eˣ) :
    ∑ a ∈ ξ.coeff.support, MonoidAlgebra.single a (ξ.coeff a) = ξ := by
  have h := MonoidAlgebra.sum_coeff_single ξ
  rwa [Finsupp.sum] at h

/-- Relabelling acts on the atoms. -/
theorem deningerGaloisMonoidAlgebra_smul_eq (σ : E ≃ₐ[F] E) (ξ : MonoidAlgebra ℤ Eˣ) :
    σ • ξ = ∑ a ∈ ξ.coeff.support,
      MonoidAlgebra.single (Units.map ((σ : E →+* E) : E →* E) a) (ξ.coeff a) := by
  conv_lhs => rw [← deningerMonoidAlgebra_sum_single ξ]
  rw [deningerGaloisMonoidAlgebra_smul_def, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [deningerMonoidAlgebraMap_single]

/-- The relabellings of a unit form a finite set. -/
theorem deningerUnitsRelabel_finite [Algebra.IsAlgebraic F E] (a : Eˣ) :
    (Set.range fun σ : E ≃ₐ[F] E => Units.map ((σ : E →+* E) : E →* E) a).Finite := by
  refine Set.Finite.of_finite_image ?_ (Units.val_injective.injOn)
  refine Set.Finite.subset (deningerAlgebraicOrbit_finite (F := F) ((a : E))) ?_
  rintro _ ⟨u, ⟨σ, rfl⟩, rfl⟩
  exact ⟨σ, rfl⟩

/-- **Deninger, Corollary 1.5(1).**  Over an algebraic extension the Galois orbits on `ℤ̲κ` are
finite. -/
theorem deningerMonoidAlgebraOrbit_finite [Algebra.IsAlgebraic F E] (ξ : MonoidAlgebra ℤ Eˣ) :
    (MulAction.orbit (E ≃ₐ[F] E) ξ).Finite := by
  classical
  set S := ξ.coeff.support with hS
  set Θ : ({x // x ∈ S} → Eˣ) → MonoidAlgebra ℤ Eˣ :=
    fun g => ∑ a ∈ S.attach, MonoidAlgebra.single (g a) (ξ.coeff (a : Eˣ)) with hΘ
  set W : Set ({x // x ∈ S} → Eˣ) :=
    Set.pi Set.univ (fun a : {x // x ∈ S} =>
      Set.range fun σ : E ≃ₐ[F] E => Units.map ((σ : E →+* E) : E →* E) (a : Eˣ)) with hW
  have hsub : MulAction.orbit (E ≃ₐ[F] E) ξ ⊆ Θ '' W := by
    rintro _ ⟨σ, rfl⟩
    refine ⟨fun a => Units.map ((σ : E →+* E) : E →* E) (a : Eˣ), ?_, ?_⟩
    · intro a _
      exact ⟨σ, rfl⟩
    · show Θ _ = σ • ξ
      rw [hΘ, deningerGaloisMonoidAlgebra_smul_eq σ ξ]
      exact Finset.sum_attach S fun a => MonoidAlgebra.single
        (Units.map ((σ : E →+* E) : E →* E) a) (ξ.coeff a)
  refine Set.Finite.subset (Set.Finite.image Θ ?_) hsub
  rw [hW]
  exact Set.Finite.pi fun a => deningerUnitsRelabel_finite (F := F) (a : Eˣ)

end RHTower
