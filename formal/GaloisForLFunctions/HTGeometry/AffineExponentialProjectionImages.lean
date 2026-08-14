import GaloisForLFunctions.HTGeometry.HopfIdealKernel
import GaloisForLFunctions.HTGeometry.AffineExponentialSubgroups

/-!
# Projection images of additive-exponential subgroups

For a closed subgroup of `Gₐⁿ × Gₘⁿ` represented by a Hopf ideal `I`, this file constructs the
scheme-theoretic projection images on both factors.  Contravariantly, each image is the kernel of
the factor-coordinate map into `𝒪(G)/I`; `HopfIdealKernel.ker_isHopfIdeal` proves these kernels are
again Hopf ideals.

The final equivalences identify torus character relations and additive linear annihilators of the
projection images exactly with the corresponding relations already lying in `I`.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialProjectionImages

noncomputable section

variable (k : Type*) [Field k]

/-- Left factor coordinate inclusion `T → T ⊗ S`. -/
noncomputable def leftCoordinateInclusion
    (T S : Type*) [CommRing T] [CommRing S] [HopfAlgebra k T] [HopfAlgebra k S] :
    T →ₐc[k] T ⊗[k] S :=
  (Bialgebra.TensorProduct.map (BialgHom.id k T) (Bialgebra.unitBialgHom k S)).comp
    (Bialgebra.TensorProduct.rid k k T).symm.toBialgHom

@[simp]
theorem leftCoordinateInclusion_apply
    (T S : Type*) [CommRing T] [CommRing S] [HopfAlgebra k T] [HopfAlgebra k S]
    (x : T) : leftCoordinateInclusion k T S x = x ⊗ₜ[k] 1 := by
  simp [leftCoordinateInclusion]

/-- Right factor coordinate inclusion `S → T ⊗ S`. -/
noncomputable def rightCoordinateInclusion
    (T S : Type*) [CommRing T] [CommRing S] [HopfAlgebra k T] [HopfAlgebra k S] :
    S →ₐc[k] T ⊗[k] S :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom k T) (BialgHom.id k S)).comp
    (Bialgebra.TensorProduct.lid k S).symm.toBialgHom

@[simp]
theorem rightCoordinateInclusion_apply
    (T S : Type*) [CommRing T] [CommRing S] [HopfAlgebra k T] [HopfAlgebra k S]
    (x : S) : rightCoordinateInclusion k T S x = 1 ⊗ₜ[k] x := by
  simp [rightCoordinateInclusion]

open AffineExponentialGroup AffineExponentialSubgroups

/-- Torus-coordinate inclusion into `𝒪(Gₐⁿ × Gₘⁿ)`. -/
noncomputable def torusInclusion (n : ℕ) :
    TorusCoordinateAlgebra k n →ₐc[k] CoordinateAlgebra k n :=
  leftCoordinateInclusion k _ _

/-- Additive-coordinate inclusion into `𝒪(Gₐⁿ × Gₘⁿ)`. -/
noncomputable def additiveInclusion (n : ℕ) :
    AdditiveCoordinateAlgebra k n →ₐc[k] CoordinateAlgebra k n :=
  rightCoordinateInclusion k _ _

@[simp]
theorem torusInclusion_apply (n : ℕ) (x : TorusCoordinateAlgebra k n) :
    torusInclusion k n x = x ⊗ₜ[k] 1 := by
  simp [torusInclusion]

@[simp]
theorem additiveInclusion_apply (n : ℕ) (x : AdditiveCoordinateAlgebra k n) :
    additiveInclusion k n x = 1 ⊗ₜ[k] x := by
  simp [additiveInclusion]

variable {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]

/-- Coordinate quotient map of a closed subgroup. -/
noncomputable def subgroupQuotientMap :
    CoordinateAlgebra k n →ₐc[k] CoordinateAlgebra k n ⧸ I :=
  Bialgebra.Quotient.mkBialgHom (R := k) I

/-- Coordinate map whose kernel defines the torus projection image. -/
noncomputable def torusProjectionMap :
    TorusCoordinateAlgebra k n →ₐc[k] CoordinateAlgebra k n ⧸ I :=
  (subgroupQuotientMap k I).comp (torusInclusion k n)

/-- Coordinate map whose kernel defines the additive projection image. -/
noncomputable def additiveProjectionMap :
    AdditiveCoordinateAlgebra k n →ₐc[k] CoordinateAlgebra k n ⧸ I :=
  (subgroupQuotientMap k I).comp (additiveInclusion k n)

/-- Hopf ideal of the scheme-theoretic torus projection image. -/
noncomputable def torusProjectionIdeal : Ideal (TorusCoordinateAlgebra k n) :=
  RingHom.ker (torusProjectionMap k I : TorusCoordinateAlgebra k n →+*
    CoordinateAlgebra k n ⧸ I)

/-- Hopf ideal of the scheme-theoretic additive projection image. -/
noncomputable def additiveProjectionIdeal : Ideal (AdditiveCoordinateAlgebra k n) :=
  RingHom.ker (additiveProjectionMap k I : AdditiveCoordinateAlgebra k n →+*
    CoordinateAlgebra k n ⧸ I)

theorem torusProjectionIdeal_isHopfIdeal :
    (torusProjectionIdeal k I).IsHopfIdeal k := by
  simpa only [torusProjectionIdeal] using
    HopfIdealKernel.ker_isHopfIdeal (k := k)
      (C := TorusCoordinateAlgebra k n) (D := CoordinateAlgebra k n ⧸ I)
      (torusProjectionMap k I)

theorem additiveProjectionIdeal_isHopfIdeal :
    (additiveProjectionIdeal k I).IsHopfIdeal k := by
  simpa only [additiveProjectionIdeal] using
    HopfIdealKernel.ker_isHopfIdeal (k := k)
      (C := AdditiveCoordinateAlgebra k n) (D := CoordinateAlgebra k n ⧸ I)
      (additiveProjectionMap k I)

/-- The torus projection ideal is precisely the contraction of `I` to torus coordinates. -/
theorem mem_torusProjectionIdeal_iff (x : TorusCoordinateAlgebra k n) :
    x ∈ torusProjectionIdeal k I ↔ x ⊗ₜ[k] 1 ∈ I := by
  change Ideal.Quotient.mk I (x ⊗ₜ[k] 1) = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The additive projection ideal is precisely the contraction of `I` to additive coordinates. -/
theorem mem_additiveProjectionIdeal_iff (x : AdditiveCoordinateAlgebra k n) :
    x ∈ additiveProjectionIdeal k I ↔ 1 ⊗ₜ[k] x ∈ I := by
  change Ideal.Quotient.mk I (1 ⊗ₜ[k] x) = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Character lattice relations in the torus projection are exactly the character relations in
the original subgroup ideal. -/
theorem torusCharacterRelation_mem_projection_iff (m : Fin n →₀ ℤ) :
    AddMonoidAlgebra.single m 1 - 1 ∈ torusProjectionIdeal k I ↔
      torusRelation k m ∈ I := by
  rw [mem_torusProjectionIdeal_iff]
  simp only [torusRelation, torusCharacter, TensorProduct.sub_tmul,
    Algebra.TensorProduct.one_def]

/-- Additive linear annihilators of the additive projection are exactly the additive linear
relations in the original subgroup ideal. -/
theorem additiveLinear_mem_projection_iff (v : Fin n → k) :
    SymmetricAlgebra.ι k (Fin n → k) v ∈ additiveProjectionIdeal k I ↔
      additiveLinear k v ∈ I := by
  rw [mem_additiveProjectionIdeal_iff]
  rfl

end
end AffineExponentialProjectionImages
end GaloisForLFunctions.HTGeometry
