import GaloisForLFunctions.HTGeometry.DifferenceGaloisIrreducibility
import GaloisForLFunctions.HTGeometry.TensorSquareDerivation

/-!
# Differential points give differential Galois automorphisms

The specialisation of the torsor at a point of the group commutes with the derivation as soon as the
point does: the elements where the two agree form a subalgebra, it contains the image of the ring —
where both sides are the derivative — and it contains the constants subalgebra, where the
specialisation is the point itself.  Generation of the tensor square by those two therefore forces
the identity everywhere.

Applied to `1 ⊗ x`, whose derivative is `1 ⊗ x′`, that makes the Galois automorphism attached to a
differential point a differential automorphism — the hypothesis the isomonodromy endgame needs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

variable {K R C : Type*} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [IsAlgClosed C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

omit [Nontrivial R] [IsAlgClosed C] in
/-- **A differential point specialises the torsor differentially.** -/
theorem torsorSpecialization_deriv (E : Subalgebra C (R ⊗[K] R))
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    (χ : E →ₐ[C] C)
    (hχ : ∀ (e : R ⊗[K] R) (he : e ∈ E),
      χ ⟨tensorSquareDerivation (K := K) e, hEδ e he⟩ = Differential.deriv (χ ⟨e, he⟩))
    (a : R ⊗[K] R) :
    torsorSpecialization E b hgen hindep χ (tensorSquareDerivation (K := K) a)
      = Differential.deriv (torsorSpecialization E b hgen hindep χ a) := by
  have hmem : a ∈ Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) := by
    rw [hgen]; trivial
  induction hmem using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with ⟨r, rfl⟩ | hxE
      · have halg : ∀ s : R, (algebraMap R (R ⊗[K] R)) s = s ⊗ₜ[K] (1 : R) := fun s => rfl
        rw [halg, tensorSquareDerivation_tmul, Derivation.map_one_eq_zero,
          TensorProduct.tmul_zero, add_zero, ← halg, ← halg]
        rw [AlgHom.commutes, AlgHom.commutes]
        simp
      · have hspec := torsorSpecialization_coe E b hgen hindep χ ⟨x, hxE⟩
        have hspecD := torsorSpecialization_coe E b hgen hindep χ
          ⟨tensorSquareDerivation (K := K) x, hEδ x hxE⟩
        show torsorSpecialization E b hgen hindep χ
            ((⟨tensorSquareDerivation (K := K) x, hEδ x hxE⟩ : E) : R ⊗[K] R) = _
        rw [hspecD]
        show algebraMap C R (χ ⟨tensorSquareDerivation (K := K) x, hEδ x hxE⟩)
          = Differential.deriv (torsorSpecialization E b hgen hindep χ x)
        rw [hχ x hxE]
        have hx2 : torsorSpecialization E b hgen hindep χ x = algebraMap C R (χ ⟨x, hxE⟩) := hspec
        rw [hx2, DifferentialAlgebra.deriv_algebraMap]
  | algebraMap c =>
      have halgC : (algebraMap C (R ⊗[K] R)) c = (algebraMap C R c) ⊗ₜ[K] (1 : R) := by
        rw [IsScalarTower.algebraMap_apply C R (R ⊗[K] R)]
        rfl
      rw [halgC, tensorSquareDerivation_tmul, Derivation.map_one_eq_zero,
        TensorProduct.tmul_zero, add_zero]
      have hval : ∀ d : C, torsorSpecialization E b hgen hindep χ
          ((algebraMap C R d) ⊗ₜ[K] (1 : R)) = algebraMap C R d := by
        intro d
        have : ((algebraMap C R d) ⊗ₜ[K] (1 : R) : R ⊗[K] R)
            = algebraMap R (R ⊗[K] R) (algebraMap C R d) := rfl
        rw [this, AlgHom.commutes]
        simp
      rw [DifferentialAlgebra.deriv_algebraMap (A := C) (B := R) c, hval, hval,
        DifferentialAlgebra.deriv_algebraMap]
  | add x y _ _ hx hy =>
      rw [map_add, map_add, map_add, hx, hy, map_add]
  | mul x y _ _ hx hy =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hx, hy,
        map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]

omit [Nontrivial R] [IsAlgClosed C] in
/-- **The Galois automorphism at a differential point is differential.** -/
theorem galoisAutAt_deriv (E : Subalgebra C (R ⊗[K] R))
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    (χ : E →ₐ[C] C)
    (hχ : ∀ (e : R ⊗[K] R) (he : e ∈ E),
      χ ⟨tensorSquareDerivation (K := K) e, hEδ e he⟩ = Differential.deriv (χ ⟨e, he⟩))
    (x : R) :
    galoisAutAt E b hgen hindep χ (Differential.deriv x)
      = Differential.deriv (galoisAutAt E b hgen hindep χ x) := by
  have hD : tensorSquareDerivation (K := K) ((1 : R) ⊗ₜ[K] x)
      = (1 : R) ⊗ₜ[K] Differential.deriv x := by
    rw [tensorSquareDerivation_tmul, Derivation.map_one_eq_zero, TensorProduct.zero_tmul, zero_add]
  rw [galoisAutAt_apply, galoisAutAt_apply, ← hD,
    torsorSpecialization_deriv E b hgen hindep hEδ χ hχ]

end

end GaloisForLFunctions.HTGeometry
