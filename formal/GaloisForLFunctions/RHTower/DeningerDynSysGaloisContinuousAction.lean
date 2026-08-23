import GaloisForLFunctions.RHTower.DeningerDynSysGaloisOrbitFinite
import GaloisForLFunctions.RHTower.DeningerDynSysInsepSubringAction
import GaloisForLFunctions.RHTower.DeningerDynSysCor15
import GaloisForLFunctions.HTGeometry.DiscreteContinuousSMul
import Mathlib.FieldTheory.KrullTopology

/-!
# Continuity of the Galois action on `ℤ̲κ`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(1).

A class in `ℤ̲κ` involves only finitely many units of `κ`, so it is fixed by every automorphism
fixing the finite subextension they generate.  That fixing subgroup is open for the Krull topology,
hence so is the stabiliser, and therefore the Galois action on the discrete space `ℤ̲κ` — and on its
stable subring `ℤ̲κ / κ₀` — is continuous.  This is the topological input of Kucharczyk–Scholze
Lemma 4.9.
-/

namespace RHTower

open MonoidAlgebra MulAction HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

omit [Algebra.IsAlgebraic F E] in
/-- An automorphism fixing the units in the support of a class fixes the class. -/
theorem deningerMonoidAlgebra_smul_eq_self (σ : E ≃ₐ[F] E) (ξ : MonoidAlgebra ℤ Eˣ)
    (h : ∀ a ∈ ξ.coeff.support, σ (a : E) = (a : E)) : σ • ξ = ξ := by
  classical
  rw [deningerGaloisMonoidAlgebra_smul_eq]
  have hterm : ∀ a ∈ ξ.coeff.support,
      MonoidAlgebra.single (Units.map ((σ : E →+* E) : E →* E) a) (ξ.coeff a)
        = MonoidAlgebra.single a (ξ.coeff a) := by
    intro a ha
    congr 1
    exact Units.ext (h a ha)
  rw [Finset.sum_congr rfl hterm, deningerMonoidAlgebra_sum_single]

/-- **The stabiliser of a class in `ℤ̲κ` is open.** -/
theorem deningerMonoidAlgebra_stabilizer_isOpen (ξ : MonoidAlgebra ℤ Eˣ) :
    IsOpen (stabilizer (E ≃ₐ[F] E) ξ : Set (E ≃ₐ[F] E)) := by
  classical
  set T : Finset E := ξ.coeff.support.image (fun a : Eˣ => (a : E)) with hT
  haveI : FiniteDimensional F (IntermediateField.adjoin F (T : Set E)) :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral (R := F) x)
  refine Subgroup.isOpen_mono ?_
    (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin F (T : Set E)))
  intro σ hσ
  show σ • ξ = ξ
  refine deningerMonoidAlgebra_smul_eq_self σ ξ fun a ha => ?_
  have hmem : (a : E) ∈ IntermediateField.adjoin F (T : Set E) := by
    refine IntermediateField.subset_adjoin F (T : Set E) ?_
    rw [hT]
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨a, ha, rfl⟩
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ _ hmem

/-- **The Galois action on the discrete space `ℤ̲κ` is continuous.** -/
theorem deningerMonoidAlgebra_continuousSMul :
    letI : TopologicalSpace (MonoidAlgebra ℤ Eˣ) := ⊥
    haveI : DiscreteTopology (MonoidAlgebra ℤ Eˣ) := ⟨rfl⟩
    ContinuousSMul (E ≃ₐ[F] E) (MonoidAlgebra ℤ Eˣ) := by
  letI : TopologicalSpace (MonoidAlgebra ℤ Eˣ) := ⊥
  haveI : DiscreteTopology (MonoidAlgebra ℤ Eˣ) := ⟨rfl⟩
  exact continuousSMul_of_isOpen_stabilizer deningerMonoidAlgebra_stabilizer_isOpen

variable (q : ℕ) [ExpChar F q] [IsAlgClosed E]

omit [IsAlgClosed E] in
/-- **The stabiliser of an element of `ℤ̲κ / κ₀` is open.** -/
theorem deningerInsepSubring_stabilizer_isOpen (x : ↥(deningerInsepSubring F E q)) :
    IsOpen (stabilizer (E ≃ₐ[F] E) x : Set (E ≃ₐ[F] E)) := by
  refine Subgroup.isOpen_mono ?_
    (deningerMonoidAlgebra_stabilizer_isOpen (x : MonoidAlgebra ℤ Eˣ))
  intro σ hσ
  refine Subtype.ext ?_
  rw [deningerInsepSubring_smul_val]
  exact hσ

omit [IsAlgClosed E] in
/-- **The Galois action on the discrete space `ℤ̲κ / κ₀` is continuous.** -/
theorem deningerInsepSubring_continuousSMul :
    letI : TopologicalSpace ↥(deningerInsepSubring F E q) := ⊥
    haveI : DiscreteTopology ↥(deningerInsepSubring F E q) := ⟨rfl⟩
    ContinuousSMul (E ≃ₐ[F] E) ↥(deningerInsepSubring F E q) := by
  letI : TopologicalSpace ↥(deningerInsepSubring F E q) := ⊥
  haveI : DiscreteTopology ↥(deningerInsepSubring F E q) := ⟨rfl⟩
  exact continuousSMul_of_isOpen_stabilizer (deningerInsepSubring_stabilizer_isOpen q)

end RHTower
