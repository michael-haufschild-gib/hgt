import GaloisForLFunctions.HTGeometry.AlgebraicClosureGaloisCompact
import GaloisForLFunctions.RHTower.DeningerDynSysGaloisContinuousAction
import GaloisForLFunctions.RHTower.DeningerDynSysOmegaEquivariant

/-!
# Corollary 1.5(1): the injectivity modulo the Galois group

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(1)
(`t28n`), and Kucharczyk–Scholze Lemma 4.9.

Deninger's subring `ℤ̲κ / κ₀` has invariants exactly `W_rat (κ₀)`, its Galois orbits are finite and
the action on it is continuous for the Krull topology.  Hence two homomorphisms `ℤ̲κ / κ₀ → C` into
a field which agree on `W_rat (κ₀)` differ by an element of the Galois group: the map
`Hom (ℤ̲κ / κ₀ , C) / H → Hom (W_rat (κ₀) , C)` is injective.
-/

namespace RHTower

noncomputable section

open MonoidAlgebra MulAction

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
variable [Algebra.IsAlgebraic F E] [IsAlgClosed E] [IsAlgClosure F E]
variable [DecidableEq Eˣ] [DecidableEq (Polynomial (perfectClosure F E))]

/-- The algebra structure of `ℤ̲κ / κ₀` over `W_rat (κ₀)`. -/
scoped instance deningerInsepWittAlgebra :
    Algebra (DeningerCanonicalRationalWittRing F) ↥(deningerInsepSubring F E q) :=
  (deningerWittToInsep (F := F) (E := E) q).toAlgebra

theorem deningerInsepWittAlgebraMap (w : DeningerCanonicalRationalWittRing F) :
    algebraMap (DeningerCanonicalRationalWittRing F) ↥(deningerInsepSubring F E q) w
      = deningerWittToInsep q w := rfl

/-- **Deninger, Proposition 1.3 (`t26n`), the lower row.**  The invariants of `ℤ̲κ / κ₀` are
`W_rat (κ₀)`. -/
instance deningerInsepWitt_isInvariant :
    Algebra.IsInvariant (DeningerCanonicalRationalWittRing F) ↥(deningerInsepSubring F E q)
      (E ≃ₐ[F] E) := by
  refine ⟨fun x hx => ?_⟩
  have hinv : ∀ σ : E ≃ₐ[F] E,
      deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E))
        (x : MonoidAlgebra ℤ Eˣ) = (x : MonoidAlgebra ℤ Eˣ) := by
    intro σ
    have h := hx σ
    have h' := congrArg (fun z : ↥(deningerInsepSubring F E q) =>
      (z : MonoidAlgebra ℤ Eˣ)) h
    rw [deningerInsepSubring_smul_val] at h'
    exact h'
  obtain ⟨w₀, hw₀⟩ := (deningerOmega_mem_image_iff q (x : MonoidAlgebra ℤ Eˣ)).2 ⟨hinv, x.2⟩
  refine ⟨w₀, ?_⟩
  refine Subtype.ext ?_
  rw [deningerInsepWittAlgebraMap, deningerWittToInsep_val]
  have hinjOmega : Function.Injective (deningerOmegaAddHom E) :=
    (deningerOmegaRingEquiv E).injective
  refine hinjOmega ?_
  rw [deningerWittToMonoidAlgebra_omega]
  exact hw₀

/-- **Deninger, Corollary 1.5(1) (`t28n`), injectivity modulo `H`.**  Two homomorphisms of
`ℤ̲κ / κ₀` into a field which agree on `W_rat (κ₀)` are conjugate under the Galois group.  No
separability hypothesis is needed: the Galois group of an algebraic closure is compact in every
characteristic. -/
theorem deningerCor15_injective {C : Type*} [Field C]
    (ψ₁ ψ₂ : ↥(deningerInsepSubring F E q) →+* C)
    (hres : ∀ w : DeningerCanonicalRationalWittRing F,
      ψ₁ (deningerWittToInsep q w) = ψ₂ (deningerWittToInsep q w)) :
    ∃ σ : E ≃ₐ[F] E, ∀ x : ↥(deningerInsepSubring F E q), ψ₂ x = ψ₁ (σ • x) := by
  letI : TopologicalSpace ↥(deningerInsepSubring F E q) := ⊥
  haveI : DiscreteTopology ↥(deningerInsepSubring F E q) := ⟨rfl⟩
  haveI : ContinuousSMul (E ≃ₐ[F] E) ↥(deningerInsepSubring F E q) :=
    deningerInsepSubring_continuousSMul q
  haveI : SMulCommClass (E ≃ₐ[F] E) (DeningerCanonicalRationalWittRing F)
      ↥(deningerInsepSubring F E q) := by
    refine ⟨fun σ w x => ?_⟩
    show σ • (algebraMap _ _ w * x) = algebraMap _ _ w * (σ • x)
    rw [smul_mul']
    congr 1
    refine Subtype.ext ?_
    rw [deningerInsepSubring_smul_val, deningerInsepWittAlgebraMap, deningerWittToInsep_val]
    have hinjOmega : Function.Injective (deningerOmegaAddHom E) :=
      (deningerOmegaRingEquiv E).injective
    refine hinjOmega ?_
    have hsm : (σ • deningerWittToMonoidAlgebra w : MonoidAlgebra ℤ Eˣ)
        = deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E))
          (deningerWittToMonoidAlgebra w) := rfl
    have hcomm : ((σ : E →+* E).comp (algebraMap F E)) = algebraMap F E :=
      RingHom.ext fun a => σ.commutes a
    rw [hsm, ← deningerOmega_equivariant, deningerWittToMonoidAlgebra_omega,
      ← deningerCanonicalRationalWittMap_comp, hcomm]
  exact deningerHom_exists_smul (A := DeningerCanonicalRationalWittRing F)
    (G := E ≃ₐ[F] E) ψ₁ ψ₂ hres

end

end RHTower