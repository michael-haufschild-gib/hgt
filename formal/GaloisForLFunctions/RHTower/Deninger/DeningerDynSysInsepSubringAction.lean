import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysOmegaEquivariant

/-!
# The Galois action on `ℤ̲κ / κ₀`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(1).

Relabelling the atoms of `ℤ̲κ` by a field automorphism permutes the coefficients, and the degree of
inseparability is invariant under an `F`-automorphism, so Deninger's subring `ℤ̲κ / κ₀` is stable.
This is the action to which Theorem 1.4 is applied in Corollary 1.5(1).
-/

namespace RHTower

noncomputable section

open MonoidAlgebra

/-- Relabelling by a bijection permutes the coefficients. -/
theorem deningerMonoidAlgebraMap_coeff {G H : Type*} [CommMonoid G] [CommMonoid H]
    (φ : G ≃* H) (ξ : MonoidAlgebra ℤ G) (r : H) :
    (deningerMonoidAlgebraMap (φ : G →* H) ξ).coeff r = ξ.coeff (φ.symm r) := by
  classical
  have hext : ((Finsupp.applyAddHom r).comp
        ((MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := H)).toAddMonoidHom.comp
          ((deningerMonoidAlgebraMap (φ : G →* H) :
            MonoidAlgebra ℤ G →+* MonoidAlgebra ℤ H) :
            MonoidAlgebra ℤ G →+ MonoidAlgebra ℤ H)))
      = (Finsupp.applyAddHom (φ.symm r)).comp
        (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := G)).toAddMonoidHom := by
    refine MonoidAlgebra.addMonoidHom_ext ?_
    intro g n
    show (deningerMonoidAlgebraMap (φ : G →* H) (MonoidAlgebra.single g n)).coeff r
      = (MonoidAlgebra.single g n).coeff (φ.symm r)
    rw [deningerMonoidAlgebraMap_single]
    show (Finsupp.single (φ g) n) r = (Finsupp.single g n) (φ.symm r)
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : φ g = r
    · rw [if_pos h, if_pos (by rw [← h, MulEquiv.symm_apply_apply])]
    · rw [if_neg h, if_neg ?_]
      intro hc
      exact h (by rw [hc, MulEquiv.apply_symm_apply])
  exact congrArg (fun F : MonoidAlgebra ℤ G →+ ℤ => F ξ) hext

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The degree of inseparability is invariant under an `F`-automorphism. -/
theorem deningerInsepDegree_algEquiv (q : ℕ) [ExpChar F q] (σ : E ≃ₐ[F] E) (x : E) :
    deningerInsepDegree F E q (σ x) = deningerInsepDegree F E q x := by
  have hset : ∀ n : ℕ, n ∈ deningerInsepExpSet F E q (σ x) ↔ n ∈ deningerInsepExpSet F E q x := by
    intro n
    rw [deningerMem_insepExpSet_iff, deningerMem_insepExpSet_iff]
    constructor
    · intro h
      have hx : σ (x ^ q ^ n) ∈ separableClosure F E := by
        rw [map_pow]; exact h
      have hsep : IsSeparable F (σ (x ^ q ^ n)) := hx
      have : IsSeparable F (x ^ q ^ n) := by
        have hmin : minpoly F (σ (x ^ q ^ n)) = minpoly F (x ^ q ^ n) :=
          minpoly.algEquiv_eq σ _
        rw [IsSeparable, ← hmin]
        exact hsep
      exact this
    · intro h
      have hsep : IsSeparable F (x ^ q ^ n) := h
      have hmin : minpoly F (σ (x ^ q ^ n)) = minpoly F (x ^ q ^ n) :=
        minpoly.algEquiv_eq σ _
      have : IsSeparable F (σ (x ^ q ^ n)) := by
        rw [IsSeparable, hmin]
        exact hsep
      rw [map_pow] at this
      exact this
  have : deningerInsepExpSet F E q (σ x) = deningerInsepExpSet F E q x := by
    ext n
    exact hset n
  rw [deningerInsepDegree, deningerInsepDegree, deningerInsepExp, deningerInsepExp, this]

/-- **Deninger, Corollary 1.5(1).**  The subring `ℤ̲κ / κ₀` is stable under the Galois action. -/
theorem deningerInsepSubring_smul_mem (q : ℕ) [ExpChar F q] [Algebra.IsAlgebraic F E]
    (σ : E ≃ₐ[F] E) {ξ : MonoidAlgebra ℤ Eˣ} (hξ : ξ ∈ deningerInsepSubring F E q) :
    deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E)) ξ
      ∈ deningerInsepSubring F E q := by
  classical
  intro r
  have hunits : (Units.mapEquiv ((σ : E ≃+* E) : E ≃* E) : Eˣ ≃* Eˣ)
      = Units.mapEquiv ((σ : E ≃+* E) : E ≃* E) := rfl
  have hcoeff : (deningerMonoidAlgebraMap (Units.map ((σ : E →+* E) : E →* E)) ξ).coeff r
      = ξ.coeff ((Units.mapEquiv ((σ : E ≃+* E) : E ≃* E)).symm r) :=
    deningerMonoidAlgebraMap_coeff (Units.mapEquiv ((σ : E ≃+* E) : E ≃* E)) ξ r
  rw [hcoeff]
  have hdeg : deningerInsepDegree F E q (r : E)
      = deningerInsepDegree F E q
        (((Units.mapEquiv ((σ : E ≃+* E) : E ≃* E)).symm r : Eˣ) : E) := by
    have h := deningerInsepDegree_algEquiv q σ
      (((Units.mapEquiv ((σ : E ≃+* E) : E ≃* E)).symm r : Eˣ) : E)
    rw [← h]
    congr 1
    show (r : E) = σ (((Units.mapEquiv ((σ : E ≃+* E) : E ≃* E)).symm r : Eˣ) : E)
    have := (Units.mapEquiv ((σ : E ≃+* E) : E ≃* E)).apply_symm_apply r
    exact congrArg (fun u : Eˣ => (u : E)) this.symm
  rw [hdeg]
  exact hξ _

end

end RHTower
