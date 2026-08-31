import GaloisForLFunctions.HTGeometry.PiFibreSplit

/-!
# The fibre of a product

```text
prodQuotSmulEquiv   ** the fibre of a product is the product of the fibres **
```

The binary companion of `piQuotSmulEquiv`, proved the same way from `smul_top_prod`: the two
projections induce the map, its kernel is exactly the product of the two `I • ⊤`, and both
surjectivity and injectivity are read off coordinatewise.

Together the two give the additivity needed to compute a fibre along the decomposition of a finitely
generated module over a principal ideal domain into a free part and finitely many cyclic torsion
parts.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise

variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- The fibre of a product is the product of the fibres. -/
noncomputable def prodQuotSmulEquiv (I : Ideal A) :
    ((M × N) ⧸ (I • (⊤ : Submodule A (M × N))))
      ≃ₗ[A] ((M ⧸ (I • (⊤ : Submodule A M))) × (N ⧸ (I • (⊤ : Submodule A N)))) := by
  classical
  set F : (M × N) →ₗ[A] ((M ⧸ (I • (⊤ : Submodule A M))) × (N ⧸ (I • (⊤ : Submodule A N)))) :=
    ((Submodule.mkQ (I • (⊤ : Submodule A M))).comp (LinearMap.fst A M N)).prod
      ((Submodule.mkQ (I • (⊤ : Submodule A N))).comp (LinearMap.snd A M N)) with hF
  have hFapp : ∀ x : M × N,
      F x = (Submodule.Quotient.mk x.1, Submodule.Quotient.mk x.2) := fun x => rfl
  have hker : I • (⊤ : Submodule A (M × N)) ≤ LinearMap.ker F := by
    intro x hx
    rw [smul_top_prod] at hx
    rw [LinearMap.mem_ker, hFapp]
    have h1 : Submodule.Quotient.mk x.1 = (0 : M ⧸ (I • (⊤ : Submodule A M))) := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact hx.1
    have h2 : Submodule.Quotient.mk x.2 = (0 : N ⧸ (I • (⊤ : Submodule A N))) := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact hx.2
    rw [h1, h2]
    rfl
  refine LinearEquiv.ofBijective (Submodule.liftQ _ F hker) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.liftQ_apply, hFapp] at hx
      rw [Submodule.Quotient.mk_eq_zero, smul_top_prod]
      constructor
      · have : Submodule.Quotient.mk y.1 = (0 : M ⧸ (I • (⊤ : Submodule A M))) :=
          congrArg Prod.fst hx
        rwa [Submodule.Quotient.mk_eq_zero] at this
      · have : Submodule.Quotient.mk y.2 = (0 : N ⧸ (I • (⊤ : Submodule A N))) :=
          congrArg Prod.snd hx
        rwa [Submodule.Quotient.mk_eq_zero] at this
  · rintro ⟨a, b⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule A M)) a
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule A N)) b
    exact ⟨Submodule.Quotient.mk (u, v), by rw [Submodule.liftQ_apply, hFapp]⟩

end GaloisForLFunctions.HTGeometry
