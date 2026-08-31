import Mathlib

/-!
# Fibres transport along equivalences and split along products

```text
map_smul_top_of_equiv   an equivalence carries I • ⊤ onto I • ⊤
quotSmulEquivOfEquiv    ** hence the fibre only depends on the isomorphism class **
smul_top_prod           ** and on a product, I • ⊤ is the product of the two I • ⊤ **
```

These are the two bookkeeping steps a fibre count needs before the structure theorem for finitely
generated modules over a principal ideal domain can be used: the count is invariant under
isomorphism, and it is additive along the decomposition into a free part and cyclic torsion parts.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise

variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

theorem map_smul_top_of_equiv (I : Ideal A) (e : M ≃ₗ[A] N) :
    Submodule.map (e : M →ₗ[A] N) (I • (⊤ : Submodule A M)) = I • (⊤ : Submodule A N) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap, Submodule.smul_le]
    intro r hr m _
    rw [Submodule.mem_comap]
    rw [show (e : M →ₗ[A] N) (r • m) = r • (e m) from map_smul e r m]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [Submodule.smul_le]
    intro r hr y _
    refine ⟨r • e.symm y, Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
    rw [show (e : M →ₗ[A] N) (r • e.symm y) = r • (e (e.symm y)) from map_smul e r _,
      e.apply_symm_apply]

/-- Transporting the fibre along a linear equivalence. -/
noncomputable def quotSmulEquivOfEquiv (I : Ideal A) (e : M ≃ₗ[A] N) :
    (M ⧸ (I • (⊤ : Submodule A M))) ≃ₗ[A] (N ⧸ (I • (⊤ : Submodule A N))) :=
  Submodule.Quotient.equiv _ _ e (map_smul_top_of_equiv I e)

theorem smul_top_prod (I : Ideal A) :
    I • (⊤ : Submodule A (M × N))
      = (I • (⊤ : Submodule A M)).prod (I • (⊤ : Submodule A N)) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.smul_le]
    intro r hr x _
    exact ⟨Submodule.smul_mem_smul hr Submodule.mem_top,
      Submodule.smul_mem_smul hr Submodule.mem_top⟩
  · rintro ⟨m, n⟩ ⟨hm, hn⟩
    have hm' : ((m, 0) : M × N) ∈ I • (⊤ : Submodule A (M × N)) := by
      refine Submodule.smul_induction_on (p := fun x => ((x, 0) : M × N) ∈ I • ⊤) hm ?_ ?_
      · intro r hr x _
        have hx : ((r • x, (0 : N))) = r • ((x, 0) : M × N) := by
          simp
        rw [hx]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · intro x y hx hy
        have hxy : ((x + y, (0 : N))) = ((x, 0) : M × N) + ((y, 0) : M × N) := by
          simp
        rw [hxy]
        exact Submodule.add_mem _ hx hy
    have hn' : (((0 : M), n) : M × N) ∈ I • (⊤ : Submodule A (M × N)) := by
      refine Submodule.smul_induction_on (p := fun y => (((0 : M), y) : M × N) ∈ I • ⊤) hn ?_ ?_
      · intro r hr y _
        have hy : (((0 : M), r • y)) = r • (((0 : M), y) : M × N) := by
          simp
        rw [hy]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · intro x y hx hy
        have hxy : (((0 : M), x + y)) = (((0 : M), x) : M × N) + (((0 : M), y) : M × N) := by
          simp
        rw [hxy]
        exact Submodule.add_mem _ hx hy
    have hsum := Submodule.add_mem _ hm' hn'
    simpa using hsum

end GaloisForLFunctions.HTGeometry
