import GaloisForLFunctions.HTGeometry.IsogenyLattice
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Isogeny classes of finitely generated abelian groups

A finitely generated abelian group is isogenous to a free module of finite rank: the structure
theorem splits it as a free part times a finite part, and projecting away the finite part is a
surjective map with finite kernel.  Consequently every finitely generated abelian group is
isogeny-regular, and the isogeny classes of finitely generated abelian groups are exactly the
ranks — torsion is invisible to isogeny, while rank is a complete invariant.
-/

open Module

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

namespace IsogenyFinitelyGenerated

/-- Projection off a finite factor is a surjective isogeny. -/
theorem isAddIsogeny_fst (A F : Type*) [AddCommGroup A] [AddCommGroup F] [Finite F] :
    IsAddIsogeny (AddMonoidHom.fst A F) := by
  refine IsAddIsogeny.of_surjective (fun a => ⟨(a, 0), rfl⟩) ?_
  refine Finite.of_injective (fun x : (AddMonoidHom.fst A F).ker => ((x : A × F).2)) ?_
  intro x y hxy
  have hx : (x : A × F).1 = 0 := x.2
  have hy : (y : A × F).1 = 0 := y.2
  exact Subtype.ext (Prod.ext (hx.trans hy.symm) hxy)

/-- An additive isomorphism is an isogeny. -/
theorem isAddIsogeny_of_addEquiv (e : G ≃+ H) : IsAddIsogeny (e : G →+ H) :=
  IsAddIsogeny.of_bijective e.bijective

/-- **Every finitely generated abelian group is isogenous to a lattice.** -/
theorem exists_isAddIsogenous_fin_fun (G : Type) [AddCommGroup G] [AddGroup.FG G] :
    ∃ n : ℕ, IsAddIsogenous G (Fin n → ℤ) := by
  obtain ⟨n, ι, hι, p, hp, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (G := G)
  refine ⟨n, ?_⟩
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_injective (DFinsupp.equivFunOnFintype (β := fun i : ι => ZMod (p i ^ e i)))
      (Equiv.injective _)
  -- `G ≃ (Fin n →₀ ℤ) × (finite)`, then project, then identify `Fin n →₀ ℤ` with `Fin n → ℤ`.
  set L := Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n) with hL
  refine ⟨((L : (Fin n →₀ ℤ) ≃+ (Fin n → ℤ)) : (Fin n →₀ ℤ) →+ (Fin n → ℤ)).comp
      ((AddMonoidHom.fst (Fin n →₀ ℤ) (DirectSum ι fun i => ZMod (p i ^ e i))).comp
        (φ : G →+ _)), ?_⟩
  exact IsAddIsogeny.comp (isAddIsogeny_of_addEquiv (L : (Fin n →₀ ℤ) ≃+ (Fin n → ℤ)))
    (IsAddIsogeny.comp (isAddIsogeny_fst _ _) (isAddIsogeny_of_addEquiv φ))

/-- Finitely generated abelian groups are isogeny-regular. -/
instance (priority := 100) isAddIsogenyRegular_of_fg (G : Type) [AddCommGroup G]
    [AddGroup.FG G] : IsAddIsogenyRegular G := by
  obtain ⟨n, f, hf⟩ := exists_isAddIsogenous_fin_fun G
  exact IsAddIsogeny.isAddIsogenyRegular_source hf

/-- **Rank is a complete isogeny invariant for finitely generated abelian groups.** -/
theorem isAddIsogenous_iff_rank_eq {m n : ℕ}
    (hG : IsAddIsogenous G (Fin m → ℤ)) (hH : IsAddIsogenous H (Fin n → ℤ)) :
    IsAddIsogenous G H ↔ m = n := by
  obtain ⟨fG, hfG⟩ := hG
  obtain ⟨fH, hfH⟩ := hH
  haveI : IsAddIsogenyRegular G := IsAddIsogeny.isAddIsogenyRegular_source hfG
  haveI : IsAddIsogenyRegular H := IsAddIsogeny.isAddIsogenyRegular_source hfH
  constructor
  · intro hGH
    obtain ⟨g, hg⟩ := IsAddIsogenous.trans
      (IsAddIsogenous.symm (⟨fG, hfG⟩ : IsAddIsogenous G (Fin m → ℤ)))
      (IsAddIsogenous.trans hGH (⟨fH, hfH⟩ : IsAddIsogenous H (Fin n → ℤ)))
    have := IsogenyLattice.finrank_eq_of_isAddIsogeny hg
    rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at this
  · rintro rfl
    exact IsAddIsogenous.trans (⟨fG, hfG⟩ : IsAddIsogenous G (Fin m → ℤ))
      (IsAddIsogenous.symm (⟨fH, hfH⟩ : IsAddIsogenous H (Fin m → ℤ)))

end IsogenyFinitelyGenerated
