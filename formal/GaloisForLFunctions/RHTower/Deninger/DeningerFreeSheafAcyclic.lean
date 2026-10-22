import GaloisForLFunctions.RHTower.Deninger.DeningerDolbeaultFine

/-!
# Free analytic sheaves of finite rank are acyclic

`Ext` out of a fixed object commutes with a finite direct sum in its second variable, so the
cohomology of a finite direct sum of sheaves is the product of their cohomologies and vanishes as
soon as each summand's does.  Applied to the structure sheaf of a character stage this is Cartan's
theorem B for a free coherent analytic sheaf of finite rank, which is the acyclicity the subquotients
of a finite relative cell filtration have.  In degree zero the same equivalence says global sections
commute with a finite direct sum.

* `RHTower.deningerBiproductCohomologyEquiv` : cohomology of a finite direct sum.
* `RHTower.deningerBiproduct_ext_eq_zero` : a finite direct sum of acyclic sheaves is acyclic.
* `RHTower.deningerFreeHolomorphicSheaf` : the free analytic sheaf of finite rank.
* `RHTower.deningerFree_ext_eq_zero_punctured` : **Cartan's theorem B for a free sheaf of finite
  rank on `(ℂ^×)^n`**.
* `RHTower.deningerBiproductSectionsEquiv` : global sections commute with a finite direct sum.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

section Biproduct

universe w u

variable {X : TopCat.{u}} [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- **Sheaf cohomology commutes with a finite direct sum of sheaves.** -/
noncomputable def deningerBiproductCohomologyEquiv (U : Opens X) {J : Type} [Fintype J]
    (F : J → TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    deningerSheafCohomology.{w} U (⨁ F) n ≃+ ∀ i, deningerSheafCohomology.{w} U (F i) n :=
  Ext.addEquivBiproduct (deningerOpenFree U) (biproduct.isBilimit F) n

/-- **A finite direct sum of sheaves without higher cohomology has none.** -/
theorem deningerBiproduct_ext_eq_zero (U : Opens X) {J : Type} [Fintype J]
    (F : J → TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (h : ∀ (i : J) (y : deningerSheafCohomology.{w} U (F i) n), y = 0)
    (x : deningerSheafCohomology.{w} U (⨁ F) n) : x = 0 := by
  refine (deningerBiproductCohomologyEquiv.{w} U F n).injective ?_
  rw [map_zero]
  funext i
  exact h i _

/-- **Acyclicity transports along an isomorphism of sheaves.** -/
theorem deningerAcyclicOn_of_iso {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ≅ G)
    (U : Opens X) (h : DeningerAcyclicOn.{w} F U) : DeningerAcyclicOn.{w} G U := by
  intro n x
  have hy : x.comp (Ext.mk₀ e.inv) (add_zero (n + 1)) = 0 := h n _
  have hback := congrArg
    (fun z : Ext.{w} (deningerOpenFree U) F (n + 1) => z.comp (Ext.mk₀ e.hom) (add_zero (n + 1)))
    hy
  simpa [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id] using hback

/-- **Global sections commute with a finite direct sum of sheaves.** -/
noncomputable def deningerBiproductSectionsEquiv (U : Opens X) {J : Type} [Fintype J]
    (F : J → TopCat.Sheaf AddCommGrpCat.{u} X) :
    ToType ((⨁ F).1.obj (op U)) ≃ ∀ i, ToType ((F i).1.obj (op U)) :=
  (deningerSheafCohomologyZeroEquiv.{w} U (⨁ F)).symm.trans
    (((deningerBiproductCohomologyEquiv.{w} U F 0).toEquiv).trans
      (Equiv.piCongrRight fun i => deningerSheafCohomologyZeroEquiv.{w} U (F i)))

end Biproduct

end RHTower

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat
  Complex

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

section Free

universe w

variable {n : ℕ}

/-- **The free analytic sheaf of finite rank on a domain**: a finite direct sum of copies of the
sheaf of holomorphic functions. -/
noncomputable def deningerFreeHolomorphicSheaf (Ω : Opens (Fin n → ℂ)) (J : Type) [Fintype J] :
    TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace Ω) :=
  ⨁ fun _ : J => deningerClosedFormSheaf Ω 0

/-- **Cartan's theorem B for a free analytic sheaf of finite rank on `ℂ^n`.** -/
theorem deningerFree_ext_eq_zero
    [CategoryTheory.HasExt.{w}
      (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (⊤ : Opens (Fin n → ℂ))))]
    (J : Type) [Fintype J] (q : ℕ)
    (x : deningerSheafCohomology.{w}
      (⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ))))
      (deningerFreeHolomorphicSheaf (⊤ : Opens (Fin n → ℂ)) J) (q + 1)) : x = 0 :=
  deningerBiproduct_ext_eq_zero.{w} _ _ _ (fun _ y => deningerHolomorphic_ext_eq_zero q y) x

/-- **Cartan's theorem B for a free analytic sheaf of finite rank on `(ℂ^×)^n`.**  These are the
subquotients of a finite relative cell filtration on a character stage, so this is the acyclicity
that lets a derived global section functor be computed by ordinary global sections. -/
theorem deningerFree_ext_eq_zero_punctured
    [CategoryTheory.HasExt.{w}
      (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n)))]
    (J : Type) [Fintype J] (q : ℕ)
    (x : deningerSheafCohomology.{w}
      (⊤ : Opens (deningerSpace (deningerPunctured n)))
      (deningerFreeHolomorphicSheaf (deningerPunctured n) J) (q + 1)) : x = 0 :=
  deningerBiproduct_ext_eq_zero.{w} _ _ _
    (fun _ y => deningerHolomorphic_ext_eq_zero_punctured q y) x

/-- A free analytic sheaf of finite rank on `ℂ^n` is acyclic. -/
theorem deningerFree_acyclicOn
    [CategoryTheory.HasExt.{w}
      (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (⊤ : Opens (Fin n → ℂ))))]
    (J : Type) [Fintype J] :
    DeningerAcyclicOn.{w} (deningerFreeHolomorphicSheaf (⊤ : Opens (Fin n → ℂ)) J) ⊤ :=
  fun q x => deningerFree_ext_eq_zero J q x

/-- **A free analytic sheaf of finite rank on `(ℂ^×)^n` is acyclic.** -/
theorem deningerFree_acyclicOn_punctured
    [CategoryTheory.HasExt.{w}
      (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n)))]
    (J : Type) [Fintype J] :
    DeningerAcyclicOn.{w} (deningerFreeHolomorphicSheaf (deningerPunctured n) J) ⊤ :=
  fun q x => deningerFree_ext_eq_zero_punctured J q x

/-- The higher cohomology of a free analytic sheaf of finite rank on `(ℂ^×)^n` is a subsingleton. -/
theorem deningerFree_subsingleton_cohomology_punctured
    [CategoryTheory.HasExt.{w}
      (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n)))]
    (J : Type) [Fintype J] (q : ℕ) :
    Subsingleton (deningerSheafCohomology.{w}
      (⊤ : Opens (deningerSpace (deningerPunctured n)))
      (deningerFreeHolomorphicSheaf (deningerPunctured n) J) (q + 1)) :=
  ⟨fun a b => by
    rw [deningerFree_ext_eq_zero_punctured J q a, deningerFree_ext_eq_zero_punctured J q b]⟩

/-- **The global sections of a free analytic sheaf of finite rank** are the tuples of holomorphic
functions. -/
noncomputable def deningerFreeSectionsEquiv
    [CategoryTheory.HasExt.{w}
      (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n)))]
    (J : Type) [Fintype J] :
    ToType ((deningerFreeHolomorphicSheaf (deningerPunctured n) J).1.obj
        (op (⊤ : Opens (deningerSpace (deningerPunctured n)))))
      ≃ ∀ _ : J, ToType ((deningerClosedFormSheaf (deningerPunctured n) 0).1.obj
        (op (⊤ : Opens (deningerSpace (deningerPunctured n))))) :=
  deningerBiproductSectionsEquiv.{w} _ _

end Free

end RHTower
