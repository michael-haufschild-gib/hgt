import GaloisForLFunctions.RHTower.DeningerCohomologyDimensionShift

/-!
# The rationalization does not change low-degree rational cohomology

The card's proof quotes `H_*(R_U;ℚ) ≅ H_*(F_m;ℚ)` from Casacuberta--Peschke.  In the degrees where
both sides are computed here the comparison is proved outright, with no import: the adjunction
identifies homomorphisms out of the rationalization with homomorphisms out of the free group, so
`H⁰` and `H¹` agree, and `H²` vanishes on both sides.

* `deningerBauHomEquiv` : the adjunction as an explicit bijection of hom-sets.
* `deningerBau_H1_equiv` : `H¹(Bau(F_ι); M) ≃ (ι → M) ≃ H¹(F_ι; M)`.
* `deningerBau_H0_equiv`, `deningerBau_isZero_H2` : degrees zero and two.
-/

namespace RHTower

open CategoryTheory Limits groupCohomology

section HomEquiv

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- **The adjunction as a bijection**: homomorphisms out of the rationalization are homomorphisms
out of the group, whenever the target has unique roots. -/
noncomputable def deningerBauHomEquiv (hH : DeningerUniquelyDivisible H) :
    (DeningerBau G →* H) ≃ (G →* H) where
  toFun F := F.comp (DeningerBau.of : G →* DeningerBau G)
  invFun f := deningerBauLift hH f
  left_inv F := (deningerBauLift_unique hH _ F (fun _ => rfl)).symm
  right_inv f := deningerBauLift_comp hH f

end HomEquiv

section BaumslagComparison

variable {ι : Type} {M : Type} [AddCommGroup M] [Module ℚ M]

/-- **`H¹` is unchanged by rationalization**: both sides are the functions on the generators. -/
noncomputable def deningerBau_H1_equiv :
    (H1 (Rep.trivial ℚ (DeningerBau (FreeGroup ι)) M) : Type) ≃ (ι → M) :=
  deningerTrivial_H1_equiv.trans
    (deningerCocycles₁Equiv.trans
      ((deningerBauHomEquiv (deningerMultiplicative_uniquelyDivisible (A := M))).trans
        (deningerCocycles₁Equiv (G := FreeGroup ι) (M := M)).symm |>.trans
          deningerFreeGroupCocycles₁Equiv))

/-- **`H⁰` is unchanged by rationalization.** -/
noncomputable def deningerBau_H0_equiv :
    (H0 (Rep.trivial ℚ (DeningerBau (FreeGroup ι)) M)) ≅ ModuleCat.of ℚ M :=
  deningerTrivial_H0_equiv

/-- **`H²` vanishes on both sides.** -/
theorem deningerBau_isZero_H2 :
    IsZero (groupCohomology (Rep.trivial ℚ (DeningerBau (FreeGroup ι)) M) 2) := by
  have hsub : Subsingleton (groupCohomology (Rep.trivial ℚ (DeningerBau (FreeGroup ι)) M) 2) :=
    ⟨fun x y => by
      rw [deningerBauFree_H2_eq_zero (ι := ι) (M := M) x,
        deningerBauFree_H2_eq_zero (ι := ι) (M := M) y]⟩
  exact ModuleCat.isZero_of_subsingleton _

end BaumslagComparison

end RHTower
