import GaloisForLFunctions.HTGeometry.Buildings.FlagIntervals
import GaloisForLFunctions.HTGeometry.RelativeSimplicialHomology
import GaloisForLFunctions.HTGeometry.NerveSubcomplex

/-!
# Relative cone chains for flag buildings

Adjoining a greatest vertex makes every order complex contractible.
The connecting map of its relative chain sequence therefore identifies
relative homology in degree `n + 2` with the original homology in degree
`n + 1`. Applied to flag intervals, this realizes the quotient Steinberg
classes by relative chains and transfers their freeness and concentration.

This is the contractible-pair mechanism in Ash--Gunnells,
arXiv:2611.03303, Lemma 3.3 and Corollary 3.4.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial

universe v u

variable (P : Type u) [PartialOrder P]

/-- The base of the order cone consists of its finite vertices. -/
def orderConeBase : (nerve (WithTop P)).Subcomplex :=
  nerveSubcomplex {x : WithTop P | x ≠ ⊤}

/-- Removing the newly adjoined top recovers the original order. -/
def orderConeBaseOrderIso : {x : WithTop P // x ≠ ⊤} ≃o P where
  toFun x := match x with
    | ⟨none, h⟩ => False.elim (h rfl)
    | ⟨some p, _⟩ => p
  invFun p := ⟨some p, by intro h; cases h⟩
  left_inv x := by
    rcases x with ⟨_ | p, h⟩
    · exact False.elim (h rfl)
    · rfl
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨_ | p, hp⟩ ⟨_ | q, hq⟩
    · exact False.elim (hp rfl)
    · exact False.elim (hp rfl)
    · exact False.elim (hq rfl)
    · exact WithTop.coe_le_coe.symm

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- Relative chains of an order cone modulo its base. -/
noncomputable def orderConeRelativeChains (R : C) : ChainComplex C ℕ :=
  relChainComplex (nerve (WithTop P)) R (orderConeBase P)

/-- The actual connecting homomorphism is invertible in positive base degrees. -/
noncomputable def orderConeRelativeHomologyIso (R : C) (n : ℕ) :
    (orderConeRelativeChains P R).homology (n + 2) ≅ (nerve P).homology R (n + 1) := by
  have hS := relChainShortExact (nerve (WithTop P)) R (orderConeBase P)
  exact (@asIso _ _ _ _ (hS.δ (n + 2) (n + 1) rfl) (hS.isIso_δ _ _ rfl
    (isZero_homology_of_orderTop (P := WithTop P) R (n + 2) (by omega))
    (isZero_homology_of_orderTop (P := WithTop P) R (n + 1) (by omega))))
    ≪≫ nerveSubcomplexHomologyIso _ R (n + 1)
    ≪≫ (SSet.homologyFunctor R (n + 1)).mapIso (orderIsoNerveIso (orderConeBaseOrderIso P))

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

/-- Relative cone homology of every flag interval is free. -/
theorem isFreeOver_flagIntervalRelativeHomology (A B : Submodule K V) (R : C) (n : ℕ) :
    IsFreeOver.{v, u, u} R
      ((orderConeRelativeChains (flagInterval A B) R).homology (n + 2)) :=
  IsFreeOver.of_iso (isFreeOver_flagIntervalHomology A B R (n + 1))
    (orderConeRelativeHomologyIso (flagInterval A B) R n)

variable [FiniteDimensional K V]

/-- The only possible nonzero positive relative degree is one above the building degree. -/
theorem flagIntervalRelativeHomology_support (A B : Submodule K V) (R : C) (n : ℕ) :
    n + 1 = Module.finrank K (flagLayer A B) - 2 ∨
      IsZero ((orderConeRelativeChains (flagInterval A B) R).homology (n + 2)) := by
  rcases flagIntervalHomology_support A B R (n + 1) with h | h | h
  · omega
  · exact Or.inl h
  · exact Or.inr (IsZero.of_iso h (orderConeRelativeHomologyIso (flagInterval A B) R n))

end Homology

end GaloisForLFunctions.HTGeometry
