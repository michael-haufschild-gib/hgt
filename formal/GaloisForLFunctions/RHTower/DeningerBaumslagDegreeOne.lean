import GaloisForLFunctions.RHTower.DeningerBaumslagRationalization
import GaloisForLFunctions.RHTower.DeningerDegreeOneInflation
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Degree one for the free rational packet

With trivial rational coefficients, first cohomology is the group of homomorphisms, so the
degree-one comparison along `a_U : Bau(F_m) ↠ A` is the restriction of homomorphisms.  That
restriction is bijective for a purely formal reason: the target is a rational vector space, hence
has unique roots, so homomorphisms out of the rationalization correspond to homomorphisms out of
the free group, and those correspond to functions on the basis — which is also what homomorphisms
out of `A` are.

No rational homology computation is needed for this: the adjunction does it.

* `deningerBauFreeHom_factors` : every homomorphism into a rational vector space factors through
  `a_U`.
* `deningerBauFree_degreeOne_bijective` : the degree-one comparison is an isomorphism.
* `deningerBauFreeKer_killed` : equivalently, every such homomorphism kills `K_U`.
-/

namespace RHTower

section BaumslagDegreeOne

universe u v w

variable {ι : Type u} {A : Type v} {M : Type w}
  [AddCommGroup A] [Module ℚ A] [AddCommGroup M] [Module ℚ M]

/-- **Every homomorphism from the rationalization of a free group into a rational vector space
factors through the surjection onto the vector space.**  The homomorphism is determined by its
values on the free generators, and those values are matched by the linear map the basis produces. -/
theorem deningerBauFreeHom_factors (b : Module.Basis ι ℚ A)
    (φ : DeningerBau (FreeGroup ι) →* Multiplicative M) :
    ∃ ψ : Multiplicative A →* Multiplicative M,
      ψ.comp (deningerBauFreeMap (⇑b)) = φ := by
  classical
  set c : ι → M := fun i => Multiplicative.toAdd (φ (DeningerBau.of (FreeGroup.of i))) with hc
  refine ⟨AddMonoidHom.toMultiplicative ((b.constr ℚ c : A →ₗ[ℚ] M).toAddMonoidHom), ?_⟩
  set ψ : Multiplicative A →* Multiplicative M :=
    AddMonoidHom.toMultiplicative ((b.constr ℚ c : A →ₗ[ℚ] M).toAddMonoidHom) with hψ
  have hcomp : (ψ.comp (deningerBauFreeMap (⇑b))).comp
      (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)) =
      φ.comp (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show ψ (deningerBauFreeMap (⇑b) (DeningerBau.of (FreeGroup.of i))) =
      φ (DeningerBau.of (FreeGroup.of i))
    rw [deningerBauFreeMap, deningerBauLift_of, FreeGroup.lift_apply_of]
    show Multiplicative.ofAdd ((b.constr ℚ c : A →ₗ[ℚ] M) (b i)) = _
    rw [Module.Basis.constr_basis]
    exact congrArg Multiplicative.ofAdd rfl
  have key : ∀ a : FreeGroup ι,
      (ψ.comp (deningerBauFreeMap (⇑b))) (DeningerBau.of a) =
        (φ.comp (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι))) a :=
    fun a => DFunLike.congr_fun hcomp a
  have h1 := deningerBauLift_unique (deningerMultiplicative_uniquelyDivisible (A := M))
    (φ.comp (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)))
    (ψ.comp (deningerBauFreeMap (⇑b))) key
  have h2 := deningerBauLift_unique (deningerMultiplicative_uniquelyDivisible (A := M))
    (φ.comp (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι))) φ (fun _ => rfl)
  exact h1.trans h2.symm

/-- **Clause 3 in degree one.**  With trivial rational coefficients the comparison along `a_U` is
an isomorphism on first cohomology. -/
theorem deningerBauFree_degreeOne_bijective (b : Module.Basis ι ℚ A) :
    Function.Bijective
      (deningerHomRestrict (M := Multiplicative M) (deningerBauFreeMap (⇑b))) :=
  ⟨deningerHomRestrict_injective (deningerBauFree_surjective (⇑b) b.span_eq),
    fun φ => deningerBauFreeHom_factors b φ⟩

/-- **Every homomorphism into a rational vector space kills `K_U`.**  This is the vanishing that
the card's degree-one reduction asks for; it needs no rational homology input. -/
theorem deningerBauFreeKer_killed (b : Module.Basis ι ℚ A)
    (psi : DeningerBau (FreeGroup ι) →* Multiplicative M)
    {k : DeningerBau (FreeGroup ι)} (hk : k ∈ (deningerBauFreeMap (⇑b)).ker) : psi k = 1 :=
  (deningerHomRestrict_bijective_iff
      (M := Multiplicative M) (deningerBauFree_surjective (⇑b) b.span_eq)).1
    (deningerBauFree_degreeOne_bijective b) psi k hk

/-- Additive maps between rational vector spaces are the same as linear maps. -/
def deningerRatHomEquiv : (A →+ M) ≃ (A →ₗ[ℚ] M) where
  toFun f := f.toRatLinearMap
  invFun g := g.toAddMonoidHom
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The degree-one cohomology of the packet is `U`.**  First cohomology with trivial rational
coefficients is the group of homomorphisms; clause 3 identifies it with the homomorphisms out of
`A = U^∨`, those are the linear functionals on `A`, and for a reflexive `U` the double dual is `U`
again. -/
noncomputable def deningerBauFree_degreeOne_equiv {U : Type v} [AddCommGroup U] [Module ℚ U]
    [Module.IsReflexive ℚ U] (b : Module.Basis ι ℚ (Module.Dual ℚ U)) :
    (DeningerBau (FreeGroup ι) →* Multiplicative ℚ) ≃ U :=
  (Equiv.ofBijective _ (deningerBauFree_degreeOne_bijective (M := ℚ) b)).symm.trans
    (AddMonoidHom.toMultiplicative.symm.trans
      (deningerRatHomEquiv.trans (Module.evalEquiv ℚ U).symm.toEquiv))

end BaumslagDegreeOne

end RHTower
