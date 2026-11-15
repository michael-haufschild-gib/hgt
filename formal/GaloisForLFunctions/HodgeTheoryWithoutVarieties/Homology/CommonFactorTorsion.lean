import GaloisForLFunctions.HTGeometry.CommonFactorKoszulHomology

/-!
# Common-factor Koszul homology with torsion

In split coordinates the differential is `(u,v) ↦ (z v,0)`. Its homology is
the quotient of the first exterior power by `z`, together with the `z`-torsion
in the second exterior power. This removes the regularity restriction from
the existing common-factor complex in every degree.

The splitting isolates the closed generator family, as in the shear of
Lemma 3.14 of Kurnosov–Ríos Ortiz, https://arxiv.org/abs/2611.01210.
-/

noncomputable section
open ExteriorAlgebra
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties
variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- Scalar torsion in an exterior power, retained even when the factor is a zero divisor. -/
abbrev exteriorScalarTorsion (z : R) (E : Type*) [AddCommGroup E] [Module R E] (p : ℕ) :=
  LinearMap.ker (commonFactorScalarMap z : (⋀[R]^p E) →ₗ[R] (⋀[R]^p E))

/-- The quotient summand of common-factor homology. -/
abbrev exteriorScalarQuotient (z : R) (E : Type*) [AddCommGroup E] [Module R E] (p : ℕ) :=
  (⋀[R]^p E) ⧸ LinearMap.range (commonFactorScalarMap z : (⋀[R]^p E) →ₗ[R] (⋀[R]^p E))

/-- Every cycle has a free first coordinate and a torsion second coordinate. -/
def commonFactorTorsionCyclesEquiv (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) : splitCommonFactorKoszulCycles z E p ≃ₗ[R]
      (⋀[R]^(p + 1) E) × exteriorScalarTorsion z E p where
  toFun x := (x.val.1, ⟨x.val.2, x.property⟩)
  invFun x := ⟨(x.1, x.2.val), x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Send a cycle to its quotient coordinate and its surviving torsion coordinate. -/
def commonFactorTorsionProjection (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) : splitCommonFactorKoszulCycles z E p →ₗ[R]
      exteriorScalarQuotient z E (p + 1) × exteriorScalarTorsion z E p :=
  (LinearMap.prodMap
    (LinearMap.range (commonFactorScalarMap z :
      (⋀[R]^(p + 1) E) →ₗ[R] (⋀[R]^(p + 1) E))).mkQ
    LinearMap.id).comp (commonFactorTorsionCyclesEquiv z E p).toLinearMap

/-- Every pair of quotient and torsion classes has a cycle representative. -/
theorem commonFactorTorsionProjection_surjective (z : R) (E : Type*) [AddCommGroup E]
    [Module R E] (p : ℕ) : Function.Surjective (commonFactorTorsionProjection z E p) := by
  rintro ⟨q, t⟩
  obtain ⟨u, hu⟩ := (LinearMap.range (commonFactorScalarMap z :
    (⋀[R]^(p + 1) E) →ₗ[R] (⋀[R]^(p + 1) E))).mkQ_surjective q
  exact ⟨(commonFactorTorsionCyclesEquiv z E p).symm (u, t), Prod.ext hu rfl⟩

/-- The projection kills precisely the actual boundaries of the complex. -/
theorem commonFactorTorsionProjection_ker (z : R) (E : Type*) [AddCommGroup E]
    [Module R E] (p : ℕ) :
    (commonFactorTorsionProjection z E p).ker = splitCommonFactorKoszulBoundaries z E p := by
  ext x
  constructor
  · intro hx
    have hq : (Submodule.Quotient.mk x.val.1 : exteriorScalarQuotient z E (p + 1)) = 0 :=
      congrArg Prod.fst hx
    have ht : x.val.2 = 0 := congrArg (fun t => (t.2 : ⋀[R]^p E)) hx
    obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    exact ⟨w, Prod.ext hw ht.symm⟩
  · rintro ⟨w, hw⟩
    apply Prod.ext
    · change Submodule.Quotient.mk x.val.1 = (0 : exteriorScalarQuotient z E (p + 1))
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨w, congrArg Prod.fst hw⟩
    · apply Subtype.ext
      exact (congrArg Prod.snd hw).symm

/-- Cycles inherit additive inverses from multiplication by minus one. -/
local instance commonFactorCyclesAddCommGroup (z : R) (E : Type*) [AddCommGroup E]
    [Module R E] (p : ℕ) : AddCommGroup (splitCommonFactorKoszulCycles z E p) :=
  Module.addCommMonoidToAddCommGroup R

/-- Homology of the split common-factor complex, using its actual boundary relation. -/
abbrev commonFactorTorsionHomology (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) : Type _ :=
  splitCommonFactorKoszulCycles z E p ⧸ splitCommonFactorKoszulBoundaries z E p

/-- The cycle projection descends to the actual homology quotient. -/
def commonFactorTorsionHomologyMap (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) : commonFactorTorsionHomology z E p →ₗ[R]
      exteriorScalarQuotient z E (p + 1) × exteriorScalarTorsion z E p :=
  (splitCommonFactorKoszulBoundaries z E p).liftQ (commonFactorTorsionProjection z E p)
    (le_of_eq (commonFactorTorsionProjection_ker z E p).symm)

theorem commonFactorTorsionHomologyMap_injective (z : R) (E : Type*) [AddCommGroup E]
    [Module R E] (p : ℕ) : Function.Injective (commonFactorTorsionHomologyMap z E p) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro u v h
  apply (Submodule.Quotient.eq (splitCommonFactorKoszulBoundaries z E p)).mpr
  rw [← commonFactorTorsionProjection_ker, LinearMap.mem_ker, map_sub]
  exact sub_eq_zero.mpr h

theorem commonFactorTorsionHomologyMap_surjective (z : R) (E : Type*) [AddCommGroup E]
    [Module R E] (p : ℕ) : Function.Surjective (commonFactorTorsionHomologyMap z E p) := by
  intro t
  obtain ⟨u, rfl⟩ := commonFactorTorsionProjection_surjective z E p t
  exact ⟨Submodule.Quotient.mk u, rfl⟩

/-- In every degree, homology is the scalar quotient plus the scalar torsion. -/
def commonFactorTorsionHomologyEquiv (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) :
    commonFactorTorsionHomology z E p ≃ₗ[R]
      exteriorScalarQuotient z E (p + 1) × exteriorScalarTorsion z E p :=
  LinearEquiv.ofBijective (commonFactorTorsionHomologyMap z E p)
    ⟨commonFactorTorsionHomologyMap_injective z E p,
      commonFactorTorsionHomologyMap_surjective z E p⟩

#print axioms commonFactorTorsionCyclesEquiv
#print axioms commonFactorTorsionProjection_ker
#print axioms commonFactorTorsionHomologyEquiv
end GaloisForLFunctions.HodgeTheoryWithoutVarieties
