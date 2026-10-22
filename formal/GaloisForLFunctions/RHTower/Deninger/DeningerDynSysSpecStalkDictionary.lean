import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysValuedLocalCriterion
import GaloisForLFunctions.HTGeometry.SpecStalkLocalization

/-!
# Evaluation of germs on an affine scheme

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 13.5 (`t45`).

On `Spec R` the stalk at a prime `𝔮` is `R_𝔮`, and for `𝔭 ⊆ 𝔮` the evaluation of a germ at the
generic point `𝔭` is computed on the image of `R`: the structure map of the stalk at `𝔮` composed
with the specialisation map is the structure map of the stalk at `𝔭`.  The kernel of the induced
map `R → κ (𝔭)` is `𝔭`.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory HTGeometry

noncomputable section

universe u

variable {R : CommRingCat.{u}}

/-- The structure map of the stalk of `Spec R` at a prime. -/
@[reducible] def deningerSpecStalkAlgebra (p : PrimeSpectrum R) :
    Algebra R ((Spec R).presheaf.stalk p) :=
  StructureSheaf.stalkAlgebra (R := (R : Type u)) p

attribute [instance] deningerSpecStalkAlgebra

theorem deningerSpecStalkAlgebraMap (p : PrimeSpectrum R) (r : R) :
    algebraMap R ((Spec R).presheaf.stalk p) r = StructureSheaf.toStalk (R : Type u) p r :=
  rfl

instance deningerSpecStalk_isLocalization (p : PrimeSpectrum R) :
    IsLocalization.AtPrime ((Spec R).presheaf.stalk p) p.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk (R := (R : Type u)) p

/-- The specialisation map on stalks of `Spec R` is the identity on the image of `R`. -/
theorem deningerSpecStalkSpecializes_algebraMap {x y : PrimeSpectrum R} (h : x ⤳ y)
    (a : R) :
    ((Spec R).presheaf.stalkSpecializes h).hom
        (algebraMap R ((Spec R).presheaf.stalk y) a)
      = algebraMap R ((Spec R).presheaf.stalk x) a :=
  StructureSheaf.toStalk_stalkSpecializes_apply (R := (R : Type u)) h a

/-- Evaluation at `x` of the germ at `y` of a global function is its value at `x`. -/
theorem deningerSpecStalkValue_algebraMap {x y : PrimeSpectrum R} (h : x ⤳ y) (a : R) :
    stalkValue h (algebraMap R ((Spec R).presheaf.stalk y) a)
      = ((Spec R).residue x).hom
        (algebraMap R ((Spec R).presheaf.stalk x) a) := by
  rw [stalkValue_def, deningerSpecStalkSpecializes_algebraMap]

/-- A global function vanishes at `x` exactly when it lies in the corresponding prime. -/
theorem deningerSpecResidue_algebraMap_eq_zero_iff (x : PrimeSpectrum R) (a : R) :
    ((Spec R).residue x).hom
        (algebraMap R ((Spec R).presheaf.stalk x) a) = 0
      ↔ a ∈ x.asIdeal := by
  have hres : ((Spec R).residue x).hom
      (algebraMap R ((Spec R).presheaf.stalk x) a)
      = IsLocalRing.residue ((Spec R).presheaf.stalk x)
        (algebraMap R ((Spec R).presheaf.stalk x) a) := rfl
  have hunder := IsLocalization.AtPrime.under_maximalIdeal
    ((Spec R).presheaf.stalk x) x.asIdeal
  constructor
  · intro h0
    have h1 : IsLocalRing.residue ((Spec R).presheaf.stalk x)
        (algebraMap R ((Spec R).presheaf.stalk x) a) = 0 := hres.symm.trans h0
    have h2 : algebraMap R ((Spec R).presheaf.stalk x) a
        ∈ IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk x) :=
      (IsLocalRing.residue_eq_zero_iff _).1 h1
    have h3 : a ∈ Ideal.under (R : Type u)
        (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk x)) := h2
    rwa [hunder] at h3
  · intro hmem
    have h3 : a ∈ Ideal.under (R : Type u)
        (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk x)) := by
      rw [hunder]; exact hmem
    have h2 : algebraMap R ((Spec R).presheaf.stalk x) a
        ∈ IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk x) := h3
    exact hres.trans ((IsLocalRing.residue_eq_zero_iff _).2 h2)

end

end RHTower
