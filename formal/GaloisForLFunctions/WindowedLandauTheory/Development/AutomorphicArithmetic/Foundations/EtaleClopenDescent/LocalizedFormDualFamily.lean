import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalizedProjectiveDualFamily
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularFormLattice
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Projective forms on a finite smooth chart give a dual family over
the fraction field of the base chart. -/

noncomputable section

open GlobalTheory.SchemeCohomology
open scoped GlobalTheory.SchemeCohomology nonZeroDivisors

namespace GlobalTheory.PD

variable {k A B F E : Type} [Field k]
  [CommRing A] [IsDomain A] [CommRing B] [Field F] [Field E]
  [Algebra k B] [Algebra k E] [Algebra A B] [Algebra A F] [Algebra A E] [Algebra B E]
  [Algebra F E] [IsScalarTower k B E] [IsScalarTower A B E] [IsScalarTower A F E]
  [IsFractionRing A F] [Module.Finite A B] [Module.Projective A B] [Algebra.Smooth k B]
  [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) E]

/-- The generic dual coordinates of regular forms on a finite
projective smooth algebra are integral on the base chart. -/
theorem exists_localized_form_dual_family (p : ℕ) :
    let u := algebraFormPullback k B E p
    ∃ (n : ℕ) (v : Fin n → ExteriorDifferentials k B p)
      (φ : Fin n → ExteriorDifferentials k E p →ₗ[F] F),
      (∀ j m, φ j (u m) ∈ (algebraMap A F).range) ∧
      ∀ w : ExteriorDifferentials k E p, w = ∑ j, φ j w • u (v j) := by
  intro u
  let M := ExteriorDifferentials k B p
  let W := ExteriorDifferentials k E p
  letI : Module A M := exteriorPowerModule p
  letI : Module A W := exteriorPowerModule p
  letI : Module B W := exteriorPowerModule p
  letI : Module F W := exteriorPowerModule p
  letI : IsScalarTower A B M := exteriorPowerScalarTower p
  letI : IsScalarTower A B W := IsScalarTower.to₁₂₄ A B E W
  letI : IsScalarTower A F W := IsScalarTower.to₁₂₄ A F E W
  letI : Module.Finite B M := inferInstance
  letI : Module.Projective B M := exteriorPower_moduleProjective p
  letI : Module.Finite A M := Module.Finite.trans B M
  letI : Module.Projective A M := by
    obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective B M
    letI : Module.Projective A (Fin n → B) :=
      Module.Projective.of_equiv' (DirectSum.linearEquivFunOnFintype A (Fin n) (fun _ => B))
    exact Module.Projective.of_split (g.restrictScalars A) (f.restrictScalars A)
      (LinearMap.ext fun b => LinearMap.congr_fun hfg b)
  let S := Algebra.algebraMapSubmonoid B A⁰
  letI : Algebra.FormallyEtale B E := .of_isLocalization S
  letI : IsLocalizedModule S u := (isLocalizedModule_iff_isBaseChange S E u).mpr
    (algebraFormPullback_isBaseChange k B E p)
  letI : IsLocalizedModule A⁰ (u.restrictScalars A) := IsLocalizedModule.restrictScalars A⁰ u
  exact exists_localized_projective_dual_family (A := A) (F := F) (u.restrictScalars A)

end GlobalTheory.PD
