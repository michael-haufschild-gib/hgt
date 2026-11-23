import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFormTrace
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Basic

/-! Regular forms on a smooth affine domain embed into forms on its function field. -/

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.SchemeCohomology

private theorem exteriorPower_isSMulRegular {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [Module.Projective A M]
    (n : ℕ) (c : A⁰) : IsSMulRegular (⋀[A]^n M) (c : A) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A M)
  let ψ := exteriorPower.map n s
  have hψ : Function.Injective ψ := exteriorPower.map_injective (n := n) _ hs
  intro x y hxy
  apply hψ
  have h := congrArg ψ hxy
  simp only [map_smul] at h
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors c.2 h

/-- Extension to the fraction field is injective on forms of a smooth domain. -/
theorem exteriorDifferentials_map_fraction_injective {k A E : Type*} [CommRing k]
    [CommRing A] [IsDomain A] [Field E] [Algebra k A] [Algebra k E] [Algebra A E]
    [IsScalarTower k A E] [IsFractionRing A E] [Algebra.Smooth k A]
    (φ : A →ₐ[k] E) (hφ : φ.toRingHom = algebraMap A E) (n : ℕ) :
    Function.Injective (ExteriorDifferentials.map φ n) := by
  letI : Algebra.FormallyEtale A E := .of_isLocalization A⁰
  let L := algebraFormPullback k A E n
  letI : IsLocalizedModule A⁰ L := (isLocalizedModule_iff_isBaseChange A⁰ E L).mpr
    (algebraFormPullback_isBaseChange k A E n)
  have hL := (IsLocalizedModule.injective_iff_isRegular A⁰ L).mpr
    (fun c => exteriorPower_isSMulRegular n c)
  intro x y h
  apply hL
  simpa only [L, algebraFormPullback_eq_map k A E φ hφ] using h

end GlobalTheory.SchemeCohomology
