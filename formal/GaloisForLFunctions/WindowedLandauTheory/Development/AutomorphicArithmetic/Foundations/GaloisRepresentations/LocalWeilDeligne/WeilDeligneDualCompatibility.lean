import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneDual
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneTameness
import Mathlib.LinearAlgebra.Matrix.Dual

/-! The inverse-transpose Weil action preserves tameness and zero
monodromy. It transports characteristic polynomials by Weil inversion
and commutes with twisting after inversion of the twisting character. -/

noncomputable section

open NumberField IsDedekindDomain Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}

theorem WD.charpoly_dual (x : WD h) (σ : Weil h) :
    x.lpDual.charpoly σ = x.charpoly σ⁻¹ := by
  refine WD.ind (fun n a => ?_) x
  rw [WD.lpDual_mk, WD.charpoly_mk, WD.charpoly_mk, WDRep.dual_ρ]
  let b := finBasis ℂ (Fin n → ℂ)
  rw [← LinearMap.charpoly_toMatrix (a.ρ σ⁻¹) b,
    ← LinearMap.charpoly_toMatrix ((a.ρ σ⁻¹).dualMap) b.dualBasis]
  change (LinearMap.toMatrix b.dualBasis b.dualBasis (Dual.transpose (R := ℂ) (a.ρ σ⁻¹))).charpoly = _
  rw [LinearMap.toMatrix_transpose, Matrix.charpoly_transpose]

theorem WD.Tame.dual {x : WD h} (hx : x.Tame) : x.lpDual.Tame := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  rw [WD.lpDual_mk, WD.tame_mk_iff]
  exact ((WD.tame_mk_iff _).mp hx).dual

theorem WD.mono0_dual {x : WD h} (hx : x.mono0) : x.lpDual.mono0 := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  rw [WD.lpDual_mk, WD.mono0_mk, WDRep.dual_N, (WD.mono0_mk _).mp hx]
  ext f w
  simp

theorem WD.lpDual_twist (x : WD h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (hi : IsSmooth χ⁻¹) :
    (x.lpTwist χ hχ).lpDual = x.lpDual.lpTwist χ⁻¹ hi := by
  refine WD.ind (fun n a => ?_) x
  rw [WD.lpTwist_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpTwist_mk]
  apply WD.sound
  refine ⟨LinearEquiv.refl ℂ _, fun σ f => LinearMap.ext fun w => ?_, fun _ => rfl⟩
  change f ((χ σ⁻¹ : ℂ) • a.ρ σ⁻¹ w) = ((χ⁻¹ σ : ℂˣ) : ℂ) • f (a.ρ σ⁻¹ w)
  rw [map_smul, map_inv]
  rfl

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WD.charpoly_dual
#print axioms GlobalTheory.WeilDeligne.WD.lpDual_twist
