import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicCongruenceTransport
import GaloisForLFunctions.WindowedLandauTheory.SatakeDualWeyl.AdelicIwasawaHecke.Spherical

/-! The integral group of a completion identified with the rational
p-adic field is the image of the integral p-adic matrices. -/

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.Reciprocity WindowedLandauTheory.UG
open WindowedLandauTheory.UG.P

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [Fact p.Prime]

theorem exists_integralGL_preimage_of_completion (v : HeightOneSpectrum (𝓞 F))
    (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i)
    (g : GL (Fin n) (v.adicCompletion F)) (hg : g ∈ GLint (Fin n) (Ov F v)) :
    ∃ k : GL (Fin n) ℤ_[p], GeneralLinearGroup.map i.toRingHom (integralInclusion p (Fin n) k) = g := by
  obtain ⟨w, rfl⟩ := (FinitePlace.equivHeightOneSpectrum (K := F)).surjective v
  let e := padicCompletionIntegersEquiv w i hi
  obtain ⟨u, rfl⟩ := hg
  refine ⟨GeneralLinearGroup.map e.symm.toRingHom u, Units.ext (Matrix.ext fun a b => ?_)⟩
  change i ((e.symm (u.val a b) : ℤ_[p]) : ℚ_[p]) = (u.val a b).val
  exact congrArg Subtype.val (e.apply_symm_apply (u.val a b))

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.exists_integralGL_preimage_of_completion
