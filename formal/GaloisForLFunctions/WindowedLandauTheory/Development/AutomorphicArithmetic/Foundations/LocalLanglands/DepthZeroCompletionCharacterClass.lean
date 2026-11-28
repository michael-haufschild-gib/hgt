import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroTypeDeterminesCharacterClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.InflatedCuspidalTypeMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.IrreducibleReparameterization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicCongruenceTransport
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothIrreducibleClass

/-! Two smooth irreducible representations over a p-adic completion
with the same central character and inflated finite cuspidal
character have the same isomorphism class. -/

noncomputable section

open NumberField IsDedekindDomain Matrix Representation
open GlobalTheory.GLq GlobalTheory.PRep

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [Fact p.Prime]

private theorem nonempty_equiv_of_comp_surjective {G H V W : Type*} [Group G] [Monoid H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (f : H →* G)
    (hf : Function.Surjective f) (e : Representation.Equiv (ρ.comp f) (ρ'.comp f)) :
    Nonempty (ρ.Equiv ρ') := by
  refine ⟨{ toLinearEquiv := e.toLinearEquiv, isIntertwining' := ?_ }⟩
  intro g
  obtain ⟨u, rfl⟩ := hf g
  exact LinearMap.ext (Representation.IntertwiningMap.isIntertwining (ρ.comp f) (ρ'.comp f) e.toIntertwiningMap u)

theorem cl_eq_of_inflated_cuspidal_character (v : HeightOneSpectrum (𝓞 F))
    (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i)
    (σ σ' : IrrRep (GL (Fin n) (v.adicCompletion F)))
    (τ τ' : FDRep ℂ (Gn p n)) (hτ : IsCusp τ.character) (he : τ'.character = τ.character)
    (hσ : HasInflatedType (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ)
    (hσ' : HasInflatedType (σ'.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ')
    (ω : (v.adicCompletion F)ˣ →* ℂˣ)
    (hω : ∀ z x, σ.ρ (GeneralLinearGroup.scalar (Fin n) z) x = (ω z : ℂ) • x)
    (hω' : ∀ z x, σ'.ρ (GeneralLinearGroup.scalar (Fin n) z) x = (ω z : ℂ) • x) :
    σ.cl = σ'.cl := by
  let f := GeneralLinearGroup.map (n := Fin n) i.toRingHom
  let ρ : Representation ℂ (GL (Fin n) ℚ_[p]) σ.V := σ.ρ.comp f
  let ρ' : Representation ℂ (GL (Fin n) ℚ_[p]) σ'.V := σ'.ρ.comp f
  letI := σ.irr
  letI := σ'.irr
  have hsurj : Function.Surjective f := generalLinearGroup_map_ringEquiv_surjective i
  letI : ρ.IsIrreducible := irreducible_comp_of_surjective σ.ρ f hsurj
  letI : ρ'.IsIrreducible := irreducible_comp_of_surjective σ'.ρ f hsurj
  have hf : Continuous f := Units.continuous_map (continuous_id.matrix_map hi)
  let ψ := ω.comp (Units.map i.toRingHom.toMonoidHom)
  have hc (z : ℚ_[p]ˣ) (x : σ.V) : ρ (GeneralLinearGroup.scalar (Fin n) z) x = (ψ z : ℂ) • x := by
    change σ.ρ (f (GeneralLinearGroup.scalar (Fin n) z)) x = _
    rw [GeneralLinearGroup.map_scalar, hω]
    rfl
  have hc' (z : ℚ_[p]ˣ) (x : σ'.V) : ρ' (GeneralLinearGroup.scalar (Fin n) z) x = (ψ z : ℂ) • x := by
    change σ'.ρ (f (GeneralLinearGroup.scalar (Fin n) z)) x = _
    rw [GeneralLinearGroup.map_scalar, hω']
    rfl
  obtain ⟨j, hj₀, hj⟩ := hσ
  obtain ⟨j', hj'₀, hj'⟩ := hσ'
  have hτ' : IsCusp τ'.character := he ▸ hτ
  obtain ⟨e⟩ := nonempty_equiv_of_cuspidal_type_character ρ ρ'
    (fun x => (σ.smooth x).preimage hf) (fun x => (σ'.smooth x).preimage hf) ψ hc hc' τ τ' hτ he
    j j' hj₀ (injective_of_cuspidal_type_map ρ τ hτ j hj₀ hj)
    (injective_of_cuspidal_type_map ρ' τ' hτ' j' hj'₀ hj') hj hj'
  exact IrrRep.cl_eq_iff.mpr (nonempty_equiv_of_comp_surjective σ.ρ σ'.ρ f hsurj e)

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.cl_eq_of_inflated_cuspidal_character
