import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroTypeFromCompletion
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroTypeCharacterUniqueness
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.InflatedCuspidalTypeMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.IrreducibleReparameterization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalGLCentralCharacter
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothIrreducibleClass

/-! The finite cuspidal type in the first principal-congruence fixed
space exists at depth zero and its character depends only on the
smooth irreducible class. -/

noncomputable section

open NumberField IsDedekindDomain Matrix Representation GlobalTheory.GLq GlobalTheory.PRep

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [Fact p.Prime]
  (v : HeightOneSpectrum (𝓞 F)) (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i)

local notation "L" => HeightOneSpectrum.adicCompletion F v

include hi in
theorem exists_inflated_cuspidal_type (hn : 0 < n) (σ : IrrRep (GL (Fin n) L))
    (hσ : IsSmoothCuspidal σ.ρ)
    (hd : invariants (σ.ρ.comp (completionPrincipalCongruenceOne v (Fin n)).subtype) ≠ ⊥) :
    ∃ τ : FDRep ℂ (Gn p n), IsCusp τ.character ∧
      HasInflatedType (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ := by
  obtain ⟨τ, j, hτ, hinj, hj⟩ := exists_cuspidal_type_of_completion v i hi hn σ.ρ hσ hd
  refine ⟨τ, hτ, j, ?_, hj⟩
  haveI := isIrreducible_of_isCusp_character τ hτ
  letI : Nontrivial τ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Gn p n)) (Representation.asModule τ.ρ)
  obtain ⟨w, hw⟩ := exists_ne (0 : τ)
  intro he
  apply hw (hinj ?_)
  rw [he]
  rfl

include hi in
theorem inflated_cuspidal_type_character_unique (σ σ' : IrrRep (GL (Fin n) L))
    (he : σ.cl = σ'.cl) (τ τ' : FDRep ℂ (Gn p n))
    (hτ : IsCusp τ.character) (hτ' : IsCusp τ'.character)
    (ha : HasInflatedType (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ)
    (ha' : HasInflatedType (σ'.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ') :
    τ.character = τ'.character := by
  let f := GeneralLinearGroup.map (n := Fin n) i.toRingHom
  let π : Representation ℂ (GL (Fin n) ℚ_[p]) σ.V := σ.ρ.comp f
  letI : σ.ρ.IsIrreducible := σ.irr
  letI : Representation.IsIrreducible π := irreducible_comp_of_surjective σ.ρ f (generalLinearGroup_map_ringEquiv_surjective i)
  have hf : Continuous f := Units.continuous_map (continuous_id.matrix_map hi)
  have hπ (w : σ.V) : IsOpen {g : GL (Fin n) ℚ_[p] | π g w = w} :=
    (σ.smooth w).preimage hf
  obtain ⟨ω, -, hω, -⟩ := exists_unique_smoothGLCentralCharacter v σ.ρ σ.smooth
  let ω' := ω.comp (Units.map i.toRingHom.toMonoidHom)
  have hc (z : ℚ_[p]ˣ) (w : σ.V) :
      π (GeneralLinearGroup.scalar (Fin n) z) w = (ω' z : ℂ) • w := by
    change σ.ρ (f (GeneralLinearGroup.scalar (Fin n) z)) w = _
    rw [GeneralLinearGroup.map_scalar, hω]
    rfl
  obtain ⟨e⟩ := IrrRep.cl_eq_iff.mp he.symm
  obtain ⟨j, hj₀, hj⟩ := ha
  obtain ⟨j', hj'₀, hj'⟩ := ha'
  let g := e.toLinearEquiv.toLinearMap.comp j'
  have hg₀ : g ≠ 0 := fun h => hj'₀ (LinearMap.ext fun x => e.toLinearEquiv.injective (by
    have he := LinearMap.congr_fun h x
    change e.toLinearEquiv (j' x) = 0 at he
    simpa only [map_zero, LinearMap.zero_apply] using he))
  have hg (k : GL (Fin n) ℤ_[p]) (w : τ') :
      g (τ'.ρ (integralReduction p (Fin n) k) w) = π (integralInclusion p (Fin n) k) (g w) := by
    change e.toLinearEquiv (j' (τ'.ρ (integralReduction p (Fin n) k) w)) =
      σ.ρ (f (integralInclusion p (Fin n) k)) (e.toLinearEquiv (j' w))
    rw [hj' k w]
    exact Representation.IntertwiningMap.isIntertwining σ'.ρ σ.ρ e.toIntertwiningMap
      (f (integralInclusion p (Fin n) k)) (j' w)
  have hinj := injective_of_cuspidal_type_map π τ hτ j hj₀ hj
  have hinj' := injective_of_cuspidal_type_map π τ' hτ' g hg₀ hg
  exact character_eq_of_common_cuspidal_inflation π hπ ω' hc τ.ρ τ'.ρ hτ hτ'
    j g hj₀ hg₀ hinj hinj' hj hg

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.exists_inflated_cuspidal_type
#print axioms GlobalTheory.GLp.inflated_cuspidal_type_character_unique
