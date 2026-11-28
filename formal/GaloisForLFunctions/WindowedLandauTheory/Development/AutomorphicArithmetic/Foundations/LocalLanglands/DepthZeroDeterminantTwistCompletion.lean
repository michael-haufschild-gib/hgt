import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroTypeFromCompletion
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroDeterminantTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.IrreducibleReparameterization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicUnitCharacterReduction

/-! The determinant twist criterion transports to a finite
completion identified continuously with the p-adic field. -/

noncomputable section

open Matrix NumberField IsDedekindDomain Representation

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [Fact p.Prime]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem determinantTwist_completionFixed_ne_bot_iff
    (v : HeightOneSpectrum (𝓞 F)) (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i) (hn : 0 < n)
    (ρ : Representation ℂ (GL (Fin n) (v.adicCompletion F)) V) [ρ.IsIrreducible]
    (hρ : ∀ x : V, IsOpen {g | ρ g x = x})
    (hd : invariants (ρ.comp (completionPrincipalCongruenceOne v (Fin n)).subtype) ≠ ⊥)
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set (v.adicCompletion F)ˣ)) :
    invariants ((ρ.scalarTwist (χ.comp GeneralLinearGroup.det)).comp
      (completionPrincipalCongruenceOne v (Fin n)).subtype) ≠ ⊥ ↔
    ∀ u : ℤ_[p]ˣ, padicUnitReduction u = 1 →
      (χ.comp (Units.map i.toRingHom.toMonoidHom))
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) = 1 := by
  let f := GeneralLinearGroup.map (n := Fin n) i.toRingHom
  let π : Representation ℂ (GL (Fin n) ℚ_[p]) V := ρ.comp f
  letI : π.IsIrreducible := irreducible_comp_of_surjective ρ f (generalLinearGroup_map_ringEquiv_surjective i)
  have hf : Continuous f := Units.continuous_map (continuous_id.matrix_map hi)
  let ψ := χ.comp (Units.map i.toRingHom.toMonoidHom)
  have hcψ : IsOpen (ψ.ker : Set ℚ_[p]ˣ) := hχ.preimage (Units.continuous_map hi)
  have htw : (ρ.scalarTwist (χ.comp GeneralLinearGroup.det)).comp f =
      π.scalarTwist (ψ.comp GeneralLinearGroup.det) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro x
    change (χ (GeneralLinearGroup.det (f g)) : ℂ) • ρ (f g) x =
      (ψ (GeneralLinearGroup.det g) : ℂ) • ρ (f g) x
    rw [GeneralLinearGroup.map_det]
    rfl
  rw [← principalFixed_comp_eq_completionFixed v i hi, htw]
  exact determinantTwist_principalFixed_ne_bot_iff hn π (fun x => (hρ x).preimage hf)
    ((principalFixed_comp_eq_completionFixed v i hi ρ).symm ▸ hd) ψ hcψ

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.determinantTwist_completionFixed_ne_bot_iff
