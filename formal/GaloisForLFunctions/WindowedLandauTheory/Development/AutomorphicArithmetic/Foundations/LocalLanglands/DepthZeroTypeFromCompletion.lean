import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicCongruenceTransport
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothCuspidalTransport
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CuspidalDepthZeroType

/-! Transporting a cuspidal representation along a p-adic
identification preserves the first principal-congruence fixed
space. A nonzero fixed space gives an inflated residue type. -/

noncomputable section

open NumberField IsDedekindDomain Matrix Representation GlobalTheory.GLq

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [Fact p.Prime]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem principalFixed_comp_eq_completionFixed
    (v : HeightOneSpectrum (𝓞 F)) (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i)
    (ρ : Representation ℂ (GL (Fin n) (v.adicCompletion F)) V) :
    principalFixed (ρ.comp (GeneralLinearGroup.map i.toRingHom)) =
      invariants (ρ.comp (completionPrincipalCongruenceOne v (Fin n)).subtype) := by
  let f := GeneralLinearGroup.map (n := Fin n) i.toRingHom
  have hK := principalCongruenceOne_map_along_padicIso (n := Fin n) v i hi
  ext x
  rw [mem_principalFixed_iff]
  constructor
  · intro hx y
    have hy : y.val ∈ (principalCongruenceOne p (Fin n)).map f := hK.symm ▸ y.2
    obtain ⟨z, hz, hz'⟩ := hy
    change ρ y.val x = x
    rw [← hz']
    exact hx z hz
  · intro hx z hz
    exact hx ⟨f z, hK ▸ ⟨z, hz, rfl⟩⟩

theorem exists_cuspidal_type_of_completion
    (v : HeightOneSpectrum (𝓞 F)) (i : ℚ_[p] ≃+* v.adicCompletion F) (hi : Continuous i)
    (hn : 0 < n) (ρ : Representation ℂ (GL (Fin n) (v.adicCompletion F)) V)
    (hρ : IsSmoothCuspidal ρ)
    (hfix : invariants (ρ.comp (completionPrincipalCongruenceOne v (Fin n)).subtype) ≠ ⊥) :
    ∃ (τ : FDRep ℂ (Gn p n)) (j : τ →ₗ[ℂ] V), IsCusp τ.character ∧ Function.Injective j ∧
      ∀ (k : GL (Fin n) ℤ_[p]) (x : τ),
        j (τ.ρ (integralReduction p (Fin n) k) x) =
          ρ (GeneralLinearGroup.map i.toRingHom (integralInclusion p (Fin n) k)) (j x) := by
  let f := GeneralLinearGroup.map (n := Fin n) i.toRingHom
  let π := ρ.comp f
  have hSub := principalFixed_comp_eq_completionFixed v i hi ρ
  have hπ := isSmoothCuspidal_comp_fieldEquiv i hi ρ hρ
  exact exists_cuspidal_type_of_principalFixed hn π hπ (hSub.symm ▸ hfix)

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.exists_cuspidal_type_of_completion
