import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.TameWeilParameterOfLocalType
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroTypeExistenceByClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticNameOrbitTransport
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PadicCompletionIsoUniqueness

/-! The tame parameter reads every inflated cuspidal type of the
given local class. Continuous p-adic charts agree, and the orbit
polynomial is independent of the residue stage and regular name. -/

noncomputable section

open Matrix Polynomial NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Reciprocity
open GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.Published GlobalTheory.PRep GlobalTheory.EllipticCharacters

namespace GlobalTheory.WeilDeligne

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}
  {n : ℕ}

local notation "Fv" => HeightOneSpectrum.adicCompletion K v

/-- The inertia polynomial attached to any inflated cuspidal type of a local class. -/
def HasInflatedInertiaPolynomials (c : IrrCl (GL (Fin n) Fv)) (a : WDRep h (Fin n → ℂ)) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (i : ℚ_[p] ≃+* Fv), Continuous i →
    ∀ (D : LocalTameStage h p n) (r : Ine (F := K) A →* D.residueˣ), D.IsInertiaResidue r →
    ∀ (τ : FDRep ℂ (Gn p n)), IsCusp τ.character →
    ∀ (θ : D.residueˣ →* ℂˣ), IsRegularChar p n θ → HasEllipticName θ τ.character →
    ∀ (σ : IrrRep (GL (Fin n) Fv)), σ.cl = c →
      HasInflatedType (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ →
      ∀ t : Ine (F := K) A, (a.ρ (ineIncl h t)).charpoly =
        ∏ j ∈ Finset.range n, (X - C ((θ (r t ^ p ^ j) : ℂˣ) : ℂ))

theorem exists_tame_wdRep_compatible_with_inflated_types {p : ℕ} [Fact p.Prime]
    {α : Weil h →* Fvˣ} (hα : IsLocalArtin K Ω α) (hn : 0 < n)
    (i : ℚ_[p] ≃+* Fv) (hi : Continuous i)
    (σ : IrrRep (GL (Fin n) Fv)) (ω : Fvˣ →* ℂˣ)
    (hω : ∀ z x, σ.ρ (GeneralLinearGroup.scalar (Fin n) z) x = (ω z : ℂ) • x)
    (τ : FDRep ℂ (Gn p n)) (hτ : IsCusp τ.character)
    (ht : HasInflatedType (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ) :
    ∃ a : WDRep h (Fin n → ℂ), a.ρ.IsIrreducible ∧ a.N = 0 ∧ a.Tame ∧
      (∀ s, LinearMap.det (a.ρ s) = (ω (α s) : ℂ)) ∧
      HasInflatedInertiaPolynomials σ.cl a := by
  obtain ⟨D⟩ := exists_localTameStage h (n := n) i hi hn
  obtain ⟨θ, a, hθ, hname, ha, hN, hT, hδ, hP⟩ :=
    exists_tame_wdRep_of_local_type hα D hn i hi σ.ρ ω hω τ hτ ht
  refine ⟨a, ha, hN, hT, hδ, ?_⟩
  intro q _ j hj D' r hr τ' hτ' θ' hθ' hname' σ' hσ' ht' t
  have hpq := padicPrime_eq_of_continuous_completionEquiv v i j hi hj
  subst q
  have hij := padicCompletionEquiv_eq_of_continuous v i j hi hj
  subst j
  have hch := inflated_cuspidal_type_character_unique v i hi σ σ' hσ'.symm τ τ' hτ hτ' ht ht'
  have hname'' : HasEllipticName θ' τ.character := by
    rw [hch]
    exact hname'
  obtain ⟨e, he⟩ := exists_residueEquiv_intertwining_inertiaResidue D D'
  rw [D'.inertiaResidue_unique r hr, he, hP]
  exact (orbitPolynomial_eq_of_equiv_of_ellipticNames hn D.residue_rank
    e θ θ' hθ hθ' τ.character hname hname'' (D.inertiaResidue t)).symm

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_tame_wdRep_compatible_with_inflated_types
