import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalTameStageNorm
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.TameWeilParameterOfRegularName
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.InflatedCuspidalTypeMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticCentralCharacter

/-! The central character of an inflated finite cuspidal type gives
the determinant of its tame Weil parameter. For any tame stage, the
inertia polynomial is read from its finite elliptic name. -/

noncomputable section

open Matrix Polynomial NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Reciprocity
open GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.Published GlobalTheory.EllipticCharacters

namespace GlobalTheory.WeilDeligne

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}
  {p n : ℕ} [Fact p.Prime]
  {α : Weil h →* (v.adicCompletion K)ˣ} (hα : IsLocalArtin K Ω α)
  {V : Type} [AddCommGroup V] [Module ℂ V]

include hα in
theorem exists_tame_wdRep_of_local_type (D : LocalTameStage h p n) (hn : 0 < n)
    (i : ℚ_[p] ≃+* v.adicCompletion K) (hi : Continuous i)
    (ρ : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V)
    (ω : (v.adicCompletion K)ˣ →* ℂˣ)
    (hω : ∀ z x, ρ (GeneralLinearGroup.scalar (Fin n) z) x = (ω z : ℂ) • x)
    (τ : FDRep ℂ (Gn p n)) (hτ : IsCusp τ.character)
    (ht : HasInflatedType (ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ) :
    ∃ (θ : D.residueˣ →* ℂˣ) (a : WDRep h (Fin n → ℂ)),
      IsRegularChar p n θ ∧ HasEllipticName θ τ.character ∧
      a.ρ.IsIrreducible ∧ a.N = 0 ∧ a.Tame ∧
      (∀ s, LinearMap.det (a.ρ s) = (ω (α s) : ℂ)) ∧
      ∀ t : Ine (F := K) A, (a.ρ (ineIncl h t)).charpoly =
        ∏ j ∈ Finset.range n, (X - C ((θ (D.inertiaResidue t ^ p ^ j) : ℂˣ) : ℂ)) := by
  letI := D.finite_residue
  obtain ⟨θ, hθ, hname⟩ := exists_ellipticName_of_isCusp hn D.residue_rank τ.character hτ
  obtain ⟨j, hj₀, hj⟩ := ht
  obtain ⟨x, hx⟩ : ∃ x, j x ≠ 0 := by
    by_contra! e
    exact hj₀ (LinearMap.ext e)
  let r := D.inertiaResidue
  have hc (t : Ine (F := K) A) : θ (∏ k ∈ Finset.range n, r t ^ p ^ k) = ω (α (ineIncl h t)) := by
    obtain ⟨z, hz, hz'⟩ := D.base_artin_unit hα r D.inertiaResidue_spec i hi hn t
    let zK := Units.map (i.toRingHom.comp (algebraMap ℤ_[p] ℚ_[p])).toMonoidHom z
    have hαz : α (ineIncl h t) = zK := Units.ext hz
    have hnorm : (∏ k ∈ Finset.range n, r t ^ p ^ k) =
        Units.map (algebraMap (ZMod p) D.residue).toMonoidHom
          (Units.map PadicInt.toZMod.toMonoidHom z) := by
      apply Units.ext
      change (Units.coeHom D.residue) (∏ k ∈ Finset.range n, r t ^ p ^ k) =
        algebraMap (ZMod p) D.residue (PadicInt.toZMod z.val)
      rw [map_prod]
      exact hz'.symm
    have hscalar := hj (GeneralLinearGroup.scalar (Fin n) z) x
    unfold integralReduction integralInclusion at hscalar
    change j (τ.ρ (GeneralLinearGroup.map PadicInt.toZMod (GeneralLinearGroup.scalar (Fin n) z)) x) =
      ρ (GeneralLinearGroup.map i.toRingHom
        (GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) (GeneralLinearGroup.scalar (Fin n) z))) (j x) at hscalar
    rw [GeneralLinearGroup.map_scalar, GeneralLinearGroup.map_scalar, GeneralLinearGroup.map_scalar] at hscalar
    change j (τ.ρ (GeneralLinearGroup.scalar (Fin n) (Units.map PadicInt.toZMod.toMonoidHom z)) x) =
      ρ (GeneralLinearGroup.scalar (Fin n) zK) (j x) at hscalar
    rw [central_character_of_ellipticName hn D.residue_rank τ θ hτ hθ hname, map_smul, hω] at hscalar
    rw [hnorm, hαz]
    exact Units.ext (smul_left_injective ℂ hx hscalar)
  have hq : normV v = p := (padicIso_place_normalization v i hi).2.2.1
  obtain ⟨a, ha, hN, hT, hδ, hpoly⟩ :=
    exists_tame_wdRep_of_regular_residue_orbit hn D.residue_rank r D.inertiaResidue_surjective
      D.inertiaResidue_open_ker D.inertiaResidue_wild (frob h) deg_frob
      (fun t t' ht => by simpa only [hq] using D.inertiaResidue_conjugation (frob h) deg_frob t t' ht)
      θ hθ (ω.comp α) hc
  exact ⟨θ, a, hθ, hname, ha, hN, hT, hδ, hpoly⟩

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_tame_wdRep_of_local_type
