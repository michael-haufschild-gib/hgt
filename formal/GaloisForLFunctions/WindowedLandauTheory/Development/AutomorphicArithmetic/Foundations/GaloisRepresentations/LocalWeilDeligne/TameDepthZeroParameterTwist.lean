import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.TameDepthZeroParameter
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.TameParameterResidueTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilScalarTwistIrreducible
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.InflatedCuspidalTypeTwist

/-! Determinant twisting of a depth-zero cusp twists the residue
name by the residue norm. Geometric inverse Artin supplies the
same character on the Weil parameter. -/

noncomputable section

open Matrix NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.Reciprocity GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.Published
open GlobalTheory.EllipticCharacters GlobalTheory.PRep

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}
  {p : ℕ} [Fact p.Prime]

local notation "Fv" => HeightOneSpectrum.adicCompletion E v

theorem tame_cuspidal_parameter_detTwist {α : Weil h →* Fvˣ} (hα : IsLocalArtin E Ω α)
    (i : ℚ_[p] ≃+* Fv) (hi : Continuous i) (x : IrrGL Fv) (hx : x.IsCusp) (hd : x.DepthZero v)
    (χ : Fvˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Fvˣ))
    (hχ₁ : ∀ z : Fvˣ, z ∈ unitsLevel v 1 → χ z = 1)
    {a b : WD h} (ha : IsTameCuspidalParameter α x a)
    (hb : IsTameCuspidalParameter α (x.detTwist χ hχ) b) :
    b = a.lpTwist (χ.comp α) (IsLocalArtin.smooth E Ω hα hχ) := by
  let σ := x.2.rep
  let σ' := σ.twist (χ.comp GeneralLinearGroup.det) (hχ.preimage GeneralLinearGroup.continuous_det)
  have hcl : σ'.cl = (x.detTwist χ hχ).2 := by
    simp only [σ', σ, IrrRep.cl_twist, IrrCl.cl_rep, IrrGL.detTwist]
  obtain ⟨D⟩ := exists_localTameStage h (n := x.1) i hi hx.1
  obtain ⟨τ, hτ, ht⟩ := exists_inflated_cuspidal_type v i hi hx.1 σ hx.2 hd
  obtain ⟨θ, hθ, hname⟩ := exists_ellipticName_of_isCusp hx.1 D.residue_rank τ.character hτ
  let χp := χ.comp (Units.map i.toRingHom.toMonoidHom)
  have hp₁ := (kills_firstUnits_iff_padic v i hi χ).mp hχ₁
  obtain ⟨δ, hδ, -⟩ := existsUnique_padicResidueCharacter χp hp₁
  let τ' := finiteDeterminantTwist τ δ
  let θ' := θ * δ.comp (residueUnitNorm D.residue)
  have hτ' : IsCusp τ'.character := isCusp_finiteDeterminantTwist τ hτ δ
  have hθ' : IsRegularChar p x.1 θ' := regular_mul_residueNorm hθ δ
  have hname' : HasEllipticName θ' τ'.character := by
    have he : τ'.character = fun y => τ.character y * (δ y.det : ℂ) :=
      funext (finiteDeterminantTwist_character τ δ)
    rw [he]
    exact hname.twistDet hx.1 D.residue_rank δ
  let f := GeneralLinearGroup.map (n := Fin x.1) i.toRingHom
  have hs : σ'.ρ.comp f = Representation.scalarTwist (σ.ρ.comp f) (χp.comp GeneralLinearGroup.det) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro w
    change (χ (GeneralLinearGroup.det (f g)) : ℂ) • σ.ρ (f g) w =
      (χp (GeneralLinearGroup.det g) : ℂ) • σ.ρ (f g) w
    rw [GeneralLinearGroup.map_det]
    rfl
  have ht' : HasInflatedType (σ'.ρ.comp f) τ' := by
    rw [hs]
    exact inflatedType_determinantTwist (σ.ρ.comp f) τ ht χp δ hδ
  have haP := (ha.types p i hi D D.inertiaResidue D.inertiaResidue_spec τ hτ θ hθ hname
    σ x.2.cl_rep ht).2
  have hbP := (hb.types p i hi D D.inertiaResidue D.inertiaResidue_spec τ' hτ' θ' hθ' hname'
    σ' hcl ht').2
  obtain ⟨d, a, rfl⟩ := a.exists_rep
  obtain ⟨m, b, rfl⟩ := b.exists_rep
  have hr : d = x.1 := by
    simpa only [WD.lpDim_mk, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using ha.rank
  subst d
  rw [WD.lpTwist_mk]
  apply WD.sound
  let s := frob h
  have he := congrArg (fun ψ : Weil h →* ℂˣ => (ψ s : ℂ)) hb.determinant
  have hca := congrArg (fun ψ : Weil h →* ℂˣ => (ψ s : ℂ)) ha.determinant
  rw [IrrGL.centralCharacter_detTwist v x χ hχ] at he
  have hdet : LinearMap.det (b.ρ s) = LinearMap.det ((a.twist (χ.comp α) (IsLocalArtin.smooth E Ω hα hχ)).ρ s) := by
    change LinearMap.det (b.ρ s) = LinearMap.det ((χ (α s) : ℂ) • a.ρ s)
    have hf : Module.finrank ℂ (Fin x.1 → ℂ) = x.1 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [LinearMap.det_smul, hf]
    rw [WD.detChar_mk] at he hca
    change LinearMap.det (b.ρ s) = (x.centralCharacter v (α s) : ℂ) * (χ (α s) : ℂ) ^ x.1 at he
    change LinearMap.det (a.ρ s) = (x.centralCharacter v (α s) : ℂ) at hca
    rw [he, hca, mul_comm]
  letI := (WD.irreducible_mk_iff a).mp ha.irreducible
  exact WDRep.iso_of_inertiaPolynomial_at_tameStage D hx.1
    (padicIso_place_normalization v i hi).2.2.1 θ' hθ' b (a.twist (χ.comp α) (IsLocalArtin.smooth E Ω hα hχ))
    ((WD.irreducible_mk_iff b).mp hb.irreducible) (a.irreducible_twist _ _)
    (fun t => (WD.charpoly_mk b _).symm.trans (hbP t))
    (WDRep.charpoly_tameTwist_at_stage hα D hx.1 i hi χ hχ δ hδ θ a
      (fun t => (WD.charpoly_mk a _).symm.trans (haP t))) hdet

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.tame_cuspidal_parameter_detTwist
