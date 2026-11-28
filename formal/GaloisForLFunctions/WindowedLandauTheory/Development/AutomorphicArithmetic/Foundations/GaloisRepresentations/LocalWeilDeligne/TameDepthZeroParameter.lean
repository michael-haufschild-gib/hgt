import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.TameParameterTypeCompatibility
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.TameParameterUniquenessAtStage
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WildParameterClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompletionDepthZeroClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompletionCentralCharacterClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroCompletionCharacterClass

/-! On a p-adic chart, the elliptic names and central character of
a depth-zero cuspidal class determine a tame Weil–Deligne class.
The association is injective. -/

noncomputable section

open Matrix Polynomial NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.Reciprocity GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.Published
open GlobalTheory.EllipticCharacters GlobalTheory.PRep

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}

local notation "Fv" => HeightOneSpectrum.adicCompletion E v

/-- The compatibility of a Weil class with every inflated cuspidal type. -/
def WD.HasInflatedTypes (a : WD h) (x : IrrGL Fv) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (i : ℚ_[p] ≃+* Fv), Continuous i →
    ∀ (D : LocalTameStage h p x.1) (r : Ine (F := E) A →* D.residueˣ), D.IsInertiaResidue r →
    ∀ (τ : FDRep ℂ (Gn p x.1)), IsCusp τ.character →
    ∀ (θ : D.residueˣ →* ℂˣ), IsRegularChar p x.1 θ → HasEllipticName θ τ.character →
    ∀ (σ : IrrRep (GL (Fin x.1) Fv)), σ.cl = x.2 →
      HasInflatedType (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ →
      a.mono0 ∧ ∀ t : Ine (F := E) A, a.charpoly (ineIncl h t) =
        ∏ j ∈ Finset.range x.1, (X - C ((θ (r t ^ p ^ j) : ℂˣ) : ℂ))

/-- Tame correspondence with the determinant and all inflated types specified. -/
structure IsTameCuspidalParameter (α : Weil h →* Fvˣ) (x : IrrGL Fv) (a : WD h) : Prop where
  irreducible : a.Irreducible
  rank : a.lpDim = x.1
  tame : a.Tame
  determinant : a.detChar = (x.centralCharacter v).comp α
  types : a.HasInflatedTypes x

private theorem centralCharacter_rep (x : IrrGL Fv) (z : Fvˣ) (w : x.2.rep.V) :
    x.2.rep.ρ (GeneralLinearGroup.scalar (Fin x.1) z) w = (x.centralCharacter v z : ℂ) • w := by
  have hx : (⟨x.1, x.2.rep.cl⟩ : IrrGL Fv) = x := congrArg (Sigma.mk x.1) x.2.cl_rep
  simpa only [hx] using IrrGL.centralCharacter_act v x.2.rep z w

variable {α : Weil h →* (v.adicCompletion E)ˣ} {p : ℕ} [Fact p.Prime]
  (i : ℚ_[p] ≃+* v.adicCompletion E) (hi : Continuous i)

include hi

theorem exists_tame_cuspidal_parameter (hα : IsLocalArtin E Ω α)
    (x : IrrGL Fv) (hx : x.IsCusp) (hd : x.DepthZero v) :
    ∃ a : WD h, IsTameCuspidalParameter α x a := by
  let σ := x.2.rep
  obtain ⟨τ, hτ, ht⟩ := exists_inflated_cuspidal_type v i hi hx.1 σ hx.2 hd
  obtain ⟨a, ha, hN, hT, hδ, hP⟩ :=
    exists_tame_wdRep_compatible_with_inflated_types hα hx.1 i hi σ (x.centralCharacter v)
      (centralCharacter_rep x) τ hτ ht
  refine ⟨WD.mk a, (WD.irreducible_mk_iff a).mpr ha, ?_, (WD.tame_mk_iff a).mpr hT, ?_, ?_⟩
  · rw [WD.lpDim_mk, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · apply MonoidHom.ext
    intro s
    apply Units.ext
    rw [WD.detChar_mk]
    exact hδ s
  · intro q _ j hj D r hr τ' hτ' θ hθ hname σ' hσ' htype
    refine ⟨(WD.mono0_mk a).mpr hN, fun t => ?_⟩
    rw [WD.charpoly_mk]
    exact hP q j hj D r hr τ' hτ' θ hθ hname σ' (hσ'.trans x.2.cl_rep.symm) htype t

theorem tame_cuspidal_parameter_unique (x : IrrGL Fv) (hx : x.IsCusp) (hd : x.DepthZero v)
    {a b : WD h} (ha : IsTameCuspidalParameter α x a) (hb : IsTameCuspidalParameter α x b) : a = b := by
  obtain ⟨D⟩ := exists_localTameStage h (n := x.1) i hi hx.1
  obtain ⟨τ, hτ, ht⟩ := exists_inflated_cuspidal_type v i hi hx.1 x.2.rep hx.2 hd
  obtain ⟨θ, hθ, hname⟩ := exists_ellipticName_of_isCusp hx.1 D.residue_rank τ.character hτ
  have haP := (ha.types p i hi D D.inertiaResidue D.inertiaResidue_spec τ hτ θ hθ hname
    x.2.rep x.2.cl_rep ht).2
  have hbP := (hb.types p i hi D D.inertiaResidue D.inertiaResidue_spec τ hτ θ hθ hname
    x.2.rep x.2.cl_rep ht).2
  obtain ⟨m, a, rfl⟩ := a.exists_rep
  obtain ⟨n, b, rfl⟩ := b.exists_rep
  apply WD.sound
  have hp := (padicIso_place_normalization v i hi).2.2.1
  exact WDRep.iso_of_inertiaPolynomial_at_tameStage D hx.1 hp θ hθ a b
    ((WD.irreducible_mk_iff a).mp ha.irreducible) ((WD.irreducible_mk_iff b).mp hb.irreducible)
    (fun t => (WD.charpoly_mk a _).symm.trans (haP t))
    (fun t => (WD.charpoly_mk b _).symm.trans (hbP t))
    (by
      have he := congrArg (fun χ : Weil h →* ℂˣ => (χ (frob h) : ℂ))
        (ha.determinant.trans hb.determinant.symm)
      change ((WD.mk a).detChar (frob h) : ℂ) = ((WD.mk b).detChar (frob h) : ℂ) at he
      rw [WD.detChar_mk, WD.detChar_mk] at he
      exact he)

theorem eq_of_common_tame_cuspidal_parameter (hα : IsLocalArtin E Ω α) (x y : IrrGL Fv)
    (hx : x.IsCusp) (hy : y.IsCusp) (hdx : x.DepthZero v) (hdy : y.DepthZero v)
    {a : WD h} (ha : IsTameCuspidalParameter α x a) (hb : IsTameCuspidalParameter α y a) : x = y := by
  obtain ⟨n, x⟩ := x
  obtain ⟨m, y⟩ := y
  have he : n = m := ha.rank.symm.trans hb.rank
  subst m
  obtain ⟨D⟩ := exists_localTameStage h (n := n) i hi hx.1
  obtain ⟨τ, hτ, ht⟩ := exists_inflated_cuspidal_type v i hi hx.1 x.rep hx.2 hdx
  obtain ⟨τ', hτ', ht'⟩ := exists_inflated_cuspidal_type v i hi hy.1 y.rep hy.2 hdy
  obtain ⟨θ, hθ, hname⟩ := exists_ellipticName_of_isCusp hx.1 D.residue_rank τ.character hτ
  obtain ⟨θ', hθ', hname'⟩ := exists_ellipticName_of_isCusp hx.1 D.residue_rank τ'.character hτ'
  have haP := (ha.types p i hi D D.inertiaResidue D.inertiaResidue_spec τ hτ θ hθ hname
    x.rep x.cl_rep ht).2
  have hbP := (hb.types p i hi D D.inertiaResidue D.inertiaResidue_spec τ' hτ' θ' hθ' hname'
    y.rep y.cl_rep ht').2
  obtain ⟨j, -, hj⟩ := exists_name_frobeniusPower_of_same_inertiaPolynomial D hx.1 θ θ'
    (fun t => (haP t).symm.trans (hbP t))
  have hn' : HasEllipticName θ' τ.character := hj.symm ▸ hname.frobeniusPower hx.1 D.residue_rank j
  have hchar := eq_cuspidal_of_same_ellipticName hx.1 D.residue_rank hθ' hτ' hτ hname' hn'
  have hω : IrrGL.centralCharacter v (⟨n, x⟩ : IrrGL Fv) = IrrGL.centralCharacter v (⟨n, y⟩ : IrrGL Fv) := by
    apply MonoidHom.ext
    intro z
    obtain ⟨s, rfl⟩ := hα.surj z
    exact DFunLike.congr_fun (ha.determinant.symm.trans hb.determinant) s
  have hc := cl_eq_of_inflated_cuspidal_character v i hi x.rep y.rep τ τ' hτ hchar ht ht'
    (IrrGL.centralCharacter v (⟨n, x⟩ : IrrGL Fv)) (centralCharacter_rep ⟨n, x⟩)
    (hω.symm ▸ centralCharacter_rep ⟨n, y⟩)
  exact congrArg (Sigma.mk n) (x.cl_rep.symm.trans (hc.trans y.cl_rep))

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_tame_cuspidal_parameter
#print axioms GlobalTheory.WeilDeligne.tame_cuspidal_parameter_unique
#print axioms GlobalTheory.WeilDeligne.eq_of_common_tame_cuspidal_parameter
