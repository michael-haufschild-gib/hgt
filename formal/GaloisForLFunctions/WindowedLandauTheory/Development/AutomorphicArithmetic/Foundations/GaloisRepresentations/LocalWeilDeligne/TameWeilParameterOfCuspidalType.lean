import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PadicUnitReduction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ResidueArtinNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ResidueArtinFrobenius
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticCentralCharacter
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicIntegralReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.TameWeilParameterOfRegularName
import Mathlib.FieldTheory.Finite.Trace

/-! A cuspidal residue type determines a regular inertia orbit on
an unramified stage. The residue norm and scalar action identify
its determinant on inertia with the central character under Artin. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField Polynomial Matrix
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.Reciprocity GlobalTheory.GLp GlobalTheory.GLq
open GlobalTheory.EllipticCharacters GlobalTheory.Published
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.WeilDeligne

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
  (h : IsPlaceOver A v) {p n : ℕ} [Fact p.Prime]

local notation "w" => finitePlaceAtAbsoluteValuation (L := L) A h
local notation "hw" => finitePlaceAtAbsoluteValuation_isPlaceOver (L := L) A h
local notation "κ" => 𝓞 K ⧸ HeightOneSpectrum.asIdeal v
local notation "κ'" => 𝓞 L ⧸ HeightOneSpectrum.asIdeal w
local notation "Fv" => HeightOneSpectrum.adicCompletion K v

theorem exists_tame_wdRep_of_cuspidal_type
    [Algebra (ZMod p) κ']
    (hn : 0 < n) (hd : Module.finrank (ZMod p) κ' = n)
    (i : ℚ_[p] ≃+* Fv) (hi : Continuous i)
    {α : Weil h →* Fvˣ} (hα : IsLocalArtin K Ω (h := h) α)
    {β : Weil hw →* ((w).adicCompletion L)ˣ} (hβ : IsLocalArtin L Ω (h := hw) β)
    (he : (w).asIdeal.ramificationIdx (𝓞 K) = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) Fv) V)
    (ω : Fvˣ →* ℂˣ)
    (hω : ∀ z v, ρ (GeneralLinearGroup.scalar (Fin n) z) v = (ω z : ℂ) • v)
    (τ : FDRep ℂ (Gn p n)) (hτ : IsCusp τ.character)
    (j : τ →ₗ[ℂ] V) (hj₀ : j ≠ 0)
    (hj : ∀ (k : GL (Fin n) ℤ_[p]) (x : τ),
      j (τ.ρ (integralReduction p (Fin n) k) x) =
        ρ (GeneralLinearGroup.map i.toRingHom (integralInclusion p (Fin n) k)) (j x)) :
    letI : (w).asIdeal.IsMaximal := (w).isMaximal
    letI : Field κ' := Ideal.Quotient.field (w).asIdeal
    ∃ (θ : κ'ˣ →* ℂˣ) (a : WDRep h (Fin n → ℂ)),
      IsRegularChar p n θ ∧ HasEllipticName (K := κ') θ τ.character ∧
      a.ρ.IsIrreducible ∧ a.N = 0 ∧ a.Tame ∧
      (∀ σ, LinearMap.det (a.ρ σ) = (ω (α σ) : ℂ)) ∧
      ∀ t : Ine (F := K) A, (a.ρ (ineIncl h t)).charpoly =
        ∏ j ∈ Finset.range n, (X - C ((θ (residueArtinOnBaseInertia K Ω L h hβ he t ^ p ^ j) : ℂˣ) : ℂ)) := by
  letI : (w).asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  letI := v.isMaximal
  letI := (w).isMaximal
  letI : Field κ := Ideal.Quotient.field v.asIdeal
  letI : Field κ' := Ideal.Quotient.field (w).asIdeal
  letI : Finite κ' := (w).asIdeal.finiteQuotientOfFreeOfNeBot (w).ne_bot
  letI : Algebra κ κ' := inferInstanceAs (Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ (w).asIdeal))
  obtain ⟨e, hE⟩ := exists_padic_residue_equiv_of_completion v i hi
  have hq : Nat.card κ = p := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod p)
  have hdeg : Module.finrank κ κ' = n := by
    letI : Fintype κ := Fintype.ofEquiv (ZMod p) e.symm.toEquiv
    letI := Fintype.ofFinite κ'
    have hq' : Fintype.card κ = p := by rw [← Nat.card_eq_fintype_card, hq]
    have h' := (Module.card_eq_pow_finrank (K := κ) (V := κ')).symm.trans
      (Module.card_eq_pow_finrank (K := ZMod p) (V := κ'))
    rw [hq', ZMod.card, hd] at h'
    exact (pow_right_strictMono₀ (Fact.out : p.Prime).one_lt).injective h'
  obtain ⟨θ, hθ, hname⟩ := exists_ellipticName_of_isCusp hn hd _ hτ
  obtain ⟨x, hx⟩ : ∃ x, j x ≠ 0 := by
    by_contra! hb
    exact hj₀ (LinearMap.ext hb)
  let r := residueArtinOnBaseInertia K Ω L h hβ he
  have hcent (t : Ine (F := K) A) : θ (∏ k ∈ Finset.range n, r t ^ p ^ k) = ω (α (ineIncl h t)) := by
    let u := localArtinOnInertia hα t
    obtain ⟨z, hzu, hzr⟩ := hE u
    let zK := Units.map (i.toRingHom.comp (algebraMap ℤ_[p] ℚ_[p])).toMonoidHom z
    have hza : α (ineIncl h t) = zK := Units.ext hzu
    have hnorm : (∏ k ∈ Finset.range n, r t ^ p ^ k) =
        Units.map (algebraMap κ κ').toMonoidHom (finiteCompletionUnitReduction v u) := by
      rw [residueArtinOnBaseInertia_norm K Ω L h hα hβ he t]
      apply Units.ext
      change (Units.coeHom κ') (∏ k ∈ Finset.range n, r t ^ p ^ k) =
        algebraMap κ κ' (Algebra.norm κ (r t : κ'))
      rw [map_prod, FiniteField.algebraMap_norm_eq_prod_pow κ κ', hdeg, hq]
      exact Finset.prod_congr rfl fun k _ => Units.val_pow_eq_pow_val _ _
    have hred : Units.map (algebraMap κ κ').toMonoidHom (finiteCompletionUnitReduction v u) =
        Units.map (algebraMap (ZMod p) κ').toMonoidHom (Units.map PadicInt.toZMod.toMonoidHom z) := by
      have hmap : (algebraMap κ κ').comp e.symm.toRingHom = algebraMap (ZMod p) κ' :=
        RingHom.ext_zmod _ _
      apply Units.ext
      rw [← hzr]
      change algebraMap κ κ' (↑(finiteCompletionUnitReduction v u) : κ) =
        algebraMap (ZMod p) κ' (e (↑(finiteCompletionUnitReduction v u) : κ))
      rw [← hmap, RingHom.comp_apply]
      change algebraMap κ κ' _ = algebraMap κ κ' (e.symm (e _))
      rw [e.symm_apply_apply]
    have hscalar := hj (GeneralLinearGroup.scalar (Fin n) z) x
    unfold integralReduction integralInclusion at hscalar
    rw [GeneralLinearGroup.map_scalar, GeneralLinearGroup.map_scalar, GeneralLinearGroup.map_scalar] at hscalar
    change j (τ.ρ (GeneralLinearGroup.scalar (Fin n) (Units.map PadicInt.toZMod.toMonoidHom z)) x) =
      ρ (GeneralLinearGroup.scalar (Fin n) zK) (j x) at hscalar
    rw [central_character_of_ellipticName hn hd τ θ hτ hθ hname, map_smul, hω] at hscalar
    rw [hnorm, hred, hza]
    exact Units.ext (smul_left_injective ℂ hx hscalar)
  obtain ⟨a, ha, hN, hT, hD, hP⟩ :=
    exists_tame_wdRep_of_regular_residue_orbit hn hd r
      (residueArtinOnBaseInertia_surjective K Ω L h hβ he)
      (residueArtinOnBaseInertia_open_ker K Ω L h hβ he)
      (residueArtinOnBaseInertia_wild K Ω L h hβ he)
      (frob h) deg_frob
      (fun t t' ht => by
        simpa only [r, show normV v = p from hq] using
          residueArtinOnBaseInertia_conjugation K Ω L h hβ he (frob h) deg_frob t t' ht)
      θ hθ (ω.comp α) hcent
  exact ⟨θ, a, hθ, hname, ha, hN, hT, hD, hP⟩

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.exists_tame_wdRep_of_cuspidal_type
