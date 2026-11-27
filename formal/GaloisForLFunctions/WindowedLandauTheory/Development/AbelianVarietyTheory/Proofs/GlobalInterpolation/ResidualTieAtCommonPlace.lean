import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InertiaComparisonFromFrobenius

/-! The integral point model transports characteristic polynomials to a
common complex valuation ring and its prescribed residue identification. -/

noncomputable section

open IsLocalRing NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N ReciprocityTheory.Gal

namespace WindowedLandauTheory.NormalizedTypes

variable {D : D7} {i : D.nd.Loc} {σ : D.what₂.FT} {P : List (Part D.naut.CG)}
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "w" => D.nd.w i
local notation "ℓ" => D.what₂.places.resChar w
local notation "hp" => D.what₂.places.resChar_prime w

/-- A continuous point lattice with the same cofinite split Frobenius
polynomials realizes the prescribed row reduction at the common place. -/
theorem residual_tie_at_common_place
    (ρ : Γ →* GL (Fin D.R.r) (D.nd.O i)) (hρ : IsRepOfSig D.nd D.naut i P ρ)
    (hP : HasParamW D.nd D.naut i σ P)
    (r : Γ →* GL (Fin D.R.r) (PadicAlgCl (D.nd.l i))) (hr : Continuous fun g => (r g).val)
    (hF : SplitFrobeniusDense D)
    (h : ∀ᶠ v in Filter.cofinite, IsSplitPl D.host v →
      ∀ (B : ValuationSubring D.nd.Om) (g : Γ), IsPlaceOver (F := D.host.E) B v →
        IsFrob (F := D.host.E) B (normV v) g →
        (ρ g).val.charpoly.map (iotaO D.nd D.naut i) =
          (r g).val.charpoly.map (D.naut.iotaQC i).toRingHom)
    (B : ValuationSubring ℂ) (κ : ResidueField B ≃+* Fb ℓ hp)
    (hκ : RedCompat D i B hp (D.nd.w_l i) κ) :
    IsSSRep (D.ntypes.rbar σ w) ∧ ∀ s : Γ, ∃ Q : B[X],
      Q.map B.subtype = (r s).val.charpoly.map (D.naut.iotaQC i).toRingHom ∧
      Q.map (κ.toRingHom.comp (residue B)) = (D.ntypes.rbar σ w s).val.charpoly := by
  let φ := (iotaO D.nd D.naut i).codRestrict B.toSubring fun y => (hκ y).choose
  let f := κ.toRingHom.comp (residue B)
  let τ := fbCast (D.nd.w_l i) hp (D.nd.lPrime i).out
  have hsub : B.subtype.comp φ = iotaO D.nd D.naut i := rfl
  have hred : τ.toRingHom.comp (f.comp φ) = (D.naut.kFbar i).comp (residue (D.nd.O i)) :=
    RingHom.ext fun y => (hκ y).choose_spec
  obtain ⟨hss, hpol⟩ := D.rbar_tie i σ P ρ hP hρ
  refine ⟨hss, fun s => ⟨(ρ s).val.charpoly.map φ, ?_, ?_⟩⟩
  · have hc := charpoly_eq_of_cofinite_split_frobenius i ρ hρ.1 r hr hF h s
    have hm := congrArg (Polynomial.map (D.naut.iotaQC i).toRingHom) hc
    rw [Matrix.charpoly_map, Polynomial.map_map] at hm
    rw [Polynomial.map_map, hsub]
    exact hm
  · apply Polynomial.map_injective τ.toRingHom τ.injective
    rw [Polynomial.map_map, Polynomial.map_map]
    change (ρ s).val.charpoly.map ((τ.toRingHom.comp f).comp φ) = _
    rw [RingHom.comp_assoc, hred]
    exact (hpol s).symm

end WindowedLandauTheory.NormalizedTypes
