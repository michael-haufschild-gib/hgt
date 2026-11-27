import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.TwGood
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralCharacterOfDenseValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DensityOfSplitFrobenius

/-! A rank-one Galois realization of the normalizing character is
integral when its Frobenius values lie in the embedded coefficient field. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N ReciprocityTheory.Gal

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7) (i : D.nd.Loc)
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "O" => D.nd.O i
local notation "L" => Qbar (D.nd.l i)
local notation "P" => (fun w => D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2))

/-- The normalized character lifts to continuous integral units and is
trivial on inertia away from the coefficient characteristic. -/
theorem exists_integral_rank_one_normalizer
    (r : Γ →* GL (Fin 1) L) (hr : Continuous fun g => (r g).val)
    (hW : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i r w = P w)
    (hE : ∀ w, ∃ x : D.what₂.LL, D.naut.frobEig (P w) = {D.what₂.embLL x}) :
    ∃ ξ : Γ →* Oˣ, (Continuous fun g => (ξ g : O)) ∧
      ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        (∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), ξ g = 1) ∧
        ∀ (B : ValuationSubring D.nd.Om) (g : Γ), IsPlaceOver (F := D.host.E) B w →
          IsFrob (F := D.host.E) B (normV w) g →
          D.naut.frobEig (P w) = {iotaO D.nd D.naut i (ξ g : O)} := by
  letI := D.nd.acOm
  letI : IsGalois D.host.E D.nd.Om := {}
  let d : Γ →* L := (Units.coeHom L).comp (Matrix.GeneralLinearGroup.det.comp r)
  have hval (g : Γ) : d g = (r g).val 0 0 := Matrix.det_fin_one _
  have hc : Continuous d := by
    show Continuous fun g => d g
    simp only [hval]
    exact hr.matrix_elem 0 0
  have hU (w : PlE D.host) (hw : w ∉ placesOver D.host.E (D.nd.l i)) :
      D.naut.unr (D.naut.wdOf i r w) := by
    rw [hW w hw]
    exact (D.naut.unr_tw _ _).mpr (D.naut.etaTinv_def w).1
  have hF (w : PlE D.host) (hw : w ∉ placesOver D.host.E (D.nd.l i))
      (B : ValuationSubring D.nd.Om) (s : Γ) (hB : IsPlaceOver (F := D.host.E) B w)
      (hs : IsFrob (F := D.host.E) B (normV w) s) :
      D.naut.frobEig (P w) = {D.naut.iotaQC i (d s)} := by
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp
      ((D.naut.frobEig_card _ (hU w hw)).trans (D.naut.wdOf_dim i r w))
    have h := D.naut.wdOf_frob i r w hw hr (hU w hw) B s hB hs
    rw [ha, Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq] at h
    simp only [Multiset.map_singleton, Multiset.prod_singleton,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
    change X - C (D.naut.iotaQC i ((r s).val 0 0)) = X - C a at h
    have he := C_injective (sub_right_injective h)
    rw [← hW w hw, ha, hval, he]
  have hfin := MainNotions.placesOver_finite_av D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  have hd := GlobalTheory.FrobDense.dense_split_frobenius D.host (Ω := D.nd.Om) _ hfin
  obtain ⟨ξ, hξc, hξ⟩ := exists_integral_character D i d hc hd (by
    rintro s ⟨w, hw, -, B, hB, hs⟩
    obtain ⟨x, hx⟩ := hE w
    have h := hF w hw B s hB hs
    rw [hx, Multiset.singleton_inj, ← D.naut.iota_LL i x] at h
    exact ⟨D.nd.embK i x, (D.naut.iotaQC i).injective h⟩)
  refine ⟨ξ, hξc, fun w hw => ⟨?_, ?_⟩⟩
  · intro s hs
    have he := (D.naut.wdOf_unr i r w hw hr).mp (hU w hw) s hs
    apply Units.ext
    apply (D.naut.iotaQ i).injective.comp (IsFractionRing.injective O (FractionRing O))
    change iotaOQ D.nd D.naut i (ξ s : O) = iotaOQ D.nd D.naut i 1
    rw [hξ s, hval s, he, Units.val_one, Matrix.one_apply_eq, map_one]
  · intro B s hB hs
    rw [hF w hw B s hB hs, ← hξ s] <;> rfl

end WindowedLandauTheory.NormalizedTypes
