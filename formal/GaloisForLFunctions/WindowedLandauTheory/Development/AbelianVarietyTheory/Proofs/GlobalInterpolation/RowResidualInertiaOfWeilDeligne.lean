import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuityOfCoefficientEmbedding
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowResidualInertiaPolynomial
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameRankOneCharacter

/-! At a localization of a good row, Weil–Deligne matching identifies the
integral inertia polynomials before reduction to the row's residue field. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N WindowedLandauTheory.CyclotomicNorms
open ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7) (i : D.nd.Loc) (σ : D.what₂.FT) (P : List (Part D.naut.CG))
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)

private theorem inertia_charpoly_of_row_wd
    (r : Γ →* GL (Fin D.R.r) (D.nd.O i)) (hr : IsRepOfSig D.nd D.naut i P r)
    (w : PlE D.host) (hw : w ∉ placesOver D.host.E (D.nd.l i))
    (hI : ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) s =
        D.naut.inePol (D.naut.lpTw (isoLoc D.nd D.naut P w) ((1 - (D.R.r : ℝ)) / 2)) s)
    (s : Γ) (hs : s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    (r s).val.charpoly.map (iotaO D.nd D.naut i) = D.naut.inePol (isoLoc D.nd D.naut P w) s := by
  let j := iotaOQ D.nd D.naut i
  let e := (D.naut.iotaQC i).toRingHom
  have hcont : Continuous fun u => (mapRep j r u).val :=
    hr.1.matrix_map (continuous_iotaOQ D i)
  have h := D.naut.wdOf_ine i (mapRep j r) w hw hcont s hs
  rw [hI s hs, D.naut.inePol_tw _ _ _ hs] at h
  rw [show iotaO D.nd D.naut i = e.comp j from rfl, ← Polynomial.map_map, ← Matrix.charpoly_map]
  exact h

/-- A full tame row label supplies both the tame and wild residual
polynomials at the coefficient place represented by the localization. -/
theorem row_residual_inertia_of_wd {jE : D.host.E →+* AlgebraicClosure ℚ}
    (T : NormalizedTypesCompatibility D jE)
    (r : Γ →* GL (Fin D.R.r) (D.nd.O i)) (hr : IsRepOfSig D.nd D.naut i P r)
    (hP : HasParamW D.nd D.naut i σ P) (hg : D.nd.goodRow σ)
    (k : Fin 2) (v : D.nd.PlG k) (hk : D.nd.l i ≠ D.host.g k)
    (hI : let w := D.naut.plGw k v
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) s =
          D.naut.inePol (D.naut.lpTw (isoLoc D.nd D.naut P w) ((1 - (D.R.r : ℝ)) / 2)) s)
    (hW : ∀ (L : D.naut.LP (D.naut.plGw k v)),
      (D.naut.items₂ k _ L).natDegree = D.naut.lpDim L →
      ∀ s ∈ wildInertia (E := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        D.naut.inePol L s = (X - 1) ^ D.naut.lpDim L) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    let ℓ := D.what₂.places.resChar (D.nd.w i)
    (D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v)).val.charpoly =
      ((rootsBar (D.nd.lab k σ v)).map fun x =>
        X - C (D.ntypes.iota k v (D.nd.w i) (primeToPart ℓ x))).prod ∧
    ∀ s ∈ wildInertia (E := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      (D.ntypes.rbar σ (D.nd.w i) s).val.charpoly = (X - 1) ^ D.R.r := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  let w := D.naut.plGw k v
  let L := isoLoc D.nd D.naut P w
  have hw := auxiliary_place_away D i k hk w (D.naut.plGw_over k v)
  have hine := inertia_charpoly_of_row_wd D i P r hr w hw hI
  refine ⟨charpoly_rbar_tg_of_local_charpoly T hP hr hg k v (hine _ (D.ntypes.tg_mem k v)), ?_⟩
  intro s hs
  have hdim : D.naut.lpDim L = D.R.r := (lpDim_isoLoc D.nd D.naut P w).trans hP.2.1
  have hfull : (D.naut.items₂ k w L).natDegree = D.naut.lpDim L := by
    change (D.naut.items₂ k w (isoLoc D.nd D.naut P w)).natDegree = D.naut.lpDim L
    rw [items₂_isoLoc_eq_lab_of_hasParamW D i σ P hP k v, (D.nd.lab_monic k σ v).2, hdim]
  have hpol := (hine s (wildInertia_le_inertia _ hs)).trans (hW L hfull s hs)
  rw [hdim] at hpol
  exact charpoly_rbar_eq_unipotent_of_local_charpoly hP hr s hpol

end WindowedLandauTheory.NormalizedTypes
