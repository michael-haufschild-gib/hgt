import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameRootExclusionAtConjugatePlaces
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DensityOfSplitFrobenius
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameRankOneCharacter

/-! The inertia input to Theorem Three Prime follows from local–global
matching for cuspidal point parameters and the tame label laws. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N WindowedLandauTheory.MainNotions.ArithmeticCylinders
open ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7)
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)

/-- Only the unramified Frobenius and the inertia comparisons at the
designated full-degree, squarefree types are needed from the cuspidal
Galois representation. -/
theorem theoremThreePrime_of_galois {jE : D.host.E →+* AlgebraicClosure ℚ}
    (T : NormalizedTypesCompatibility D jE)
    (hTw : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)) (s : ℝ),
      D.naut.items₂ k _ (D.naut.lpTw a s) = D.naut.items₂ k _ a)
    (hDegree : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)),
      (D.naut.items₂ k _ a).natDegree ≤ D.naut.lpDim a)
    (hWild : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)),
      (D.naut.items₂ k _ a).natDegree = D.naut.lpDim a →
      ∀ s ∈ wildInertia (E := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        D.naut.inePol a s = (X - 1) ^ D.naut.lpDim a)
    (hUndo : ∀ π : D.naut.CG D.R.r, D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π)
    (hEta : D.naut.csd D.naut.etaT)
    (hEtaInf : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ))
    (hGal : ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π →
      ∃ r : Γ →* GL (Fin D.R.r) (Qbar (D.nd.l i)), (Continuous fun s => (r s).val) ∧
        (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.locG π w) →
          D.naut.wdOf i r w = D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∧
        (∀ (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k →
          let w := D.naut.plGw k v
          let L := D.naut.locG π w
          (D.naut.items₂ k w L).natDegree = D.naut.lpDim L →
          Squarefree (D.naut.items₂ k w L) →
          ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
            D.naut.inePol (D.naut.wdOf i r w) s =
              D.naut.inePol (D.naut.lpTw L ((1 - (D.R.r : ℝ)) / 2)) s)) :
    TheoremThreePrime D := by
  apply theoremThreePrime_of_inertia D hTw hDegree
  intro i P hx hf hg hc ρ hρ
  obtain ⟨π, rfl⟩ := hc
  obtain ⟨x, hx⟩ := hx
  obtain ⟨hc, ha⟩ := csd_ralg_of_hasParamX_single D i x π hx (hUndo π) hEta hEtaInf
  obtain ⟨r, hr, hFrob, hI⟩ := hGal i π hc ha
  have hDense : SplitFrobeniusDense D := fun S hS =>
    GlobalTheory.FrobDense.dense_split_frobenius D.host S hS
  refine residual_tame_conditions_of_local_matching D i T hDense hc ρ hρ hg hf ?_ ?_
    (auxiliary_place_away D i)
  · intro k hk v
    dsimp only
    intro s hsi
    have hw := auxiliary_place_away D i k hk _ (D.naut.plGw_over k v)
    have hu : ∀ᶠ w in Filter.cofinite, D.naut.unr (isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] w) := by
      simpa only [isoLoc_single] using D.naut.locG_unr_ae π
    refine inertia_charpoly_of_frobenius i hρ r hr hu ?_ hDense _ hw s hsi ?_
    · simpa only [isoLoc_single] using hFrob
    · rw [isoLoc_single]
      have hf' : (D.naut.items₂ k _ (isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] (D.naut.plGw k v))).natDegree =
          D.naut.lpDim (isoLoc D.nd D.naut [⟨D.R.r, π, 1⟩] (D.naut.plGw k v)) := hf k v
      exact hI k v hk (by simpa only [isoLoc_single] using hf')
        (by simpa only [isoLoc_single] using (hg k).1.2.1 v) s hsi
  · intro k hk v
    dsimp only
    intro s hsw
    refine ⟨?_, chi_eq_one_on_auxiliary_wild D i k hk _ (D.naut.plGw_over k v) hsw⟩
    simpa only [isoLoc_single, D.naut.locG_dim] using hWild k v _ (hf k v) s hsw

end WindowedLandauTheory.NormalizedTypes
