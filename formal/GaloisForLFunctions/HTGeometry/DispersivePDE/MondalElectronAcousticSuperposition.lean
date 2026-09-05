import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticKP

/-!
# Electron-acoustic KP superposition obstruction (arXiv:2609.03539)

The paper describes head-on collision plots built from separately derived right- and left-moving
profiles, but gives no coupled exact collision formula.  These closed identities record the precise
nonlinear obstruction to treating a visual profile overlay as another KP solution.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

theorem generalKPResidual_add
    (α δ ρ : ℝ) (J K : RealEvolutionJetKP) (t x y : ℝ) :
    generalKPResidual α δ ρ (realEvolutionJetKPAdd J K) t x y =
      generalKPResidual α δ ρ J t x y + generalKPResidual α δ ρ K t x y
        + α * (2 * J.ux t x y * K.ux t x y
          + J.u t x y * K.uxx t x y + K.u t x y * J.uxx t x y) := by
  unfold generalKPResidual realEvolutionJetKPAdd
  ring

theorem generalKPResidual_scale
    (α δ ρ c : ℝ) (J : RealEvolutionJetKP) (t x y : ℝ) :
    generalKPResidual α δ ρ (realEvolutionJetKPScale c J) t x y =
      c * generalKPResidual α δ ρ J t x y
        + α * c * (c - 1) * (J.ux t x y ^ 2 + J.u t x y * J.uxx t x y) := by
  unfold generalKPResidual realEvolutionJetKPScale
  ring

noncomputable def mondalCanonicalDoubledJet : RealEvolutionJetKP :=
  realEvolutionJetKPScale 2 (mondalSolitonJet 6 1 3 2 0 0)

theorem mondalCanonicalDoubledResidual_origin :
    generalKPResidual 6 1 3 mondalCanonicalDoubledJet 0 0 0 = -96 := by
  rw [show mondalCanonicalDoubledJet =
      realEvolutionJetKPScale 2 (mondalSolitonJet 6 1 3 2 0 0) by rfl,
    generalKPResidual_scale,
    (mondalSoliton_solves 6 1 3 2 0 0) 0 0 0]
  simp [mondalSolitonJet, mondalSoliton, mondalPhase, mondalFrequency,
    solitonQ, solitonQ1, solitonQ2, solitonT]
  norm_num

theorem mondalCanonicalDoubled_not_solves :
    ¬ SolvesGeneralKP 6 1 3 mondalCanonicalDoubledJet := by
  intro h
  have horigin := h 0 0 0
  rw [mondalCanonicalDoubledResidual_origin] at horigin
  norm_num at horigin

end GaloisForLFunctions.HTGeometry.DispersivePDE
