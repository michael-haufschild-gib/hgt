import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticKP

/-!
# Electron-acoustic KP lump singularity audit (arXiv:2609.03539)

The corrected equation-(45) quadratic tau function solves the bilinear equation, but its physical
sign chamber forces a negative constant offset.  The determinant-one parameterization makes the
affine pair surjective, so every member of that physical family has a real zero.  A separate closed
witness shows the printed sign of `b₇` creates a nonzero Hirota residual.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

noncomputable def mondalNegativeBetaLumpOffset (betaLog gammaLog r : ℝ) : ℝ :=
  mondalLumpOffset (-Real.exp betaLog) gammaLog r

theorem mondalNegativeBetaLumpOffset_neg (betaLog gammaLog r : ℝ) :
    mondalNegativeBetaLumpOffset betaLog gammaLog r < 0 := by
  unfold mondalNegativeBetaLumpOffset mondalLumpOffset mondalLumpNormSq
  have hgamma : 0 < Real.exp gammaLog := Real.exp_pos gammaLog
  have hbeta : 0 < Real.exp betaLog := Real.exp_pos betaLog
  have hnorm : 0 < 1 + r ^ 2 := by nlinarith [sq_nonneg r]
  have hleft : 3 * (-Real.exp betaLog) / Real.exp gammaLog < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) (neg_lt_zero.mpr hbeta)) hgamma
  exact mul_neg_of_neg_of_pos hleft (pow_pos hnorm 3)

noncomputable def mondalLumpZeroRadius (betaLog gammaLog r : ℝ) : ℝ :=
  Real.sqrt (-mondalNegativeBetaLumpOffset betaLog gammaLog r)

noncomputable def mondalLumpZeroX
    (betaLog gammaLog r b d m : ℝ) : ℝ :=
  mondalLumpH r b * (mondalLumpZeroRadius betaLog gammaLog r - d) + b * m

noncomputable def mondalLumpZeroY
    (betaLog gammaLog r _b d m : ℝ) : ℝ :=
  -r * (mondalLumpZeroRadius betaLog gammaLog r - d) - m

theorem mondalLumpZero_affineF (betaLog gammaLog r b d m : ℝ) :
    mondalAffineForm 1 b (mondalLumpVelocityF gammaLog r b) d 0
      (mondalLumpZeroX betaLog gammaLog r b d m)
      (mondalLumpZeroY betaLog gammaLog r b d m) =
        mondalLumpZeroRadius betaLog gammaLog r := by
  unfold mondalAffineForm mondalLumpZeroX mondalLumpZeroY mondalLumpH
  ring

theorem mondalLumpZero_affineG (betaLog gammaLog r b d m : ℝ) :
    mondalAffineForm r (mondalLumpH r b) (mondalLumpVelocityG gammaLog r b) m 0
      (mondalLumpZeroX betaLog gammaLog r b d m)
      (mondalLumpZeroY betaLog gammaLog r b d m) = 0 := by
  unfold mondalAffineForm mondalLumpZeroX mondalLumpZeroY mondalLumpH
  ring

theorem mondalCorrectedNegativeBetaLumpTau_has_zero
    (betaLog gammaLog r b d m : ℝ) :
    (mondalCorrectedLumpTauJet (-Real.exp betaLog) gammaLog r b d m).u 0
      (mondalLumpZeroX betaLog gammaLog r b d m)
      (mondalLumpZeroY betaLog gammaLog r b d m) = 0 := by
  have hnonneg : 0 ≤ -mondalNegativeBetaLumpOffset betaLog gammaLog r :=
    le_of_lt (neg_pos.mpr (mondalNegativeBetaLumpOffset_neg betaLog gammaLog r))
  simp only [mondalCorrectedLumpTauJet, mondalQuadraticTauJet, mondalQuadraticTau]
  rw [mondalLumpZero_affineF, mondalLumpZero_affineG]
  unfold mondalLumpZeroRadius
  rw [Real.sq_sqrt hnonneg]
  unfold mondalNegativeBetaLumpOffset
  ring

noncomputable def mondalPrintedLumpWitness : RealEvolutionJetKP :=
  mondalQuadraticTauJet 1 0 (-1 / 2) 0 1 1 (-1 / 2) 0 (-24)

theorem mondalPrintedLumpWitness_hirotaResidual_origin :
    hirotaKPResidual (-1) (-1) mondalPrintedLumpWitness 0 0 0 = 96 := by
  unfold hirotaKPResidual mondalPrintedLumpWitness mondalQuadraticTauJet
    mondalQuadraticTau mondalAffineForm
  norm_num

theorem mondalPrintedLumpWitness_not_solvesHirota :
    ¬ SolvesHirotaKP (-1) (-1) mondalPrintedLumpWitness := by
  intro h
  have horigin := h 0 0 0
  rw [mondalPrintedLumpWitness_hirotaResidual_origin] at horigin
  norm_num at horigin

end GaloisForLFunctions.HTGeometry.DispersivePDE
