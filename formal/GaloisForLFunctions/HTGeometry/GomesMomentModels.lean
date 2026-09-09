import GaloisForLFunctions.HTGeometry.GomesArcsineFrameGeometry
import GaloisForLFunctions.HTGeometry.GomesGammaFrameGeometry
import GaloisForLFunctions.HTGeometry.GomesCompletedFockFrameGeometry
import GaloisForLFunctions.HTGeometry.ComplexSecondKind
import GaloisForLFunctions.HTGeometry.GomesFavardData

/-!
# Concrete moment models without positivity premises

Shared data interface for corpus applications of the internal-frame and invariant
viewpoints in https://arxiv.org/abs/2607.24901,
https://arxiv.org/abs/2509.25276, and https://arxiv.org/abs/2404.10461.
Every constructor names an existing concrete moment family and carries only
mathematical data. Positivity is proved by the existing source constructions,
so later frame and projective-quotient results need no supplied proof hypotheses.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Concrete corpus constructions, with mathematical data but no proof inputs. -/
inductive GomesMomentModel where
  | arcsine
  | gamma (logShape : ℝ)
  | fock {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
  | favard (logMass : ℝ) (diagonal logLower : ℕ → ℝ)

/-- The underlying moment sequence supplied by each concrete construction. -/
def GomesMomentModel.moments : GomesMomentModel → ℕ → ℝ
  | .arcsine => normalizedCentralBinom
  | .gamma r => gammaShapeMoment (Real.exp r)
  | .fock B => gomesCompletedFockMoment B
  | .favard r a q => gomesFavardMoment r a q

/-- Every construction discharges positivity internally. -/
theorem gomesMomentModel_positive (M : GomesMomentModel) : PositiveMomentForm M.moments := by
  cases M with
  | arcsine => exact normalizedCentralBinom_positiveMomentForm
  | gamma r => exact gammaShapeMoment_positiveMomentForm (Real.exp_pos r)
  | fock B => exact gomesCompletedFockMoment_positiveMomentForm B
  | favard r a q => exact gomesFavardMoment_positive r a q

/-- Every nonzero monic level has strictly positive squared moment norm. -/
theorem gomesMomentModel_norm_pos (M : GomesMomentModel) (n : ℕ) :
    0 < momentInner M.moments (monicOrtho M.moments n) (monicOrtho M.moments n) :=
  M |> gomesMomentModel_positive |>.pos_of_ne_zero _ (monicOrtho_ne_zero M.moments n)

/-- Every step of every concrete model has a strictly positive recurrence coupling. -/
theorem gomesMomentModel_recurOff_pos (M : GomesMomentModel) (n : ℕ) :
    0 < recurOff M.moments n :=
  div_pos (gomesMomentModel_norm_pos M (n+1)) (gomesMomentModel_norm_pos M n)

end GaloisForLFunctions.HTGeometry
