import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicTransport

/-!
# Marked-boundary observability of the parabolic coverage codiagonal

The literal matched-minus-quantile codiagonal has zero mass.  Its parabolic self-form therefore
sees only its linear coordinate and is blind to the second coordinate containing the completed
source charge and squared displacement debt.  A mass-nonzero marked boundary is the minimal
polarization that reads that hidden coordinate exactly.
-/

noncomputable section

namespace RHTower

/-- Mass-one lightlike boundary port for the parabolic moment carrier. -/
def ccmParabolicLightlikeBoundary : Fin 3 → ℝ := ![1, 0, 0]

/-- A mass-neutral parabolic vector has a self-form independent of its second coordinate. -/
theorem ccmParabolicForm_massNeutral {v : Fin 3 → ℝ} (hv : v 0 = 0) :
    ccmParabolicForm v = -(v 1) ^ (2 : ℕ) := by
  rw [ccmParabolicForm, hv]
  ring

/-- A mass-neutral vector can expose its second coordinate only through a marked boundary
pairing with nonzero mass port. -/
theorem ccmParabolicPairing_massNeutral
    {v : Fin 3 → ℝ} (hv : v 0 = 0) (w : Fin 3 → ℝ) :
    ccmParabolicPairing v w = w 0 * v 2 - w 1 * v 1 := by
  rw [ccmParabolicPairing, hv]
  ring

/-- The mass-one lightlike boundary reads the hidden second coordinate exactly. -/
theorem ccmParabolicPairing_massNeutral_lightlike
    {v : Fin 3 → ℝ} (hv : v 0 = 0) :
    ccmParabolicPairing v ccmParabolicLightlikeBoundary = v 2 := by
  rw [ccmParabolicPairing_massNeutral hv]
  simp [ccmParabolicLightlikeBoundary]

/-- The actual finite matched-minus-quantile codiagonal is mass-neutral, so its self-form cannot
control the second source coordinate. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_form (K : ℕ) :
    ccmParabolicForm (ccmActualHeadMatchedQuantileParabolicCodiagonal K) =
      -(ccmActualHeadMatchedQuantileParabolicCodiagonal K 1) ^ (2 : ℕ) := by
  exact ccmParabolicForm_massNeutral
    (ccmActualHeadMatchedQuantileParabolicCodiagonal_zero K)

/-- Every actual marked-boundary readout splits into the hidden second coordinate and the
already-visible linear coordinate. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing
    (K : ℕ) (w : Fin 3 → ℝ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K) w =
      w 0 * ccmActualHeadMatchedQuantileParabolicCodiagonal K 2 -
        w 1 * ccmActualHeadMatchedQuantileParabolicCodiagonal K 1 := by
  exact ccmParabolicPairing_massNeutral
    (ccmActualHeadMatchedQuantileParabolicCodiagonal_zero K) w

/-- The canonical lightlike marked-boundary readout is precisely the second finite source
coordinate. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_lightlike (K : ℕ) :
    ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
      ccmParabolicLightlikeBoundary =
        ccmActualHeadMatchedQuantileParabolicCodiagonal K 2 := by
  exact ccmParabolicPairing_massNeutral_lightlike
    (ccmActualHeadMatchedQuantileParabolicCodiagonal_zero K)

end RHTower
