import GaloisForLFunctions.HTGeometry.GomesCanonicalMomentGeometry
import GaloisForLFunctions.RHTower.XiShiftedProjectiveAdjacentMeanResetBarrier

/-!
Concrete corpus applications of the internal-frame and tensor-observation viewpoint in
Gomes, arXiv:2404.10461 and arXiv:2509.25276v7. Source equality is proved before
transferring the geometry. These are applications, not numbered paper transcriptions.
-/
open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.RHTower
open _root_.HTGeometry
open GaloisForLFunctions.HTGeometry
open _root_.RHTower.XiShiftedCanonicalAdmission

/-- The canonical frame model of this concrete corpus source. -/
def gomesResetCounterModel (a r t : ℝ) : GomesMomentModel := gomesCanonicalMomentModel (resetCounterMoment a (Real.exp r) (Real.exp t))

/-- Exact source identification, retaining its original mass. -/
theorem gomesResetCounterModel_moments (a r t : ℝ) :
    (gomesResetCounterModel a r t).moments = (resetCounterMoment a (Real.exp r) (Real.exp t)) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  exact resetCounterMoment_positiveMomentForm a (Real.exp_pos r) (Real.exp_pos t)

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesResetCounter_quotient_height (a r t : ℝ) (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (resetCounterMoment a (Real.exp r) (Real.exp t)) ((n+1)+1) z /
      monicOrthoC (resetCounterMoment a (Real.exp r) (Real.exp t)) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesResetCounterModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesResetCounterModel a r t) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesResetCounter_flux_signature (a r t : ℝ) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesResetCounterModel a r t) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesResetCounterModel a r t) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesResetCounter_mass_probe (a r t : ℝ) :
    gomesMomentNormalizedFlux (gomesResetCounterModel a r t) 0 Complex.I 0 0 = ((2/(resetCounterMoment a (Real.exp r) (Real.exp t)) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesResetCounterModel_moments]

end GaloisForLFunctions.RHTower
