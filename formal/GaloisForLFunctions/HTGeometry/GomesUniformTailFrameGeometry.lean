import GaloisForLFunctions.HTGeometry.GomesCanonicalMomentGeometry
import GaloisForLFunctions.HTGeometry.StieltjesSemidefiniteExistence

/-!
Concrete corpus applications of the internal-frame and tensor-observation viewpoint in
Gomes, arXiv:2404.10461 and arXiv:2509.25276v7. Source equality is proved before
transferring the geometry. These are applications, not numbered paper transcriptions.
-/
open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry
open GaloisForLFunctions.HTGeometry


/-- The canonical frame model of this concrete corpus source. -/
def gomesUniformTailModel : GomesMomentModel := gomesCanonicalMomentModel (reciprocalTailClock)

/-- Exact source identification, retaining its original mass. -/
theorem gomesUniformTailModel_moments :
    (gomesUniformTailModel).moments = (reciprocalTailClock) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  exact reciprocalTailClock_positiveMomentForm

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesUniformTail_quotient_height (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (reciprocalTailClock) ((n+1)+1) z /
      monicOrthoC (reciprocalTailClock) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesUniformTailModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesUniformTailModel) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesUniformTail_flux_signature (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesUniformTailModel) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesUniformTailModel) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesUniformTail_mass_probe :
    gomesMomentNormalizedFlux (gomesUniformTailModel) 0 Complex.I 0 0 = ((2/(reciprocalTailClock) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesUniformTailModel_moments]

end GaloisForLFunctions.HTGeometry
