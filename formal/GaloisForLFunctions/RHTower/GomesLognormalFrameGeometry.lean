import GaloisForLFunctions.HTGeometry.GomesCanonicalMomentGeometry
import GaloisForLFunctions.RHTower.JacobiBoundaryQuantumRecurrenceLaw

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
open _root_.RHTower
/-- Every positive lognormal variance, supplied without proof parameters. -/
def gomesLognormalVariance (r : ℝ) : NNReal := ⟨Real.exp r, (Real.exp_pos r).le⟩


/-- The canonical frame model of this concrete corpus source. -/
def gomesLognormalModel (r : ℝ) : GomesMomentModel := gomesCanonicalMomentModel (positiveRecurrenceSeparationMoments (gomesLognormalVariance r))

/-- Exact source identification, retaining its original mass. -/
theorem gomesLognormalModel_moments (r : ℝ) :
    (gomesLognormalModel r).moments = (positiveRecurrenceSeparationMoments (gomesLognormalVariance r)) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  apply positiveMomentForm_positiveRecurrenceSeparationMoments
  change 0 < Real.exp r
  exact Real.exp_pos r

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesLognormal_quotient_height (r : ℝ) (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (positiveRecurrenceSeparationMoments (gomesLognormalVariance r)) ((n+1)+1) z /
      monicOrthoC (positiveRecurrenceSeparationMoments (gomesLognormalVariance r)) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesLognormalModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesLognormalModel r) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesLognormal_flux_signature (r : ℝ) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesLognormalModel r) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesLognormalModel r) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesLognormal_mass_probe (r : ℝ) :
    gomesMomentNormalizedFlux (gomesLognormalModel r) 0 Complex.I 0 0 = ((2/(positiveRecurrenceSeparationMoments (gomesLognormalVariance r)) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesLognormalModel_moments]

end GaloisForLFunctions.RHTower
