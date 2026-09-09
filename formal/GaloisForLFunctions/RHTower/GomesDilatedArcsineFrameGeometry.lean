import GaloisForLFunctions.HTGeometry.GomesCanonicalMomentGeometry
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionRelativeSourceCoercivity

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
open _root_.RHTower.XiShiftedArcsineAdmission
/-- Nonzero dilation data include both coordinate orientations. -/
def gomesSignedDilation (negative : Bool) (r : ℝ) : ℝ :=
  if negative then -Real.exp r else Real.exp r

/-- Either orientation yields a nondegenerate coordinate dilation. -/
theorem gomesSignedDilation_ne_zero (negative : Bool) (r : ℝ) :
    gomesSignedDilation negative r ≠ 0 := by
  cases negative <;> simp [gomesSignedDilation,Real.exp_ne_zero]


/-- The canonical frame model of this concrete corpus source. -/
def gomesDilatedArcsineModel (negative : Bool) (r : ℝ) : GomesMomentModel := gomesCanonicalMomentModel (coordinateDilatedMoment (gomesSignedDilation negative r))

/-- Exact source identification, retaining its original mass. -/
theorem gomesDilatedArcsineModel_moments (negative : Bool) (r : ℝ) :
    (gomesDilatedArcsineModel negative r).moments = (coordinateDilatedMoment (gomesSignedDilation negative r)) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  exact coordinateDilatedMoment_positiveMomentForm (gomesSignedDilation_ne_zero negative r)

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesDilatedArcsine_quotient_height (negative : Bool) (r : ℝ) (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (coordinateDilatedMoment (gomesSignedDilation negative r)) ((n+1)+1) z /
      monicOrthoC (coordinateDilatedMoment (gomesSignedDilation negative r)) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesDilatedArcsineModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesDilatedArcsineModel negative r) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesDilatedArcsine_flux_signature (negative : Bool) (r : ℝ) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesDilatedArcsineModel negative r) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesDilatedArcsineModel negative r) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesDilatedArcsine_mass_probe (negative : Bool) (r : ℝ) :
    gomesMomentNormalizedFlux (gomesDilatedArcsineModel negative r) 0 Complex.I 0 0 = ((2/(coordinateDilatedMoment (gomesSignedDilation negative r)) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesDilatedArcsineModel_moments]

end GaloisForLFunctions.RHTower
