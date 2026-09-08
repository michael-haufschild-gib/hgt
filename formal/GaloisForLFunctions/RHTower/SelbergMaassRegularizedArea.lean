import GaloisForLFunctions.RHTower.SelbergMaassTraceRegularized
import GaloisForLFunctions.RHTower.SelbergModularPotentialGreen

/-!
# Integrated regularized curvature of the actual Maass trace

The source's regularized amplitude satisfies C² regularity and the literal side
and circular current cancellations. Standard-area Green integration gives

  integral R_e/rho_e = top current + lambda * integral D/(y²*rho_e).

The top current and nodal regularization remain present. The mass, Laplacian,
and remainder are proved integrable. Remainder nonnegativity gives a weighted
mass/flux inequality; it does not establish the quarter comparison or Selberg.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassRegularizedArea
open SelbergMaassMean SelbergMaassCongruenceTrace SelbergMaassTraceEnergy
  SelbergMaassTraceBoundary SelbergMaassTraceRegularized SelbergMaassTraceStokes
  SelbergModularDomainSlices
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (e : Ioi (0 : ℝ))

/-- The actual regularized first coordinate current. -/
def regularizedCurrent (v : ℂ) (x y : ℝ) : ℝ := dir v (radius N f e) (point x y)

/-- The coordinate current is the original trace current divided by twice the radius. -/
theorem regularizedCurrent_eq (v : ℂ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    regularizedCurrent N f e v x y =
      current N f v (ofComplex (point x y)) / (2 * radius N f e (point x y)) := by
  have h := radius_dir N f e v (ofComplex (point x y))
  have hc : ((ofComplex (point x y) : ℍ) : ℂ) = point x y := by
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point x y).im)]
  simpa only [hc, regularizedCurrent] using h

/-- The original inversion symmetry pairs the regularized radii on the circular boundary. -/
theorem radius_arc_eq {x y : ℝ} (hy : 0 < y) (hxy : x ^ 2 + y ^ 2 = 1) :
    radius N f e (point (-x) y) = radius N f e (point x y) := by
  have h := radius_invariant N f e ModularGroup.S (ofComplex (point x y))
  rw [inversion_on_unit_circle hy hxy] at h
  simpa only [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point (-x) y).im),
    ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point x y).im)] using h

/-- The original translation pairs the regularized radii on the vertical sides. -/
theorem radius_side_eq {y : ℝ} (hy : 0 < y) :
    radius N f e (point (1 / 2) y) = radius N f e (point (-(1 / 2)) y) := by
  have h := radius_invariant N f e ModularGroup.T (ofComplex (point (-(1 / 2)) y))
  rw [translation_point _ hy, show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] at h
  simpa only [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point (1 / 2) y).im),
    ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point (-(1 / 2)) y).im)] using h

/-- Actual regularized side currents cancel; no boundary condition is assumed. -/
theorem regularized_side {y : ℝ} (hy : 0 < y) :
    regularizedCurrent N f e 1 (1 / 2) y = regularizedCurrent N f e 1 (-(1 / 2)) y := by
  simp only [regularizedCurrent_eq N f e _ _ hy, radius_side_eq N f e hy,
    side_current_cancellation N f hy]

/-- Actual regularized arc currents cancel with their full geometric weight. -/
theorem regularized_arc {x y : ℝ} (hy : 0 < y) (hxy : x ^ 2 + y ^ 2 = 1) :
    (x / y) * (regularizedCurrent N f e 1 (-x) y - regularizedCurrent N f e 1 x y) -
      regularizedCurrent N f e Complex.I (-x) y - regularizedCurrent N f e Complex.I x y = 0 := by
  simp only [regularizedCurrent_eq N f e _ _ hy, radius_arc_eq N f e hy hxy]
  have h := congrArg (fun t : ℝ => t / (2 * radius N f e (point x y)))
    (arc_current_cancellation N f hy hxy)
  convert h using 1 <;> ring

/-- Actual Green identity for the regularized amplitude in standard two-dimensional area. -/
theorem regularized_area_stokes {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, realLaplacian (radius N f e) (point p.1 p.2)) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), regularizedCurrent N f e Complex.I x Y :=
  SelbergModularPotentialGreen.area_laplacian_eq_top (radius N f e) (radius_contDiffOn N f e)
    (fun hy => regularized_side N f e hy) (fun hy hxy => regularized_arc N f e hy hxy) hY

/-- Actual source mass density with the inverse regularized amplitude weight. -/
def weightedMassDensity (p : ℝ × ℝ) : ℝ :=
  density N f (ofComplex (point p.1 p.2)) / (p.2 ^ 2 * radius N f e (point p.1 p.2))

/-- Actual nonnegative regularized curvature remainder in planar coordinates. -/
def weightedRemainder (p : ℝ × ℝ) : ℝ :=
  remainder N f e (ofComplex (point p.1 p.2)) / radius N f e (point p.1 p.2)

/-- The actual inverse-radius weighted remainder is nonnegative everywhere. -/
theorem weightedRemainder_nonneg (p : ℝ × ℝ) : 0 ≤ weightedRemainder N f e p :=
  div_nonneg (remainder_nonneg N f e _) (radius_pos N f e _).le

/-- The source curvature equation becomes an exact additive planar identity. -/
theorem weightedRemainder_eq {p : ℝ × ℝ} (hp : 0 < p.2) :
    weightedRemainder N f e p = realLaplacian (radius N f e) (point p.1 p.2) +
      lam * weightedMassDensity N f e p := by
  have h := radius_laplacian_identity N f e (ofComplex (point p.1 p.2))
  have hz : 0 < (point p.1 p.2).im := by simpa [point] using hp
  have him : (ofComplex (point p.1 p.2)).im = p.2 := by
    change (ofComplex (point p.1 p.2) : ℂ).im = p.2
    rw [ofComplex_apply_of_im_pos hz]
    simp [point]
  rw [him] at h
  have hc : ((ofComplex (point p.1 p.2) : ℍ) : ℂ) = point p.1 p.2 := by
    rw [ofComplex_apply_of_im_pos hz]
  rw [hc] at h
  unfold weightedRemainder weightedMassDensity
  have hr := (radius_pos N f e (point p.1 p.2)).ne'
  field_simp
  field_simp at h
  nlinarith

/-- The actual weighted mass is continuous on the compact modular cell. -/
theorem weightedMassDensity_continuousOn (Y : ℝ) :
    ContinuousOn (weightedMassDensity N f e) (cell Y) := by
  have hp : MapsTo (fun p : ℝ × ℝ => point p.1 p.2) (cell Y) {z : ℂ | 0 < z.im} := by
    intro p hp
    have hy := hp.2.1
    change 0 < (point p.1 p.2).im
    simp only [point, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
    linarith
  have hc : Continuous (fun p : ℝ × ℝ => point p.1 p.2) := by unfold point; fun_prop
  apply ((density_contDiffOn N f).continuousOn.comp hc.continuousOn hp).div
    ((continuous_snd.pow 2).continuousOn.mul ((radius_contDiffOn N f e).continuousOn.comp hc.continuousOn hp))
  intro p hp
  exact mul_ne_zero (pow_ne_zero 2 (by have hy := hp.2.1; linarith)) (radius_pos N f e _).ne'

/-- The actual weighted source mass is integrable on standard modular area. -/
theorem weightedMassDensity_integrableOn (Y : ℝ) :
    IntegrableOn (weightedMassDensity N f e) (domain Y) :=
  ((weightedMassDensity_continuousOn N f e Y).mono (domain_subset_cell Y)).integrableOn_compact
    (isCompact_domain Y)

/-- The actual Laplacian is integrable on standard modular area. -/
theorem laplacian_integrableOn (Y : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => realLaplacian (radius N f e) (point p.1 p.2)) (domain Y) :=
  (SelbergModularPotentialGreen.secondAt_integrableOn (radius N f e) (radius_contDiffOn N f e) 1 1 Y).add
    (SelbergModularPotentialGreen.secondAt_integrableOn (radius N f e) (radius_contDiffOn N f e) Complex.I Complex.I Y)

/-- The retained remainder is genuinely integrable on standard modular area. -/
theorem weightedRemainder_integrableOn (Y : ℝ) :
    IntegrableOn (weightedRemainder N f e) (domain Y) := by
  apply ((laplacian_integrableOn N f e Y).add
    ((weightedMassDensity_integrableOn N f e Y).const_mul lam)).congr_fun
    ?_ (isCompact_domain Y).measurableSet
  intro p hp
  have hc := domain_subset_cell Y hp
  exact (weightedRemainder_eq N f e (by linarith [hc.2.1])).symm

/-- Integrating the actual curvature equation retains the full top current. -/
theorem weighted_remainder_balance {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, weightedRemainder N f e p) =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), regularizedCurrent N f e Complex.I x Y) +
        lam * ∫ p in domain Y, weightedMassDensity N f e p := by
  calc
    _ = ∫ p in domain Y, realLaplacian (radius N f e) (point p.1 p.2) +
        lam * weightedMassDensity N f e p := by
      apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
      intro p hp
      have hc := domain_subset_cell Y hp
      exact weightedRemainder_eq N f e (by linarith [hc.2.1])
    _ = _ := by
      rw [integral_add (laplacian_integrableOn N f e Y)
        ((weightedMassDensity_integrableOn N f e Y).const_mul lam),
        integral_const_mul, regularized_area_stokes N f e hY]

/-- A proved weighted source inequality, with the top flux retained explicitly. -/
theorem weighted_mass_flux_nonneg {Y : ℝ} (hY : 1 ≤ Y) :
    0 ≤ (∫ x in (-(1 / 2 : ℝ))..(1 / 2), regularizedCurrent N f e Complex.I x Y) +
      lam * ∫ p in domain Y, weightedMassDensity N f e p := by
  rw [← weighted_remainder_balance N f e hY]
  exact integral_nonneg (weightedRemainder_nonneg N f e)

end
end GaloisForLFunctions.RHTower.SelbergMaassRegularizedArea
