import GaloisForLFunctions.RHTower.SelbergModularPotentialGreen

/-!
# Actual modular-core Green theorem and full Maass quarter form

The core uses standard two-dimensional Lebesgue measure on the truncated modular
domain. Actual C² trace regularity supplies integrability; both Fubini slice orders,
FTC, translation, circular substitution, and inversion cancel the side and arc
currents. The remaining top is the actual congruence-normalized cusp flux.

Integrating the pointwise source identity and adjoining the previously proved cusp
Bessel decomposition gives the exact core-plus-cusp quarter form. All terms come
from the original Maass eigenform; there is no assumed core operator or positivity
certificate. The missing lower bound on the combined core and Bessel boundary
form, and hence Selberg's conjecture, are not proved here.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassTraceArea
open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy
  SelbergMaassTraceBoundary SelbergMaassTraceStokes SelbergModularDomainSlices
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The actual second trace derivative in standard planar coordinates. -/
def secondAt (v w : ℂ) (p : ℝ × ℝ) : ℝ :=
  dir v (dir w (density N f ∘ ofComplex)) (point p.1 p.2)

/-- Actual C² source regularity gives joint continuity on every compact cell. -/
theorem secondAt_continuousOn (v w : ℂ) (Y : ℝ) :
    ContinuousOn (secondAt N f v w) (cell Y) := by
  apply (trace_second_dir_continuousOn N f v w).comp
    (show Continuous (fun p : ℝ × ℝ => point p.1 p.2) by unfold point; fun_prop).continuousOn
  intro p hp
  have hy := hp.2.1
  change 0 < (point p.1 p.2).im
  simp only [point, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  linarith

/-- The actual second trace derivative is integrable for standard domain area measure. -/
theorem secondAt_integrableOn (v w : ℂ) (Y : ℝ) :
    IntegrableOn (secondAt N f v w) (domain Y) :=
  ((secondAt_continuousOn N f v w Y).mono (domain_subset_cell Y)).integrableOn_compact
    (isCompact_domain Y)

/-- The actual first trace current restricts continuously to the circular boundary. -/
theorem current_arc_continuousOn (v : ℂ) :
    ContinuousOn (fun x => currentAt N f v x (arcHeight x))
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  apply (trace_dir_contDiffOn N f v).continuousOn.comp
    (show Continuous (fun x => point x (arcHeight x)) by
      unfold point; exact Complex.continuous_ofReal.add ((Complex.continuous_ofReal.comp continuous_arcHeight).mul continuous_const)).continuousOn
  intro x hx
  change 0 < (point x (arcHeight x)).im
  simpa [point] using arcHeight_pos hx

/-- Horizontal Fubini, side FTC, and the exact circular substitution identify the area term. -/
theorem horizontal_area_eq_arc {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, secondAt N f 1 1 p) =
      ∫ x in (0 : ℝ)..(1 / 2), x / arcHeight x *
        (currentAt N f 1 (-x) (arcHeight x) - currentAt N f 1 x (arcHeight x)) := by
  exact SelbergModularPotentialGreen.horizontal_area_eq_arc
    (density N f ∘ ofComplex) (density_contDiffOn N f)
    (fun hy => currentAt_side_cancellation N f hy) hY

/-- Inversion turns the horizontal area term into the full lower vertical current. -/
theorem horizontal_area_eq_bottom {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, secondAt N f 1 1 p) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt N f Complex.I x (arcHeight x) := by
  exact SelbergModularPotentialGreen.horizontal_area_eq_bottom
    (density N f ∘ ofComplex) (density_contDiffOn N f)
    (fun hy => currentAt_side_cancellation N f hy)
    (fun hy hxy => currentAt_arc_cancellation N f hy hxy) hY

/-- Vertical Fubini and actual FTC retain both the top and circular boundary terms. -/
theorem vertical_area_eq_top_sub_bottom {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, secondAt N f Complex.I Complex.I p) =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt N f Complex.I x Y) -
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2), currentAt N f Complex.I x (arcHeight x) := by
  exact SelbergModularPotentialGreen.vertical_area_eq_top_sub_bottom
    (density N f ∘ ofComplex) (density_contDiffOn N f) hY

/-- The standard two-dimensional trace Laplacian integral equals twice the actual cusp flux. -/
theorem area_stokes_flux {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, realLaplacian (density N f ∘ ofComplex) (point p.1 p.2)) =
      2 * ∑ q : Deck N, SelbergMaassFlux.flux N (quotientForm N f q) Y := by
  change (∫ p in domain Y, secondAt N f 1 1 p + secondAt N f Complex.I Complex.I p) = _
  rw [integral_add (secondAt_integrableOn N f 1 1 Y) (secondAt_integrableOn N f Complex.I Complex.I Y),
    horizontal_area_eq_bottom N f hY, vertical_area_eq_top_sub_bottom N f hY]
  rw [← add_sub_assoc, add_sub_cancel_left]
  have hy : 0 < Y := by linarith
  have hp := (currentAt_periodic N f Complex.I hy).intervalIntegral_add_eq (-(1 / 2)) 0
  norm_num at hp
  rw [hp, unit_current_eq_sum_flux N f hy]

/-- Actual core hyperbolic trace mass with standard two-dimensional area measure. -/
def coreMass (Y : ℝ) : ℝ :=
  ∫ p in domain Y, density N f (ofComplex (point p.1 p.2)) / p.2 ^ (2 : ℕ)

/-- Actual core gradient energy minus one quarter of its hyperbolic trace mass. -/
def coreQuarter (Y : ℝ) : ℝ :=
  ∫ p in domain Y, quarterDensity N f (ofComplex (point p.1 p.2))

/-- The actual hyperbolic trace density is integrable on every compact core. -/
theorem core_mass_integrable (Y : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => density N f (ofComplex (point p.1 p.2)) / p.2 ^ (2 : ℕ))
      (domain Y) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => density N f (ofComplex (point p.1 p.2))) (cell Y) := by
    apply (density_contDiffOn N f).continuousOn.comp
      (show Continuous (fun p : ℝ × ℝ => point p.1 p.2) by unfold point; fun_prop).continuousOn
    intro p hp
    change 0 < (point p.1 p.2).im
    have hy := hp.2.1
    simp only [point, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
    linarith
  apply ContinuousOn.integrableOn_compact (isCompact_domain Y)
  apply (hc.div₀ (continuous_snd.pow 2).continuousOn (fun p hp => ?_)).mono (domain_subset_cell Y)
  apply pow_ne_zero 2
  have hy := hp.2.1
  linarith

/-- Actual core quarter energy equals the outgoing flux plus its exact spectral mass correction. -/
theorem core_quarter_identity {Y : ℝ} (hY : 1 ≤ Y) :
    coreQuarter N f Y = (∑ q : Deck N, SelbergMaassFlux.flux N (quotientForm N f q) Y) +
      (lam - 1 / 4) * coreMass N f Y := by
  have he : coreQuarter N f Y =
      ∫ p in domain Y, (1 / 2) * realLaplacian (density N f ∘ ofComplex) (point p.1 p.2) +
        (lam - 1 / 4) * (density N f (ofComplex (point p.1 p.2)) / p.2 ^ (2 : ℕ)) := by
    unfold coreQuarter
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro p hp
    have hy : 0 < p.2 := by have h := hp.1.2.1; linarith
    have hc : (ofComplex (point p.1 p.2) : ℂ) = point p.1 p.2 := by
      rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]
    have hi : (ofComplex (point p.1 p.2)).im = p.2 := by
      change (ofComplex (point p.1 p.2) : ℂ).im = p.2
      rw [hc]
      simp [point]
    dsimp only
    rw [quarterDensity_eq_laplacian_mass N f, hc, hi]
    ring
  have hl : IntegrableOn (fun p : ℝ × ℝ => realLaplacian (density N f ∘ ofComplex) (point p.1 p.2))
      (domain Y) := (secondAt_integrableOn N f 1 1 Y).add (secondAt_integrableOn N f Complex.I Complex.I Y)
  rw [he, integral_add (hl.const_mul (1 / 2)) ((core_mass_integrable N f Y).const_mul (lam - 1 / 4)),
    integral_const_mul, integral_const_mul, area_stokes_flux N f hY]
  change (1 / 2) * (2 * _) + (lam - 1 / 4) * coreMass N f Y = _
  ring

/-- The actual core hyperbolic trace mass is nonnegative. -/
theorem coreMass_nonneg (Y : ℝ) : 0 ≤ coreMass N f Y :=
  integral_nonneg (fun p => div_nonneg (density_nonneg N f (ofComplex (point p.1 p.2))) (sq_nonneg p.2))


/-- The earlier paired-coordinate divergence integral equals the standard two-dimensional area integral. -/
theorem area_eq_pairedBulk {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, realLaplacian (density N f ∘ ofComplex) (point p.1 p.2)) =
      pairedBulk N f Y := by
  rw [area_stokes_flux N f hY, paired_stokes_flux N f (by linarith)]


/-- Exact full actual core-plus-cusp quarter form, with the complete nonnegative Fourier square remainder. -/
theorem core_cusp_quarter_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    coreQuarter N f (Real.exp T) + boundarySum N f T + squareSum N f T =
      ((lam : ℝ) - 1 / 4) * (coreMass N f (Real.exp T) + tailMass N f (Real.exp T)) := by
  rw [core_quarter_identity N f (Real.one_le_exp hT)]
  have h := trace_flux_boundary_identity N lam f T
  linear_combination -h

/-- The nonnegative square remainder gives an upper bound for the actual combined core and Bessel form. -/
theorem core_boundary_upper_bound (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (T : ℝ) (hT : 0 ≤ T) :
    coreQuarter N f (Real.exp T) + boundarySum N f T ≤
      ((lam : ℝ) - 1 / 4) * (coreMass N f (Real.exp T) + tailMass N f (Real.exp T)) := by
  rw [← core_cusp_quarter_identity N lam f T hT]
  exact le_add_of_nonneg_right (squareSum_nonneg N f T)

end
end GaloisForLFunctions.RHTower.SelbergMaassTraceArea
