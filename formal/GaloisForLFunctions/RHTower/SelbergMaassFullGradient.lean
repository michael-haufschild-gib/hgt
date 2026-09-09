import GaloisForLFunctions.RHTower.SelbergMaassCellCurvature
import GaloisForLFunctions.RHTower.SelbergMaassCurvatureCovariance

/-!
# Full physical Maass gradient on the modular cell

The original trace PDE and actual Mobius Laplacian pullback prove invariance
of the hyperbolic gradient density. Truncated source Stokes, established cusp
flux decay, and monotone domain exhaustion then prove full gradient
integrability and the exact eigenvalue-times-mass identity. Original source
nonvanishing supplies strictly positive complete-cell mass and energy.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassFullGradient
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassTraceArea
  SelbergMaassTraceMass SelbergMaassFullCurvatureBudget SelbergMaassCellCurvature
  SelbergMaassMean SelbergModularDomainSlices SelbergMaassCurvatureCovariance
  SelbergMaassCuspTransport SelbergMaassCuspDecay
noncomputable section

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

private theorem complex_density_laplacian (z : ℍ) :
    positiveHyperbolicLaplacian (fun w : ℍ => (density N f w : ℂ)) z =
      (-(z.im ^ 2 * realLaplacian (density N f ∘ ofComplex) (z : ℂ)) : ℝ) := by
  change -(z.im : ℂ) ^ 2 * GaloisForLFunctions.HTGeometry.ComplexC2Laplacian.laplacian
    (fun w : ℂ => (density N f (ofComplex w) : ℂ)) (z : ℂ) = _
  have he := laplacian_ofReal ((density_contDiffOn N f).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos))
  simp only [Function.comp_def] at he
  rw [he]
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow, neg_mul, Function.comp_def]

/-- The hyperbolic Laplacian of the literal congruence trace is modular invariant. -/
theorem density_laplacian_invariant (A : SL2Z) (z : ℍ) :
    (A • z : ℍ).im ^ 2 * realLaplacian (density N f ∘ ofComplex) (A • z : ℍ) =
      z.im ^ 2 * realLaplacian (density N f ∘ ofComplex) (z : ℂ) := by
  have hs : IsRealSmoothUpperHalfPlane (fun w : ℍ => (density N f w : ℂ)) :=
    Complex.ofRealCLM.contDiff.fun_comp_contDiffOn (density_contDiffOn N f)
  have h := positive_laplacian_pullback A (fun w : ℍ => (density N f w : ℂ)) hs z
  have he : (fun w : ℍ => (density N f (A • w) : ℂ)) =
      (fun w : ℍ => (density N f w : ℂ)) := by
    funext w
    rw [density_invariant]
  rw [he, complex_density_laplacian, complex_density_laplacian] at h
  exact neg_injective (Complex.ofReal_injective h.symm)

/-- Actual full gradient energy density relative to hyperbolic volume. -/
def hyperbolicGradient (z : ℍ) : ℝ := z.im ^ 2 * gradientDensity N f (z : ℂ)

/-- The original trace equation expresses energy through its actual Laplacian and mass. -/
theorem hyperbolicGradient_eq (z : ℍ) :
    hyperbolicGradient N f z =
      (1 / 2) * z.im ^ 2 * realLaplacian (density N f ∘ ofComplex) (z : ℂ) +
        lam * density N f z := by
  rw [hyperbolicGradient, trace_laplacian]
  field_simp [z.im_pos.ne']
  ring

/-- The actual full source gradient energy is modular invariant. -/
theorem hyperbolicGradient_invariant (A : SL2Z) (z : ℍ) :
    hyperbolicGradient N f (A • z) = hyperbolicGradient N f z := by
  simp only [hyperbolicGradient_eq, mul_assoc, density_laplacian_invariant, density_invariant]

/-- Every physical squared derivative contributes nonnegative energy. -/
theorem hyperbolicGradient_nonneg (z : ℍ) : 0 ≤ hyperbolicGradient N f z :=
  mul_nonneg (sq_nonneg _) (gradientDensity_nonneg N f _)

/-- Actual planar gradient density in the real chart. -/
def planarGradient (p : ℝ × ℝ) : ℝ := gradientDensity N f (point p.1 p.2)

/-- The trace PDE gives the original planar gradient without extra regularity assumptions. -/
theorem planarGradient_eq {p : ℝ × ℝ} (hp : 0 < p.2) :
    planarGradient N f p =
      (1 / 2) * realLaplacian (density N f ∘ ofComplex) (point p.1 p.2) +
        lam * massDensity N f p := by
  let z : ℍ := ⟨point p.1 p.2, by simpa [point] using hp⟩
  have h := trace_laplacian N f z
  have hz : z.im = p.2 := by simp [z, UpperHalfPlane.im, point]
  have hc : ofComplex (point p.1 p.2) = z := by
    exact ofComplex_apply_of_im_pos z.im_pos
  rw [hz] at h
  change planarGradient N f p = _
  dsimp only [planarGradient, massDensity]
  rw [hc]
  change gradientDensity N f (z : ℂ) =
    (1 / 2) * realLaplacian (density N f ∘ ofComplex) (z : ℂ) + lam * (density N f z / p.2 ^ 2)
  rw [h]
  ring

/-- Actual gradient energy is integrable on every truncated modular core. -/
theorem core_gradient_integrable (Y : ℝ) : IntegrableOn (planarGradient N f) (domain Y) := by
  have hl : IntegrableOn (fun p : ℝ × ℝ =>
      realLaplacian (density N f ∘ ofComplex) (point p.1 p.2)) (domain Y) :=
    (secondAt_integrableOn N f 1 1 Y).add (secondAt_integrableOn N f Complex.I Complex.I Y)
  have hm : IntegrableOn (massDensity N f) (domain Y) := core_mass_integrable N f Y
  apply ((hl.const_mul (1 / 2)).add (hm.const_mul lam)).congr
  filter_upwards [ae_restrict_mem (isCompact_domain Y).measurableSet] with p hp
  exact (planarGradient_eq N f (fullDomain_height_pos (domain_subset_full Y hp))).symm

/-- Source Stokes identifies truncated full gradient energy, including the actual cusp flux. -/
theorem core_gradient_identity {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ p in domain Y, planarGradient N f p) =
      (∑ q : Deck N, SelbergMaassFlux.flux N (quotientForm N f q) Y) +
        lam * coreMass N f Y := by
  have hl : IntegrableOn (fun p : ℝ × ℝ =>
      realLaplacian (density N f ∘ ofComplex) (point p.1 p.2)) (domain Y) :=
    (secondAt_integrableOn N f 1 1 Y).add (secondAt_integrableOn N f Complex.I Complex.I Y)
  have hm : IntegrableOn (massDensity N f) (domain Y) := core_mass_integrable N f Y
  have he := setIntegral_congr_fun (μ := volume) (isCompact_domain Y).measurableSet
    (fun p hp => planarGradient_eq N f (fullDomain_height_pos (domain_subset_full Y hp)))
  rw [he, integral_add (hl.const_mul (1 / 2)) (hm.const_mul lam),
    integral_const_mul, integral_const_mul, area_stokes_flux N f hY]
  change (1 / 2) * (2 * _) + lam * coreMass N f Y = _
  ring

section Exceptional
variable (lam : Ioo (0 : ℝ) (1 / 4))
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

/-- Proved cusp flux decay fixes the actual limit of truncated energy. -/
theorem core_gradient_limit :
    Tendsto (fun Y => ∫ p in domain Y, planarGradient N f p) atTop
      (𝓝 ((lam : ℝ) * ∫ p in fullDomain, massDensity N f p)) := by
  have hf := tendsto_finsetSum Finset.univ
    (fun q (_ : q ∈ Finset.univ) => flux_decay N lam (quotientForm N f q))
  have hm := (full_integral_tendsto (full_mass_integrable N lam f)).const_mul (lam : ℝ)
  have ht := hf.add hm
  simp only [Finset.sum_const_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  exact (core_gradient_identity N f hY).symm

/-- Exhaustion and the actual source limit prove full-domain gradient integrability. -/
theorem full_gradient_integrable : IntegrableOn (planarGradient N f) fullDomain := by
  apply domain_aecover.integrable_of_integral_tendsto_of_nonneg_ae
    ((lam : ℝ) * ∫ p in fullDomain, massDensity N f p)
  · intro Y
    simpa only [IntegrableOn, full_restrict_domain] using core_gradient_integrable N f Y
  · exact Eventually.of_forall (fun p => gradientDensity_nonneg N f _)
  · simpa only [full_restrict_domain] using core_gradient_limit N lam f

/-- The original full energy equals eigenvalue times full mass, with no terminal-flux premise. -/
theorem full_gradient_identity :
    (∫ p in fullDomain, planarGradient N f p) =
      (lam : ℝ) * ∫ p in fullDomain, massDensity N f p :=
  tendsto_nhds_unique (full_integral_tendsto (full_gradient_integrable N lam f))
    (core_gradient_limit N lam f)

/-- Original nonvanishing supplies positive mass on the complete modular cell. -/
theorem full_mass_pos : 0 < ∫ p in fullDomain, massDensity N f p := by
  obtain ⟨Y, _, hY⟩ := exists_coreMass_pos N f
  exact hY.trans_le (setIntegral_mono_set (full_mass_integrable N lam f)
    (Eventually.of_forall (massDensity_nonneg N f))
    (Eventually.of_forall (domain_subset_full Y)))

/-- The literal hyperbolic cell energy retains the exact positive source budget. -/
theorem cell_gradient_identity :
    (∫ z : ℍ in fd, hyperbolicGradient N f z) =
      (lam : ℝ) * ∫ p in fullDomain, massDensity N f p := by
  have he : (∫ z : ℍ in fd, hyperbolicGradient N f z) =
      ∫ p in fullDomain, planarGradient N f p := by
    convert integral_height_sq_cell (planarGradient N f) using 1
    congr 1
    funext z
    simp only [hyperbolicGradient, planarGradient]
    rw [show point z.re z.im = (z : ℂ) from Complex.re_add_im (z : ℂ)]
  rw [he, full_gradient_identity]

/-- The actual full-cell energy is positive. -/
theorem cell_gradient_pos : 0 < ∫ z : ℍ in fd, hyperbolicGradient N f z := by
  rw [cell_gradient_identity]
  exact mul_pos lam.2.1 (full_mass_pos N lam f)

/-- Positivity and the exact integral discharge full-cell hyperbolic integrability. -/
theorem cell_gradient_integrable : IntegrableOn (hyperbolicGradient N f) fd :=
  Integrable.of_integral_ne_zero (cell_gradient_pos N lam f).ne'

end Exceptional
end
end GaloisForLFunctions.RHTower.SelbergMaassFullGradient
