import GaloisForLFunctions.RHTower.SelbergMaassRegularizedCusp
import GaloisForLFunctions.RHTower.SelbergMaassTraceMass
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Full standard-area curvature budget of the actual Maass source

The truncated modular domains exhaust the literal full domain. Original source
mass controls the inverse-radius weighted mass at each fixed positive regulator.
The proved cusp-current limit and nonnegative retained remainder give genuine
full-domain integrability and the exact budget

  integral R_e/rho_e = lambda * integral D/(y²*rho_e).

Original source nonvanishing makes both sides strictly positive in the exceptional
interval. The full radius Laplacian is integrable and has zero integral. No
regulator-limit interchange or quarter lower bound is asserted.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget
open SelbergMaassMean SelbergMaassCongruenceTrace SelbergMaassTraceEnergy
  SelbergMaassTraceRegularized SelbergMaassRegularizedArea SelbergMaassRegularizedCusp
  SelbergMaassTraceStokes SelbergModularDomainSlices SelbergMaassTraceMass SelbergMaassTraceArea
noncomputable section

/-- Literal full modular domain in real planar coordinates, including its boundary. -/
def fullDomain : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ arcHeight p.1 ≤ p.2}

/-- The actual full modular domain is measurable. -/
theorem fullDomain_measurable : MeasurableSet fullDomain := by
  exact ((isClosed_Icc.preimage continuous_fst).inter
    (isClosed_le (continuous_arcHeight.comp continuous_fst) continuous_snd)).measurableSet

/-- Every compact truncated domain lies in the full modular domain. -/
theorem domain_subset_full (Y : ℝ) : domain Y ⊆ fullDomain :=
  fun _ hp => ⟨hp.1.1, hp.2⟩

/-- Every point of the full modular domain has positive height. -/
theorem fullDomain_height_pos {p : ℝ × ℝ} (hp : p ∈ fullDomain) : 0 < p.2 :=
  (arcHeight_pos hp.1).trans_le hp.2

/-- Restricting full-domain area again to a truncated domain recovers its original area. -/
theorem full_restrict_domain (Y : ℝ) :
    (volume.restrict fullDomain).restrict (domain Y) = volume.restrict (domain Y) := by
  rw [Measure.restrict_restrict (isCompact_domain Y).measurableSet,
    inter_eq_left.mpr (domain_subset_full Y)]

/-- The actual truncated modular domains exhaust full-domain area at infinite height. -/
theorem domain_aecover : AECover (volume.restrict fullDomain) atTop domain where
  measurableSet Y := (isCompact_domain Y).measurableSet
  ae_eventually_mem := by
    filter_upwards [ae_restrict_mem fullDomain_measurable] with p hp
    filter_upwards [eventually_ge_atTop p.2] with Y hY
    exact ⟨⟨hp.1, (arcHeight_half_le hp.1).trans hp.2, hY⟩, hp.2⟩

/-- Every integrable full-domain source is the limit of its actual truncated integrals. -/
theorem full_integral_tendsto {F : ℝ × ℝ → ℝ} (hi : IntegrableOn F fullDomain) :
    Tendsto (fun Y => ∫ p in domain Y, F p) atTop (𝓝 (∫ p in fullDomain, F p)) := by
  simpa only [full_restrict_domain] using domain_aecover.integral_tendsto_of_countably_generated hi

/-- A uniform eventual truncated integral bound proves full-domain integrability for a nonnegative source. -/
theorem full_integrable_of_nonneg_bound {F : ℝ × ℝ → ℝ} (hi : ∀ Y, IntegrableOn F (domain Y))
    (hn : ∀ p, 0 ≤ F p) {B : ℝ} (hb : ∀ᶠ Y in atTop, (∫ p in domain Y, F p) ≤ B) :
    IntegrableOn F fullDomain := by
  apply domain_aecover.integrable_of_integral_bounded_of_nonneg_ae B
    (fun Y => by simpa only [IntegrableOn, full_restrict_domain] using hi Y)
    (Eventually.of_forall hn)
  simpa only [full_restrict_domain] using hb

variable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (e : Ioi (0 : ℝ))

/-- Original cusp mass control proves integrability of actual hyperbolic trace mass on the full domain. -/
theorem full_mass_integrable : IntegrableOn (massDensity N f) fullDomain := by
  apply full_integrable_of_nonneg_bound (fun Y => core_mass_integrable N f Y)
    (massDensity_nonneg N f) (B := coreMass N f 1 + tailMass N f 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  have h := totalMass_eq_one N lam f hY
  have hn := tailMass_nonneg N f Y
  change coreMass N f Y ≤ _
  linarith

/-- The actual positive regularized radius bounds its regulator from below. -/
theorem regulator_le_radius (z : ℂ) : (e : ℝ) ≤ radius N f e z := by
  have hs := radius_sq N f e z
  have hr := radius_pos N f e z
  have he : 0 < (e : ℝ) := e.2
  nlinarith [density_nonneg N f (ofComplex z)]

/-- The literal inverse-radius weighted source mass is nonnegative. -/
theorem weightedMassDensity_nonneg (p : ℝ × ℝ) : 0 ≤ weightedMassDensity N f e p :=
  div_nonneg (density_nonneg N f _) (mul_nonneg (sq_nonneg _) (radius_pos N f e _).le)

/-- At fixed positive regulator, weighted mass is bounded by original mass divided by the regulator. -/
theorem weightedMassDensity_le_mass (p : ℝ × ℝ) :
    weightedMassDensity N f e p ≤ massDensity N f p / (e : ℝ) := by
  rw [weightedMassDensity, massDensity, ← div_div]
  exact div_le_div_of_nonneg_left (div_nonneg (density_nonneg N f _) (sq_nonneg _)) e.2
    (regulator_le_radius N lam f e _)

/-- The actual inverse-radius weighted spectral mass is integrable on the full modular domain. -/
theorem full_weightedMass_integrable : IntegrableOn (weightedMassDensity N f e) fullDomain := by
  apply full_integrable_of_nonneg_bound (weightedMassDensity_integrableOn N f e)
    (weightedMassDensity_nonneg N lam f e) (B := (coreMass N f 1 + tailMass N f 1) / (e : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  calc
    (∫ p in domain Y, weightedMassDensity N f e p) ≤ ∫ p in domain Y, massDensity N f p / (e : ℝ) :=
      integral_mono (weightedMassDensity_integrableOn N f e Y)
        ((core_mass_integrable N f Y).div_const (e : ℝ)) (weightedMassDensity_le_mass N lam f e)
    _ = coreMass N f Y / (e : ℝ) := by rw [integral_div]; rfl
    _ ≤ (coreMass N f 1 + tailMass N f 1) / (e : ℝ) := by
      apply div_le_div_of_nonneg_right ?_ e.2.le
      have h := totalMass_eq_one N lam f hY
      linarith [tailMass_nonneg N f Y]

/-- Source Stokes and the proved top-current limit give the finite limit of truncated retained curvature. -/
theorem truncated_remainder_limit :
    Tendsto (fun Y => ∫ p in domain Y, weightedRemainder N f e p) atTop
      (𝓝 ((lam : ℝ) * ∫ p in fullDomain, weightedMassDensity N f e p)) := by
  have h := (top_current_limit N f e).add
    ((full_integral_tendsto (full_weightedMass_integrable N lam f e)).const_mul (lam : ℝ))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  exact (weighted_remainder_balance N f e hY).symm

/-- Nonnegativity and the actual truncated limit prove full-domain integrability of the retained curvature. -/
theorem full_weightedRemainder_integrable : IntegrableOn (weightedRemainder N f e) fullDomain := by
  apply domain_aecover.integrable_of_integral_tendsto_of_nonneg_ae
    ((lam : ℝ) * ∫ p in fullDomain, weightedMassDensity N f e p)
    (fun Y => by simpa only [IntegrableOn, full_restrict_domain] using weightedRemainder_integrableOn N f e Y)
    (Eventually.of_forall (weightedRemainder_nonneg N f e))
  simpa only [full_restrict_domain] using truncated_remainder_limit N lam f e

/-- Exact full standard-area retained-curvature budget, with every source and boundary condition proved. -/
theorem full_curvature_budget :
    (∫ p in fullDomain, weightedRemainder N f e p) =
      (lam : ℝ) * ∫ p in fullDomain, weightedMassDensity N f e p :=
  tendsto_nhds_unique (full_integral_tendsto (full_weightedRemainder_integrable N lam f e))
    (truncated_remainder_limit N lam f e)

/-- The actual regularized radius Laplacian is integrable on the full domain. -/
theorem full_laplacian_integrable :
    IntegrableOn (fun p : ℝ × ℝ => realLaplacian (radius N f e) (point p.1 p.2)) fullDomain := by
  apply ((full_weightedRemainder_integrable N lam f e).sub
    ((full_weightedMass_integrable N lam f e).const_mul (lam : ℝ))).congr_fun
    ?_ fullDomain_measurable
  intro p hp
  simp only [Pi.sub_apply]
  rw [weightedRemainder_eq N f e (fullDomain_height_pos hp)]
  ring

/-- The full standard-area Laplacian integral vanishes by the proved cusp-current limit. -/
theorem full_laplacian_integral_zero :
    (∫ p in fullDomain, realLaplacian (radius N f e) (point p.1 p.2)) = 0 := by
  apply tendsto_nhds_unique (full_integral_tendsto (full_laplacian_integrable N lam f e))
  apply (top_current_limit N f e).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  exact (regularized_area_stokes N f e hY).symm

/-- Original nonvanishing forces strictly positive full-domain inverse-radius weighted mass. -/
theorem full_weightedMass_pos : 0 < ∫ p in fullDomain, weightedMassDensity N f e p := by
  obtain ⟨Y, _, hY⟩ := exists_coreMass_pos N f
  have hs : 0 < volume (Function.support (massDensity N f) ∩ domain Y) :=
    (setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall (massDensity_nonneg N f))
      (show IntegrableOn (massDensity N f) (domain Y) volume from core_mass_integrable N f Y)).mp hY
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (weightedMassDensity_nonneg N lam f e))
    (full_weightedMass_integrable N lam f e)).mpr
  apply lt_of_lt_of_le hs (measure_mono ?_)
  rintro p ⟨hm, hd⟩
  refine ⟨?_, domain_subset_full Y hd⟩
  change weightedMassDensity N f e p ≠ 0
  have he : weightedMassDensity N f e p = massDensity N f p / radius N f e (point p.1 p.2) := by
    unfold weightedMassDensity massDensity
    rw [div_div]
  rw [he]
  exact div_ne_zero hm (radius_pos N f e _).ne'

/-- Every hypothetical exceptional source has strictly positive full-domain retained curvature. -/
theorem full_weightedRemainder_pos : 0 < ∫ p in fullDomain, weightedRemainder N f e p := by
  rw [full_curvature_budget N lam f e]
  exact mul_pos lam.2.1 (full_weightedMass_pos N lam f e)

end
end GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget
