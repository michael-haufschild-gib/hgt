import GaloisForLFunctions.RHTower.SelbergModularHyperbolicArea
import GaloisForLFunctions.RHTower.SelbergSquareRootRegularizationError

/-!
# Quantitative regulator removal in the actual full curvature budget

Actual finite hyperbolic area and original source mass prove full integrability
of sqrt(D)/y². The uniform scalar error e/2 gives L¹ spectral-weight error at most
e on the modular domain. The actual total retained curvature therefore converges
monotonically to lambda times the strictly positive amplitude mass, with error
at most lambda*e. No integral of a pointwise curvature limit is substituted.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergMaassRegulatorMass
open SelbergMaassMean SelbergMaassCongruenceTrace SelbergMaassTraceRegularized
  SelbergMaassRegularizedArea SelbergMaassFullCurvatureBudget SelbergModularHyperbolicArea
  SelbergMaassTraceMass SelbergSquareRootRegularizationError
noncomputable section

variable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

/-- Actual square-root trace mass with the literal hyperbolic area weight. -/
def amplitudeMassDensity (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (density N f (ofComplex (point p.1 p.2))) / p.2 ^ (2 : ℕ)

/-- The actual amplitude mass density is everywhere nonnegative. -/
theorem amplitudeMassDensity_nonneg (p : ℝ × ℝ) : 0 ≤ amplitudeMassDensity N lam f p :=
  div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)

/-- Original source regularity gives amplitude-mass continuity at every positive-height point. -/
theorem amplitudeMassDensity_continuousAt {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (amplitudeMassDensity N lam f) p := by
  have hz : 0 < (point p.1 p.2).im := by simpa [point] using hp
  have hc := ((density_contDiffOn N f).continuousOn.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).comp (f := fun q : ℝ × ℝ => point q.1 q.2)
      (show Continuous (fun q : ℝ × ℝ => point q.1 q.2) by unfold point; fun_prop).continuousAt
  exact hc.sqrt.div ((continuous_snd.pow 2).continuousAt) (pow_ne_zero 2 hp.ne')

/-- Original trace mass plus hyperbolic area dominates the actual amplitude mass. -/
theorem amplitudeMassDensity_le_mass_majorant (p : ℝ × ℝ) :
    amplitudeMassDensity N lam f p ≤ (massDensity N f p + 1 / p.2 ^ (2 : ℕ)) / 2 := by
  have hd := density_nonneg N f (ofComplex (point p.1 p.2))
  have hs := Real.sq_sqrt hd
  have h : Real.sqrt (density N f (ofComplex (point p.1 p.2))) ≤
      (density N f (ofComplex (point p.1 p.2)) + 1) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (density N f (ofComplex (point p.1 p.2))) - 1)]
  have hh := div_le_div_of_nonneg_right h (sq_nonneg p.2)
  unfold amplitudeMassDensity massDensity
  calc
    _ ≤ (density N f (ofComplex (point p.1 p.2)) + 1) / 2 / p.2 ^ (2 : ℕ) := hh
    _ = _ := by ring

/-- Actual full-domain amplitude mass is integrable without a regulator. -/
theorem full_amplitudeMass_integrable : IntegrableOn (amplitudeMassDensity N lam f) fullDomain := by
  have hc : ContinuousOn (amplitudeMassDensity N lam f) fullDomain :=
    fun p hp => (amplitudeMassDensity_continuousAt N lam f (fullDomain_height_pos hp)).continuousWithinAt
  apply (((full_mass_integrable N lam f).add full_weight_integrable).div_const 2).mono'
    (hc.aestronglyMeasurable fullDomain_measurable)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (amplitudeMassDensity_nonneg N lam f p)]
  exact amplitudeMassDensity_le_mass_majorant N lam f p

variable (e : Ioi (0 : ℝ))

/-- One actual integrable amplitude density dominates every positive-regulator spectral weight. -/
theorem weightedMassDensity_le_amplitude (p : ℝ × ℝ) :
    weightedMassDensity N f e p ≤ amplitudeMassDensity N lam f p := by
  unfold weightedMassDensity amplitudeMassDensity radius
  rw [mul_comm (p.2 ^ (2 : ℕ)), ← div_div]
  exact div_le_div_of_nonneg_right (weighted_sqrt_le (density_nonneg N f _) e.2) (sq_nonneg p.2)

/-- The actual pointwise weighted spectral error is bounded by half the regulator times hyperbolic density. -/
theorem amplitude_error_le (p : ℝ × ℝ) :
    amplitudeMassDensity N lam f p - weightedMassDensity N f e p ≤ (e : ℝ) / 2 * (1 / p.2 ^ (2 : ℕ)) := by
  have h := div_le_div_of_nonneg_right
    (weighted_sqrt_error_le_half (density_nonneg N f (ofComplex (point p.1 p.2))) e.2) (sq_nonneg p.2)
  unfold amplitudeMassDensity weightedMassDensity radius
  calc
    _ = (Real.sqrt (density N f (ofComplex (point p.1 p.2))) -
        density N f (ofComplex (point p.1 p.2)) / Real.sqrt (density N f (ofComplex (point p.1 p.2)) + (e : ℝ) ^ (2 : ℕ))) / p.2 ^ (2 : ℕ) := by ring
    _ ≤ (e : ℝ) / 2 / p.2 ^ (2 : ℕ) := h
    _ = _ := by ring

/-- Actual full weighted spectral mass lies below full amplitude mass. -/
theorem full_mass_error_nonneg :
    0 ≤ (∫ p in fullDomain, amplitudeMassDensity N lam f p) -
      ∫ p in fullDomain, weightedMassDensity N f e p := by
  apply sub_nonneg.mpr
  exact integral_mono (full_weightedMass_integrable N lam f e) (full_amplitudeMass_integrable N lam f)
    (weightedMassDensity_le_amplitude N lam f e)

/-- The full actual spectral mass error is bounded by the regulator itself. -/
theorem full_mass_error_le_regulator :
    (∫ p in fullDomain, amplitudeMassDensity N lam f p) -
      (∫ p in fullDomain, weightedMassDensity N f e p) ≤ (e : ℝ) := by
  rw [← integral_sub (full_amplitudeMass_integrable N lam f) (full_weightedMass_integrable N lam f e)]
  calc
    (∫ p in fullDomain, amplitudeMassDensity N lam f p - weightedMassDensity N f e p) ≤
        ∫ p in fullDomain, (e : ℝ) / 2 * (1 / p.2 ^ (2 : ℕ)) :=
      integral_mono ((full_amplitudeMass_integrable N lam f).sub (full_weightedMass_integrable N lam f e))
        (full_weight_integrable.const_mul _) (amplitude_error_le N lam f e)
    _ = (e : ℝ) / 2 * ∫ p in fullDomain, 1 / p.2 ^ (2 : ℕ) := integral_const_mul _ _
    _ ≤ (e : ℝ) / 2 * 2 := mul_le_mul_of_nonneg_left full_weight_integral_le_two (half_pos e.2).le
    _ = (e : ℝ) := by ring

/-- Original nonvanishing forces strictly positive unregularized full amplitude mass. -/
theorem full_amplitudeMass_pos : 0 < ∫ p in fullDomain, amplitudeMassDensity N lam f p := by
  let e : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  have h := full_weightedMass_pos N lam f e
  have hle := full_mass_error_nonneg N lam f e
  linarith

/-- The actual retained-curvature budget lies below its limiting amplitude budget. -/
theorem full_curvature_error_nonneg :
    0 ≤ (lam : ℝ) * (∫ p in fullDomain, amplitudeMassDensity N lam f p) -
      ∫ p in fullDomain, weightedRemainder N f e p := by
  rw [full_curvature_budget N lam f e, ← mul_sub]
  exact mul_nonneg lam.2.1.le (full_mass_error_nonneg N lam f e)

/-- The actual total retained-curvature error is bounded by eigenvalue times regulator. -/
theorem full_curvature_error_le :
    (lam : ℝ) * (∫ p in fullDomain, amplitudeMassDensity N lam f p) -
      (∫ p in fullDomain, weightedRemainder N f e p) ≤ (lam : ℝ) * (e : ℝ) := by
  rw [full_curvature_budget N lam f e, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (full_mass_error_le_regulator N lam f e) lam.2.1.le

/-- The actual positive regulators approaching zero, expressed by the subtype-value pullback filter. -/
def regulatorAtZero : Filter (Ioi (0 : ℝ)) :=
  Filter.comap (fun e : Ioi (0 : ℝ) => (e : ℝ)) (𝓝 0)

/-- Positive regulators accumulate at zero, so the regulator-limit filter is nontrivial. -/
instance regulatorAtZero_neBot : NeBot regulatorAtZero := by
  change NeBot (Filter.comap (fun e : Ioi (0 : ℝ) => (e : ℝ)) (𝓝 (0 : ℝ)))
  apply comap_neBot_iff_frequently.mpr
  rw [Subtype.range_val]
  have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact (show (0 : ℝ) ≤ 0 from le_rfl)
  exact mem_closure_iff_frequently.mp h0

/-- Actual positive regulator values tend to zero along their limit filter. -/
theorem regulator_coe_limit :
    Tendsto (fun e : Ioi (0 : ℝ) => (e : ℝ)) regulatorAtZero (𝓝 0) := tendsto_comap

/-- The proved uniform actual mass-error bound forces the error to zero. -/
theorem full_mass_error_limit :
    Tendsto (fun e : Ioi (0 : ℝ) => (∫ p in fullDomain, amplitudeMassDensity N lam f p) -
      ∫ p in fullDomain, weightedMassDensity N f e p) regulatorAtZero (𝓝 0) :=
  tendsto_const_nhds.squeeze' regulator_coe_limit
    (Eventually.of_forall (full_mass_error_nonneg N lam f))
    (Eventually.of_forall (full_mass_error_le_regulator N lam f))

/-- Actual weighted spectral mass converges to the unregularized amplitude mass. -/
theorem full_weightedMass_limit :
    Tendsto (fun e : Ioi (0 : ℝ) => ∫ p in fullDomain, weightedMassDensity N f e p)
      regulatorAtZero (𝓝 (∫ p in fullDomain, amplitudeMassDensity N lam f p)) := by
  have h := (tendsto_const_nhds (x := ∫ p in fullDomain, amplitudeMassDensity N lam f p)).sub
    (full_mass_error_limit N lam f)
  simpa only [sub_sub_cancel, sub_zero] using h

/-- The actual total retained curvature converges to eigenvalue times the full amplitude mass. -/
theorem full_curvature_limit :
    Tendsto (fun e : Ioi (0 : ℝ) => ∫ p in fullDomain, weightedRemainder N f e p)
      regulatorAtZero (𝓝 ((lam : ℝ) * ∫ p in fullDomain, amplitudeMassDensity N lam f p)) := by
  simpa only [full_curvature_budget N lam f] using (full_weightedMass_limit N lam f).const_mul (lam : ℝ)

/-- The actual spectral densities converge in full-domain L¹ with error at most the regulator. -/
theorem full_amplitude_error_l1_le :
    (∫ p in fullDomain, ‖amplitudeMassDensity N lam f p - weightedMassDensity N f e p‖) ≤ (e : ℝ) := by
  have he : (fun p => ‖amplitudeMassDensity N lam f p - weightedMassDensity N f e p‖) =
      (fun p => amplitudeMassDensity N lam f p - weightedMassDensity N f e p) := by
    funext p
    exact Real.norm_of_nonneg (sub_nonneg.mpr (weightedMassDensity_le_amplitude N lam f e p))
  rw [he, integral_sub (full_amplitudeMass_integrable N lam f) (full_weightedMass_integrable N lam f e)]
  exact full_mass_error_le_regulator N lam f e

/-- The actual weighted spectral density decreases as the positive regulator increases. -/
theorem weightedMassDensity_antitone (p : ℝ × ℝ) :
    Antitone (fun e : Ioi (0 : ℝ) => weightedMassDensity N f e p) := by
  intro a b hab
  have ha : 0 < (a : ℝ) := a.2
  have hb : 0 < (b : ℝ) := b.2
  have hab' : (a : ℝ) ≤ (b : ℝ) := hab
  have hr : radius N f a (point p.1 p.2) ≤ radius N f b (point p.1 p.2) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  unfold weightedMassDensity
  dsimp only
  rw [← div_div, ← div_div]
  exact div_le_div_of_nonneg_left (div_nonneg (density_nonneg N f _) (sq_nonneg p.2))
    (radius_pos N f a _) hr

/-- The actual full weighted spectral mass is antitone in the positive regulator. -/
theorem full_weightedMass_antitone :
    Antitone (fun e : Ioi (0 : ℝ) => ∫ p in fullDomain, weightedMassDensity N f e p) := by
  intro a b hab
  exact integral_mono (full_weightedMass_integrable N lam f b) (full_weightedMass_integrable N lam f a)
    (fun p => weightedMassDensity_antitone N lam f p hab)

/-- The actual total retained curvature is antitone in the regulator; no pointwise curvature monotonicity is asserted. -/
theorem full_curvature_antitone :
    Antitone (fun e : Ioi (0 : ℝ) => ∫ p in fullDomain, weightedRemainder N f e p) := by
  intro a b hab
  dsimp only
  rw [full_curvature_budget N lam f a, full_curvature_budget N lam f b]
  exact mul_le_mul_of_nonneg_left (full_weightedMass_antitone N lam f hab) lam.2.1.le

end
end GaloisForLFunctions.RHTower.SelbergMaassRegulatorMass
