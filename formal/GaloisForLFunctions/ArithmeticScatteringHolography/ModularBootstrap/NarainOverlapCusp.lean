import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainEisensteinNormalization
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartitionRegularity
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainModularity
import GaloisForLFunctions.RHTower.EisensteinFundamentalDomainIntegrability

/-!
# Vanishing of the Narain Eisenstein cusp correction

Linear partition growth and the exact Eisenstein constant terms make
the corrected product integrable on the fundamental domain for `Re s > 1`.
Dominated convergence then removes its high-cusp tail.
-/

open Complex RHTower UpperHalfPlane ModularGroup Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private theorem height_mul_exp_le (y : ℝ) :
    y * Real.exp (-(2 * Real.pi * y)) ≤ 1 / (2 * Real.pi) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * Real.pi * y))
    (Real.exp_pos (-(2 * Real.pi * y))).le
  rw [add_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h
  apply (le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
  nlinarith only [h, (Real.exp_pos (-(2 * Real.pi * y))).le]

/-- After removal of the leading Eisenstein term, the actual Narain cusp product is integrable. -/
theorem integrableOn_narainEisenstein_cusp (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun τ : UpperHalfPlane => narainPartitionOnUpperHalfPlane ρ σ τ *
      (narainOverlapEisenstein s τ - (τ.im : ℂ) ^ s)) fd := by
  obtain ⟨C, hC, hZ⟩ := narainPartition_linear_cusp ρ σ (a := 1 / 2) (by norm_num)
  let D := tailConst (s - 1 / 2) / ‖msA (s - 1 / 2)‖
  have hD : 0 ≤ D := div_nonneg (tailConst_nonneg _) (norm_nonneg _)
  have hp : IntegrableOn (fun τ : UpperHalfPlane => τ.im ^ (2 - s.re)) fd := by
    have h : IntegrableOn (fun τ : UpperHalfPlane => ‖((τ.im ^ (2 - s.re) : ℝ) : ℂ)‖) fd :=
      (integrableOn_fd_rpow (β := 2 - s.re) (by linarith only [hs])).norm
    exact h.congr_fun (fun τ _ => by
      change ‖((τ.im ^ (2 - s.re) : ℝ) : ℂ)‖ = τ.im ^ (2 - s.re)
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg τ.im_pos.le _)])
      isClosed_fd.measurableSet
  have hc : IntegrableOn (fun _ : UpperHalfPlane => C * D / (2 * Real.pi)) fd :=
    integrableOn_const (by simp [volume_fd_ne_top])
  have hmZ : Measurable (narainPartitionOnUpperHalfPlane ρ σ) :=
    (measurable_narainPartition ρ σ).comp
      (UpperHalfPlane.continuous_re.measurable.prodMk UpperHalfPlane.continuous_im.measurable)
  have hmE : Measurable (narainOverlapEisenstein s) := by
    have he : narainOverlapEisenstein s =
        fun τ => eisensteinLineModel (s - 1 / 2) τ / msA (s - 1 / 2) :=
      funext (narainOverlapEisenstein_eq_line hs)
    rw [he]
    exact (continuous_eisensteinLineModel (s - 1 / 2)).measurable.div_const _
  have hm : Measurable (fun τ : UpperHalfPlane => narainPartitionOnUpperHalfPlane ρ σ τ *
      (narainOverlapEisenstein s τ - (τ.im : ℂ) ^ s)) :=
    hmZ.mul (hmE.sub (by fun_prop))
  apply ((hp.const_mul (C * ‖narainOverlapScattering s‖)).add hc).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with τ hτ
  have hy : 1 / 2 ≤ τ.im := (half_lt_im_of_mem_fd' hτ).le
  have hz : ‖narainPartitionOnUpperHalfPlane ρ σ τ‖ ≤ C * τ.im := hZ τ.re τ.im hy
  have he := norm_narainOverlapEisenstein_sub_le hs hy
  have hpw : τ.im * τ.im ^ (1 - s.re) = τ.im ^ (2 - s.re) := by
    calc
      _ = τ.im ^ (1 : ℝ) * τ.im ^ (1 - s.re) := by rw [Real.rpow_one]
      _ = τ.im ^ ((1 : ℝ) + (1 - s.re)) := (Real.rpow_add τ.im_pos _ _).symm
      _ = _ := by congr 1; ring
  rw [norm_mul]
  calc
    _ ≤ (C * τ.im) * (‖narainOverlapScattering s‖ * τ.im ^ (1 - s.re) +
        D * Real.exp (-(2 * Real.pi * τ.im))) :=
      mul_le_mul hz he (norm_nonneg _) (mul_nonneg hC τ.im_pos.le)
    _ = C * ‖narainOverlapScattering s‖ * τ.im ^ (2 - s.re) +
        C * D * (τ.im * Real.exp (-(2 * Real.pi * τ.im))) := by
      rw [← hpw]
      ring
    _ ≤ C * ‖narainOverlapScattering s‖ * τ.im ^ (2 - s.re) +
        C * D * (1 / (2 * Real.pi)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (height_mul_exp_le τ.im) (mul_nonneg hC hD))
    _ = _ := by simp only [Pi.add_apply]; ring

/-- The cusp correction left by incomplete Eisenstein truncation. -/
def narainEisensteinCuspTail (ρ σ : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (T : ℝ) : ℂ :=
  ∫ τ in fd, if T < τ.im then narainPartitionOnUpperHalfPlane ρ σ τ *
    (narainOverlapEisenstein s τ - (τ.im : ℂ) ^ s) else 0

/-- The complete cusp correction vanishes in the region of absolute convergence. -/
theorem narainEisensteinCuspTail_tendsto_zero (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (narainEisensteinCuspTail ρ σ s) atTop (𝓝 0) := by
  let g : UpperHalfPlane → ℂ := fun τ => narainPartitionOnUpperHalfPlane ρ σ τ *
    (narainOverlapEisenstein s τ - (τ.im : ℂ) ^ s)
  have hi : Integrable g (volume.restrict fd) := integrableOn_narainEisenstein_cusp ρ σ hs
  have hm (T : ℝ) : MeasurableSet {τ : UpperHalfPlane | T < τ.im} :=
    measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict fd) (l := atTop)
    (F := fun T : ℝ => {τ : UpperHalfPlane | T < τ.im}.indicator g)
    (f := fun _ => (0 : ℂ)) (fun τ => ‖g τ‖)
    (Eventually.of_forall fun T => (hi.indicator (hm T)).aestronglyMeasurable)
    (Eventually.of_forall fun T => Eventually.of_forall fun τ => by
      by_cases hτ : T < τ.im
      · rw [indicator_of_mem (show τ ∈ {τ : UpperHalfPlane | T < τ.im} from hτ)]
      · rw [indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | T < τ.im} from hτ), norm_zero]
        exact norm_nonneg _)
    hi.norm
    (Eventually.of_forall fun τ => tendsto_const_nhds.congr' <|
      (eventually_ge_atTop τ.im).mono fun T hT =>
        (indicator_of_notMem (show τ ∉ {τ : UpperHalfPlane | T < τ.im} from not_lt.mpr hT) g).symm)
  change Tendsto (fun T : ℝ => ∫ τ in fd, if T < τ.im then g τ else 0) atTop (𝓝 0)
  simpa only [indicator_apply, mem_setOf_eq, integral_zero] using h

#print axioms integrableOn_narainEisenstein_cusp
#print axioms narainEisensteinCuspTail_tendsto_zero
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
