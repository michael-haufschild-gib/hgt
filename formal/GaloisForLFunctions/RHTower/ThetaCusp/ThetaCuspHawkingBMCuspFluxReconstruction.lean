import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspFluxMoment

/-!
# Exact reconstruction from actual boundary data, limiting fluxes and full source tails.

The field is the original native energy response. Its identification with
continued retarded propagation and any extinction law remain separate.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection D4BMGlobalAngularResponse
noncomputable section

/-- The original roots' Wronskian gap, with no normalization removed. -/
def rootGap (q : XiZeroCopy) (branch : Bool) : ℂ := root q branch true-root q branch false

/-- The actual Xi parameters never coalesce the two cusp roots. -/
theorem rootGap_ne_zero (q : XiZeroCopy) (branch : Bool) : rootGap q branch ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hb := (physicalRate_re_bounds q branch).2
  norm_num [rootGap,root] at hr
  linarith

private theorem power_complement (q : XiZeroCopy) (branch alternate : Bool)
    {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^(root q branch alternate)*(y:ℂ)^(root q branch (!alternate)-1)=1 := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
  have he : root q branch alternate+(root q branch (!alternate)-1)=0 := by
    cases alternate <;> simp [root] <;> ring
  rw [he,Complex.cpow_zero]

/-- The full actual mean is recovered exactly from its two Wronskian coefficients. -/
theorem responseMean_flux_reconstruction (q : XiZeroCopy) (branch : Bool)
    {y : ℝ} (hy : 0 < y) :
    responseMean q branch y =
      ((y:ℂ)^(root q branch true)*responseFlux q branch false y-
        (y:ℂ)^(root q branch false)*responseFlux q branch true y)/rootGap q branch := by
  apply (eq_div_iff (rootGap_ne_zero q branch)).mpr
  rw [responseFlux,responseFlux]
  have h1 := power_complement q branch true hy
  have h0 := power_complement q branch false hy
  simp only [Bool.not_true,Bool.not_false] at h1 h0
  calc
    responseMean q branch y*rootGap q branch =
        (root q branch true*((y:ℂ)^(root q branch false)*(y:ℂ)^(root q branch true-1))-
          root q branch false*((y:ℂ)^(root q branch true)*(y:ℂ)^(root q branch false-1)))*responseMean q branch y := by
      rw [h0,h1]
      simp only [mul_one,rootGap]
      ring
    _ = _ := by ring

/-- Exact variation of constants for the original response, retaining the two
boundary fluxes and both complete finite-height source moments. -/
theorem responseMean_boundary_source (q : XiZeroCopy) (branch : Bool)
    {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    responseMean q branch y =
      ((y:ℂ)^(root q branch true)*(responseFlux q branch false a+
          ∫ t in a..y, fluxSource q branch false t)-
        (y:ℂ)^(root q branch false)*(responseFlux q branch true a+
          ∫ t in a..y, fluxSource q branch true t))/rootGap q branch := by
  rw [responseFlux_segment q branch false ha hy,responseFlux_segment q branch true ha hy]
  convert responseMean_flux_reconstruction q branch hy using 1
  ring

/-- The two normalized limiting Wronskian coefficients of the actual native response.
Their causal interpretation remains separate. -/
def limitingCoefficient (q : XiZeroCopy) (branch alternate : Bool) : ℂ :=
  if alternate then limitingFlux q branch false/rootGap q branch
    else -limitingFlux q branch true/rootGap q branch


/-- The actual flux equals its constructed limit minus the complete remaining source moment. -/
theorem responseFlux_eq_limit_sub_tail (q : XiZeroCopy) (branch alternate : Bool)
    {y : ℝ} (hy : 3 < y) :
    responseFlux q branch alternate y = limitingFlux q branch alternate-
      ∫ t in Ioi y, fluxSource q branch alternate t := by
  have hi := fluxSource_integrable q branch alternate
  have h4 := hi.mono_set (Ioi_subset_Ioi (by norm_num : (3:ℝ)≤4))
  have hyi := hi.mono_set (Ioi_subset_Ioi hy.le)
  have h := intervalIntegral.integral_interval_add_Ioi h4 hyi
  rw [responseFlux_segment q branch alternate (by norm_num) (by linarith)] at h
  unfold limitingFlux
  linear_combination h

/-- The original response is exactly the two limiting homogeneous coefficients
plus explicit full-source tail corrections. No boundary datum is set to zero. -/
theorem responseMean_limit_source (q : XiZeroCopy) (branch : Bool)
    {y : ℝ} (hy : 3 < y) :
    responseMean q branch y =
      (y:ℂ)^(root q branch false)*limitingCoefficient q branch false+
      (y:ℂ)^(root q branch true)*limitingCoefficient q branch true+
      ((y:ℂ)^(root q branch false)*(∫ t in Ioi y, fluxSource q branch true t)-
        (y:ℂ)^(root q branch true)*(∫ t in Ioi y, fluxSource q branch false t))/rootGap q branch := by
  rw [responseMean_flux_reconstruction q branch (by linarith),
    responseFlux_eq_limit_sub_tail q branch false hy,
    responseFlux_eq_limit_sub_tail q branch true hy]
  simp only [limitingCoefficient,Bool.false_eq_true,if_false,if_true]
  ring

end
end RHTower.D4BMCuspResponse
