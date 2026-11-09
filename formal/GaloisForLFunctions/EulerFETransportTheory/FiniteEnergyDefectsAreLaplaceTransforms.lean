import GaloisForLFunctions.EulerFETransportTheory.TheDefectHasAUnitaryMellinSource
import GaloisForLFunctions.HTGeometry.ComplexRateGammaIntegral
import GaloisForLFunctions.HTGeometry.HalfPlaneHardy
import GaloisForLFunctions.HTGeometry.HardyLineIsometry
import GaloisForLFunctions.RHTower.GammaRCubeThetaPairsL2

/-!
# Finite-energy defects are half-line Laplace transforms

Mellin–Plancherel pairs the explicit defect source with a decaying exponential.
The complex-rate Gamma integral and the Gamma multiplier identity then recover the
actual Hamburger defect integral throughout the right half-plane.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ExactEventTheory

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Each actual defect kernel is the Laplace transform of its Gamma-normalized power. -/
theorem boundaryPairKernel_eq_laplace_power (t : ℝ) {z : ℂ} (hz : 0 < z.re) :
    boundaryPairKernel (2 * t) z = defectMellinMultiplier t *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (-linePt (2 * t)) * expRay z u := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hi := _root_.HTGeometry.integral_cpow_mul_cexp_neg_mul_complex
    (w := 1 - linePt (2 * t)) (by norm_num [linePt]) hz
  rw [show 1 - linePt (2 * t) - 1 = -linePt (2 * t) by ring] at hi
  rw [boundaryPairKernel_eq_cpow_div_sin (2 * t) hz0]
  change _ = defectMellinMultiplier t *
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (-linePt (2 * t)) * cexp (-(z * u))
  rw [hi, ← mul_assoc, defectMellinMultiplier_mul_gamma,
    show -(1 - linePt (2 * t)) = linePt (2 * t) - 1 by ring]
  ring

private def laplaceExponential (z : ℂ) (hz : 0 < z.re) : HalfLineL2 :=
  (memLp_two_expRay_restrict hz 0).toLp (expRay z)

private theorem mellin_laplaceExponential {z : ℂ} (hz : 0 < z.re) :
    (halfLineMellinUnitary (laplaceExponential z hz) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => Gamma (1 / 2 - 2 * Real.pi * ξ * I) *
        z ^ (-(1 / 2 - 2 * Real.pi * ξ * I)) := by
  have hint : Integrable (halfDensityPullback (expRay z)) := by
    apply _root_.RHTower.integrable_halfDensityPullback_of_mellinConvergent
    have hi := _root_.HTGeometry.integrableOn_complexRateGammaIntegrand
      (w := ((1 / 2 : ℝ) : ℂ)) (by norm_num) hz
    change IntegrableOn (fun u : ℝ =>
      (u : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - 1) * cexp (-(z * u))) (Ioi 0) at hi
    simpa only [MellinConvergent, smul_eq_mul, expRay] using hi
  have hM := halfLineMellinUnitary_ae_eq_mellin (laplaceExponential z hz) (expRay z)
    (memLp_two_expRay_restrict hz 0).coeFn_toLp hint
  filter_upwards [hM] with ξ hξ
  rw [hξ, mellin]
  simpa only [smul_eq_mul, expRay] using
    _root_.HTGeometry.integral_cpow_mul_cexp_neg_mul_complex
      (w := 1 / 2 - 2 * Real.pi * ξ * I) (by simp) hz

private theorem conjugate_mellin_laplaceExponential {z : ℂ} (hz : 0 < z.re) :
    (fun ξ => (starRingEnd ℂ)
      (halfLineMellinUnitary (laplaceExponential ((starRingEnd ℂ) z)
        (by simpa using hz)) ξ)) =ᵐ[volume]
      fun ξ => Gamma (1 - linePt (2 * (-Real.pi * ξ))) *
        z ^ (linePt (2 * (-Real.pi * ξ)) - 1) := by
  have harg : z.arg ≠ Real.pi := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    have hneg : z.re < 0 := by simpa using h.1
    linarith
  filter_upwards [mellin_laplaceExponential (z := (starRingEnd ℂ) z)
    (by simpa using hz)] with ξ hξ
  rw [hξ, map_mul, ← Complex.Gamma_conj,
    ← Complex.cpow_conj _ _ harg]
  have hw : (starRingEnd ℂ) (1 / 2 - 2 * Real.pi * ξ * I : ℂ) =
      1 - linePt (2 * (-Real.pi * ξ)) := by
    change star (1 / 2 - 2 * Real.pi * ξ * I : ℂ) = _
    apply Complex.ext <;> norm_num [linePt] <;> ring
  rw [map_neg, hw]
  congr 2
  ring

/-- The Hamburger integral of every finite-energy defect is its actual half-line
Laplace transform. No separate boundary or Hardy premise is needed. -/
theorem defectLaplace_eq_laplaceRay (g : DefectL2) {z : ℂ} (hz : 0 < z.re) :
    defectLaplace (g : ℝ → ℂ) z = laplaceRay (defectMellinSource g) z := by
  let ψ := defectMellinSource g
  let k := laplaceExponential ((starRingEnd ℂ) z) (by simpa using hz)
  have hpair : laplaceRay ψ z = inner ℂ k ψ := by
    rw [laplaceRay, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_two_expRay_restrict
      (w := (starRingEnd ℂ) z) (by simpa using hz) 0).coeFn_toLp] with u hu
    rw [RCLike.inner_apply]
    change ψ u * expRay z u = ψ u * (starRingEnd ℂ) (k u)
    change k u = expRay ((starRingEnd ℂ) z) u at hu
    rw [hu, expRay, expRay, ← Complex.exp_conj, map_neg, map_mul,
      Complex.conj_conj, Complex.conj_ofReal]
  have hspectral : inner ℂ k ψ =
      ∫ ξ : ℝ, (1 / 2 : ℂ) *
        ((g : ℝ → ℂ) (-Real.pi * ξ) * boundaryPairKernel (2 * (-Real.pi * ξ)) z) := by
    rw [← halfLineMellinUnitary.inner_map_map k ψ, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [conjugate_mellin_laplaceExponential hz,
      mellin_defectMellinSource g] with ξ hk hψ
    rw [RCLike.inner_apply, mul_comm]
    change (starRingEnd ℂ) (halfLineMellinUnitary k ξ) *
      halfLineMellinUnitary ψ ξ = _
    change (starRingEnd ℂ) (halfLineMellinUnitary k ξ) = _ at hk
    change halfLineMellinUnitary ψ ξ = _ at hψ
    rw [hk, hψ, boundaryPairKernel_eq_cpow_div_sin _
      (show z ≠ 0 by intro h; simp [h] at hz)]
    have hm := defectMellinMultiplier_mul_gamma (-Real.pi * ξ)
    linear_combination (1 / 2 : ℂ) * g (-Real.pi * ξ) *
      z ^ (linePt (2 * (-Real.pi * ξ)) - 1) * hm
  rw [hpair, hspectral, integral_const_mul,
    Measure.integral_comp_mul_left (fun t => g t * boundaryPairKernel (2 * t) z) (-Real.pi)]
  rw [← closedDefectLaplace_eq hz, closedDefectLaplace]
  simp only [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr Real.pi_pos), Complex.real_smul]
  push_cast
  ring

/-- Finite-energy defects satisfy the actual Hardy bound, with the sharp source constant. -/
theorem isHalfPlaneHardy_defectLaplace (g : DefectL2) :
    IsHalfPlaneHardy (defectLaplace (g : ℝ → ℂ))
      ((2 * Real.pi ^ 2)⁻¹ * ‖g‖ ^ 2) := by
  have hH := isHalfPlaneHardy_laplaceRay (Lp.memLp (defectMellinSource g))
  have henergy : (∫ u in Ioi (0 : ℝ), ‖defectMellinSource g u‖ ^ 2) =
      (2 * Real.pi ^ 2)⁻¹ * ‖g‖ ^ 2 := by
    rw [← Lp_two_norm_sq_eq_integral, norm_sq_defectMellinSource]
  have hline (σ : ℝ) (hσ : 0 < σ) :
      (fun ξ => defectLaplace (g : ℝ → ℂ) (rayLine σ ξ)) =
        fun ξ => laplaceRay (defectMellinSource g) (rayLine σ ξ) := by
    funext ξ
    exact defectLaplace_eq_laplaceRay g (by simpa using hσ)
  constructor
  · apply hH.holo.congr
    intro z hz
    exact defectLaplace_eq_laplaceRay g hz
  · intro σ hσ
    rw [hline σ hσ]
    exact hH.memLp σ hσ
  · intro σ hσ
    change (∫ ξ, ‖(fun ξ => defectLaplace (g : ℝ → ℂ) (rayLine σ ξ)) ξ‖ ^ 2) ≤ _
    rw [hline σ hσ, ← henergy]
    exact hH.bound σ hσ

/-- The vertical energy increases to `π⁻¹‖g‖²`, now for arbitrary `L²` defects. -/
theorem tendsto_vertical_energy_defectLaplace (g : DefectL2) :
    Tendsto (fun σ : ℝ => ∫ y : ℝ,
      ‖defectLaplace (g : ℝ → ℂ) (hardyVerticalLine σ y)‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi⁻¹ * ‖g‖ ^ 2)) := by
  have h := tendsto_integral_norm_sq_laplaceRay_vertical
    (Lp.memLp (defectMellinSource g))
  have he : 2 * Real.pi * (∫ u in Ioi (0 : ℝ), ‖defectMellinSource g u‖ ^ 2) =
      Real.pi⁻¹ * ‖g‖ ^ 2 := by
    rw [← Lp_two_norm_sq_eq_integral, norm_sq_defectMellinSource]
    field_simp
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  apply integral_congr_ae
  filter_upwards with y
  rw [defectLaplace_eq_laplaceRay g (by simpa using hσ)]

/-- Every right-half-plane Hardy function is an actual finite-energy defect transform. -/
theorem exists_defectLaplace_eq_of_hardy {F : ℂ → ℂ} {M : ℝ}
    (hF : IsHalfPlaneHardy F M) :
    ∃ g : DefectL2, EqOn (defectLaplace (g : ℝ → ℂ)) F {z : ℂ | 0 < z.re} := by
  let ψ : HalfLineL2 := (memLp_two_hardyDatum hF).toLp (hardyDatum F hF)
  obtain ⟨g, hg⟩ := defectMellinSource_bijective.2 ψ
  refine ⟨g, fun z hz => ?_⟩
  rw [defectLaplace_eq_laplaceRay g hz, hg, isHalfPlaneHardy_eq_laplaceRay hF hz]
  apply integral_congr_ae
  filter_upwards [(memLp_two_hardyDatum hF).coeFn_toLp] with u hu
  change ψ u = hardyDatum F hF u at hu
  exact congrArg (fun a => a * expRay z u) hu

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.defectLaplace_eq_laplaceRay
#print axioms GaloisForLFunctions.EulerFETransportTheory.isHalfPlaneHardy_defectLaplace
#print axioms GaloisForLFunctions.EulerFETransportTheory.tendsto_vertical_energy_defectLaplace
#print axioms GaloisForLFunctions.EulerFETransportTheory.exists_defectLaplace_eq_of_hardy
