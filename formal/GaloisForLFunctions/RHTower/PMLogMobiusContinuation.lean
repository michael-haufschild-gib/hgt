import GaloisForLFunctions.RHTower.PMLogMobiusContinuousBudget
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Continuation of the literal logarithmic Möbius defect

The reciprocal-variable defect has the exact Mellin pair on `Re s > 0`.
Convergence of the canonical Fermi error gives absolute Mellin convergence
and analyticity throughout `Re s > -1/2`. The entire residue unit continues
the cleared source identity across this connected half-plane, including zero.
This is a conditional transfer; convergence of the canonical error is not proved.
-/

open MeasureTheory Set Filter Topology Asymptotics
noncomputable section
namespace RHTower

def pmLogDefectReciprocal (t : ℝ) : ℂ := (pmLogMobiusMeanDefect t⁻¹ : ℂ)

theorem hasMellin_pmLogDefectReciprocal {s : ℂ} (hs : 0 < s.re) :
    HasMellin pmLogDefectReciprocal s
      (1 / (s ^ 2 * riemannZeta (s + 1)) +
        deriv riemannZeta (s + 1) / ((s + 1) ^ 2 * riemannZeta (s + 1))) := by
  have hB := hasMellin_moebiusShiftedLogKernelReal_inv hs
  have hm := hasMellin_pmPrimeLogMean_inv hs
  have h := hasMellin_sub hB.1 hm.1
  rw [hB.2, hm.2] at h
  change HasMellin (fun t => ((Sieve.moebiusShiftedLogKernelReal 0 t⁻¹ - pmPrimeLogMean t⁻¹ : ℝ) : ℂ)) s _
  simpa only [Complex.ofReal_sub,
    neg_div, sub_neg_eq_add] using h

theorem locallyIntegrableOn_pmLogDefectReciprocal :
    LocallyIntegrableOn pmLogDefectReciprocal (Ioi 0) := by
  have h := (hasMellin_pmLogDefectReciprocal (s := 1) (by norm_num)).1
  have hi : IntegrableOn pmLogDefectReciprocal (Ioi 0) := by
    simpa only [MellinConvergent, sub_self, Complex.cpow_zero, one_smul] using h
  exact hi.locallyIntegrableOn

theorem pmLogDefectReciprocal_eq_zero {t : ℝ} (ht : 1 < t) :
    pmLogDefectReciprocal t = 0 := by
  have hf : ⌊t⁻¹⌋₊ = 0 := Nat.floor_eq_zero.mpr (inv_lt_one_of_one_lt₀ ht)
  simp [pmLogDefectReciprocal, pmLogMobiusMeanDefect,
    Sieve.moebiusShiftedLogKernelReal, pmPrimeLogMean, hf]

theorem pmLogDefectReciprocal_isBigO_exp :
    pmLogDefectReciprocal =O[atTop] (fun t : ℝ => Real.exp (-1 * t)) := by
  have hz : pmLogDefectReciprocal =ᶠ[atTop] (fun _ => (0 : ℂ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact pmLogDefectReciprocal_eq_zero ht
  exact hz.isBigO.trans (isBigO_zero _ _)

theorem pmLogMobiusMeanDefect_isBigO_rpow
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0)) {b : ℝ} (hb : -1 / 2 < b) :
    pmLogMobiusMeanDefect =O[atTop] (fun x : ℝ => x ^ b) := by
  have hlog := isLittleO_log_rpow_atTop (by linarith : 0 < b + 1 / 2)
  have hmul := hlog.mul_isBigO
    (isBigO_refl (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) atTop)
  have hk : (fun x : ℝ => Real.log x / Real.sqrt x) =o[atTop] (fun x : ℝ => x ^ b) := by
    apply hmul.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp only [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg hx.le]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
  exact ((pmLogMobiusMeanDefect_isLittleO_of_error hE).trans hk).isBigO

theorem pmLogDefectReciprocal_isBigO_rpow
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0)) {b : ℝ} (hb : -1 / 2 < b) :
    pmLogDefectReciprocal =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  have h := (pmLogMobiusMeanDefect_isBigO_rpow hE hb).comp_tendsto tendsto_inv_nhdsGT_zero
  have hr : (fun t : ℝ => pmLogMobiusMeanDefect t⁻¹) =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (-b)) := by
    apply h.congr' (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with t ht
    dsimp only [Function.comp_def]
    rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]
  apply IsBigO.of_norm_left
  simpa only [pmLogDefectReciprocal, Complex.norm_real] using hr.norm_left

theorem mellinConvergent_pmLogDefectReciprocal
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0)) {s : ℂ} (hs : -1 / 2 < s.re) :
    MellinConvergent pmLogDefectReciprocal s := by
  let b := (-1 / 2 + s.re) / 2
  have hb : -1 / 2 < b := by dsimp [b]; linarith
  have hbs : b < s.re := by dsimp [b]; linarith
  exact mellinConvergent_of_isBigO_rpow_exp one_pos
    locallyIntegrableOn_pmLogDefectReciprocal pmLogDefectReciprocal_isBigO_exp
    (pmLogDefectReciprocal_isBigO_rpow hE hb) hbs

theorem analyticOnNhd_pmLogDefectMellin
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0)) :
    AnalyticOnNhd ℂ (mellin pmLogDefectReciprocal) {s : ℂ | -1 / 2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  let b := (-1 / 2 + s.re) / 2
  have hb : -1 / 2 < b := by dsimp [b]; change -1 / 2 < s.re at hs; linarith
  have hbs : b < s.re := by dsimp [b]; change -1 / 2 < s.re at hs; linarith
  exact (mellin_differentiableAt_of_isBigO_rpow_exp one_pos
    locallyIntegrableOn_pmLogDefectReciprocal pmLogDefectReciprocal_isBigO_exp
    (pmLogDefectReciprocal_isBigO_rpow hE hb) hbs).differentiableWithinAt

theorem pm_deriv_zetaResidueUnit {z : ℂ} (hz : z ≠ 1) :
    deriv zetaResidueUnit z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
  rw [(zetaResidueUnit_eventuallyEq hz).deriv_eq]
  simpa only [one_mul, id_eq, Pi.mul_def] using
    (((hasDerivAt_id z).sub_const 1).mul (differentiableAt_riemannZeta hz).hasDerivAt).deriv

theorem pmLogDefectMellin_unit_identity_right {s : ℂ} (hs : 0 < s.re) :
    s * (s + 1) ^ 2 * zetaResidueUnit (s + 1) * mellin pmLogDefectReciprocal s =
      (s + 1) ^ 2 + s * deriv zetaResidueUnit (s + 1) - zetaResidueUnit (s + 1) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hz : s + 1 ≠ 1 := by simpa using hs0
  have h := pmLogMobiusMeanDefect_mellin_cleared hs
  have hm : mellin pmLogDefectReciprocal s =
      mellin (fun x : ℝ => (pmLogMobiusMeanDefect x : ℂ)) (-s) :=
    mellin_comp_inv (fun x : ℝ => (pmLogMobiusMeanDefect x : ℂ)) s
  rw [← hm] at h
  rw [pm_deriv_zetaResidueUnit hz]
  simp only [zetaResidueUnit, Function.update_of_ne hz, add_sub_cancel_right]
  convert h using 1 <;> ring

theorem pmLogDefectMellin_unit_identity
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0)) {s : ℂ} (hs : -1 / 2 < s.re) :
    s * (s + 1) ^ 2 * zetaResidueUnit (s + 1) * mellin pmLogDefectReciprocal s =
      (s + 1) ^ 2 + s * deriv zetaResidueUnit (s + 1) - zetaResidueUnit (s + 1) := by
  let U : Set ℂ := {s | -1 / 2 < s.re}
  have hF := analyticOnNhd_pmLogDefectMellin hE
  have hleft : AnalyticOnNhd ℂ (fun z =>
      z * (z + 1) ^ 2 * zetaResidueUnit (z + 1) * mellin pmLogDefectReciprocal z) U := by
    intro z hz
    have hq : AnalyticAt ℂ (fun z : ℂ => z + 1) z := analyticAt_id.add analyticAt_const
    exact ((analyticAt_id.mul (hq.pow 2)).mul
      ((analyticAt_zetaResidueUnit (z + 1)).comp (f := fun w : ℂ => w + 1) hq)).mul (hF z hz)
  have hright : AnalyticOnNhd ℂ (fun z =>
      (z + 1) ^ 2 + z * deriv zetaResidueUnit (z + 1) - zetaResidueUnit (z + 1)) U := by
    intro z hz
    have hq : AnalyticAt ℂ (fun z : ℂ => z + 1) z := analyticAt_id.add analyticAt_const
    exact ((hq.pow 2).add (analyticAt_id.mul
      ((analyticAt_zetaResidueUnit (z + 1)).deriv.comp (f := fun w : ℂ => w + 1) hq))).sub
        ((analyticAt_zetaResidueUnit (z + 1)).comp (f := fun w : ℂ => w + 1) hq)
  have hevent : (fun z => z * (z + 1) ^ 2 * zetaResidueUnit (z + 1) *
      mellin pmLogDefectReciprocal z) =ᶠ[𝓝 (1 : ℂ)] (fun z =>
      (z + 1) ^ 2 + z * deriv zetaResidueUnit (z + 1) - zetaResidueUnit (z + 1)) := by
    have hgt : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with z hz
    exact pmLogDefectMellin_unit_identity_right hz
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (convex_halfSpace_re_gt (-1 / 2)).isPreconnected
    (by change (-1 / 2 : ℝ) < 1; norm_num) hevent hs

theorem pmLogDefectMellin_cleared_identity
    (hE : Tendsto logMobiusFermiErrorEnergy atTop (𝓝 0)) {s : ℂ}
    (hs : -1 / 2 < s.re) (hs0 : s ≠ 0) :
    s ^ 2 * (s + 1) ^ 2 * riemannZeta (s + 1) * mellin pmLogDefectReciprocal s =
      (s + 1) ^ 2 + s ^ 2 * deriv riemannZeta (s + 1) := by
  have hz : s + 1 ≠ 1 := by simpa using hs0
  have h := pmLogDefectMellin_unit_identity hE hs
  rw [pm_deriv_zetaResidueUnit hz] at h
  simp only [zetaResidueUnit, Function.update_of_ne hz, add_sub_cancel_right] at h
  convert h using 1 <;> ring

end RHTower
