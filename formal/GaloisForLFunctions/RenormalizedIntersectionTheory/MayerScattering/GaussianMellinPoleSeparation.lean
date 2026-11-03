import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.GaussianCoreMellinSynthesis
import GaloisForLFunctions.RHTower.XiSignedFactorZeroSeparation
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected
import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareGaussianMajorant
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.FarFieldAnchor
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!+# Mellin poles of Gaussian resonance-core sums

The continued kernel is written using entire xi and explicit pole factors.
This form distinguishes a removable pole from the raw total Gamma-function value.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology Zeta23
open scoped lp ENNReal ComplexConjugate
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open ArithmeticPolarization SpacingScaleHarmonicAnalysis
open RenormalizedIntersectionTheory
open MayerQuadraticCone MayerCauchyMellinSymbol MayerScatteringCore MayerCoreMellin MayerEpsteinHeightMeasurability

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The xi expression for the continued Mellin transform, away from its explicit pole factors. -/
def resonantMellinKernel (s : upperMayerResonances) (u : ℂ) : ℂ :=
  4 * symbol (2 * s.1) u * _root_.RHTower.xi u * _root_.RHTower.xi (2 * s.1 - u) /
    (Gammaℝ (2 * s.1) * u * (u - 1) * (2 * s.1 - u) * (2 * s.1 - u - 1))


private theorem gamma_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have h := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at h
  linarith only [hz, h, Nat.cast_nonneg (α := ℝ) n]

private theorem gamma_differentiableAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n hn
  have h := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at h
  linarith only [hz, h, Nat.cast_nonneg (α := ℝ) n]

private theorem resonantSymbol_differentiableAt (s : upperMayerResonances) {u : ℂ}
    (hu0 : -1 < u.re) (hu1 : u.re < 1) :
    DifferentiableAt ℂ (symbol (2 * s.1)) u := by
  have h1 : 0 < ((u + 1) / 2).re := by simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]; linarith only [hu0]
  have h2 : 0 < ((2 * s.1 + 1 - u) / 2).re := by
    have he : ((2 * s.1 + 1 - u) / 2).re = (2 * s.1.re + 1 - u.re) / 2 := by simp
    rw [he]
    linarith only [s.2.2.1, hu1]
  have hd1 := (gamma_differentiableAt_of_re_pos h1).comp u
    ((differentiableAt_id.add_const (1 : ℂ)).div_const 2)
  have hd2 := (gamma_differentiableAt_of_re_pos h2).comp u
    ((differentiableAt_const (2 * s.1 + 1) |>.sub differentiableAt_id).div_const 2)
  exact (hd1.mul hd2).div_const _

private theorem resonantSymbol_ne_zero (s : upperMayerResonances) {u : ℂ}
    (hu0 : -1 < u.re) (hu1 : u.re < 1) : symbol (2 * s.1) u ≠ 0 := by
  have h1 : 0 < ((u + 1) / 2).re := by simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]; linarith only [hu0]
  have h2 : 0 < ((2 * s.1 + 1 - u) / 2).re := by
    have he : ((2 * s.1 + 1 - u) / 2).re = (2 * s.1.re + 1 - u.re) / 2 := by simp
    rw [he]
    linarith only [s.2.2.1, hu1]
  have hd : 0 < ((2 * s.1 + 1) / 2).re := by
    have he : ((2 * s.1 + 1) / 2).re = (2 * s.1.re + 1) / 2 := by simp
    rw [he]
    linarith only [s.2.2.1]
  exact div_ne_zero
    (mul_ne_zero (gamma_ne_zero_of_re_pos h1) (gamma_ne_zero_of_re_pos h2))
    (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) (gamma_ne_zero_of_re_pos hd))

private theorem resonantCore_hasMellin_narrow (s : upperMayerResonances) {u : ℂ}
    (hu0 : 0 < u.re) (hu1 : u.re < 2 * s.1.re) :
    HasMellin (mayerPeriodCore s.1) u
      (symbol (2 * s.1) u *
        (Gammaℝ u * Gammaℝ (2 * s.1 - u) / Gammaℝ (2 * s.1) *
          riemannZeta u * riemannZeta (2 * s.1 - u))) := by
  have hw0 : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have hwim : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hu2 : u.re < 1 := by linarith only [s.2.2.2.1, hu1]
  have hwu0 : 0 < (2 * s.1 - u).re := by simp; linarith only [hu1]
  have hwu1 : (2 * s.1 - u).re < 1 := by simp; linarith only [s.2.2.2.1, hu0]
  have hker := cauchyKernel_hasMellin hw0 (by linarith only [hu0] : -1 < u.re)
    (show u.re < (2 * s.1).re + 1 by simp; linarith only [hu1])
  have hcore := core_hasMellin_gammaR hu0 hu2 hwu0 hwu1 hwim
  have hkm : Measurable (cauchyKernel (2 * s.1)) := by
    unfold cauchyKernel cauchyWeight
    fun_prop
  have hfm : Measurable (fieldCore (2 * s.1)) := by
    have hwne0 : 2 * s.1 ≠ 0 := by intro h; rw [h, Complex.zero_im] at hwim; exact lt_irrefl 0 hwim
    have hwne2 : 2 * s.1 ≠ 2 := by intro h; rw [h] at hwim; norm_num at hwim
    have he := measurable_epsteinField hwne0 hwne2
    unfold fieldCore scatteringPowers
    fun_prop
  have h := _root_.RHTower.hasMellin_positiveMellinConvolution hkm hfm hker.1 hcore.1
  rw [hker.2, hcore.2] at h
  exact h

private theorem gammaR_zeta_xi {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) :
    Gammaℝ z * riemannZeta z = 2 * _root_.RHTower.xi z / (z * (z - 1)) := by
  have hzne0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz0; exact lt_irrefl 0 hz0
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hz0
  have hΛ : Gammaℝ z * riemannZeta z = completedRiemannZeta z := by
    rw [riemannZeta_def_of_ne_zero hzne0]
    field_simp [hG]
  rw [hΛ, _root_.RHTower.xi_eq_half_mul hzne0 hz1]
  field_simp [mul_ne_zero hzne0 (sub_ne_zero.mpr hz1)]

private theorem resonantMellin_cleared_narrow (s : upperMayerResonances) {u : ℂ}
    (hu0 : 0 < u.re) (hu1 : u.re < 2 * s.1.re) :
    (Gammaℝ (2 * s.1) * u * (u - 1) * (2 * s.1 - u) * (2 * s.1 - u - 1)) *
      mellin (mayerPeriodCore s.1) u =
      4 * symbol (2 * s.1) u * _root_.RHTower.xi u * _root_.RHTower.xi (2 * s.1 - u) := by
  have hu2 : u.re < 1 := by linarith only [hu1, s.2.2.2.1]
  have hwu0 : 0 < (2 * s.1 - u).re := by simp; linarith only [hu1]
  have hwu1 : (2 * s.1 - u).re < 1 := by simp; linarith only [hu0, s.2.2.2.1]
  have hu_ne0 : u ≠ 0 := by intro h; rw [h, Complex.zero_re] at hu0; exact lt_irrefl 0 hu0
  have hu_ne1 : u ≠ 1 := by intro h; rw [h, Complex.one_re] at hu2; exact lt_irrefl 1 hu2
  have hwu_ne0 : 2 * s.1 - u ≠ 0 := by intro h; rw [h, Complex.zero_re] at hwu0; exact lt_irrefl 0 hwu0
  have hwu_ne1 : 2 * s.1 - u ≠ 1 := by intro h; rw [h, Complex.one_re] at hwu1; exact lt_irrefl 1 hwu1
  have hG : Gammaℝ (2 * s.1) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith only [s.2.2.1])
  rw [(resonantCore_hasMellin_narrow s hu0 hu1).2]
  have he : Gammaℝ u * Gammaℝ (2 * s.1 - u) / Gammaℝ (2 * s.1) *
      riemannZeta u * riemannZeta (2 * s.1 - u) =
      (Gammaℝ u * riemannZeta u) * (Gammaℝ (2 * s.1 - u) * riemannZeta (2 * s.1 - u)) /
        Gammaℝ (2 * s.1) := by ring
  rw [he, gammaR_zeta_xi hu0 hu_ne1, gammaR_zeta_xi hwu0 hwu_ne1]
  field_simp [hG, hu_ne0, sub_ne_zero.mpr hu_ne1, hwu_ne0, sub_ne_zero.mpr hwu_ne1]
  ring

/-- Clearing the moving pole factors extends the exact physical Mellin identity across
the common strip, including its removable points. -/
theorem upperMayerCore_mellin_cleared (s : upperMayerResonances) {u : ℂ}
    (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    (Gammaℝ (2 * s.1) * u * (u - 1) * (2 * s.1 - u) * (2 * s.1 - u - 1)) *
      mellin (mayerPeriodCore s.1) u =
      4 * symbol (2 * s.1) u * _root_.RHTower.xi u * _root_.RHTower.xi (2 * s.1 - u) := by
  let V : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
  let V₀ : Set ℂ := {z | 0 < z.re ∧ z.re < 2 * s.1.re}
  let F : ℂ → ℂ := fun z =>
    (Gammaℝ (2 * s.1) * z * (z - 1) * (2 * s.1 - z) * (2 * s.1 - z - 1)) *
      mellin (mayerPeriodCore s.1) z -
      4 * symbol (2 * s.1) z * _root_.RHTower.xi z * _root_.RHTower.xi (2 * s.1 - z)
  have hVo : IsOpen V := isOpen_Ioo.preimage Complex.continuous_re
  have hV₀o : IsOpen V₀ := isOpen_Ioo.preimage Complex.continuous_re
  have hVconv : Convex ℝ V := by
    intro x hx y hy a b ha hb hab
    simp only [V, mem_setOf_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by linarith only [hab]
      simpa [hb1] using hy
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      constructor
      · exact add_pos_of_pos_of_nonneg (mul_pos hap hx.1) (mul_nonneg hb hy.1.le)
      · have hax : a * x.re < a * 1 := mul_lt_mul_of_pos_left hx.2 hap
        have hby : b * y.re ≤ b * 1 := mul_le_mul_of_nonneg_left hy.2.le hb
        linarith only [hax, hby, hab]
  have hF : AnalyticOnNhd ℂ F V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro z hz
    have hm := upperMayerCore_mellin_differentiableAt s
      (by linarith only [s.2.2.2.1, hz.1] : 2 * s.1.re - 1 < z.re) hz.2
    have hd : DifferentiableAt ℂ (fun z : ℂ =>
        Gammaℝ (2 * s.1) * z * (z - 1) * (2 * s.1 - z) * (2 * s.1 - z - 1)) z := by
      fun_prop
    have hsym := resonantSymbol_differentiableAt s (by linarith only [hz.1]) hz.2
    have hxi := _root_.RHTower.xi_differentiable z
    have hshift := (_root_.RHTower.xi_differentiable (2 * s.1 - z)).comp z
      ((differentiableAt_const (2 * s.1)).sub differentiableAt_id)
    exact ((hd.mul hm).sub (((hsym.const_mul 4).mul hxi).mul hshift)).differentiableWithinAt
  have hcenter : (s.1.re : ℂ) ∈ V₀ := by
    change 0 < s.1.re ∧ s.1.re < 2 * s.1.re
    exact ⟨s.2.2.1, by linarith only [s.2.2.1]⟩
  have hcenterV : (s.1.re : ℂ) ∈ V := by
    change 0 < s.1.re ∧ s.1.re < 1
    exact ⟨s.2.2.1, by linarith only [s.2.2.2.1]⟩
  have hzero : EqOn F 0 V := by
    apply hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hVconv.isPreconnected hcenterV
    filter_upwards [hV₀o.mem_nhds hcenter] with z hz
    exact sub_eq_zero.mpr (resonantMellin_cleared_narrow s hz.1 hz.2)
  exact sub_eq_zero.mp (hzero ⟨hu0, hu1⟩)

/-- Away from the removable moving point, the literal Mellin transform equals the xi kernel. -/
theorem upperMayerCore_mellin_eq_kernel (s : upperMayerResonances) {u : ℂ}
    (hu0 : 0 < u.re) (hu1 : u.re < 1) (huw : u ≠ 2 * s.1) :
    mellin (mayerPeriodCore s.1) u = resonantMellinKernel s u := by
  have hu_ne0 : u ≠ 0 := by intro h; rw [h, Complex.zero_re] at hu0; exact lt_irrefl 0 hu0
  have hu_ne1 : u ≠ 1 := by intro h; rw [h, Complex.one_re] at hu1; exact lt_irrefl 1 hu1
  have hwun1 : 2 * s.1 - u - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith only [hr, hu0, s.2.2.2.1]
  have hG : Gammaℝ (2 * s.1) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith only [s.2.2.1])
  unfold resonantMellinKernel
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hG hu_ne0)
    (sub_ne_zero.mpr hu_ne1)) (sub_ne_zero.mpr huw.symm)) hwun1)).mpr
  rw [mul_comm]
  exact upperMayerCore_mellin_cleared s hu0 hu1

#print axioms upperMayerCore_mellin_cleared
#print axioms upperMayerCore_mellin_eq_kernel


private theorem xi_vertical_strip_bound (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖_root_.RHTower.xi z‖ ≤ C := by
  have hc : ContinuousOn (fun t : ℝ => _root_.RHTower.xi (t : ℂ)) (Icc a b) :=
    ((_root_.RHTower.xi_differentiable.continuous).comp Complex.continuous_ofReal).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun z hza hzb => ?_⟩
  exact (_root_.RHTower.XiGlobalKummer.norm_xi_le_real_axis z).trans
    ((Complex.re_le_norm _).trans ((hC z.re ⟨hza, hzb⟩).trans (le_max_left _ _)))

private theorem resonant_gamma_denominator_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : upperMayerResonances,
      ‖(Gamma ((2 * s.1 + 1) / 2))⁻¹‖ ≤ C * Real.exp (Real.pi * s.1.im) := by
  obtain ⟨C, hC, hb⟩ := HTGeometry.exists_bound_Real_Gamma_Icc (a := 1) (b := 2) zero_lt_one
  refine ⟨C / Real.pi, by positivity, fun s => ?_⟩
  have hre : ((2 * s.1 + 1) / 2).re = s.1.re + 1 / 2 := by simp; ring
  have him : ((2 * s.1 + 1) / 2).im = s.1.im := by simp
  have hy := (upperMayerResonance_reciprocal_bound s).1
  have hbase := HTGeometry.norm_inv_Gamma_le_shift
    (z := (2 * s.1 + 1) / 2) (by rw [hre]; linarith only [s.2.2.2.1])
    (by rw [him, abs_of_pos s.2.1]; linarith only [hy])
  rw [hre, him, abs_of_pos s.2.1] at hbase
  have hΓ := hb (2 - (s.1.re + 1 / 2))
    (by linarith only [s.2.2.2.1]) (by linarith only [s.2.2.1])
  calc
    _ ≤ Real.Gamma (2 - (s.1.re + 1 / 2)) * Real.exp (Real.pi * s.1.im) / Real.pi := hbase
    _ ≤ C * Real.exp (Real.pi * s.1.im) / Real.pi :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hΓ (Real.exp_pos _).le) Real.pi_pos.le
    _ = _ := by ring

private theorem resonantSymbol_strip_bound {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : upperMayerResonances, ∀ u : ℂ,
      a ≤ u.re → u.re ≤ b → ‖symbol (2 * s.1) u‖ ≤ C * Real.exp (Real.pi * s.1.im) := by
  obtain ⟨C₁, hC₁, hΓ₁⟩ := HTGeometry.exists_bound_Real_Gamma_Icc
    (a := (a + 1) / 2) (b := (b + 1) / 2) (by linarith only [ha])
  obtain ⟨C₂, hC₂, hΓ₂⟩ := HTGeometry.exists_bound_Real_Gamma_Icc
    (a := (1 - b) / 2) (b := (2 - a) / 2) (by linarith only [hb])
  obtain ⟨D, hD, hd⟩ := resonant_gamma_denominator_bound
  refine ⟨C₁ * C₂ * D / ‖(Real.pi : ℂ) ^ (1 / 2 : ℂ)‖, by positivity, fun s u hua hub => ?_⟩
  have hr₁ : ((u + 1) / 2).re = (u.re + 1) / 2 := by simp
  have hr₂ : ((2 * s.1 + 1 - u) / 2).re = (2 * s.1.re + 1 - u.re) / 2 := by simp
  have hg₁ : ‖Gamma ((u + 1) / 2)‖ ≤ C₁ := by
    apply (HTGeometry.norm_Gamma_le_Gamma_re (by rw [hr₁]; linarith only [ha, hua])).trans
    rw [hr₁]
    exact hΓ₁ _ (by linarith only [hua]) (by linarith only [hub])
  have hg₂ : ‖Gamma ((2 * s.1 + 1 - u) / 2)‖ ≤ C₂ := by
    apply (HTGeometry.norm_Gamma_le_Gamma_re
      (by rw [hr₂]; linarith only [s.2.2.1, hub, hb])).trans
    rw [hr₂]
    exact hΓ₂ _ (by linarith only [s.2.2.1, hub]) (by linarith only [s.2.2.2.1, hua])
  calc
    _ = (‖Gamma ((u + 1) / 2)‖ * ‖Gamma ((2 * s.1 + 1 - u) / 2)‖ *
        ‖(Gamma ((2 * s.1 + 1) / 2))⁻¹‖) / ‖(Real.pi : ℂ) ^ (1 / 2 : ℂ)‖ := by
      simp only [symbol, norm_div, norm_mul, norm_inv]
      ring
    _ ≤ (C₁ * C₂ * (D * Real.exp (Real.pi * s.1.im))) / ‖(Real.pi : ℂ) ^ (1 / 2 : ℂ)‖ :=
      div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul hg₁ hg₂ (norm_nonneg _) hC₁) (hd s)
          (norm_nonneg _) (mul_nonneg hC₁ hC₂)) (norm_nonneg _)
    _ = _ := by ring

private theorem resonant_gammaR_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : upperMayerResonances,
      ‖(Gammaℝ (2 * s.1))⁻¹‖ ≤ C * Real.exp (Real.pi * s.1.im) := by
  obtain ⟨C, hC, hb⟩ := HTGeometry.exists_bound_norm_inv_Gammaℝ 0 1 (by norm_num)
  refine ⟨C, hC, fun s => ?_⟩
  have hre : (2 * s.1).re = 2 * s.1.re := by simp
  have him : (2 * s.1).im = 2 * s.1.im := by simp
  have hy := (upperMayerResonance_reciprocal_bound s).1
  have h := hb (2 * s.1) (by rw [hre]; linarith only [s.2.2.1])
    (by rw [hre]; linarith only [s.2.2.2.1])
    (by rw [him, abs_of_pos (mul_pos (by norm_num) s.2.1)]; linarith only [hy])
  rw [him, abs_of_pos (mul_pos (by norm_num) s.2.1),
    show Real.pi * (2 * s.1.im) / 2 = Real.pi * s.1.im by ring] at h
  exact h

private theorem resonantMellin_numerator_strip_bound {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : upperMayerResonances, ∀ u : ℂ, a ≤ u.re → u.re ≤ b →
      ‖4 * symbol (2 * s.1) u * _root_.RHTower.xi u * _root_.RHTower.xi (2 * s.1 - u) /
        Gammaℝ (2 * s.1)‖ ≤ C * Real.exp (2 * Real.pi * s.1.im) := by
  obtain ⟨S, hS, hs⟩ := resonantSymbol_strip_bound ha hb
  obtain ⟨X, hX, hx⟩ := xi_vertical_strip_bound a b
  obtain ⟨Y, hY, hy⟩ := xi_vertical_strip_bound (-b) (1 - a)
  obtain ⟨G, hG, hg⟩ := resonant_gammaR_bound
  refine ⟨4 * S * X * Y * G, by positivity, fun s u hua hub => ?_⟩
  have hx' := hx u hua hub
  have hy' := hy (2 * s.1 - u)
    (by simp; linarith only [s.2.2.1, hub]) (by simp; linarith only [s.2.2.2.1, hua])
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (4 * (S * Real.exp (Real.pi * s.1.im)) * X * Y) *
        (G * Real.exp (Real.pi * s.1.im)) :=
      mul_le_mul
        (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hs s u hua hub) (by norm_num))
          hx' (norm_nonneg _) (by positivity)) hy' (norm_nonneg _) (by positivity))
        (hg s) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show 2 * Real.pi * s.1.im = Real.pi * s.1.im + Real.pi * s.1.im by ring, Real.exp_add]
      ring

#print axioms resonantMellin_numerator_strip_bound


private theorem resonantMellinKernel_strip_bound {a b δ : ℝ}
    (ha : -1 < a) (hb : b < 1) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : upperMayerResonances, ∀ u : ℂ,
      a ≤ u.re → u.re ≤ b → δ ≤ ‖u‖ → δ ≤ ‖u - 1‖ →
      δ ≤ ‖2 * s.1 - u‖ → δ ≤ ‖2 * s.1 - u - 1‖ →
      ‖resonantMellinKernel s u‖ ≤ C * Real.exp (2 * Real.pi * s.1.im) := by
  obtain ⟨C, hC, hc⟩ := resonantMellin_numerator_strip_bound ha hb
  refine ⟨C / δ ^ 4, by positivity, fun s u hua hub hu0 hu1 hwu0 hwu1 => ?_⟩
  have hp : δ ^ 4 ≤ ‖u‖ * ‖u - 1‖ * ‖2 * s.1 - u‖ * ‖2 * s.1 - u - 1‖ := by
    calc
      _ = δ * δ * δ * δ := by ring
      _ ≤ _ := by gcongr
  calc
    _ = ‖4 * symbol (2 * s.1) u * _root_.RHTower.xi u * _root_.RHTower.xi (2 * s.1 - u) /
          Gammaℝ (2 * s.1)‖ /
        (‖u‖ * ‖u - 1‖ * ‖2 * s.1 - u‖ * ‖2 * s.1 - u - 1‖) := by
      simp only [resonantMellinKernel, norm_mul, div_eq_mul_inv, mul_inv, norm_inv]
      ring
    _ ≤ ‖4 * symbol (2 * s.1) u * _root_.RHTower.xi u * _root_.RHTower.xi (2 * s.1 - u) /
          Gammaℝ (2 * s.1)‖ / δ ^ 4 :=
      div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hδ 4) hp
    _ ≤ C * Real.exp (2 * Real.pi * s.1.im) / δ ^ 4 :=
      div_le_div_of_nonneg_right (hc s u hua hub) (pow_nonneg hδ.le 4)
    _ = _ := by ring

private theorem pole_distance_on_half_ball {Ω : Set ℂ} {z : ℂ} {r : ℝ}
    (hball : Metric.ball z r ⊆ Ω) {u : ℂ} (hu : u ∈ Metric.ball z (r / 2))
    {p : ℂ} (hp : p ∉ Ω) : r / 2 ≤ ‖u - p‖ := by
  have hsep : r ≤ dist p z := le_of_not_gt fun h => hp (hball h)
  have htri := dist_triangle p u z
  change dist u z < r / 2 at hu
  rw [← dist_eq_norm, dist_comm u p]
  linarith only [hsep, htri, hu]

private theorem gaussianKernel_normal_on {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (J : Set upperMayerResonances) (Ω : Set ℂ)
    (hΩ : IsOpen Ω) (hstrip : ∀ u ∈ Ω, -1 < u.re ∧ u.re < 1)
    (h0 : (0 : ℂ) ∉ Ω) (h1 : (1 : ℂ) ∉ Ω)
    (hpoles : ∀ s ∈ J, 2 * s.1 ∉ Ω ∧ 2 * s.1 - 1 ∉ Ω) :
    SummableLocallyUniformlyOn
      (fun s : J => fun u : ℂ =>
        (Real.exp (-ε * s.1.1.im ^ 2) : ℂ) * x (upperMayerZero s.1) * resonantMellinKernel s.1 u) Ω := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
    (g := fun u => ∑' s : J,
      (Real.exp (-ε * s.1.1.im ^ 2) : ℂ) * x (upperMayerZero s.1) * resonantMellinKernel s.1 u)
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  let a : ℝ := (z.re - 1) / 2
  let b : ℝ := (z.re + 1) / 2
  have ha : -1 < a := by dsimp [a]; linarith only [(hstrip z hz).1]
  have hb : b < 1 := by dsimp [b]; linarith only [(hstrip z hz).2]
  have haz : a < z.re := by dsimp [a]; linarith only [(hstrip z hz).1]
  have hzb : z.re < b := by dsimp [b]; linarith only [(hstrip z hz).2]
  have hopen : IsOpen (Ω ∩ {u : ℂ | u.re ∈ Ioo a b}) :=
    hΩ.inter (isOpen_Ioo.preimage Complex.continuous_re)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z ⟨hz, haz, hzb⟩
  have hsmall : Metric.ball z (r / 2) ⊆ Metric.ball z r :=
    Metric.ball_subset_ball (by linarith only [hr])
  obtain ⟨C, hC, hbound⟩ := resonantMellinKernel_strip_bound ha hb (half_pos hr)
  have hmaj : Summable (fun s : upperMayerResonances =>
      (C * ‖x‖) * (Real.exp (-ε * s.1.im ^ 2) * Real.exp (2 * Real.pi * s.1.im))) := by
    simpa only [pow_zero, mul_one] using
      (upperMayer_gaussian_growth_summable hε (2 * Real.pi) 0).mul_left (C * ‖x‖)
  refine ⟨Metric.ball z (r / 2), nhdsWithin_le_nhds (Metric.ball_mem_nhds z (half_pos hr)), ?_⟩
  apply HasSumUniformlyOn.of_norm_le_summable (hmaj.subtype J)
  intro s u hu
  have hur := (hball (hsmall hu)).2
  have hdist (p : ℂ) (hp : p ∉ Ω) : r / 2 ≤ ‖u - p‖ :=
    pole_distance_on_half_ball (hball := fun t ht => (hball ht).1) hu hp
  have hu0 : r / 2 ≤ ‖u‖ := by simpa only [sub_zero] using hdist 0 h0
  have hu1 : r / 2 ≤ ‖u - 1‖ := hdist 1 h1
  have hwu0 : r / 2 ≤ ‖2 * s.1.1 - u‖ := by
    rw [norm_sub_rev]
    exact hdist (2 * s.1.1) (hpoles s.1 s.2).1
  have hwu1 : r / 2 ≤ ‖2 * s.1.1 - u - 1‖ := by
    rw [show 2 * s.1.1 - u - 1 = (2 * s.1.1 - 1) - u by ring, norm_sub_rev]
    exact hdist (2 * s.1.1 - 1) (hpoles s.1 s.2).2
  have hk := hbound s.1 u hur.1.le hur.2.le hu0 hu1 hwu0 hwu1
  have hx := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x (upperMayerZero s.1)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ (Real.exp (-ε * s.1.1.im ^ 2) * ‖x‖) *
        (C * Real.exp (2 * Real.pi * s.1.1.im)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le) hk
        (norm_nonneg _) (by positivity)
    _ = _ := by dsimp only [Function.comp_def]; ring

#print axioms gaussianKernel_normal_on


/-- The upper Mellin strip with the two translated xi zero sets removed. -/
def mellinPoleDomain : Set ℂ :=
  {u | -1 < u.re ∧ u.re < 1 ∧ 0 < u.im ∧
    _root_.RHTower.xi u ≠ 0 ∧ _root_.RHTower.xi (u + 1) ≠ 0}

private theorem mellinPoleDomain_isOpen : IsOpen mellinPoleDomain := by
  have hxi : IsOpen {u : ℂ | _root_.RHTower.xi u ≠ 0} :=
    _root_.RHTower.isClosed_xiZeroSet.isOpen_compl
  have hshift : IsOpen {u : ℂ | _root_.RHTower.xi (u + 1) ≠ 0} :=
    hxi.preimage (continuous_id.add continuous_const)
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter (hxi.inter hshift)))

private theorem upperMayer_xi_zero (s : upperMayerResonances) : _root_.RHTower.xi (2 * s.1) = 0 :=
  (isMayerScatteringResonance_iff_xi_zero s.2.2.1 s.2.2.2.1).mp s.2.2

private theorem zero_not_mellinPoleDomain : (0 : ℂ) ∉ mellinPoleDomain := by
  intro h
  exact (lt_irrefl 0) h.2.2.1

private theorem one_not_mellinPoleDomain : (1 : ℂ) ∉ mellinPoleDomain := by
  intro h
  exact (lt_irrefl 0) h.2.2.1

private theorem upperMayer_poles_not_mem (s : upperMayerResonances) :
    2 * s.1 ∉ mellinPoleDomain ∧ 2 * s.1 - 1 ∉ mellinPoleDomain := by
  constructor
  · intro h
    exact h.2.2.2.1 (upperMayer_xi_zero s)
  · intro h
    have hn := h.2.2.2.2
    rw [sub_add_cancel] at hn
    exact hn (upperMayer_xi_zero s)

/-- The Gaussian sum of the continued physical Mellin kernels. -/
def gaussianMellinContinuation (ε : ℝ) (x : ℓ²(zetaZeroConfig.carrier, ℂ)) (u : ℂ) : ℂ :=
  ∑' s : upperMayerResonances,
    (Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s) * resonantMellinKernel s u

/-- Gaussian damping makes the continued core kernels locally normally summable away from poles. -/
theorem gaussianMellinContinuation_normal {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    SummableLocallyUniformlyOn
      (fun s : upperMayerResonances => fun u : ℂ =>
        (Real.exp (-ε * s.1.im ^ 2) : ℂ) * x (upperMayerZero s) * resonantMellinKernel s u)
      mellinPoleDomain := by
  have h := gaussianKernel_normal_on hε x Set.univ mellinPoleDomain mellinPoleDomain_isOpen
    (fun u hu => ⟨hu.1, hu.2.1⟩) zero_not_mellinPoleDomain one_not_mellinPoleDomain
    (fun s _ => upperMayer_poles_not_mem s)
  exact HTGeometry.SummableLocallyUniformlyOn.comp_injective_open mellinPoleDomain_isOpen h
    (e := fun s : upperMayerResonances => (⟨s, Set.mem_univ s⟩ : (Set.univ : Set upperMayerResonances)))
    (by intro s t hst; exact congrArg Subtype.val hst)

private theorem resonantMellinKernel_differentiableAt (s : upperMayerResonances) {u : ℂ}
    (hu0 : -1 < u.re) (hu1 : u.re < 1) (h0 : u ≠ 0) (h1 : u ≠ 1)
    (hw0 : u ≠ 2 * s.1) (hw1 : u ≠ 2 * s.1 - 1) :
    DifferentiableAt ℂ (resonantMellinKernel s) u := by
  have hsym := resonantSymbol_differentiableAt s hu0 hu1
  have hxi := _root_.RHTower.xi_differentiable u
  have hshift := (_root_.RHTower.xi_differentiable (2 * s.1 - u)).comp u
    ((differentiableAt_const (2 * s.1)).sub differentiableAt_id)
  have hd : DifferentiableAt ℂ (fun z : ℂ =>
      Gammaℝ (2 * s.1) * z * (z - 1) * (2 * s.1 - z) * (2 * s.1 - z - 1)) u := by fun_prop
  have hG : Gammaℝ (2 * s.1) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith only [s.2.2.1])
  have hw1' : 2 * s.1 - u - 1 ≠ 0 := by
    rw [show 2 * s.1 - u - 1 = (2 * s.1 - 1) - u by ring]
    exact sub_ne_zero.mpr hw1.symm
  exact (((hsym.const_mul 4).mul hxi).mul hshift).div hd
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hG h0)
      (sub_ne_zero.mpr h1)) (sub_ne_zero.mpr hw0.symm)) hw1')

/-- The normally convergent Gaussian kernel sum is holomorphic on the punctured upper strip. -/
theorem gaussianMellinContinuation_differentiableOn {ε : ℝ} (hε : 0 < ε)
    (x : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    DifferentiableOn ℂ (gaussianMellinContinuation ε x) mellinPoleDomain := by
  apply (gaussianMellinContinuation_normal hε x).differentiableOn mellinPoleDomain_isOpen
  intro s u hu
  have h0 : u ≠ 0 := fun h => zero_not_mellinPoleDomain (h ▸ hu)
  have h1 : u ≠ 1 := fun h => one_not_mellinPoleDomain (h ▸ hu)
  have hw0 : u ≠ 2 * s.1 := fun h => (upperMayer_poles_not_mem s).1 (h ▸ hu)
  have hw1 : u ≠ 2 * s.1 - 1 := fun h => (upperMayer_poles_not_mem s).2 (h ▸ hu)
  exact (resonantMellinKernel_differentiableAt s hu.1 hu.2.1 h0 h1 hw0 hw1).const_mul _

private theorem xi_ne_zero_low_upper {u : ℂ} (hu0 : 0 < u.re) (hu1 : u.re < 1)
    (hui : 0 < u.im) (hu4 : u.im < 4) : _root_.RHTower.xi u ≠ 0 := by
  intro hz
  have hr : (u / 2).re = u.re / 2 := by simp
  have hi : (u / 2).im = u.im / 2 := by simp
  have hs0 : 0 < (u / 2).re := by rw [hr]; linarith only [hu0]
  have hs1 : (u / 2).re < 1 / 2 := by rw [hr]; linarith only [hu1]
  have hsi : 0 < (u / 2).im := by rw [hi]; linarith only [hui]
  have hs : IsMayerScatteringResonance (u / 2) :=
    (isMayerScatteringResonance_iff_xi_zero hs0 hs1).mpr
      (by rw [show (2 : ℂ) * (u / 2) = u by ring]; exact hz)
  let s : upperMayerResonances := ⟨u / 2, hsi, hs⟩
  have hy := (upperMayerResonance_reciprocal_bound s).1
  change 2 ≤ (u / 2).im at hy
  rw [hi] at hy
  linarith only [hy, hu4]

private theorem half_add_I_mem_mellinPoleDomain : (1 / 2 + I : ℂ) ∈ mellinPoleDomain := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · exact xi_ne_zero_low_upper (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact _root_.RHTower.xi_ne_zero_of_one_lt_re (by norm_num)

private theorem mellinPoleDomain_preconnected : IsPreconnected mellinPoleDomain := by
  let V : Set ℂ := {u | -1 < u.re ∧ u.re < 1 ∧ 0 < u.im}
  let Z : Set ℂ := {u | _root_.RHTower.xi u = 0 ∨ _root_.RHTower.xi (u + 1) = 0}
  have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))
  have hVc : Convex ℝ V := by
    intro x hx y hy a b ha hb hab
    simp only [V, mem_setOf_eq, Complex.add_re, Complex.smul_re, Complex.add_im,
      Complex.smul_im, smul_eq_mul] at hx hy ⊢
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by linarith only [hab]
      simpa [hb1] using hy
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      refine ⟨?_, ?_, add_pos_of_pos_of_nonneg (mul_pos hap hx.2.2) (mul_nonneg hb hy.2.2.le)⟩
      · have hx' := mul_lt_mul_of_pos_left hx.1 hap
        have hy' := mul_le_mul_of_nonneg_left hy.1.le hb
        linarith only [hx', hy', hab]
      · have hx' := mul_lt_mul_of_pos_left hx.2.1 hap
        have hy' := mul_le_mul_of_nonneg_left hy.2.1.le hb
        linarith only [hx', hy', hab]
  have hz : {u : ℂ | _root_.RHTower.xi u = 0}.Countable :=
    _root_.RHTower.isClosed_xiZeroSet.isLindelof.countable_of_isDiscrete
      _root_.RHTower.isDiscrete_xiZeroSet
  have hshift : {u : ℂ | _root_.RHTower.xi (u + 1) = 0}.Countable :=
    hz.preimage (show Function.Injective (fun u : ℂ => u + 1) from
      fun _ _ h => add_right_cancel h)
  have hZ : Z.Countable := hz.union hshift
  have he : mellinPoleDomain = V \ Z := by
    ext u
    simp only [mellinPoleDomain, V, Z, mem_setOf_eq, Set.mem_sdiff, not_or]
    tauto
  rw [he]
  apply HTGeometry.isPreconnected_diff_of_countable_of_convex_complex hVc hVo hZ
    (a := (1 / 2 + I : ℂ))
  rw [← he]
  exact half_add_I_mem_mellinPoleDomain

#print axioms gaussianMellinContinuation_normal
#print axioms gaussianMellinContinuation_differentiableOn
#print axioms mellinPoleDomain_preconnected

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
