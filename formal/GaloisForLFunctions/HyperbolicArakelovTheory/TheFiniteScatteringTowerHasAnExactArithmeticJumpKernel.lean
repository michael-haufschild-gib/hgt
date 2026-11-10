import GaloisForLFunctions.HyperbolicArakelovTheory.TheIntrinsicGeometricWeilDiagonal
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine
import GaloisForLFunctions.HTGeometry.LSeriesPowerTwist
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The exact arithmetic kernel of a finite scattering tower

A tower of height `N` retains the archimedean jump density
`(1 - exp(-N*t)) * archLevyDensity t` and prime contacts weighted by
`1 - n⁻ᴺ`. The finite geometric series removes the apparent singularity at
zero. Its critically shifted Laplace transform is the difference of the
Gamma logarithmic derivatives at `s+N` and `s`.

Tilted Fourier inversion and the Euler telescope identify the full packet
energy of the raw primitive-pair scattering fields, with the two polar
moments and the geometric Robin subtraction retained exactly.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter Set Topology
open scoped Classical ENNReal BigOperators InnerProductSpace
namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
open _root_.RHTower

/-- The finite-height archimedean jump kernel, with its removable value at zero. -/
def scatteringCutoffKernel (N : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t / 2) / (1 + Real.exp (-t)) *
    ∑ j ∈ Finset.range N, Real.exp (-(j : ℝ) * t)

theorem scatteringCutoffKernel_nonneg (N : ℕ) (t : ℝ) :
    0 ≤ scatteringCutoffKernel N t := by
  exact mul_nonneg (div_nonneg (Real.exp_pos _).le (by positivity))
    (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)

theorem continuous_scatteringCutoffKernel (N : ℕ) :
    Continuous (scatteringCutoffKernel N) := by
  unfold scatteringCutoffKernel
  have hd (t : ℝ) : 1 + Real.exp (-t) ≠ 0 := ne_of_gt (by positivity)
  fun_prop (disch := exact hd _)

theorem scatteringCutoffKernel_bound (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    scatteringCutoffKernel N t ≤ N * Real.exp (-t / 2) := by
  have hsum : (∑ j ∈ Finset.range N, Real.exp (-(j : ℝ) * t)) ≤ N := by
    calc
      _ ≤ ∑ _j ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (Nat.cast_nonneg j)) ht)
      _ = _ := by simp
  have hfrac : Real.exp (-t / 2) / (1 + Real.exp (-t)) ≤ Real.exp (-t / 2) :=
    div_le_self (Real.exp_pos _).le (by linarith only [Real.exp_pos (-t)])
  unfold scatteringCutoffKernel
  exact (mul_le_mul hfrac hsum (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)
    (Real.exp_pos _).le).trans_eq (mul_comm _ _)

/-- Scattering height kills the long Gamma tower by an exponential factor in distance. -/
theorem scatteringCutoffKernel_eq (N : ℕ) {t : ℝ} (ht : 0 < t) :
    scatteringCutoffKernel N t = (1 - Real.exp (-(N : ℝ) * t)) * archLevyDensity t := by
  let q := Real.exp (-t)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hqne : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hplus : 1 + q ≠ 0 := by positivity
  have hexp (j : ℕ) : Real.exp (-(j : ℝ) * t) = q ^ j := by
    rw [show -(j : ℝ) * t = (j : ℝ) * (-t) by ring, Real.exp_nat_mul]
  have htwo : Real.exp (-2 * t) = q ^ 2 := by simpa using hexp 2
  have hsum : (∑ j ∈ Finset.range N, q ^ j) = (1 - q ^ N) / (1 - q) := by
    apply (eq_div_iff hqne).mpr
    have h := geom_sum_mul q N
    linear_combination -h
  unfold scatteringCutoffKernel archLevyDensity
  simp_rw [hexp]
  rw [htwo, hsum, show (1 - q ^ 2 : ℝ) = (1 - q) * (1 + q) by ring]
  change Real.exp (-t / 2) / (1 + q) * ((1 - q ^ N) / (1 - q)) = _
  field_simp [hqne, hplus]

private theorem integral_scatteringCutoff_majorant {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    IntegrableOn (fun t : ℝ => (N : ℝ) * Real.exp (-s.re * t)) (Ioi 0) :=
  (exp_neg_integrableOn_Ioi 0 hs).const_mul _

private def cutoffLaplaceKernel (N : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  (scatteringCutoffKernel N t : ℂ) * Complex.exp (-(s - 1 / 2) * t)

private theorem norm_cutoffLaplaceKernel (N : ℕ) (s : ℂ) (t : ℝ) :
    ‖cutoffLaplaceKernel N s t‖ =
      scatteringCutoffKernel N t * Real.exp (-(s.re - 1 / 2) * t) := by
  rw [cutoffLaplaceKernel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (scatteringCutoffKernel_nonneg N t), Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.div_ofNat_re,
    Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem cutoffLaplaceKernel_bound (N : ℕ) (s : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖cutoffLaplaceKernel N s t‖ ≤ N * Real.exp (-s.re * t) := by
  rw [norm_cutoffLaplaceKernel]
  calc
    _ ≤ (N * Real.exp (-t / 2)) * Real.exp (-(s.re - 1 / 2) * t) :=
      mul_le_mul_of_nonneg_right (scatteringCutoffKernel_bound N ht) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private theorem continuous_cutoffLaplaceKernel (N : ℕ) (s : ℂ) :
    Continuous (cutoffLaplaceKernel N s) := by
  exact ((Complex.continuous_ofReal.comp (continuous_scatteringCutoffKernel N)).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))

private theorem integrable_cutoffLaplaceKernel (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (cutoffLaplaceKernel N s) (Ioi 0) := by
  apply (integral_scatteringCutoff_majorant hs N).mono'
  · exact (continuous_cutoffLaplaceKernel N s).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cutoffLaplaceKernel_bound N s ht.le


private theorem cutoffLaplaceKernel_eq (N : ℕ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    cutoffLaplaceKernel N s t = Complex.exp (-s * t) *
      (((1 - Real.exp (-(N : ℝ) * t)) / (1 - Real.exp (-2 * t)) : ℝ) : ℂ) := by
  have he : (Real.exp (-t / 2) : ℂ) * Complex.exp (-(s - 1 / 2) * t) =
      Complex.exp (-s * t) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [cutoffLaplaceKernel, scatteringCutoffKernel_eq N ht, archLevyDensity]
  calc
    _ = (((1 - Real.exp (-(N : ℝ) * t)) / (1 - Real.exp (-2 * t)) : ℝ) : ℂ) *
        ((Real.exp (-t / 2) : ℂ) * Complex.exp (-(s - 1 / 2) * t)) := by
      push_cast
      ring
    _ = _ := by rw [he, mul_comm]

/- The finite geometric approximants have one integrable majorant, uniform in truncation. -/
private def cutoffLaplacePartial (N : ℕ) (s : ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1),
    (Complex.exp (-(s + 2 * j) * t) - Complex.exp (-(s + N + 2 * j) * t))

private theorem cutoffLaplacePartial_eq (N : ℕ) (s : ℂ) (m : ℕ)
    {t : ℝ} (ht : 0 < t) :
    cutoffLaplacePartial N s m t = cutoffLaplaceKernel N s t *
      ((1 - Real.exp (-2 * t) ^ (m + 1) : ℝ) : ℂ) := by
  let q : ℂ := Real.exp (-2 * t)
  have hqR : (1 - Real.exp (-2 * t) : ℝ) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))).ne'
  have hq : (1 - q : ℂ) ≠ 0 := by
    dsimp only [q]
    exact_mod_cast hqR
  have he (z : ℂ) (j : ℕ) :
      Complex.exp (-(z + 2 * j) * t) = Complex.exp (-z * t) * q ^ j := by
    rw [show -(z + 2 * j) * (t : ℂ) = -z * t + (j : ℂ) * (((-2 * t : ℝ) : ℂ)) by
      push_cast; ring, Complex.exp_add, Complex.exp_nat_mul, ← Complex.ofReal_exp]
  have hn : Complex.exp (-(s + N) * t) =
      Complex.exp (-s * t) * (Real.exp (-(N : ℝ) * t) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hg : (∑ j ∈ Finset.range (m + 1), q ^ j) = (1 - q ^ (m + 1)) / (1 - q) := by
    apply (eq_div_iff hq).mpr
    have h := geom_sum_mul q (m + 1)
    linear_combination -h
  rw [cutoffLaplacePartial]
  simp_rw [he, ← sub_mul]
  rw [← Finset.mul_sum, hn, hg, cutoffLaplaceKernel_eq N s ht]
  change _ = Complex.exp (-s * t) *
    (((1 - Real.exp (-(N : ℝ) * t)) / (1 - Real.exp (-2 * t)) : ℝ) : ℂ) *
      ((1 - Real.exp (-2 * t) ^ (m + 1) : ℝ) : ℂ)
  dsimp only [q]
  push_cast
  ring

private theorem cutoffLaplacePartial_bound (N : ℕ) (s : ℂ) (m : ℕ)
    {t : ℝ} (ht : 0 < t) :
    ‖cutoffLaplacePartial N s m t‖ ≤ N * Real.exp (-s.re * t) := by
  have hq0 : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ht])
  have hp := pow_le_one₀ hq0 hq1 (n := m + 1)
  have hnn : 0 ≤ 1 - Real.exp (-2 * t) ^ (m + 1) := sub_nonneg.mpr hp
  rw [cutoffLaplacePartial_eq N s m ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
  exact (mul_le_of_le_one_right (norm_nonneg _) (by
    linarith only [pow_nonneg hq0 (m + 1)])).trans (cutoffLaplaceKernel_bound N s ht.le)

private theorem tendsto_cutoffLaplacePartial (N : ℕ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun m => cutoffLaplacePartial N s m t) atTop (𝓝 (cutoffLaplaceKernel N s t)) := by
  have hq0 : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [ht])
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).const_mul (cutoffLaplaceKernel N s t)
  simp only [sub_zero, Complex.ofReal_one, mul_one] at h
  exact h.congr fun m => (cutoffLaplacePartial_eq N s m ht).symm

private theorem integrable_exp_shift (s : ℂ) (hs : 0 < s.re) (j : ℕ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s + 2 * j) * t)) (Ioi 0) := by
  apply integrableOn_exp_mul_complex_Ioi _ 0
  norm_num
  linarith only [hs, Nat.cast_nonneg (α := ℝ) j]

private theorem integral_exp_shift (s : ℂ) (hs : 0 < s.re) (j : ℕ) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(s + 2 * j) * t)) = (s + 2 * j)⁻¹ := by
  have hr : (-(s + 2 * j)).re < 0 := by
    norm_num
    linarith only [hs, Nat.cast_nonneg (α := ℝ) j]
  rw [integral_exp_mul_complex_Ioi hr 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg, one_div]

private theorem integral_cutoffLaplacePartial (N : ℕ) {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    (∫ t in Ioi (0 : ℝ), cutoffLaplacePartial N s m t) =
      ∑ j ∈ Finset.range (m + 1), ((s + 2 * j)⁻¹ - (s + N + 2 * j)⁻¹) := by
  have hsN : 0 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hs, Nat.cast_nonneg (α := ℝ) N]
  simp only [cutoffLaplacePartial]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_sub (integrable_exp_shift s hs j) (integrable_exp_shift (s + N) hsN j),
      integral_exp_shift s hs j, integral_exp_shift (s + N) hsN j]
  · intro j _
    exact (integrable_exp_shift s hs j).sub (integrable_exp_shift (s + N) hsN j)

/- Subtracting the two Gauss limits cancels their logarithmic divergences. -/
private theorem tendsto_reciprocal_difference (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun m => ∑ j ∈ Finset.range (m + 1),
      ((s + 2 * j)⁻¹ - (s + N + 2 * j)⁻¹)) atTop
      (𝓝 (logDeriv Complex.Gammaℝ (s + N) - logDeriv Complex.Gammaℝ s)) := by
  have hsN : 0 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hs, Nat.cast_nonneg (α := ℝ) N]
  have hs2 : 0 < (s / 2).re := by simpa only [Complex.div_ofNat_re] using half_pos hs
  have hsN2 : 0 < ((s + N) / 2).re := by simpa only [Complex.div_ofNat_re] using half_pos hsN
  have h := ((Complex.digamma_tendsto_euler hsN2).sub
    (Complex.digamma_tendsto_euler hs2)).div_const (2 : ℂ)
  have hlim : (Complex.digamma ((s + N) / 2) - Complex.digamma (s / 2)) / 2 =
      logDeriv Complex.Gammaℝ (s + N) - logDeriv Complex.Gammaℝ s := by
    rw [GaloisForLFunctions.logDeriv_Gammaℝ hsN, GaloisForLFunctions.logDeriv_Gammaℝ hs]
    unfold gammaRealLogConnection
    ring
  rw [hlim] at h
  refine h.congr fun m => ?_
  calc
    _ = ((∑ j ∈ Finset.range (m + 1), (s / 2 + j)⁻¹) -
      ∑ j ∈ Finset.range (m + 1), ((s + N) / 2 + j)⁻¹) / 2 := by ring
    _ = _ := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      have he (z : ℂ) : (z / 2 + j)⁻¹ = 2 * (z + 2 * j)⁻¹ := by
        rw [show z / 2 + j = (z + 2 * j) / 2 by ring, inv_div]
        rfl
      rw [he, he]
      ring

/-- The Laplace transform of the finite-height kernel is the shifted Gamma difference. -/
theorem laplace_scatteringCutoffKernel (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (0 : ℝ), (scatteringCutoffKernel N t : ℂ) *
      Complex.exp (-(s - 1 / 2) * t)) =
      logDeriv Complex.Gammaℝ (s + N) - logDeriv Complex.Gammaℝ s := by
  have hlim : Tendsto (fun m => ∫ t in Ioi (0 : ℝ), cutoffLaplacePartial N s m t)
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), cutoffLaplaceKernel N s t)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun t : ℝ => (N : ℝ) * Real.exp (-s.re * t))
      ?_ (integral_scatteringCutoff_majorant hs N) ?_ ?_
    · intro m
      exact (by unfold cutoffLaplacePartial; fun_prop :
        Continuous (cutoffLaplacePartial N s m)).aestronglyMeasurable
    · intro m
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cutoffLaplacePartial_bound N s m ht
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact tendsto_cutoffLaplacePartial N s ht
  have hgamma := tendsto_reciprocal_difference N hs
  simp_rw [← integral_cutoffLaplacePartial N hs] at hgamma
  exact tendsto_nhds_unique hlim hgamma


open Zeta23 Zeta23.WeilEF RHTower.WeilLineIntegral RHTower.WeilLineAnyAbscissa

private theorem integrable_Hfn_line_all {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (c : ℝ) :
    Integrable (fun y : ℝ => Hfn k ((c : ℂ) + y * I)) := by
  simpa only [Hfn_line] using
    Zeta23.EF.integrable_paperFT_ofReal
      (Zeta23.EF.integrable_fourier_of_contDiff_two (tilt_contDiff hk (c - 1 / 2))
        (tilt_hasCompactSupport hkc (c - 1 / 2)))

private theorem integrable_line_exponential {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (c t : ℝ) :
    Integrable (fun y : ℝ => Hfn k ((c : ℂ) + y * I) *
      Complex.exp (-((c : ℂ) + y * I - 1 / 2) * t)) := by
  refine (integrable_Hfn_line_all hk hkc c).mul_bdd
    (c := Real.exp (-(c - 1 / 2) * t)) (by fun_prop) ?_
  filter_upwards with y
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.div_ofNat_re, Complex.one_re, mul_zero, zero_mul, sub_zero, add_zero]
  exact le_rfl

/- Tilted Fourier inversion returns the packet at the literal logarithmic displacement. -/
private theorem integral_line_exponential {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (c t : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, Hfn k ((c : ℂ) + y * I) *
      Complex.exp (-((c : ℂ) + y * I - 1 / 2) * t) = k t := by
  have he (y : ℝ) : Complex.exp (-((c : ℂ) + y * I - 1 / 2) * t) =
      (Real.exp (-(c - 1 / 2) * t) : ℂ) * Complex.exp (-I * y * t) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he, Hfn_line]
  have hfactor : (fun y : ℝ => paperFT (tilt k (c - 1 / 2)) y *
      ((Real.exp (-(c - 1 / 2) * t) : ℂ) * Complex.exp (-I * y * t))) =
      fun y : ℝ => (Real.exp (-(c - 1 / 2) * t) : ℂ) *
        (paperFT (tilt k (c - 1 / 2)) y * Complex.exp (-I * y * t)) := by
    funext y
    ring
  rw [hfactor, integral_const_mul, ← mul_assoc,
    mul_comm (1 / (2 * (Real.pi : ℂ))), mul_assoc,
    tilted_inversion hk hkc]
  have hc : (Real.exp (-(c - 1 / 2) * t) : ℂ) *
      (Real.exp ((c - 1 / 2) * t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  calc
    _ = k t * ((Real.exp (-(c - 1 / 2) * t) : ℂ) *
        (Real.exp ((c - 1 / 2) * t) : ℂ)) := by ring
    _ = _ := by rw [hc, mul_one]

private theorem integrable_lineF_exponential {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (c t : ℝ) :
    Integrable (fun y : ℝ => lineF k c y *
      Complex.exp (-((c : ℂ) + y * I - 1 / 2) * t)) := by
  refine ((integrable_line_exponential hk hkc c t).add
    (integrable_line_exponential (k := fun x => k (-x)) (hk.comp contDiff_neg)
      (hkc.comp_homeomorph (Homeomorph.neg ℝ)) c t)).congr
        (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, lineF, Hfn_mirror, add_mul]

private theorem integral_lineF_exponential {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (c t : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, lineF k c y *
      Complex.exp (-((c : ℂ) + y * I - 1 / 2) * t) = k t + k (-t) := by
  simp_rw [lineF, Hfn_mirror, add_mul]
  rw [integral_add (integrable_line_exponential hk hkc c t)
    (integrable_line_exponential (k := fun x => k (-x)) (hk.comp contDiff_neg)
      (hkc.comp_homeomorph (Homeomorph.neg ℝ)) c t), mul_add,
    integral_line_exponential hk hkc,
    integral_line_exponential (k := fun x => k (-x)) (hk.comp contDiff_neg)
      (hkc.comp_homeomorph (Homeomorph.neg ℝ))]

private theorem continuous_lineF {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (c : ℝ) : Continuous (lineF k c) :=
  ((differentiable_Hfn hk hkc).continuous.comp (by fun_prop)).add
    ((differentiable_Hfn hk hkc).continuous.comp (by fun_prop))

private theorem integrable_lineF {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (c : ℝ) : Integrable (lineF k c) := by
  change Integrable (fun y : ℝ => Hfn k ((c : ℂ) + y * I) + Hfn k (1 - c - y * I))
  refine ((integrable_Hfn_line_all hk hkc c).add
    (integrable_Hfn_line_all (k := fun x => k (-x)) (hk.comp contDiff_neg)
      (hkc.comp_homeomorph (Homeomorph.neg ℝ)) c)).congr
        (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, Hfn_mirror]

/- Absolute integrability on the product justifies exchanging the spectral and distance integrals. -/
private theorem integrable_cutoff_line_pair {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Integrable (fun p : ℝ × ℝ => lineF k c p.1 *
      cutoffLaplaceKernel N ((c : ℂ) + p.1 * I) p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hbound := (integrable_lineF hk hkc c).norm.mul_prod
    (integral_scatteringCutoff_majorant (s := (c : ℂ)) (by simpa using hc) N)
  have hm : Continuous (fun p : ℝ × ℝ => lineF k c p.1 *
      cutoffLaplaceKernel N ((c : ℂ) + p.1 * I) p.2) := by
    unfold cutoffLaplaceKernel
    exact ((continuous_lineF hk hkc c).comp continuous_fst).mul
      (((Complex.continuous_ofReal.comp (continuous_scatteringCutoffKernel N)).comp
        continuous_snd).mul (by fun_prop))
  refine hbound.mono' hm.aestronglyMeasurable ?_
  have ht : ∀ᵐ p : ℝ × ℝ ∂volume.prod (volume.restrict (Ioi (0 : ℝ))), 0 < p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards with y
    exact ae_restrict_mem measurableSet_Ioi
  filter_upwards [ht] with p hp
  rw [norm_mul]
  have hb := cutoffLaplaceKernel_bound N ((c : ℂ) + p.1 * I) hp.le
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hb ⊢
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-- Fourier inversion turns the finite scattering Gamma difference into its physical kernel. -/
theorem integral_lineF_gamma_difference {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, lineF k c y *
      (logDeriv Complex.Gammaℝ ((c : ℂ) + y * I + N) -
        logDeriv Complex.Gammaℝ ((c : ℂ) + y * I)) =
      ∫ t in Ioi (0 : ℝ), (scatteringCutoffKernel N t : ℂ) * (k t + k (-t)) := by
  have he (y : ℝ) : lineF k c y *
      (logDeriv Complex.Gammaℝ ((c : ℂ) + y * I + N) -
        logDeriv Complex.Gammaℝ ((c : ℂ) + y * I)) =
      ∫ t in Ioi (0 : ℝ), lineF k c y * cutoffLaplaceKernel N ((c : ℂ) + y * I) t := by
    rw [integral_const_mul]
    congr 1
    exact (laplace_scatteringCutoffKernel N (by simpa using hc)).symm
  rw [integral_congr_ae (Eventually.of_forall he),
    integral_integral_swap (integrable_cutoff_line_pair hk hkc hc N), ← integral_const_mul]
  dsimp only [cutoffLaplaceKernel]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hf : (fun y : ℝ => lineF k c y *
      ((scatteringCutoffKernel N t : ℂ) *
        Complex.exp (-((c : ℂ) + y * I - 1 / 2) * t))) =
      fun y => (scatteringCutoffKernel N t : ℂ) * (lineF k c y *
        Complex.exp (-((c : ℂ) + y * I - 1 / 2) * t)) := by
    funext y
    ring
  dsimp only
  rw [hf, integral_const_mul]
  calc
    _ = (scatteringCutoffKernel N t : ℂ) *
      ((1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, lineF k c y *
        Complex.exp (-((c : ℂ) + y * I - 1 / 2) * t)) := by ring
    _ = _ := by rw [integral_lineF_exponential hk hkc]

/-- The actual Euler contact retained by a finite scattering height. -/
def scatteringHeightMangoldt (N n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (1 - ((n : ℝ)⁻¹) ^ N)

/- The shifted Euler series retains exactly the finite-height prime weight. -/
private theorem heightMangoldt_term (N : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => (scatteringHeightMangoldt N n : ℂ)) s n =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n -
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + N) n := by
  have ht := lseriesPowerTwist_term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (-(N : ℂ)) s n
  simp only [sub_neg_eq_add] at ht
  rw [← ht]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, sub_self]
  · simp only [LSeries.term_of_ne_zero hn, lseriesPowerTwistCoeff,
      scatteringHeightMangoldt, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rw [inv_pow]
    ring

private theorem summable_heightMangoldt (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (scatteringHeightMangoldt N n : ℂ)) s := by
  have hsN : 1 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hs, Nat.cast_nonneg (α := ℝ) N]
  exact (Summable.sub (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hsN)).congr
      fun n => (heightMangoldt_term N s n).symm

private theorem lseries_heightMangoldt (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (scatteringHeightMangoldt N n : ℂ)) s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + N) := by
  have hsN : 1 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hs, Nat.cast_nonneg (α := ℝ) N]
  simp only [LSeries, heightMangoldt_term]
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).tsum_sub
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hsN)

private theorem continuous_LSeries_line_of_summable {a : ℕ → ℂ} {c : ℝ}
    (ha : LSeriesSummable a c) : Continuous (fun y : ℝ => LSeries a ((c : ℂ) + y * I)) := by
  have hcont (n : ℕ) : Continuous (fun y : ℝ => LSeries.term a ((c : ℂ) + y * I) n) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simpa only [LSeries.term_zero] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ (fun y => ?_)
      · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn))
      · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  exact continuous_tsum hcont ha.norm fun n y => by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp

private theorem integrable_Hfn_LSeries {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {a : ℕ → ℂ} {c : ℝ} (ha : LSeriesSummable a c) :
    Integrable (fun y : ℝ => Hfn k ((c : ℂ) + y * I) * LSeries a ((c : ℂ) + y * I)) := by
  exact (integrable_Hfn_line_all hk hkc c).mul_bdd
    (continuous_LSeries_line_of_summable ha).aestronglyMeasurable
    (Eventually.of_forall (norm_LSeries_line_le ha))

private theorem integrable_lineF_LSeries {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {a : ℕ → ℂ} {c : ℝ} (ha : LSeriesSummable a c) :
    Integrable (fun y : ℝ => lineF k c y * LSeries a ((c : ℂ) + y * I)) := by
  refine ((integrable_Hfn_LSeries hk hkc ha).add
    (integrable_Hfn_LSeries (k := fun x => k (-x)) (hk.comp contDiff_neg)
      (hkc.comp_homeomorph (Homeomorph.neg ℝ)) ha)).congr
        (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, lineF, Hfn_mirror, add_mul]

private theorem hasSum_lineF_LSeries {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {a : ℕ → ℂ} {c : ℝ} (ha : LSeriesSummable a c) :
    HasSum (fun n : ℕ => a n / Real.sqrt n * (k (Real.log n) + k (-Real.log n)))
      ((1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, lineF k c y * LSeries a ((c : ℂ) + y * I)) := by
  have hn : ContDiff ℝ 2 (fun x => k (-x)) := hk.comp contDiff_neg
  have hnc := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  simp_rw [lineF, Hfn_mirror, add_mul]
  rw [integral_add (integrable_Hfn_LSeries hk hkc ha)
    (integrable_Hfn_LSeries hn hnc ha), mul_add]
  exact ((hasSum_prime_side_line hk hkc ha).add
    (hasSum_prime_side_line hn hnc ha)).congr_fun fun n => by ring

private theorem renormalizedTower_eq_cutoff {s : ℂ} (hs : 1 < s.re)
    (him : s.im ≠ 0) (N : ℕ) :
    renormalizedTower s N =
      -(logDeriv Complex.Gammaℝ (s + N) - logDeriv Complex.Gammaℝ s) +
        robinCounterterm (s.re + N) + gPair 0 s -
          LSeries (fun n => (scatteringHeightMangoldt N n : ℂ)) s := by
  have hsN : 1 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hs, Nat.cast_nonneg (α := ℝ) N]
  rw [renormalizedTower, geometricTower_eq hs him, completedLogDeriv_eq hs,
    completedLogDeriv_eq hsN, lseries_heightMangoldt N hs]
  simp only [gPair, sub_zero]
  ring

private theorem integrable_lineF_gamma_difference {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Integrable (fun y : ℝ => lineF k c y *
      (logDeriv Complex.Gammaℝ ((c : ℂ) + y * I + N) -
        logDeriv Complex.Gammaℝ ((c : ℂ) + y * I))) := by
  have h := (integrable_cutoff_line_pair hk hkc hc N).integral_prod_left
  refine h.congr (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [integral_const_mul]
  congr 1
  exact laplace_scatteringCutoffKernel N (by simpa using hc)

private theorem integrable_lineF_poles {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc : 1 < c) :
    Integrable (fun y : ℝ => lineF k c y * gPair 0 ((c : ℂ) + y * I)) := by
  have hre (y : ℝ) : ((c : ℂ) + y * I).re = c := by simp
  have hcont : Continuous (fun y : ℝ => gPair 0 ((c : ℂ) + y * I)) := by
    unfold gPair
    refine (continuous_const.div (by fun_prop) (fun y h => ?_)).add
      (continuous_const.div (by fun_prop) (fun y h => ?_))
    · have hr := congrArg Complex.re h
      simp at hr
      linarith only [hc, hr]
    · have hr := congrArg Complex.re h
      simp at hr
      linarith only [hc, hr]
  refine (integrable_lineF hk hkc c).mul_bdd
    (c := 1 / c + 1 / (c - 1)) hcont.aestronglyMeasurable ?_
  filter_upwards with y
  unfold gPair
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_one, sub_zero]
    refine div_le_div_of_nonneg_left zero_le_one (by linarith only [hc]) ?_
    have h := Complex.abs_re_le_norm ((c : ℂ) + y * I)
    rwa [hre, abs_of_pos (by linarith only [hc])] at h
  · rw [norm_div, norm_one]
    refine div_le_div_of_nonneg_left zero_le_one (sub_pos.mpr hc) ?_
    have h := Complex.abs_re_le_norm ((c : ℂ) + y * I - (1 - 0))
    simpa only [Complex.sub_re, hre, sub_zero, Complex.one_re,
      abs_of_pos (sub_pos.mpr hc)] using h

private theorem integral_lineF_constant {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (c : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, lineF k c y = 2 * k 0 := by
  simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, neg_zero,
    two_mul] using integral_lineF_exponential hk hkc c 0

private theorem integral_lineF_poles {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, lineF k (3 / 2) y *
      gPair 0 ((3 / 2 : ℂ) + y * I) = Hfn k 0 + Hfn k 1 := by
  obtain ⟨C, _, hC⟩ := norm_Hfn_le_wide hk hkc 1
  have h := two_line_pair (differentiable_Hfn hk hkc) (c := 3 / 2) (C := C)
    (fun σ t h1 h2 => hC σ t (abs_le.mpr ⟨by linarith only [h1], by linarith only [h2]⟩))
    (z₀ := 0) (by norm_num) (by norm_num)
  simpa only [sub_zero, lineF, Complex.ofReal_div, Complex.ofReal_ofNat] using h

/-- The exact physical packet form at finite scattering height. -/
def scatteringPhysicalPacket (N : ℕ) (k : ℝ → ℂ) : ℂ :=
  2 * robinCounterterm ((3 / 2 : ℝ) + N) * k 0 + Hfn k 0 + Hfn k 1 -
    (∫ t in Ioi (0 : ℝ), (scatteringCutoffKernel N t : ℂ) * (k t + k (-t))) -
    ∑' n : ℕ, (scatteringHeightMangoldt N n : ℂ) / Real.sqrt n *
      (k (Real.log n) + k (-Real.log n))

private theorem integral_four_parts {F G H J : ℝ → ℂ}
    (hF : Integrable F) (hG : Integrable G) (hH : Integrable H) (hJ : Integrable J) :
    (∫ y : ℝ, -F y + G y + H y - J y) =
      -(∫ y : ℝ, F y) + (∫ y : ℝ, G y) + (∫ y : ℝ, H y) - ∫ y : ℝ, J y := by
  have h₁ := integral_sub ((hF.neg.add hG).add hH) hJ
  have h₂ := integral_add (hF.neg.add hG) hH
  have h₃ := integral_add hF.neg hG
  simp only [Pi.add_apply, Pi.neg_apply] at h₁ h₂ h₃
  rw [h₁, h₂, h₃, integral_neg]

/- Keep the Robin term and both polar residues while telescoping the raw scattering symbol. -/
private theorem renormalizedPacket_eq_cutoff {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (N : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, lineF k (3 / 2) y *
      renormalizedTower ((3 / 2 : ℂ) + y * I) N = scatteringPhysicalPacket N k := by
  unfold scatteringPhysicalPacket
  have hiG := integrable_lineF_gamma_difference hk hkc (c := 3 / 2) (by norm_num) N
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hiG
  have hiR := (integrable_lineF hk hkc (3 / 2)).mul_const
    (robinCounterterm ((3 / 2 : ℝ) + N))
  have hiP := integrable_lineF_poles hk hkc (c := 3 / 2) (by norm_num)
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hiP
  have hsum := summable_heightMangoldt N (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)
  have hiL := integrable_lineF_LSeries hk hkc (c := 3 / 2) hsum
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hiL
  have hprime := (hasSum_lineF_LSeries hk hkc (c := 3 / 2) hsum).tsum_eq
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hprime
  have hgamma := integral_lineF_gamma_difference hk hkc (c := 3 / 2) (by norm_num) N
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hgamma
  have hsymbol : (fun y : ℝ => lineF k (3 / 2) y *
      renormalizedTower ((3 / 2 : ℂ) + y * I) N) =ᵐ[volume]
      (fun y => -(lineF k (3 / 2) y *
        (logDeriv Complex.Gammaℝ ((3 / 2 : ℂ) + y * I + N) -
          logDeriv Complex.Gammaℝ ((3 / 2 : ℂ) + y * I))) +
        lineF k (3 / 2) y * robinCounterterm ((3 / 2 : ℝ) + N) +
        lineF k (3 / 2) y * gPair 0 ((3 / 2 : ℂ) + y * I) -
        lineF k (3 / 2) y * LSeries (fun n => (scatteringHeightMangoldt N n : ℂ))
          ((3 / 2 : ℂ) + y * I)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
    rw [renormalizedTower_eq_cutoff (s := (3 / 2 : ℂ) + y * I) (by norm_num) (by simpa using hy)]
    norm_num
    ring
  change (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, lineF k (3 / 2) y *
    renormalizedTower ((3 / 2 : ℂ) + y * I) N = _
  rw [integral_congr_ae hsymbol,
    integral_four_parts hiG hiR hiP hiL, integral_mul_const]
  rw [mul_sub, mul_add, mul_add, mul_neg,
    hgamma,
    integral_lineF_poles hk hkc,
    ← hprime,
    ← mul_assoc, integral_lineF_constant hk hkc]
  ring

/-- The raw primitive-pair scattering energy has exactly the physical cutoff normalization. -/
theorem rawEnergy_eq_cutoff {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (N : ℕ) :
    RawGeometry.energy f N = scatteringPhysicalPacket N (EF.weilTest f f) := by
  rw [RawGeometry.energy_eq, geometricWeilEnergy]
  exact renormalizedPacket_eq_cutoff (EF.weilTest_contDiff hf hf.continuous hfc)
    (EF.weilTest_hasCompactSupport hfc hfc) N


#print axioms laplace_scatteringCutoffKernel
#print axioms rawEnergy_eq_cutoff

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
