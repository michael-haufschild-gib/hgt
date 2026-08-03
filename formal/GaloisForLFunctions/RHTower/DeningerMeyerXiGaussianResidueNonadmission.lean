import GaloisForLFunctions.RHTower.XiOrdinateEndpointObstruction
import GaloisForLFunctions.RHTower.DeningerMeyerXiGaussianGammaResidue
import GaloisForLFunctions.RHTower.FuchsProlateScale
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# Nonadmission of the forced Gaussian--Gamma residue packet

The singular Deninger--Meyer lift has a coefficient-faithful completed residue at every Xi-divisor
copy.  At the safe Gaussian centre `c = 2`, this module proves that the raw residue packet cannot
belong to the ordinary unweighted `ℓ²` incidence completion.

The mechanism is stronger than pointwise nonadmission.  Euler reflection and the Gaussian
quadratic exponent show that the unique analytic factor which flattens the residue tends to zero
cofinally on the actual Xi divisor.  Since the factor times the residue is identically one, the
residue norm tends cofinally to infinity.  Hence the raw packet is not square-summable.

The positive survivor is exact: every diagonal source-faithful admission has the form
`h * normalizer`, and its weighted residue packet is square-summable exactly when the independent
horizon grade `h` is square-summable.  Analytic residue normalization and global source grading
are therefore separate, unavoidable gates.
-/

open Complex Filter Topology Set
open scoped Real

namespace RHTower.DeningerMeyerGaussianGreen

noncomputable section

/-- Coarse exponential bound for complex sine, sufficient for the uniform strip Gamma estimate. -/
theorem norm_sin_le_exp_norm (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo]
  calc
    ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2
        ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ (Real.exp ‖-z * I‖ + Real.exp ‖z * I‖) / 2 := by
          gcongr <;> exact Complex.norm_exp_le_exp_norm _
    _ = Real.exp ‖z‖ := by simp

/-- On the reflected half-strip, the Gamma modulus is bounded by `sqrt π`. -/
theorem norm_Gamma_one_sub_half_le_sqrt_pi
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ‖Complex.Gamma (1 - rho / 2)‖ ≤ Real.sqrt Real.pi := by
  have hre : 0 < (1 - rho / 2).re := by simp; linarith
  have hnorm := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re hre
  have hy : (1 - (rho / 2).re) ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> simp <;> linarith
  have hx : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by norm_num
  have hxy : (1 / 2 : ℝ) < 1 - (rho / 2).re := by simp; linarith
  have hanti := Real.Gamma_strictAntiOn_Ioc hx hy hxy
  calc
    ‖Complex.Gamma (1 - rho / 2)‖ ≤ Real.Gamma (1 - rho / 2).re := hnorm
    _ = Real.Gamma (1 - (rho / 2).re) := by congr 1
    _ ≤ Real.Gamma (1 / 2) := hanti.le
    _ = Real.sqrt Real.pi := Real.Gamma_one_half_eq

/-- Euler reflection turns the reflected-half-strip upper bound into a reciprocal Gamma bound. -/
theorem inv_norm_Gamma_half_le_sin
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ‖Complex.Gamma (rho / 2)‖⁻¹ ≤
      ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ / Real.sqrt Real.pi := by
  have hzre : 0 < (rho / 2).re := by simp; linarith
  have hz : Complex.Gamma (rho / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hzre
  have hother := norm_Gamma_one_sub_half_le_sqrt_pi hstrip
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (rho / 2)
  have hn := congrArg (fun w : ℂ => ‖w‖) hrefl
  simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at hn
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ ≠ 0 := by
    intro hs
    rw [hs, div_zero] at hn
    have hgo : Complex.Gamma (1 - rho / 2) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    exact (mul_ne_zero (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hgo)) hn
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have ha : ‖Complex.Gamma (rho / 2)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have heq : ‖Complex.Gamma (rho / 2)‖⁻¹ =
      ‖Complex.Gamma (1 - rho / 2)‖ *
        ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ / Real.pi := by
    have hn' : ‖Complex.Gamma (rho / 2)‖ *
        ‖Complex.Gamma (1 - rho / 2)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ = Real.pi :=
      (eq_div_iff hsin).mp hn
    apply (eq_div_iff Real.pi_ne_zero).2
    rw [inv_mul_eq_div]
    apply (div_eq_iff ha).2
    calc
      Real.pi = ‖Complex.Gamma (rho / 2)‖ *
          ‖Complex.Gamma (1 - rho / 2)‖ *
            ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ := hn'.symm
      _ = ‖Complex.Gamma (1 - rho / 2)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ *
            ‖Complex.Gamma (rho / 2)‖ := by ring
  rw [heq]
  calc
    ‖Complex.Gamma (1 - rho / 2)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ / Real.pi
        ≤ Real.sqrt Real.pi *
          ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ / Real.pi := by
            gcongr
    _ = ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ / Real.sqrt Real.pi := by
          apply (div_eq_div_iff Real.pi_ne_zero (ne_of_gt hsqrt)).2
          calc
            Real.sqrt Real.pi *
                  ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ * Real.sqrt Real.pi
                = (Real.sqrt Real.pi * Real.sqrt Real.pi) *
                    ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ := by ring
            _ = Real.pi * ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ := by rw [hpi]
            _ = ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ * Real.pi := by ring

/-- Uniform open-strip bound for the reciprocal real Archimedean Gamma factor. -/
theorem inv_norm_GammaR_le_exp_norm
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ‖Complex.Gammaℝ rho‖⁻¹ ≤
      Real.exp ((Real.pi / 2) * ‖rho‖) := by
  have hhalf := inv_norm_Gamma_half_le_sin hstrip
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hrpow : Real.pi ^ (rho.re / 2) ≤ Real.sqrt Real.pi := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hpi1 (by linarith)
  have hsin := norm_sin_le_exp_norm ((Real.pi : ℂ) * (rho / 2))
  rw [GaloisForLFunctions.HTGeometry.norm_Gammaℝ]
  have hneg : -rho.re / 2 = -(rho.re / 2) := by ring
  rw [hneg, Real.rpow_neg Real.pi_nonneg]
  have hp : Real.pi ^ (rho.re / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have hg : ‖Complex.Gamma (rho / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
  have hinv : ((Real.pi ^ (rho.re / 2))⁻¹ *
      ‖Complex.Gamma (rho / 2)‖)⁻¹ =
      Real.pi ^ (rho.re / 2) * ‖Complex.Gamma (rho / 2)‖⁻¹ := by
    field_simp [hp, hg]
  rw [hinv]
  calc
    Real.pi ^ (rho.re / 2) * ‖Complex.Gamma (rho / 2)‖⁻¹
        ≤ Real.sqrt Real.pi *
            (‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ / Real.sqrt Real.pi) := by
              gcongr
    _ = ‖Complex.sin ((Real.pi : ℂ) * (rho / 2))‖ := by
          field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]
    _ ≤ Real.exp ‖(Real.pi : ℂ) * (rho / 2)‖ := hsin
    _ = Real.exp ((Real.pi / 2) * ‖rho‖) := by
          congr 1
          rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos]
          norm_num
          ring

/-- The Gaussian Mellin character decays quadratically in centered spectral norm, uniformly across
the critical strip. -/
theorem norm_gaussianMellinCharacter_two_le
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    ‖gaussianMellinCharacter 2 rho‖ ≤
      Real.exp ((17 / 4 - ‖rho - 1 / 2‖ ^ 2) / (4 * Real.pi)) := by
  rw [gaussianMellinCharacter, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre2 : (rho.re - 2) ^ 2 ≤ (4 : ℝ) := by nlinarith
  have hrehalf : (rho.re - 1 / 2) ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hnormsq : ‖rho - 1 / 2‖ ^ 2 =
      (rho.re - 1 / 2) ^ 2 + rho.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hexpre : (((rho - 2) ^ 2 / (4 * (Real.pi : ℂ))).re) =
      ((rho.re - 2) ^ 2 - rho.im ^ 2) / (4 * Real.pi) := by
    simp [Complex.div_re, Complex.normSq_apply, pow_two, Complex.mul_re]
    field_simp [Real.pi_ne_zero]
  rw [hexpre]
  rw [hnormsq]
  have hden : 0 < 4 * Real.pi := by positivity
  apply (div_le_div_iff₀ hden hden).2
  nlinarith

/-- Beyond centered norm four, the rational factor in the residue normalizer has norm at most one. -/
theorem norm_sub_two_le_norm_mul_norm_sub_one_of_four_le
    {rho : ℂ} (hfour : 4 ≤ ‖rho - 1 / 2‖) :
    ‖rho - 2‖ ≤ ‖rho‖ * ‖rho - 1‖ := by
  set t : ℝ := ‖rho - 1 / 2‖ with ht
  have ht0 : 0 ≤ t - 1 / 2 := by dsimp [t]; linarith
  have hrho : t - 1 / 2 ≤ ‖rho‖ := by
    have h := norm_add_le rho (-(1 / 2 : ℂ))
    have heq : rho + -(1 / 2 : ℂ) = rho - 1 / 2 := by ring
    rw [heq, ← ht] at h
    norm_num at h ⊢
    linarith
  have hrho1 : t - 1 / 2 ≤ ‖rho - 1‖ := by
    have h := norm_add_le (rho - 1) (1 / 2 : ℂ)
    have heq : rho - 1 + (1 / 2 : ℂ) = rho - 1 / 2 := by ring
    rw [heq, ← ht] at h
    norm_num at h ⊢
    linarith
  have hprod : (t - 1 / 2) ^ 2 ≤ ‖rho‖ * ‖rho - 1‖ := by
    rw [pow_two]
    exact mul_le_mul hrho hrho1 ht0 (norm_nonneg _)
  have hnum : ‖rho - 2‖ ≤ t + 3 / 2 := by
    have h := norm_sub_le (rho - 1 / 2) (3 / 2 : ℂ)
    have heq : (rho - 1 / 2) - (3 / 2 : ℂ) = rho - 2 := by ring
    rw [heq, ← ht] at h
    norm_num at h
    exact h
  have hquad : t + 3 / 2 ≤ (t - 1 / 2) ^ 2 := by
    dsimp [t] at hfour
    nlinarith
  exact hnum.trans (hquad.trans hprod)

/-- Forced completed Xi/Green residue at each divisor-multiplicity copy, based at `c = 2`. -/
def xiGaussianGammaResiduePacket (q : XiZeroCopy) : ℂ :=
  -(2 * (Real.pi : ℂ) * archFactor (q.1 : ℂ) /
    (gaussianMellinCharacter 2 (q.1 : ℂ) * ((q.1 : ℂ) - 2)))

/-- The unique diagonal analytic factor that flattens the forced residue packet. -/
def xiGaussianGammaResidueNormalizer (q : XiZeroCopy) : ℂ :=
  -(gaussianMellinCharacter 2 (q.1 : ℂ) * ((q.1 : ℂ) - 2) /
    (2 * (Real.pi : ℂ) * archFactor (q.1 : ℂ)))

/-- Exact coefficientwise flattening: the analytic normalizer times the actual residue is one. -/
theorem xiGaussianGammaResidueNormalizer_mul_packet (q : XiZeroCopy) :
    xiGaussianGammaResidueNormalizer q * xiGaussianGammaResiduePacket q = 1 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have harch : archFactor (q.1 : ℂ) ≠ 0 := archFactor_ne_zero_strip hstrip
  have hchar : gaussianMellinCharacter 2 (q.1 : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hr2 : (q.1 : ℂ) - 2 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [xiGaussianGammaResidueNormalizer, xiGaussianGammaResiduePacket]
  field_simp [harch, hchar, hr2, Real.pi_ne_zero]

/-- Normal form separating Gaussian, rational, and reciprocal-Gamma factors. -/
theorem xiGaussianGammaResidueNormalizer_eq (q : XiZeroCopy) :
    xiGaussianGammaResidueNormalizer q =
      -(1 / (Real.pi : ℂ)) * gaussianMellinCharacter 2 (q.1 : ℂ) *
        (((q.1 : ℂ) - 2) / ((q.1 : ℂ) * ((q.1 : ℂ) - 1))) *
          (Complex.Gammaℝ (q.1 : ℂ))⁻¹ := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hrho : (q.1 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    linarith
  have hrho1 : (q.1 : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.one_re] at hre
    linarith
  have hgamma : Complex.Gammaℝ (q.1 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hstrip.1
  rw [xiGaussianGammaResidueNormalizer, archFactor]
  field_simp [hrho, hrho1, hgamma, Real.pi_ne_zero]

/-- Explicit cofinal Gaussian majorant for the residue normalizer. -/
theorem norm_xiGaussianGammaResidueNormalizer_le
    (q : XiZeroCopy) (hfour : 4 ≤ ‖(q.1 : ℂ) - 1 / 2‖) :
    ‖xiGaussianGammaResidueNormalizer q‖ ≤
      Real.exp ((17 / 4 - ‖(q.1 : ℂ) - 1 / 2‖ ^ 2) / (4 * Real.pi) +
        (Real.pi / 2) * (‖(q.1 : ℂ) - 1 / 2‖ + 1 / 2)) := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hchar := norm_gaussianMellinCharacter_two_le hstrip
  have hgamma := inv_norm_GammaR_le_exp_norm hstrip
  have hpoly := norm_sub_two_le_norm_mul_norm_sub_one_of_four_le hfour
  have hrhonorm : ‖(q.1 : ℂ)‖ ≤ ‖(q.1 : ℂ) - 1 / 2‖ + 1 / 2 := by
    have h := norm_add_le ((q.1 : ℂ) - 1 / 2) (1 / 2 : ℂ)
    have heq : (q.1 : ℂ) - 1 / 2 + (1 / 2 : ℂ) = (q.1 : ℂ) := by ring
    rw [heq] at h
    norm_num at h
    exact h
  have hgamma' : ‖Complex.Gammaℝ (q.1 : ℂ)‖⁻¹ ≤
      Real.exp ((Real.pi / 2) * (‖(q.1 : ℂ) - 1 / 2‖ + 1 / 2)) := by
    exact hgamma.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrhonorm (by positivity)))
  have hratio : ‖((q.1 : ℂ) - 2) /
      ((q.1 : ℂ) * ((q.1 : ℂ) - 1))‖ ≤ 1 := by
    rw [norm_div, norm_mul]
    exact (div_le_one (mul_pos
      (norm_pos_iff.mpr (by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.zero_re] at hre
        linarith))
      (norm_pos_iff.mpr (by
        apply sub_ne_zero.mpr
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.one_re] at hre
        linarith)))).mpr hpoly
  rw [xiGaussianGammaResidueNormalizer_eq, norm_mul, norm_mul, norm_mul, norm_neg,
    norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    norm_inv]
  calc
    (1 / Real.pi) * ‖gaussianMellinCharacter 2 (q.1 : ℂ)‖ *
          ‖((q.1 : ℂ) - 2) / ((q.1 : ℂ) * ((q.1 : ℂ) - 1))‖ *
          ‖Complex.Gammaℝ (q.1 : ℂ)‖⁻¹
        ≤ 1 * Real.exp ((17 / 4 - ‖(q.1 : ℂ) - 1 / 2‖ ^ 2) /
            (4 * Real.pi)) * 1 *
          Real.exp ((Real.pi / 2) * (‖(q.1 : ℂ) - 1 / 2‖ + 1 / 2)) := by
            gcongr
            · exact (div_le_one Real.pi_pos).mpr (by linarith [Real.one_le_pi_div_two])
    _ = Real.exp ((17 / 4 - ‖(q.1 : ℂ) - 1 / 2‖ ^ 2) / (4 * Real.pi) +
        (Real.pi / 2) * (‖(q.1 : ℂ) - 1 / 2‖ + 1 / 2)) := by
          rw [one_mul, mul_one, Real.exp_add]

/-- Scalar envelope appearing in the cofinal normalizer bound. -/
def xiGaussianGammaResidueNormalizerEnvelope (t : ℝ) : ℝ :=
  Real.exp ((17 / 4 - t ^ 2) / (4 * Real.pi) +
    (Real.pi / 2) * (t + 1 / 2))

/-- Quadratic Gaussian decay dominates the linear reciprocal-Gamma growth. -/
theorem tendsto_xiGaussianGammaResidueNormalizerEnvelope_atTop :
    Tendsto xiGaussianGammaResidueNormalizerEnvelope atTop (nhds 0) := by
  let C : ℝ := 17 / (16 * Real.pi) + Real.pi / 4
  let b : ℝ := 1 / (8 * Real.pi)
  have hb : 0 < b := by dsimp [b]; positivity
  have hgauss := tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero 0 hb
  have hbase : Tendsto (fun t : ℝ => Real.exp (-(b * t ^ 2))) atTop (nhds 0) := by
    simpa using hgauss
  have hmajor : Tendsto (fun t : ℝ => Real.exp C * Real.exp (-(b * t ^ 2)))
      atTop (nhds 0) := by
    simpa using hbase.const_mul (Real.exp C)
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => Real.exp_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop (4 * Real.pi ^ 2)] with t ht
  dsimp [xiGaussianGammaResidueNormalizerEnvelope, C, b]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 ≤ t := by nlinarith
  have hlinear : Real.pi / 2 * t ≤ t ^ 2 / (8 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * Real.pi)).2
    nlinarith
  calc
    (17 / 4 - t ^ 2) / (4 * Real.pi) + Real.pi / 2 * (t + 1 / 2)
        ≤ 17 / (16 * Real.pi) + Real.pi / 4 - t ^ 2 / (8 * Real.pi) := by
          field_simp [Real.pi_ne_zero] at hlinear ⊢
          nlinarith
    _ = 17 / (16 * Real.pi) + Real.pi / 4 + -(1 / (8 * Real.pi) * t ^ 2) := by ring

/-- The unique analytic residue normalizer tends to zero cofinally on the actual Xi divisor. -/
theorem tendsto_xiGaussianGammaResidueNormalizer_cofinite_zero :
    Tendsto xiGaussianGammaResidueNormalizer cofinite (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have henv : Tendsto
      (fun q : XiZeroCopy => xiGaussianGammaResidueNormalizerEnvelope
        ‖(q.1 : ℂ) - 1 / 2‖) cofinite (nhds 0) :=
    tendsto_xiGaussianGammaResidueNormalizerEnvelope_atTop.comp
      (by simpa only [norm_xiSpectralPoint] using tendsto_norm_xiSpectralPoint_cofinite)
  refine squeeze_zero' (Filter.Eventually.of_forall fun q => norm_nonneg _) ?_ henv
  filter_upwards [tendsto_norm_xiSpectralPoint_cofinite.eventually
    (eventually_ge_atTop 4)] with q hq
  rw [norm_xiSpectralPoint] at hq
  exact norm_xiGaussianGammaResidueNormalizer_le q hq

/-- **Cofinal blow-up.** The forced residue norms escape every finite bound off a finite set of
actual Xi divisor copies. -/
theorem tendsto_norm_xiGaussianGammaResiduePacket_cofinite_atTop :
    Tendsto (fun q : XiZeroCopy => ‖xiGaussianGammaResiduePacket q‖)
      cofinite atTop := by
  have hnorm0 : Tendsto (fun q : XiZeroCopy =>
      ‖xiGaussianGammaResidueNormalizer q‖) cofinite (nhds 0) :=
    by simpa using tendsto_xiGaussianGammaResidueNormalizer_cofinite_zero.norm
  have hnormGT : Tendsto (fun q : XiZeroCopy =>
      ‖xiGaussianGammaResidueNormalizer q‖) cofinite (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [nhdsWithin]
    refine tendsto_inf.2 ⟨hnorm0, tendsto_principal.2 ?_⟩
    exact Filter.Eventually.of_forall fun q => by
      have hprod := xiGaussianGammaResidueNormalizer_mul_packet q
      have hne : xiGaussianGammaResidueNormalizer q ≠ 0 := by
        intro h
        rw [h, zero_mul] at hprod
        norm_num at hprod
      exact norm_pos_iff.mpr hne
  have hinv : Tendsto (fun q : XiZeroCopy =>
      ‖xiGaussianGammaResidueNormalizer q‖⁻¹) cofinite atTop :=
    tendsto_inv_nhdsGT_zero.comp hnormGT
  apply hinv.congr'
  exact Filter.Eventually.of_forall fun q => by
    have hprod := xiGaussianGammaResidueNormalizer_mul_packet q
    have hn := congrArg (fun z : ℂ => ‖z‖) hprod
    simp only [norm_mul, norm_one] at hn
    have hw : ‖xiGaussianGammaResidueNormalizer q‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      intro h
      rw [h, zero_mul] at hprod
      norm_num at hprod
    field_simp [hw]
    simpa [mul_comm] using hn.symm

/-- **Unweighted incidence obstruction.** The actual forced residue packet is not square-summable
on the Xi divisor copies, hence does not lie in the ordinary unweighted `ℓ²` incidence completion. -/
theorem not_summable_norm_sq_xiGaussianGammaResiduePacket :
    ¬ Summable (fun q : XiZeroCopy => ‖xiGaussianGammaResiduePacket q‖ ^ 2) := by
  intro hsum
  have hsq0 : Tendsto (fun q : XiZeroCopy => ‖xiGaussianGammaResiduePacket q‖ ^ 2)
      cofinite (nhds 0) := hsum.tendsto_cofinite_zero
  have hnorm0 : Tendsto (fun q : XiZeroCopy => ‖xiGaussianGammaResiduePacket q‖)
      cofinite (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq0
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hpacket0 : Tendsto xiGaussianGammaResiduePacket cofinite (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0
  have hprod0 : Tendsto (fun q : XiZeroCopy =>
      xiGaussianGammaResidueNormalizer q * xiGaussianGammaResiduePacket q)
      cofinite (nhds 0) := by
    simpa only [zero_mul] using
      tendsto_xiGaussianGammaResidueNormalizer_cofinite_zero.mul hpacket0
  have hone : Tendsto (fun _q : XiZeroCopy => (1 : ℂ)) cofinite (nhds 1) :=
    tendsto_const_nhds
  have heq : (fun q : XiZeroCopy =>
      xiGaussianGammaResidueNormalizer q * xiGaussianGammaResiduePacket q) =
      (fun _q : XiZeroCopy => (1 : ℂ)) := by
    funext q
    exact xiGaussianGammaResidueNormalizer_mul_packet q
  rw [heq] at hprod0
  have h10 : (1 : ℂ) = 0 := tendsto_nhds_unique hone hprod0
  norm_num at h10

/-- Exact survivor: after the forced analytic normalizer, every diagonal admission is precisely an
independent horizon grade `h`; no analytic freedom remains in the residue cancellation. -/
theorem horizonGrade_mul_normalizer_mul_packet (h : XiZeroCopy → ℂ) (q : XiZeroCopy) :
    (h q * xiGaussianGammaResidueNormalizer q) * xiGaussianGammaResiduePacket q = h q := by
  rw [mul_assoc, xiGaussianGammaResidueNormalizer_mul_packet, mul_one]

/-- Weighted residue admission is equivalent to square summability of the independent horizon
grade.  The analytic normalizer alone corresponds to the non-summable constant grade `h = 1`. -/
theorem summable_weighted_packet_iff_horizonGrade (h : XiZeroCopy → ℂ) :
    Summable (fun q : XiZeroCopy =>
      ‖(h q * xiGaussianGammaResidueNormalizer q) *
        xiGaussianGammaResiduePacket q‖ ^ 2) ↔
      Summable (fun q : XiZeroCopy => ‖h q‖ ^ 2) := by
  simp_rw [horizonGrade_mul_normalizer_mul_packet]

end

end RHTower.DeningerMeyerGaussianGreen
