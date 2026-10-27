import GaloisForLFunctions.ConjugateDiagonalGeometry.XiSourceCurrent
import GaloisForLFunctions.ConjugateDiagonalGeometry.XiLogRegularization

/-!
# Positive arithmetic readings of the conjugate diagonal

Compact source integrals use the smooth nonnegative density constructed from
xi and xi'. Removing its regulator retains every divisor multiplicity.
Exhausting the plane then recovers each collided depth-kernel moment.
-/

open Complex MeasureTheory Filter Set Laplacian InnerProductSpace
open scoped Laplacian Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization HTGeometry _root_.RHTower

/-- A twice continuously differentiable planar test has a continuous Laplacian. -/
theorem continuous_test_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (Δ φ) := by
  have hd (v : ℂ) : Continuous (Bottcher.dderiv φ v) := by
    have hfirst : ContDiff ℝ 1 (fun z => fderiv ℝ φ z v) :=
      (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact (hfirst.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have he : Δ φ = fun z => Bottcher.dderiv φ 1 z + Bottcher.dderiv φ Complex.I z :=
    funext (Bottcher.laplacian_eq_dderiv φ hφ)
  rw [he]
  exact (hd 1).add (hd Complex.I)

/-- Differentiation preserves compact support of the planar test. -/
theorem compact_test_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) : HasCompactSupport (Δ φ) := by
  have he : Δ φ = fun z => Bottcher.dderiv φ 1 z + Bottcher.dderiv φ Complex.I z :=
    funext (Bottcher.laplacian_eq_dderiv φ hφ)
  rw [he]
  exact ((hc.fderiv_apply ℝ 1).fderiv_apply ℝ 1).add
    ((hc.fderiv_apply ℝ Complex.I).fderiv_apply ℝ Complex.I)

/-- Each compact diagonal kernel is tested against a smooth positive arithmetic density. -/
def xiPositiveReading (f : CompactTest) (L : ℝ) (j n k : ℕ) : ℝ :=
  ∫ z : ℂ, sourceCutoff n z * sourceDepthKernel f L j z *
    xiCurvatureDensity (sourceRegulator k) z

theorem continuous_xiCurvatureDensity {ε : ℝ} (hε : 0 < ε) :
    Continuous (xiCurvatureDensity ε) := by
  have he : xiCurvatureDensity ε = fun z =>
      (1 / 2 : ℝ) * Δ (xiLogPotential ε) z := by
    funext z
    rw [laplacian_xiLogPotential hε]
    ring
  rw [he]
  exact continuous_const.mul (continuous_test_laplacian (contDiff_xiLogPotential hε))

/-- Every finite source reading is an ordinary integrable compact density. -/
theorem integrable_xiPositiveReading (f : CompactTest) (L : ℝ) (j n k : ℕ) :
    Integrable (fun z : ℂ => sourceCutoff n z * sourceDepthKernel f L j z *
      xiCurvatureDensity (sourceRegulator k) z) :=
  (((sourceCutoff n).continuous.mul (contDiff_sourceDepthKernel f L j).continuous).mul
    (continuous_xiCurvatureDensity (sourceRegulator_pos k))).integrable_of_hasCompactSupport
      ((sourceCutoff n).hasCompactSupport.mul_right.mul_right)

theorem xiPositiveReading_nonneg (f : CompactTest) (L : ℝ) (j n k : ℕ) :
    0 ≤ xiPositiveReading f L j n k := by
  apply integral_nonneg
  intro z
  exact mul_nonneg (mul_nonneg (sourceCutoff n).nonneg
    (mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) j)))
    (xiCurvatureDensity_nonneg (sourceRegulator_pos k).le z)

/-- Compact testing moves the source curvature onto the logarithmic potential. -/
theorem twice_integral_xiCurvatureDensity (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (k : ℕ) :
    2 * (∫ z, φ z * xiCurvatureDensity (sourceRegulator k) z) =
      ∫ z, xiLogPotential (sourceRegulator k) z * Δ φ z := by
  calc
    2 * (∫ z, φ z * xiCurvatureDensity (sourceRegulator k) z) =
        ∫ z, φ z * (2 * xiCurvatureDensity (sourceRegulator k) z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ = ∫ z, φ z * Δ (xiLogPotential (sourceRegulator k)) z := by
      simp_rw [laplacian_xiLogPotential (sourceRegulator_pos k)]
    _ = ∫ z, Δ φ z * xiLogPotential (sourceRegulator k) z :=
      source_green_identity _ φ (contDiff_xiLogPotential (sourceRegulator_pos k)) hp hc
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      exact mul_comm _ _

/-- The positive arithmetic densities converge to the xi current on every compact smooth test. -/
theorem tendsto_integral_xiCurvatureDensity (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) :
    Tendsto (fun k => ∫ z, φ z * xiCurvatureDensity (sourceRegulator k) z) atTop
      (𝓝 ((1 / 2 : ℝ) * ∫ z, Real.log ‖xi z‖ * Δ φ z)) := by
  have h := (tendsto_integral_xiLogPotential (Δ φ)
    (continuous_test_laplacian hp) (compact_test_laplacian hp hc)).const_mul (1 / 2 : ℝ)
  have heq (k : ℕ) : (1 / 2 : ℝ) *
      (∫ z, xiLogPotential (sourceRegulator k) z * Δ φ z) =
        ∫ z, φ z * xiCurvatureDensity (sourceRegulator k) z := by
    rw [← twice_integral_xiCurvatureDensity φ hp hc]
    ring
  simpa only [heq] using h

/-- Removing the regulator computes the exact cutoff divisor trace, without simplicity assumptions. -/
theorem tendsto_xiPositiveReading (f : CompactTest) (L : ℝ) (j n : ℕ) :
    Tendsto (fun k => xiPositiveReading f L j n k) atTop
      (𝓝 (Real.pi * ∑' ρ : zetaZeroConfig.carrier,
        sourceCutoff n ρ * (zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j))) := by
  let φ : ℂ → ℝ := fun z => sourceCutoff n z * sourceDepthKernel f L j z
  have hp : ContDiff ℝ 2 φ :=
    (sourceCutoff n).contDiff.mul (contDiff_sourceDepthKernel f L j)
  have hc : HasCompactSupport φ := (sourceCutoff n).hasCompactSupport.mul_right
  have h := tendsto_integral_xiCurvatureDensity φ hp hc
  have htarget : (1 / 2 : ℝ) * (∫ z, Real.log ‖xi z‖ * Δ φ z) =
      Real.pi * ∑' ρ : zetaZeroConfig.carrier,
        sourceCutoff n ρ * (zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j) := by
    change (1 / 2 : ℝ) * sourceCurrentReading f L j n = _
    rw [sourceCurrentReading_eq_trace]
    ring
  rw [htarget] at h
  simpa only [xiPositiveReading, φ] using h

/-- An iterated arithmetic limit; its definition contains no sum over zeros. -/
def xiSourceMoment (f : CompactTest) (L : ℝ) (j : ℕ) : ℝ :=
  Real.pi⁻¹ * limUnder atTop (fun n => limUnder atTop (xiPositiveReading f L j n))

/-- Cutoff exhaustion after regulator removal recovers every convergent collided kernel moment. -/
theorem xiSourceMoment_eq_trace (f : CompactTest) (L : ℝ) (j : ℕ) :
    xiSourceMoment f L j =
      ∑' ρ : zetaZeroConfig.carrier, zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j := by
  have houter : Tendsto (fun n => Real.pi * ∑' ρ : zetaZeroConfig.carrier,
      sourceCutoff n ρ * (zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j)) atTop
        (𝓝 (Real.pi * ∑' ρ : zetaZeroConfig.carrier,
          zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j)) := by
    have hconst (x : ℝ) : (1 / 2 : ℝ) * (2 * Real.pi * x) = Real.pi * x := by ring
    simpa only [sourceCurrentReading_eq_trace, hconst] using
      (tendsto_sourceCurrentReading f L j).const_mul (1 / 2 : ℝ)
  unfold xiSourceMoment
  simp_rw [(tendsto_xiPositiveReading f L j _).limUnder_eq]
  rw [houter.limUnder_eq, inv_mul_cancel_left₀ Real.pi_ne_zero]

/-- The arithmetic source metric on compact source tests. -/
def xiSourceMetric (f : CompactTest) : ℝ := xiSourceMoment f 0 0

/-- The source-defined positive metric computes the actual conjugate-diagonal form. -/
theorem xiSourceMetric_eq_collided (f : CompactTest) :
    xiSourceMetric f = collidedForm zetaZeroConfig f.1 := by
  simpa only [xiSourceMetric, pow_zero, mul_one, zetaWeight, collidedForm] using
    xiSourceMoment_eq_trace f 0 0

/-- The first source moment computes the complete symmetric Hecke defect. -/
theorem xiSourceMoment_one_eq_heckeDefect (f : CompactTest) (L : ℝ) :
    xiSourceMoment f L 1 = heckeDefect f L := by
  simpa only [pow_one, heckeDefect] using xiSourceMoment_eq_trace f L 1

/-- Centred translation preserves the natural source-test domain. -/
def sourceTranslate (L : ℝ) (f : CompactTest) : CompactTest :=
  ⟨ArithmeticPolarization.translate L f.1,
    f.2.1.comp (contDiff_id.sub contDiff_const),
    f.2.2.comp_homeomorph (Homeomorph.subRight L)⟩

/-- The translation law holds on the positive source densities before either limiting operation. -/
theorem xiPositiveReading_second_difference (f : CompactTest) (L : ℝ) (n k : ℕ) :
    xiPositiveReading (sourceTranslate L f) 0 0 n k +
      xiPositiveReading (sourceTranslate (-L) f) 0 0 n k -
        2 * xiPositiveReading f 0 0 n k = xiPositiveReading f L 1 n k := by
  have hp := integrable_xiPositiveReading (sourceTranslate L f) 0 0 n k
  have hm := integrable_xiPositiveReading (sourceTranslate (-L) f) 0 0 n k
  have h0 := integrable_xiPositiveReading f 0 0 n k
  have hpm : Integrable (fun z : ℂ =>
      sourceCutoff n z * sourceDepthKernel (sourceTranslate L f) 0 0 z *
        xiCurvatureDensity (sourceRegulator k) z +
      sourceCutoff n z * sourceDepthKernel (sourceTranslate (-L) f) 0 0 z *
        xiCurvatureDensity (sourceRegulator k) z) := hp.add hm
  unfold xiPositiveReading
  rw [← integral_add hp hm, ← integral_const_mul, ← integral_sub hpm (h0.const_mul 2)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [sourceDepthKernel, sourceTranslate, pow_zero, mul_one, pow_one,
    tr_translate, Complex.normSq_mul, normSq_exp_translate, depthKernel, Real.cosh_eq]
  rw [show 2 * (z.re - 1 / 2) * (-L) = -(2 * (z.re - 1 / 2) * L) by ring]
  ring

/-- The arithmetic metric's full translation defect is its nonnegative first source moment. -/
theorem xiSourceMetric_second_difference (f : CompactTest) (L : ℝ) :
    xiSourceMetric (sourceTranslate L f) + xiSourceMetric (sourceTranslate (-L) f) -
      2 * xiSourceMetric f = xiSourceMoment f L 1 := by
  simp only [xiSourceMetric_eq_collided, sourceTranslate,
    xiSourceMoment_one_eq_heckeDefect]
  exact (heckeDefect_eq_second_difference f L).symm

end GaloisForLFunctions.ConjugateDiagonalGeometry
