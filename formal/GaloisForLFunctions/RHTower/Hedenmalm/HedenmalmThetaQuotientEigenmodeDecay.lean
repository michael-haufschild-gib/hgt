import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaDerivativePrimitiveBounds

/-!
# Rapid decay of the canonically normalized theta divisor quotient mode

The quotient is the literal source space modulo the inverse image of the closed
quantile derivative history. Exact primitive recurrence removes every finite
source-derivative term. The remaining primitive has an actual strip-uniform
weighted norm bound, giving decay of every natural order with real-part threshold
one. The source vector keeps its canonical integral equal to the theta mass; its
quotient remains nonzero. No Riemann-hypothesis premise is used.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.HedenmalmThetaSource
open GaloisForLFunctions.HTGeometry HedenmalmQuantile HedenmalmPrimeTranslation

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

private abbrev HS := SourceSpace thetaSource
private abbrev μS := (volume : Measure ℝ).withDensity (realDensity (sourceWeight thetaSource))
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The literal inverse image of the closed quantile derivative history. -/
def thetaSourceDerivativeHistory : Submodule ℂ HS :=
  thetaQuantileDerivativeHistory.comap (quantileUnitary thetaSource).toLinearMap

theorem thetaSourceDerivativeHistory_isClosed :
    IsClosed (thetaSourceDerivativeHistory : Set HS) :=
  thetaQuantileDerivativeHistory_isClosed.preimage (quantileUnitary thetaSource).continuous

local instance : IsClosed (thetaSourceDerivativeHistory : Set HS) :=
  thetaSourceDerivativeHistory_isClosed

def thetaSourceDerivativeHistoryQuotientProjection :
    HS →L[ℂ] (HS ⧸ thetaSourceDerivativeHistory) := thetaSourceDerivativeHistory.mkQL

theorem thetaSourceDerivativeVector_mem_sourceHistory (n : ℕ) :
    thetaSourceDerivativeVector n ∈ thetaSourceDerivativeHistory := by
  apply Submodule.mem_comap.mpr
  exact thetaQuantileDerivativeVector_mem_history n

theorem thetaSourceDerivativeHistoryQuotientProjection_derivative (n : ℕ) :
    thetaSourceDerivativeHistoryQuotientProjection (thetaSourceDerivativeVector n) = 0 :=
  (Submodule.Quotient.mk_eq_zero thetaSourceDerivativeHistory).mpr
    (thetaSourceDerivativeVector_mem_sourceHistory n)

theorem norm_thetaSourceDerivativeHistoryQuotientProjection_le (f : HS) :
    ‖thetaSourceDerivativeHistoryQuotientProjection f‖ ≤ ‖f‖ :=
  Submodule.Quotient.norm_mk_le _ f

def thetaDerivativeOscillatorySourceVector (n : ℕ) (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) : HS :=
  (thetaDerivativeOscillatoryPrimitive_memLp n hstrip hzero).toLp
    (thetaDerivativeOscillatoryPrimitive n z)

theorem thetaDerivativeOscillatorySourceVector_coe (n : ℕ) (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    (thetaDerivativeOscillatorySourceVector n z hstrip hzero : ℝ → ℂ) =ᵐ[μS]
      thetaDerivativeOscillatoryPrimitive n z :=
  (thetaDerivativeOscillatoryPrimitive_memLp n hstrip hzero).coeFn_toLp

theorem norm_thetaDerivativeOscillatorySourceVector_le (n : ℕ) (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    ‖thetaDerivativeOscillatorySourceVector n z hstrip hzero‖ ≤
      thetaDerivativePrimitiveUniformNormBound n :=
  norm_thetaDerivativeOscillatoryPrimitive_toLp_le n hstrip hzero

theorem thetaDerivativeOscillatorySourceVector_succ (n : ℕ) (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    thetaDerivativeOscillatorySourceVector (n + 1) z hstrip hzero =
      thetaSourceDerivativeVector n -
        (Complex.I * z) • thetaDerivativeOscillatorySourceVector n z hstrip hzero := by
  have hg : (thetaSourceDerivativeVector n : ℝ → ℂ) =ᵐ[μS]
      thetaSourceDerivativeFunction n :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mpr (thetaSourceDerivativeVector_coe n)
  apply Lp.ext
  filter_upwards [thetaDerivativeOscillatorySourceVector_coe (n + 1) z hstrip hzero,
    Lp.coeFn_sub (thetaSourceDerivativeVector n)
      ((Complex.I * z) • thetaDerivativeOscillatorySourceVector n z hstrip hzero),
    Lp.coeFn_smul (Complex.I * z) (thetaDerivativeOscillatorySourceVector n z hstrip hzero),
    hg, thetaDerivativeOscillatorySourceVector_coe n z hstrip hzero] with x hnext hsub hsmul hgn hn
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub hsmul
  rw [hnext, hsub, hsmul, hgn, hn]
  exact thetaDerivativeOscillatoryPrimitive_succ n z x

def thetaCanonicalSourceQuotientMode (z : ℂ) (hstrip : |z.im| ≤ 1 / 2)
    (hzero : XiC z = 0) : HS ⧸ thetaSourceDerivativeHistory :=
  thetaSourceDerivativeHistoryQuotientProjection (thetaDivisorSourceVector z
    (lt_of_le_of_lt hstrip (by norm_num))
    (by rw [xiC_thetaSource (lt_of_le_of_lt hstrip (by norm_num))]; exact hzero))

theorem integral_thetaDivisorSourceVector_eq_mass (z : ℂ) (hstrip : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    (∫ x, (thetaDivisorSourceVector z hstrip hzero : ℝ → ℂ) x) =
      (thetaSource.mass : ℂ) := by
  rw [integral_congr_ae (thetaDivisorSourceVector_ae z hstrip hzero)]
  exact integral_sourceModeF_thetaSource_eq_mass hstrip hzero

theorem thetaCanonicalSourceQuotientMode_ne_zero (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    thetaCanonicalSourceQuotientMode z hstrip hzero ≠ 0 := by
  have hs : |z.im| < 1 := lt_of_le_of_lt hstrip (by norm_num)
  have hz : xiC thetaSource z = 0 := by rw [xiC_thetaSource hs]; exact hzero
  intro hq
  have hm : thetaDivisorSourceVector z hs hz ∈ thetaSourceDerivativeHistory :=
    (Submodule.Quotient.mk_eq_zero thetaSourceDerivativeHistory).mp hq
  have hU := Submodule.mem_comap.mp hm
  exact thetaDivisorEigenvector_quotient_ne_zero z hs hz
    ((Submodule.Quotient.mk_eq_zero thetaQuantileDerivativeHistory).mpr hU)

theorem thetaCanonicalSourceQuotientMode_eq_neg_primitive (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    thetaCanonicalSourceQuotientMode z hstrip hzero =
      -thetaSourceDerivativeHistoryQuotientProjection
        (thetaDerivativeOscillatorySourceVector 1 z hstrip hzero) := by
  have hs : |z.im| < 1 := lt_of_le_of_lt hstrip (by norm_num)
  have hz : xiC thetaSource z = 0 := by rw [xiC_thetaSource hs]; exact hzero
  have heq : thetaDivisorSourceVector z hs hz = thetaSourceDerivativeVector 0 -
      thetaDerivativeOscillatorySourceVector 1 z hstrip hzero := by
    apply Lp.ext
    apply (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mpr
    have hsub := (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp
        (Lp.coeFn_sub (thetaSourceDerivativeVector 0)
          (thetaDerivativeOscillatorySourceVector 1 z hstrip hzero))
    have hp := (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp
        (thetaDerivativeOscillatorySourceVector_coe 1 z hstrip hzero)
    filter_upwards [thetaDivisorSourceVector_ae z hs hz, hsub,
      thetaSourceDerivativeVector_coe 0, hp] with x hf hsubx hg hpx
    simp only [Pi.sub_apply] at hsubx
    rw [hf, hsubx, hg, hpx, sourceModeF_eq_thetaDerivativeOscillatoryPrimitive_zero]
    linear_combination thetaDerivativeOscillatoryPrimitive_succ 0 z x
  change thetaSourceDerivativeHistoryQuotientProjection (thetaDivisorSourceVector z hs hz) = _
  rw [heq, map_sub, thetaSourceDerivativeHistoryQuotientProjection_derivative, zero_sub]

theorem thetaDerivativeOscillatorySourceVector_quotient_reciprocal (n : ℕ) (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    thetaSourceDerivativeHistoryQuotientProjection
        (thetaDerivativeOscillatorySourceVector n z hstrip hzero) =
      (-Complex.I * z)⁻¹ • thetaSourceDerivativeHistoryQuotientProjection
        (thetaDerivativeOscillatorySourceVector (n + 1) z hstrip hzero) := by
  have hz : z ≠ 0 := fun h => XiC_zero_ne (by simpa [h] using hzero)
  have hc : -Complex.I * z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz
  have h := congrArg thetaSourceDerivativeHistoryQuotientProjection
    (thetaDerivativeOscillatorySourceVector_succ n z hstrip hzero)
  rw [map_sub, map_smul, thetaSourceDerivativeHistoryQuotientProjection_derivative,
    zero_sub, ← neg_smul, ← neg_mul] at h
  rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem thetaCanonicalSourceQuotientMode_eq_remainder (A : ℕ) (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    thetaCanonicalSourceQuotientMode z hstrip hzero =
      -((-Complex.I * z)⁻¹ ^ A) • thetaSourceDerivativeHistoryQuotientProjection
        (thetaDerivativeOscillatorySourceVector (A + 1) z hstrip hzero) := by
  induction A with
  | zero =>
      simpa only [zero_add, pow_zero, neg_smul, one_smul] using
        thetaCanonicalSourceQuotientMode_eq_neg_primitive z hstrip hzero
  | succ A ih =>
      rw [ih, thetaDerivativeOscillatorySourceVector_quotient_reciprocal (A + 1) z hstrip hzero,
        smul_smul, pow_succ, neg_mul]

theorem norm_thetaCanonicalSourceQuotientMode_le_inverse_power (A : ℕ) (z : ℂ)
    (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0) :
    ‖thetaCanonicalSourceQuotientMode z hstrip hzero‖ ≤
      ‖z‖⁻¹ ^ A * thetaDerivativePrimitiveUniformNormBound (A + 1) := by
  rw [thetaCanonicalSourceQuotientMode_eq_remainder A z hstrip hzero,
    norm_smul, norm_neg, norm_pow, norm_inv, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_thetaSourceDerivativeHistoryQuotientProjection_le _).trans
      (norm_thetaDerivativeOscillatorySourceVector_le (A + 1) z hstrip hzero))
    (pow_nonneg (inv_nonneg.mpr (norm_nonneg z)) _)

/-- Rapid decay under the actual canonical mean normalization, with threshold one. -/
theorem thetaCanonicalSourceQuotientMode_rapid_decay (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0),
      1 ≤ |z.re| → ‖thetaCanonicalSourceQuotientMode z hstrip hzero‖ ≤
        C / (1 + ‖z‖) ^ A := by
  refine ⟨2 ^ A * thetaDerivativePrimitiveUniformNormBound (A + 1),
    mul_nonneg (pow_nonneg (by norm_num) _) (thetaDerivativePrimitiveUniformNormBound_nonneg _), ?_⟩
  intro z hstrip hzero hre
  have hn : 1 ≤ ‖z‖ := hre.trans (Complex.abs_re_le_norm z)
  have hnpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hn
  have hp : 0 < 1 + ‖z‖ := by positivity
  have hpow : (1 + ‖z‖) ^ A ≤ 2 ^ A * ‖z‖ ^ A := by
    calc
      (1 + ‖z‖) ^ A ≤ (2 * ‖z‖) ^ A := by gcongr; linarith
      _ = 2 ^ A * ‖z‖ ^ A := mul_pow _ _ _
  apply (le_div_iff₀ (pow_pos hp _)).mpr
  calc
    ‖thetaCanonicalSourceQuotientMode z hstrip hzero‖ * (1 + ‖z‖) ^ A ≤
        (‖z‖⁻¹ ^ A * thetaDerivativePrimitiveUniformNormBound (A + 1)) *
          (2 ^ A * ‖z‖ ^ A) :=
      mul_le_mul (norm_thetaCanonicalSourceQuotientMode_le_inverse_power A z hstrip hzero) hpow
        (pow_nonneg hp.le _) (mul_nonneg (pow_nonneg (inv_nonneg.mpr hnpos.le) _)
          (thetaDerivativePrimitiveUniformNormBound_nonneg _))
    _ = 2 ^ A * thetaDerivativePrimitiveUniformNormBound (A + 1) := by
      rw [inv_pow]
      field_simp [hnpos.ne']

theorem thetaCanonicalSourceQuotientMode_rapid_decay_rpow (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (hstrip : |z.im| ≤ 1 / 2) (hzero : XiC z = 0),
      1 ≤ |z.re| → ‖thetaCanonicalSourceQuotientMode z hstrip hzero‖ ≤
        C * (1 + ‖z‖) ^ (-(A : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := thetaCanonicalSourceQuotientMode_rapid_decay A
  refine ⟨C, hC, fun z hstrip hzero hre => ?_⟩
  rw [Real.rpow_neg (by positivity) _, Real.rpow_natCast, ← div_eq_mul_inv]
  exact hbound z hstrip hzero hre

end RHTower.HedenmalmThetaSource
