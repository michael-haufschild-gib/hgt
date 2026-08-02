import GaloisForLFunctions.RHTower.MFreeLadder
import GaloisForLFunctions.RHTower.XiThetaL2Cyclicity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries

/-!
# Physical Möbius--theta source landing in Xi

This module realizes the high-exponent reciprocal-zeta multiplier before spectral evaluation.
The source is an absolutely convergent `L²` sum of logarithmic translates of the canonical theta
source, with coefficients supplied by the power-supported Möbius arithmetic function.  Plancherel
then proves that its real Fourier boundary is `ζ(m(1/2+it))⁻¹ XiC(t)`.

Unlike the earlier value-level complete-resolution vector, `mobiusThetaRung m` contains no `XiC`,
spectral parameter, or zero.  Thus the theorem is an unconditional physical source-to-Xi landing,
not scalar multiplication by a preselected target value.
-/

open Complex Real MeasureTheory ArithmeticFunction LSeries Filter Topology
open scoped BigOperators LSeries.notation Moebius FourierTransform SchwartzMap

noncomputable section
namespace RHTower

/-- Ambient Hilbert space of the physical logarithmic source. -/
abbrev MobiusThetaSourceL2 := Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)

/-- One half-density, power-supported Möbius coefficient acting on the corresponding logarithmic
translate of the canonical theta source. -/
def mobiusThetaRungTerm (m n : ℕ) : MobiusThetaSourceL2 :=
  LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n •
    MellinL2.additiveTranslationUnitary
      (-Real.log n * MellinL2.spectralNormalization) xiThetaSourceL2

theorem norm_mobiusThetaRungTerm (m n : ℕ) :
    ‖mobiusThetaRungTerm m n‖ =
      ‖LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n‖ *
        ‖xiThetaSourceL2‖ := by
  rw [mobiusThetaRungTerm, norm_smul, LinearIsometryEquiv.norm_map]

theorem summable_mobiusThetaRungTerm {m : ℕ} (hm : m ≠ 0)
    (hmhalf : 1 / (m : ℝ) < (1 / 2 : ℂ).re) :
    Summable (mobiusThetaRungTerm m) := by
  have hcoeff := LSeriesSummable_mPart_moebius hm hmhalf
  unfold LSeriesSummable at hcoeff
  apply Summable.of_norm
  simpa only [norm_mobiusThetaRungTerm] using hcoeff.norm.mul_right ‖xiThetaSourceL2‖

theorem summable_mobiusThetaRungTerm_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    Summable (mobiusThetaRungTerm m) := by
  apply summable_mobiusThetaRungTerm (by omega)
  norm_num [Complex.div_re]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmPos : (0 : ℝ) < m := by positivity
  rw [inv_lt_comm₀ hmPos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

/-- Target-free physical Möbius--theta rung.  For `m ≥ 3` this is an absolutely convergent
Hilbert-space series. -/
def mobiusThetaRung (m : ℕ) : MobiusThetaSourceL2 :=
  ∑' n : ℕ, mobiusThetaRungTerm m n

/-- Fourier-side term obtained from the physical translate by Plancherel. -/
def mobiusThetaFourierTerm (m n : ℕ) : MobiusThetaSourceL2 :=
  LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n •
    MellinL2.fourierPhaseMulUnitary
      (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2

theorem norm_mobiusThetaFourierTerm (m n : ℕ) :
    ‖mobiusThetaFourierTerm m n‖ =
      ‖LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n‖ *
        ‖xiThetaFourierSourceL2‖ := by
  rw [mobiusThetaFourierTerm, norm_smul, LinearIsometryEquiv.norm_map]

theorem summable_norm_mobiusThetaFourierTerm {m : ℕ} (hm : 3 ≤ m) :
    Summable (fun n : ℕ => ‖mobiusThetaFourierTerm m n‖) := by
  have hcoeff := LSeriesSummable_mPart_moebius
    (s := (1 / 2 : ℂ)) (by omega : m ≠ 0) (by
      norm_num [Complex.div_re]
      have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
      have hmPos : (0 : ℝ) < m := by positivity
      rw [inv_lt_comm₀ hmPos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith)
  unfold LSeriesSummable at hcoeff
  simpa only [norm_mobiusThetaFourierTerm] using
    hcoeff.norm.mul_right ‖xiThetaFourierSourceL2‖

theorem summable_mobiusThetaFourierTerm {m : ℕ} (hm : 3 ≤ m) :
    Summable (mobiusThetaFourierTerm m) :=
  Summable.of_norm (summable_norm_mobiusThetaFourierTerm hm)

/-- Plancherel commutes with the physical Möbius source sum term by term. -/
theorem fourier_mobiusThetaRung {m : ℕ} (hm : 3 ≤ m) :
    𝓕 (mobiusThetaRung m) =
      ∑' n : ℕ, mobiusThetaFourierTerm m n := by
  rw [mobiusThetaRung]
  change (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
      (∑' n : ℕ, mobiusThetaRungTerm m n) = _
  calc
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
        (∑' n : ℕ, mobiusThetaRungTerm m n) =
        ∑' n : ℕ, (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
          (mobiusThetaRungTerm m n) := by
      exact ContinuousLinearMap.map_tsum
        (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
        (summable_mobiusThetaRungTerm_of_three_le hm)
    _ = _ := by
      apply tsum_congr
      intro n
      rw [mobiusThetaRungTerm, mobiusThetaFourierTerm, map_smul]
      congr 1
      change 𝓕 (MellinL2.additiveTranslationUnitary
        (-Real.log n * MellinL2.spectralNormalization) xiThetaSourceL2) = _
      rw [MellinL2.fourier_additiveTranslation, fourier_xiThetaSourceL2]

theorem fourierPhase_neg_log_normalized (n : ℕ) (t : ℝ) :
    MellinL2.fourierPhase
        (-Real.log n * MellinL2.spectralNormalization) t =
      MellinL2.mellinCharacter n (-t) := by
  rw [show -Real.log n * MellinL2.spectralNormalization =
      Real.log n * MellinL2.spectralNormalization * (-1) by ring]
  unfold MellinL2.fourierPhase MellinL2.spectralNormalization
    MellinL2.mellinCharacter
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Half-density Dirichlet coefficient times the physical translation character is the centered
Dirichlet coefficient. -/
theorem LSeries_term_half_mul_mellinCharacter_neg
    (f : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    LSeries.term f (1 / 2 : ℂ) n * MellinL2.mellinCharacter n (-t) =
      LSeries.term f ((1 / 2 : ℂ) + (t : ℂ) * I) n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    MellinL2.mellinCharacter_eq_cpow n hnpos (-t)]
  rw [show I * ((-t : ℝ) : ℂ) = -((t : ℂ) * I) by push_cast; ring,
    Complex.cpow_neg]
  rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  norm_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem summable_mobiusThetaFourierValueTerm {m : ℕ} (hm : 3 ≤ m) (t : ℝ) :
    Summable (fun n : ℕ =>
      LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n *
        MellinL2.mellinCharacter n (-t) * XiC (t : ℂ)) := by
  have hc : Summable (LSeries.term
      (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ)) := by
    exact LSeriesSummable_mPart_moebius
      (s := (1 / 2 : ℂ)) (by omega : m ≠ 0) (by
        norm_num [Complex.div_re]
        have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
        have hmPos : (0 : ℝ) < m := by positivity
        rw [inv_lt_comm₀ hmPos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith)
  apply Summable.of_norm
  simpa only [norm_mul, MellinL2.norm_mellinCharacter, one_mul, mul_assoc] using
    hc.norm.mul_right ‖XiC (t : ℂ)‖

theorem tsum_enorm_mobiusThetaFourierTerm_ne_top {m : ℕ} (hm : 3 ≤ m) :
    ∑' n : ℕ, ‖mobiusThetaFourierTerm m n‖ₑ ≠ ⊤ := by
  simp only [enorm_eq_nnnorm]
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simpa only [coe_nnnorm] using summable_norm_mobiusThetaFourierTerm hm

theorem mobiusThetaFourierTerm_ae (m n : ℕ) :
    mobiusThetaFourierTerm m n =ᵐ[volume]
      fun t : ℝ =>
        LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n *
          MellinL2.mellinCharacter n (-t) * XiC (t : ℂ) := by
  change
    (LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n •
      MellinL2.fourierPhaseMulUnitary
        (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2) =ᵐ[volume] _
  have hphase :
      MellinL2.fourierPhaseMulUnitary
          (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2 =ᵐ[volume]
        fun t : ℝ =>
          MellinL2.fourierPhase
              (-Real.log n * MellinL2.spectralNormalization) t *
            xiThetaFourierSourceL2 t := by
    change MellinL2.fourierPhaseMulAux
        (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2 =ᵐ[volume] _
    exact MellinL2.fourierPhaseMulAux_ae _ _
  filter_upwards [Lp.coeFn_smul
      (LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n)
      (MellinL2.fourierPhaseMulUnitary
        (-Real.log n * MellinL2.spectralNormalization) xiThetaFourierSourceL2),
    hphase, xiThetaFourierSourceL2_ae] with t hsmul hphase_t hxi
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hphase_t, hxi, fourierPhase_neg_log_normalized]
  ring

/-- **Unconditional physical source-to-Xi landing on the Plancherel boundary.**  For every
high-exponent rung, the Fourier transform of the target-free translated theta source is the full
centered Xi function times the corresponding reciprocal-zeta multiplier, almost everywhere on
the real spectral line. -/
theorem fourier_mobiusThetaRung_ae {m : ℕ} (hm : 3 ≤ m) :
    ((𝓕 (mobiusThetaRung m) : MobiusThetaSourceL2) : ℝ → ℂ) =ᵐ[volume]
      fun t : ℝ =>
        (riemannZeta ((m : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I)))⁻¹ * XiC (t : ℂ) := by
  have hfourier := fourier_mobiusThetaRung hm
  rw [hfourier]
  have hcoe :
      (((∑' n : ℕ, mobiusThetaFourierTerm m n) : MobiusThetaSourceL2) : ℝ → ℂ) =ᵐ[volume]
        fun t : ℝ => ∑' n : ℕ, mobiusThetaFourierTerm m n t :=
    Lp.coeFn_tsum (tsum_enorm_mobiusThetaFourierTerm_ne_top hm)
  have hterm : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
      mobiusThetaFourierTerm m n t =
        LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n *
          MellinL2.mellinCharacter n (-t) * XiC (t : ℂ) :=
    ae_all_iff.mpr fun n => mobiusThetaFourierTerm_ae m n
  filter_upwards [hcoe, hterm] with t hcoe_t hterm_t
  rw [hcoe_t]
  calc
    (∑' n : ℕ, mobiusThetaFourierTerm m n t) =
        ∑' n : ℕ,
          LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
              ((1 / 2 : ℂ) + (t : ℂ) * I) n * XiC (t : ℂ) := by
      apply tsum_congr
      intro n
      rw [hterm_t n, LSeries_term_half_mul_mellinCharacter_neg]
    _ = LSeries (↗(mPart m (μ : ArithmeticFunction ℤ)))
          ((1 / 2 : ℂ) + (t : ℂ) * I) * XiC (t : ℂ) := tsum_mul_right
    _ = (riemannZeta ((m : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I)))⁻¹ *
          XiC (t : ℂ) := by
      rw [LSeries_mPart_moebius (by omega : m ≠ 0)]
      norm_num [Complex.div_re]
      have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
      have hmPos : (0 : ℝ) < m := by positivity
      rw [inv_lt_comm₀ hmPos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith

/-! ## Singular prime-normal extraction

The source below is the physical normal form obtained after peeling at the integer `p`, translating
the `p`-channel back to the origin, and multiplying by its half-density normalization.  Its leading
channel is `μ(p) • xiThetaSourceL2`; every later channel carries the exact relative coefficient
`μ(n) (p / n)^(m/2)` and relative logarithmic translation.  No spectral value or zero occurs in
the construction.
-/

/-- Summable `m = 3` envelope for the prime-normal tail. -/
def mobiusThetaPrimeNormalMajorant (p k : ℕ) : ℝ :=
  ((p : ℝ) / (p + k + 1 : ℕ)) ^ (3 / 2 : ℝ) * ‖xiThetaSourceL2‖

theorem summable_mobiusThetaPrimeNormalMajorant (p : ℕ) :
    Summable (mobiusThetaPrimeNormalMajorant p) := by
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable
      (fun k : ℕ => ((k + (p + 1) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (_root_.summable_nat_add_iff (p + 1)).2 hs
  have hmul := hshift.mul_left ((p : ℝ) ^ (3 / 2 : ℝ) * ‖xiThetaSourceL2‖)
  refine hmul.congr fun k => ?_
  rw [mobiusThetaPrimeNormalMajorant,
    Real.div_rpow (by positivity) (by positivity),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ ((k + (p + 1) : ℕ) : ℝ))]
  push_cast
  ring_nf

/-- Exact real coefficient of the `k`-th channel strictly beyond the peeled index `p`. -/
def mobiusThetaPrimeNormalWeight (p m k : ℕ) : ℝ :=
  (μ (p + k + 1) : ℝ) *
    ((p : ℝ) / (p + k + 1 : ℕ)) ^ ((m : ℝ) / 2)

/-- The `k`-th physical relative channel after prime-normal recentering. -/
def mobiusThetaPrimeNormalTailTerm (p m k : ℕ) : MobiusThetaSourceL2 :=
  (mobiusThetaPrimeNormalWeight p m k : ℂ) •
    MellinL2.additiveTranslationUnitary
      (-((m : ℝ) * Real.log ((p + k + 1 : ℕ) / (p : ℝ))) *
        MellinL2.spectralNormalization)
      xiThetaSourceL2

theorem norm_mobiusThetaPrimeNormalTailTerm (p m k : ℕ) :
    ‖mobiusThetaPrimeNormalTailTerm p m k‖ =
      |mobiusThetaPrimeNormalWeight p m k| * ‖xiThetaSourceL2‖ := by
  rw [mobiusThetaPrimeNormalTailTerm, norm_smul, LinearIsometryEquiv.norm_map,
    Complex.norm_real, Real.norm_eq_abs]

/-- Uniform Tannery bound for every high-exponent physical relative channel. -/
theorem norm_mobiusThetaPrimeNormalTailTerm_le_majorant
    {p m : ℕ} (hp : 1 ≤ p) (hm : 3 ≤ m) (k : ℕ) :
    ‖mobiusThetaPrimeNormalTailTerm p m k‖ ≤
      mobiusThetaPrimeNormalMajorant p k := by
  rw [norm_mobiusThetaPrimeNormalTailTerm, mobiusThetaPrimeNormalWeight, abs_mul]
  have hmu : |(μ (p + k + 1) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p + k + 1)
  have hratio_pos : 0 < (p : ℝ) / (p + k + 1 : ℕ) := by positivity
  rw [abs_of_nonneg (Real.rpow_nonneg hratio_pos.le _)]
  have hratio_le : (p : ℝ) / (p + k + 1 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (by omega : p ≤ p + k + 1)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hexp : (3 / 2 : ℝ) ≤ (m : ℝ) / 2 := by linarith
  unfold mobiusThetaPrimeNormalMajorant
  calc
    |(μ (p + k + 1) : ℝ)| *
          ((p : ℝ) / (p + k + 1 : ℕ)) ^ ((m : ℝ) / 2) * ‖xiThetaSourceL2‖ ≤
        1 * ((p : ℝ) / (p + k + 1 : ℕ)) ^ ((m : ℝ) / 2) *
          ‖xiThetaSourceL2‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg hratio_pos.le _))
        (norm_nonneg xiThetaSourceL2)
    _ ≤ ((p : ℝ) / (p + k + 1 : ℕ)) ^ (3 / 2 : ℝ) *
          ‖xiThetaSourceL2‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hratio_pos hratio_le hexp)
        (norm_nonneg xiThetaSourceL2)

/-- Every fixed post-`p` relative channel vanishes strongly as the exponent grows.  Translation
may escape without converging; the exact half-density coefficient nevertheless forces its norm to
zero. -/
theorem tendsto_mobiusThetaPrimeNormalTailTerm_zero
    {p : ℕ} (hp : 1 ≤ p) (k : ℕ) :
    Tendsto (fun m : ℕ => mobiusThetaPrimeNormalTailTerm p m k) atTop (nhds 0) := by
  have hratio_pos : 0 < (p : ℝ) / (p + k + 1 : ℕ) := by positivity
  have hratio_lt : (p : ℝ) / (p + k + 1 : ℕ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast (by omega : p < p + k + 1)
  have hpow : Tendsto
      (fun m : ℕ => ((p : ℝ) / (p + k + 1 : ℕ)) ^ ((m : ℝ) / 2))
      atTop (nhds 0) := by
    have hb := tendsto_rpow_atTop_of_base_lt_one
      ((p : ℝ) / (p + k + 1 : ℕ)) (by linarith) hratio_lt
    exact hb.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hscalar : Tendsto
      (fun m : ℕ => |(μ (p + k + 1) : ℝ)| *
        ((p : ℝ) / (p + k + 1 : ℕ)) ^ ((m : ℝ) / 2) * ‖xiThetaSourceL2‖)
      atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds.mul hpow).mul tendsto_const_nhds)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert hscalar using 1
  funext m
  rw [norm_mobiusThetaPrimeNormalTailTerm, mobiusThetaPrimeNormalWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hratio_pos.le _)]

/-- The full post-`p` physical tail vanishes strongly.  This is the infinite-source step: the
conclusion is about the `L²` sum, not any finite projection or scalar multiplier. -/
theorem tendsto_tsum_mobiusThetaPrimeNormalTailTerm_zero
    {p : ℕ} (hp : 1 ≤ p) :
    Tendsto (fun m : ℕ => ∑' k : ℕ, mobiusThetaPrimeNormalTailTerm p m k)
      atTop (nhds 0) := by
  rw [show (0 : MobiusThetaSourceL2) = ∑' _k : ℕ, 0 by simp]
  apply tendsto_tsum_of_dominated_convergence
    (summable_mobiusThetaPrimeNormalMajorant p)
  · exact tendsto_mobiusThetaPrimeNormalTailTerm_zero hp
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with m hm k
    exact norm_mobiusThetaPrimeNormalTailTerm_le_majorant hp hm k

/-- Singular prime-normal physical source: retained `p`-channel plus its complete later tail. -/
def mobiusThetaPrimeNormalResidual (p m : ℕ) : MobiusThetaSourceL2 :=
  ((μ p : ℝ) : ℂ) • xiThetaSourceL2 +
    ∑' k : ℕ, mobiusThetaPrimeNormalTailTerm p m k

/-- **Unconditional physical prime-normal extraction.**  At every positive peeled index, the full
recentered Möbius--theta source converges strongly to its retained oriented channel.  In particular,
for prime `p` the limit is `-xiThetaSourceL2`; the sign is derived from `μ(p)`, not selected from a
Xi value. -/
theorem tendsto_mobiusThetaPrimeNormalResidual
    {p : ℕ} (hp : 1 ≤ p) :
    Tendsto (mobiusThetaPrimeNormalResidual p) atTop
      (nhds (((μ p : ℝ) : ℂ) • xiThetaSourceL2)) := by
  unfold mobiusThetaPrimeNormalResidual
  simpa using tendsto_const_nhds.add (tendsto_tsum_mobiusThetaPrimeNormalTailTerm_zero hp)

/-- Prime specialization: the oriented retained channel is canonically negative. -/
theorem tendsto_mobiusThetaPrimeNormalResidual_of_prime
    {p : ℕ} (hp : p.Prime) :
    Tendsto (mobiusThetaPrimeNormalResidual p) atTop (nhds (-xiThetaSourceL2)) := by
  simpa [ArithmeticFunction.moebius_apply_prime hp] using
    tendsto_mobiusThetaPrimeNormalResidual (p := p) hp.one_le

/-! ## Complete physical codiagonal

The case `p = 1` of prime-normal extraction is the direct power-indexed Möbius--theta rung.  Its
successive differences retain every exponent channel while telescoping back to one physical source
vector.  This is countable retention inside `L²`, not a closed multivalued relation into a product
target.
-/

/-- Direct physical Möbius--theta rung, expressed by its principal channel and complete relative
tail. -/
def mobiusThetaDirectPhysicalRung (m : ℕ) : MobiusThetaSourceL2 :=
  mobiusThetaPrimeNormalResidual 1 m

/-- The direct physical rungs converge strongly to the canonical theta source. -/
theorem tendsto_mobiusThetaDirectPhysicalRung :
    Tendsto mobiusThetaDirectPhysicalRung atTop (nhds xiThetaSourceL2) := by
  change Tendsto (mobiusThetaPrimeNormalResidual 1) atTop (nhds xiThetaSourceL2)
  simpa using
    (tendsto_mobiusThetaPrimeNormalResidual (p := 1) (by omega : 1 ≤ 1))

/-- Complete physical difference channel based at exponent `K`. -/
def mobiusThetaCompletePhysicalChannel (K : ℕ) : ℕ → MobiusThetaSourceL2
  | 0 => mobiusThetaDirectPhysicalRung K
  | j + 1 =>
      mobiusThetaDirectPhysicalRung (K + j + 1) -
        mobiusThetaDirectPhysicalRung (K + j)

/-- Exact finite physical codiagonal: all internal exponent channels cancel. -/
theorem sum_range_mobiusThetaCompletePhysicalChannel (K N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), mobiusThetaCompletePhysicalChannel K j =
      mobiusThetaDirectPhysicalRung (K + N) := by
  induction N with
  | zero => simp [mobiusThetaCompletePhysicalChannel]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp [mobiusThetaCompletePhysicalChannel, add_assoc]

/-- **Unconditional complete physical codiagonal limit.**  The full sequence of difference
channels has a canonical strong sum limit equal to the theta source. -/
theorem tendsto_sum_range_mobiusThetaCompletePhysicalChannel (K : ℕ) :
    Tendsto
      (fun N : ℕ =>
        ∑ j ∈ Finset.range (N + 1), mobiusThetaCompletePhysicalChannel K j)
      atTop (nhds xiThetaSourceL2) := by
  have h := tendsto_mobiusThetaDirectPhysicalRung.comp (tendsto_add_atTop_nat K)
  have h' : Tendsto (fun N : ℕ => mobiusThetaDirectPhysicalRung (K + N))
      atTop (nhds xiThetaSourceL2) := by
    simpa [Function.comp_def, Nat.add_comm] using h
  exact h'.congr' (Filter.Eventually.of_forall fun N =>
    (sum_range_mobiusThetaCompletePhysicalChannel K N).symm)

end RHTower
