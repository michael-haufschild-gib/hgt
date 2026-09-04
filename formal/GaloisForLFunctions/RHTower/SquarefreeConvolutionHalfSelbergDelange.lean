import GaloisForLFunctions.RHTower.SelbergDelangeConvolutionTransfer
import GaloisForLFunctions.RHTower.SuzukiCriticalAperturePrimeCurrent
import GaloisForLFunctions.RHTower.ZetaBinomialHalfFractionalPole
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion

/-!
# Selberg--Delange assembly for the signed squarefree convolution half

This module assembles the exact signed convolution conclusion from the positive zeta-half
Wiener--Ikehara input and a summable hyperbola majorant.  The correction is the square-supported
coefficient system already shown to converge absolutely on `Re s > 1/2`.

The analytic Tauberian core is deliberately exposed as a named proposition rather than hidden as
an axiom: proving that proposition is precisely the remaining fractional Wiener--Ikehara theorem.
-/

open ArithmeticFunction Complex Filter Topology Set
open scoped BigOperators ArithmeticFunction.zeta ComplexOrder Moebius

noncomputable section

namespace RHTower

/-- Natural-number normalization `N / sqrt(log N)` for the order-`1/2` Selberg--Delange law. -/
def selbergDelangeHalfScale (N : ℕ) : ℂ :=
  ((((N : ℝ) / Real.sqrt (Real.log N)) : ℝ) : ℂ)

/-- Undilated conclusion of the order-`1/2` Kato--Ikehara theorem for the positive zeta half. -/
def ZetaBinomialHalfKatoInversion : Prop :=
  Tendsto
    (fun N : ℕ => arithmeticSummatory zetaBinomialHalf N /
      selbergDelangeHalfScale N)
    atTop (𝓝 ((1 / Real.sqrt Real.pi : ℝ) : ℂ))

/-- Exact fixed-dilation form of fractional Wiener--Ikehara for the positive zeta half. -/
def ZetaBinomialHalfWienerIkehara : Prop :=
  ∀ d : ℕ, d ≠ 0 →
    Tendsto
      (fun N ↦ arithmeticSummatory zetaBinomialHalf (N / d) /
        selbergDelangeHalfScale N)
      atTop (𝓝 (((1 / Real.sqrt Real.pi : ℝ) : ℂ) / (d : ℂ)))

private theorem tendsto_log_natDiv_div_log {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => Real.log ((N / d : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  have hdiff := GaloisForLFunctions.HTGeometry.tendsto_log_natDiv_sub_log hd
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero := hdiff.div_atTop hlog
  have hone := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  have hone' : Tendsto (fun N : ℕ =>
      1 + (Real.log ((N / d : ℕ) : ℝ) - Real.log (N : ℝ)) /
        Real.log (N : ℝ)) atTop (𝓝 1) := by
    simpa using hone
  refine hone'.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hlogne : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp
  ring

private theorem tendsto_sqrt_log_natDiv_ratio {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ =>
      Real.sqrt (Real.log (N : ℝ)) /
        Real.sqrt (Real.log ((N / d : ℕ) : ℝ))) atTop (𝓝 1) := by
  have hratio := tendsto_log_natDiv_div_log hd
  have hinv := hratio.inv₀ one_ne_zero
  have hratio' : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) / Real.log ((N / d : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hinv' : Tendsto (fun N : ℕ =>
        (Real.log ((N / d : ℕ) : ℝ) / Real.log (N : ℝ))⁻¹) atTop (𝓝 1) := by
      simpa using hinv
    refine hinv'.congr' ?_
    filter_upwards [eventually_ge_atTop (2 * d)] with N hN
    have hM : 2 ≤ N / d := by
      rw [Nat.le_div_iff_mul_le hd]
      simpa [mul_comm] using hN
    have hlogN : Real.log (N : ℝ) ≠ 0 := by
      have : 1 < N := lt_of_lt_of_le (by omega : 1 < 2 * d) hN
      exact (Real.log_pos (by exact_mod_cast this)).ne'
    have hlogM : Real.log ((N / d : ℕ) : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hM)).ne'
    rw [inv_div]
  have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hratio'
  simp only [Real.sqrt_one] at hsqrt
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  change Real.sqrt (Real.log (N : ℝ) / Real.log ((N / d : ℕ) : ℝ)) = _
  rw [Real.sqrt_div (Real.log_nonneg (by exact_mod_cast hN))]

/-- Fixed integer decimation changes `N / sqrt(log N)` by exactly the reciprocal density. -/
theorem tendsto_selbergDelangeHalfScale_natDiv_ratio {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ =>
      selbergDelangeHalfScale (N / d) / selbergDelangeHalfScale N)
      atTop (𝓝 ((1 / (d : ℝ) : ℝ) : ℂ)) := by
  have hnat := GaloisForLFunctions.HTGeometry.tendsto_natDiv_div_self hd
  have hsqrt := tendsto_sqrt_log_natDiv_ratio hd
  have hreal := hnat.mul hsqrt
  have hreal0 : Tendsto (fun N : ℕ =>
      (((N / d : ℕ) : ℝ) / (N : ℝ)) *
        (Real.sqrt (Real.log (N : ℝ)) /
          Real.sqrt (Real.log ((N / d : ℕ) : ℝ)))) atTop (𝓝 (1 / (d : ℝ))) := by
    simpa using hreal
  have hreal' : Tendsto (fun N : ℕ =>
      (((N / d : ℕ) : ℝ) / Real.sqrt (Real.log ((N / d : ℕ) : ℝ))) /
        ((N : ℝ) / Real.sqrt (Real.log (N : ℝ)))) atTop (𝓝 (1 / (d : ℝ))) := by
    refine hreal0.congr' ?_
    filter_upwards [eventually_ge_atTop (2 * d)] with N hN
    have hM : 2 ≤ N / d := by
      rw [Nat.le_div_iff_mul_le hd]
      simpa [mul_comm] using hN
    have hsN : Real.sqrt (Real.log (N : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.2 (Real.log_pos
        (by exact_mod_cast (show 1 < N by omega)))).ne'
    have hsM : Real.sqrt (Real.log ((N / d : ℕ) : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.2 (Real.log_pos
        (by exact_mod_cast (show 1 < N / d by omega)))).ne'
    field_simp
  exact (hreal'.ofReal).congr' (Eventually.of_forall fun N => by
    simp only [selbergDelangeHalfScale]
    norm_cast)

/-- The single undilated Kato conclusion supplies every fixed dilation needed by Tannery. -/
theorem zetaBinomialHalfWienerIkehara_of_katoInversion
    (hbase : ZetaBinomialHalfKatoInversion) : ZetaBinomialHalfWienerIkehara := by
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hmain := hbase.comp
    (GaloisForLFunctions.HTGeometry.tendsto_natDiv_atTop hdpos)
  have hscale := tendsto_selbergDelangeHalfScale_natDiv_ratio hdpos
  have hmul := hmain.mul hscale
  have hmul' : Tendsto (fun N : ℕ =>
      (arithmeticSummatory zetaBinomialHalf (N / d) /
        selbergDelangeHalfScale (N / d)) *
      (selbergDelangeHalfScale (N / d) / selbergDelangeHalfScale N))
      atTop (𝓝 (((1 / Real.sqrt Real.pi : ℝ) : ℂ) / (d : ℂ))) := by
    convert hmul using 1
    · ext N
      rfl
    · push_cast
      ring
  refine hmul'.congr' ?_
  filter_upwards [eventually_ge_atTop (2 * d)] with N hN
  have hM : 2 ≤ N / d := by
    rw [Nat.le_div_iff_mul_le hdpos]
    simpa [mul_comm] using hN
  have hscaleM : selbergDelangeHalfScale (N / d) ≠ 0 := by
    have hsqrt : Real.sqrt (Real.log ((N / d : ℕ) : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.2
        (Real.log_pos (by exact_mod_cast (show 1 < N / d by omega)))).ne'
    simp [selbergDelangeHalfScale, hsqrt, (show N / d ≠ 0 by omega)]
  field_simp

/-- Fixed-dilation fractional Wiener--Ikehara is equivalent to its undilated Kato conclusion. -/
theorem zetaBinomialHalfKatoInversion_iff_wienerIkehara :
    ZetaBinomialHalfKatoInversion ↔ ZetaBinomialHalfWienerIkehara := by
  constructor
  · exact zetaBinomialHalfWienerIkehara_of_katoInversion
  · intro hWI
    simpa [ZetaBinomialHalfKatoInversion] using hWI 1 (by norm_num)

/-- The Möbius half and positive zeta half are exact convolution inverses. -/
theorem moebiusBinomialHalf_mul_zetaBinomialHalf :
    moebiusBinomialHalf * zetaBinomialHalf = 1 := by
  have hsq :
      (moebiusBinomialHalf * zetaBinomialHalf) *
          (moebiusBinomialHalf * zetaBinomialHalf) =
        (1 : ArithmeticFunction ℂ) := by
    calc
      (moebiusBinomialHalf * zetaBinomialHalf) *
          (moebiusBinomialHalf * zetaBinomialHalf) =
          (moebiusBinomialHalf * moebiusBinomialHalf) *
            (zetaBinomialHalf * zetaBinomialHalf) := by ring
      _ = (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) *
          ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) := by
        rw [moebiusBinomialHalf_mul_self, zetaBinomialHalf_mul_self]
      _ = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hhalf := convolutionHalf_unique (1 : ArithmeticFunction ℂ)
    (moebiusBinomialHalf * zetaBinomialHalf) (by simp) hsq
  have hone := convolutionHalf_unique (1 : ArithmeticFunction ℂ)
    (1 : ArithmeticFunction ℂ) (by simp) (by simp)
  exact hhalf.trans hone.symm

/-- The square-correction `L`-value at one has square `1 / ζ(2)`. -/
theorem LSeries_squareDilatedMoebiusBinomialHalf_one_sq_mul_riemannZeta_two :
    LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) *
        LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) *
          riemannZeta (2 : ℂ) = 1 := by
  have hc : LSeriesSummable squareDilatedMoebiusBinomialHalf (1 : ℂ) :=
    LSeriesSummable_squareDilatedMoebiusBinomialHalf (by norm_num)
  have hu : LSeriesSummable moebiusBinomialHalf (2 : ℂ) :=
    LSeriesSummable_moebiusBinomialHalf (by norm_num)
  have hz : LSeriesSummable ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
      (2 : ℂ) := by
    change LSeriesSummable (fun n ↦ ((ζ : ArithmeticFunction ℕ) n : ℂ)) (2 : ℂ)
    exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr (by norm_num)
  have hmu : LSeriesSummable
      ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) (2 : ℂ) := by
    have hfun : (⇑(((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) : ℕ → ℂ) =
        (fun n ↦ (μ n : ℂ)) := by
      funext n
      simp [ArithmeticFunction.intCoe_apply]
    rw [hfun]
    exact LSeriesSummable_moebius_iff.mpr (by norm_num)
  have hmuZ :
      LSeries (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) (2 : ℂ) *
        riemannZeta (2 : ℂ) = 1 := by
    have hzeta :
        LSeries (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) (2 : ℂ) =
          riemannZeta (2 : ℂ) := by
      change LSeries (fun n ↦ ((ζ : ArithmeticFunction ℕ) n : ℂ)) (2 : ℂ) =
        riemannZeta (2 : ℂ)
      exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by norm_num)
    calc
      LSeries (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) (2 : ℂ) *
          riemannZeta (2 : ℂ) =
          LSeries (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) (2 : ℂ) *
            LSeries (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) (2 : ℂ) := by
        rw [hzeta]
      _ = LSeries (fun n ↦
          ((((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) *
            ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) n)) (2 : ℂ) :=
        (ArithmeticFunction.LSeries_mul' hmu hz).symm
      _ = 1 := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
        rw [ArithmeticFunction.one_eq_delta, LSeries_delta]
        rfl
  calc
    LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) *
          LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) * riemannZeta (2 : ℂ) =
        (LSeries moebiusBinomialHalf (2 : ℂ) *
          LSeries moebiusBinomialHalf (2 : ℂ)) * riemannZeta (2 : ℂ) := by
      rw [squareDilatedMoebiusBinomialHalf, LSeries_mPart two_ne_zero]
      norm_num
    _ = LSeries (fun n ↦
        (moebiusBinomialHalf * moebiusBinomialHalf) n) (2 : ℂ) *
          riemannZeta (2 : ℂ) := by
      rw [ArithmeticFunction.LSeries_mul' hu hu]
    _ = LSeries (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) (2 : ℂ) *
          riemannZeta (2 : ℂ) := by rw [moebiusBinomialHalf_mul_self]
    _ = 1 := hmuZ

/-- The correction constant is the positive reciprocal square root of the real zeta value at two. -/
theorem LSeries_squareDilatedMoebiusBinomialHalf_one_eq_inv_sqrt_zeta_two :
    LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) =
      ((1 / Real.sqrt (riemannZeta (2 : ℂ)).re : ℝ) : ℂ) := by
  let U : ℂ := LSeries moebiusBinomialHalf (2 : ℂ)
  let B : ℂ := LSeries zetaBinomialHalf (2 : ℂ)
  have hu : LSeriesSummable moebiusBinomialHalf (2 : ℂ) :=
    LSeriesSummable_moebiusBinomialHalf (by norm_num)
  have hb : LSeriesSummable zetaBinomialHalf (2 : ℂ) :=
    LSeriesSummable_zetaBinomialHalf (by norm_num)
  have hUB : U * B = 1 := by
    calc
      U * B = LSeries (fun n ↦
          (moebiusBinomialHalf * zetaBinomialHalf) n) (2 : ℂ) := by
        dsimp [U, B]
        exact (ArithmeticFunction.LSeries_mul' hu hb).symm
      _ = LSeries (fun n ↦ (1 : ArithmeticFunction ℂ) n) (2 : ℂ) := by
        rw [moebiusBinomialHalf_mul_zetaBinomialHalf]
      _ = 1 := by
        rw [ArithmeticFunction.one_eq_delta, LSeries_delta]
        rfl
  have hBnonneg : 0 ≤ B := by
    exact LSeries_zetaBinomialHalf_nonneg (x := 2)
  have hBre0 : 0 ≤ B.re := (Complex.nonneg_iff.mp hBnonneg).1
  have hBim : B.im = 0 := (Complex.nonneg_iff.mp hBnonneg).2.symm
  have hBne : B ≠ 0 := by
    intro hB
    rw [hB, mul_zero] at hUB
    norm_num at hUB
  have hBreNe : B.re ≠ 0 := by
    intro h
    apply hBne
    apply Complex.ext
    · simpa using h
    · simpa using hBim
  have hBsq := LSeries_zetaBinomialHalf_sq (s := (2 : ℂ)) (by norm_num)
  have hBsqRe : B.re ^ 2 = (riemannZeta (2 : ℂ)).re := by
    change B * B = riemannZeta (2 : ℂ) at hBsq
    have hre := congrArg Complex.re hBsq
    simp only [Complex.mul_re] at hre
    rw [hBim] at hre
    simpa [pow_two] using hre
  have hsqrt : Real.sqrt (riemannZeta (2 : ℂ)).re = B.re := by
    rw [← hBsqRe, Real.sqrt_sq hBre0]
  have hBreal : B = (B.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hBim
  have hCU :
      LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) = U := by
    rw [squareDilatedMoebiusBinomialHalf, LSeries_mPart two_ne_zero]
    norm_num [U]
  rw [hCU, eq_inv_of_mul_eq_one_left hUB, hBreal, ← hsqrt]
  push_cast
  rw [one_div]

/-- The positive zeta-half summatory function is bounded by the number of terms. -/
theorem norm_arithmeticSummatory_zetaBinomialHalf_le (N : ℕ) :
    ‖arithmeticSummatory zetaBinomialHalf N‖ ≤ N := by
  rw [arithmeticSummatory]
  calc
    ‖∑ n ∈ Finset.Icc 1 N, zetaBinomialHalf n‖ ≤
        ∑ n ∈ Finset.Icc 1 N, ‖zetaBinomialHalf n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
      exact Finset.sum_le_sum fun n _hn => norm_zetaBinomialHalf_le_one n
    _ = N := by simp

/-- The undilated Kato conclusion implies one concrete global summatory estimate.  Writing the
estimate without division also covers `N = 0, 1`, where the Selberg--Delange scale vanishes. -/
theorem exists_zetaBinomialHalf_summatory_bound
    (hbase : ZetaBinomialHalfKatoInversion) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖arithmeticSummatory zetaBinomialHalf N‖ * Real.sqrt (Real.log N) ≤ C * N := by
  let q : ℕ → ℂ := fun N =>
    arithmeticSummatory zetaBinomialHalf N / selbergDelangeHalfScale N
  have hq : Tendsto q atTop (𝓝 ((1 / Real.sqrt Real.pi : ℝ) : ℂ)) := by
    simpa [q, ZetaBinomialHalfKatoInversion] using hbase
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto q hq).subset_closedBall (0 : ℂ)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro N
  by_cases hN : N ≤ 1
  · interval_cases N <;> simp
  · have hN2 : 2 ≤ N := by omega
    have hNpos : (0 : ℝ) < N := by positivity
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    have hsqrt : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.2 hlog
    have hmem : q N ∈ Metric.closedBall (0 : ℂ) C := hC ⟨N, rfl⟩
    have hqC : ‖q N‖ ≤ C := by simpa [Metric.mem_closedBall] using hmem
    have heq :
        ‖arithmeticSummatory zetaBinomialHalf N‖ * Real.sqrt (Real.log N) =
          ‖q N‖ * N := by
      dsimp [q]
      rw [norm_div]
      simp only [selbergDelangeHalfScale, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (div_pos hNpos hsqrt)]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hqC.trans (le_max_left _ _)) (by positivity)

private theorem sqrt_log_divisor_comparison {N d : ℕ}
    (hd : 1 ≤ d) (hdN : d ≤ N) (hN2 : 2 ≤ N) (hdd : d * d ≤ N) :
    Real.sqrt (Real.log (N : ℝ)) ≤
      2 * Real.sqrt (Real.log ((N / d : ℕ) : ℝ)) := by
  have hd0 : 0 < d := hd
  let M := N / d
  have hdM : d ≤ M := (Nat.le_div_iff_mul_le hd0).2 hdd
  have hM2 : 2 ≤ M := by
    by_cases hd1 : d = 1
    · subst d
      simpa [M] using hN2
    · omega
  have hNlt : N < d * (M + 1) := by
    simpa [M] using Nat.lt_mul_div_succ N hd0
  have hNM4 : N ≤ M ^ 4 := by
    have hprod : d * (M + 1) ≤ M * (M + 1) := Nat.mul_le_mul_right (M + 1) hdM
    have hplus : M + 1 ≤ M * M := by nlinarith
    calc
      N ≤ d * (M + 1) := hNlt.le
      _ ≤ M * (M + 1) := hprod
      _ ≤ M * (M * M) := Nat.mul_le_mul_left M hplus
      _ = M ^ 3 := by ring
      _ = M ^ 3 * 1 := by ring
      _ ≤ M ^ 3 * M := Nat.mul_le_mul_left (M ^ 3) (by omega)
      _ = M ^ 4 := by ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hd0 hdN)
  have hcast : (N : ℝ) ≤ (M : ℝ) ^ 4 := by exact_mod_cast hNM4
  have hlog : Real.log (N : ℝ) ≤ 4 * Real.log (M : ℝ) := by
    have hmono := Real.strictMonoOn_log.monotoneOn hNpos
      (by positivity : (0 : ℝ) < (M : ℝ) ^ 4) hcast
    simpa [Real.log_pow] using hmono
  have hlogM : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hsqN := Real.sq_sqrt (Real.log_nonneg hNone)
  have hsqM := Real.sq_sqrt hlogM
  have hsN := Real.sqrt_nonneg (Real.log (N : ℝ))
  have hsM := Real.sqrt_nonneg (Real.log (M : ℝ))
  have hresult : Real.sqrt (Real.log (N : ℝ)) ≤
      2 * Real.sqrt (Real.log (M : ℝ)) := by nlinarith
  simpa [M] using hresult

private theorem nat_rpow_three_quarters_le_self {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) ^ ((3 : ℝ) / 4) ≤ d := by
  exact Real.rpow_le_self_of_one_le (by exact_mod_cast hd) (by norm_num)

private theorem nat_rpow_eighth_le_quarter {N d : ℕ} (hd : 1 ≤ d)
    (hNdd : N < d * d) :
    (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (d : ℝ) ^ ((1 : ℝ) / 4) := by
  have hcast : (N : ℝ) ≤ (d : ℝ) ^ 2 := by
    rw [pow_two]
    exact_mod_cast hNdd.le
  have hpow := Real.rpow_le_rpow (by positivity) hcast (by norm_num : (0 : ℝ) ≤ 1 / 8)
  calc
    (N : ℝ) ^ ((1 : ℝ) / 8) ≤ ((d : ℝ) ^ 2) ^ ((1 : ℝ) / 8) := hpow
    _ = (d : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ d)]
      norm_num

private theorem zetaBinomialHalf_moving_ratio_le
    {C : ℝ} (hC : 0 ≤ C)
    (hglobal : ∀ M : ℕ,
      ‖arithmeticSummatory zetaBinomialHalf M‖ * Real.sqrt (Real.log M) ≤ C * M)
    {N d : ℕ} (hdmem : d ∈ Finset.Icc 1 N) :
    ‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
        Real.sqrt (Real.log N) / N ≤
      2 * max C 1 / ((d : ℝ) ^ ((3 : ℝ) / 4)) := by
  rcases Finset.mem_Icc.mp hdmem with ⟨hd, hdN⟩
  have hd0 : 0 < d := hd
  have hN0 : 0 < N := lt_of_lt_of_le hd0 hdN
  have hK0 : 0 ≤ max C 1 := le_trans (by norm_num) (le_max_right C 1)
  have hdR : (0 : ℝ) < d := by positivity
  have hdPow : 0 < (d : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hdR _
  by_cases hN1 : N = 1
  · subst N
    have hd1 : d = 1 := by omega
    subst d
    simp
  by_cases hdd : d * d ≤ N
  · have hN2 : 2 ≤ N := by omega
    have hsqrt := sqrt_log_divisor_comparison hd hdN hN2 hdd
    have hbase := hglobal (N / d)
    have hsum0 : 0 ≤ ‖arithmeticSummatory zetaBinomialHalf (N / d)‖ := norm_nonneg _
    have hpre :
        ‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
            Real.sqrt (Real.log (N : ℝ)) ≤ 2 * C * (N / d : ℕ) := by
      calc
        ‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
            Real.sqrt (Real.log (N : ℝ)) ≤
            ‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
              (2 * Real.sqrt (Real.log ((N / d : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hsqrt hsum0
        _ = 2 * (‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
              Real.sqrt (Real.log ((N / d : ℕ) : ℝ))) := by ring
        _ ≤ 2 * (C * (N / d : ℕ)) := mul_le_mul_of_nonneg_left hbase (by norm_num)
        _ = 2 * C * (N / d : ℕ) := by ring
    have hMd : ((N / d : ℕ) : ℝ) * d ≤ N := by
      exact_mod_cast Nat.div_mul_le_self N d
    have hCd :
        (2 * C * (N / d : ℕ)) / N ≤ 2 * C / d := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < N) hdR]
      nlinarith [hC]
    have hpowle := nat_rpow_three_quarters_le_self hd
    calc
      ‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
          Real.sqrt (Real.log N) / N ≤ (2 * C * (N / d : ℕ)) / N :=
        div_le_div_of_nonneg_right hpre (by positivity)
      _ ≤ 2 * C / d := hCd
      _ ≤ 2 * max C 1 / ((d : ℝ) ^ ((3 : ℝ) / 4)) := by
        exact div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left (le_max_left C 1) (by norm_num)) hdPow hpowle
  · have hNdd : N < d * d := lt_of_not_ge hdd
    have hsqrtN := sqrt_log_le_two_mul_rpow
      (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast (show 1 ≤ N by omega))
    have hrpow := nat_rpow_eighth_le_quarter hd hNdd
    have hsum := norm_arithmeticSummatory_zetaBinomialHalf_le (N / d)
    have hMd : ((N / d : ℕ) : ℝ) * d ≤ N := by
      exact_mod_cast Nat.div_mul_le_self N d
    have hthreeEq :
        (d : ℝ) ^ ((1 : ℝ) / 4) * (d : ℝ) ^ ((3 : ℝ) / 4) = d := by
      rw [← Real.rpow_add hdR]
      norm_num
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < N) hdPow]
    have hsqrtBound : Real.sqrt (Real.log (N : ℝ)) ≤
        2 * (d : ℝ) ^ ((1 : ℝ) / 4) :=
      hsqrtN.trans (mul_le_mul_of_nonneg_left hrpow (by norm_num))
    have hsumR : ‖arithmeticSummatory zetaBinomialHalf (N / d)‖ ≤
        ((N / d : ℕ) : ℝ) := hsum
    have hpair :
        ‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
            Real.sqrt (Real.log (N : ℝ)) ≤
          ((N / d : ℕ) : ℝ) * (2 * (d : ℝ) ^ ((1 : ℝ) / 4)) :=
      mul_le_mul hsumR hsqrtBound (Real.sqrt_nonneg _) (by positivity)
    calc
      (‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
          Real.sqrt (Real.log N)) * (d : ℝ) ^ ((3 : ℝ) / 4) ≤
          (((N / d : ℕ) : ℝ) * (2 * (d : ℝ) ^ ((1 : ℝ) / 4))) *
            (d : ℝ) ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hpair hdPow.le
      _ = 2 * ((N / d : ℕ) : ℝ) *
          ((d : ℝ) ^ ((1 : ℝ) / 4) * (d : ℝ) ^ ((3 : ℝ) / 4)) := by ring
      _ = 2 * (((N / d : ℕ) : ℝ) * d) := by rw [hthreeEq]; ring
      _ ≤ 2 * N := mul_le_mul_of_nonneg_left hMd (by norm_num)
      _ ≤ (2 * max C 1) * N := by
        have htwo : (2 : ℝ) ≤ 2 * max C 1 := by nlinarith [le_max_right C 1]
        exact mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg N)

/-- Explicit `3/4`-line majorant for the moving Tannery array. -/
def squarefreeConvolutionHalfTanneryBound (C : ℝ) (d : ℕ) : ℝ :=
  2 * max C 1 * ‖LSeries.term squareDilatedMoebiusBinomialHalf
    (((3 : ℝ) / 4 : ℝ) : ℂ) d‖

theorem summable_squarefreeConvolutionHalfTanneryBound (C : ℝ) :
    Summable (squarefreeConvolutionHalfTanneryBound C) := by
  have hc : LSeriesSummable squareDilatedMoebiusBinomialHalf
      (((3 : ℝ) / 4 : ℝ) : ℂ) :=
    LSeriesSummable_squareDilatedMoebiusBinomialHalf (by norm_num)
  exact hc.norm.mul_left (2 * max C 1)

private theorem norm_LSeriesTerm_squareCorrection_three_quarters {d : ℕ} (hd : 1 ≤ d) :
    ‖LSeries.term squareDilatedMoebiusBinomialHalf
        (((3 : ℝ) / 4 : ℝ) : ℂ) d‖ =
      ‖squareDilatedMoebiusBinomialHalf d‖ /
        ((d : ℝ) ^ ((3 : ℝ) / 4)) := by
  rw [LSeries.term_of_ne_zero (by omega), norm_div]
  congr 1
  have hp := Complex.norm_cpow_eq_rpow_re_of_pos
    (x := (d : ℝ)) (by positivity : (0 : ℝ) < d)
    ((((3 : ℝ) / 4 : ℝ) : ℂ))
  norm_num at hp ⊢
  simpa using hp

private theorem norm_squareCorrection_hyperbola {N d : ℕ}
    (hdmem : d ∈ Finset.Icc 1 N) :
    ‖squareDilatedMoebiusBinomialHalf d *
        arithmeticSummatory zetaBinomialHalf (N / d) /
          selbergDelangeHalfScale N‖ =
      ‖squareDilatedMoebiusBinomialHalf d‖ *
        (‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
          Real.sqrt (Real.log N) / N) := by
  rcases Finset.mem_Icc.mp hdmem with ⟨hd, hdN⟩
  by_cases hN1 : N = 1
  · subst N
    have hd1 : d = 1 := by omega
    subst d
    simp [selbergDelangeHalfScale]
  have hN2 : 2 ≤ N := by omega
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hsqrt : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.2 hlog
  rw [norm_div, norm_mul]
  simp only [selbergDelangeHalfScale, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (div_pos (by positivity : (0 : ℝ) < N) hsqrt)]
  field_simp

theorem squareCorrection_hyperbola_le_tanneryBound
    {C : ℝ} (hC : 0 ≤ C)
    (hglobal : ∀ M : ℕ,
      ‖arithmeticSummatory zetaBinomialHalf M‖ * Real.sqrt (Real.log M) ≤ C * M)
    {N d : ℕ} (hdmem : d ∈ Finset.Icc 1 N) :
    ‖squareDilatedMoebiusBinomialHalf d *
        arithmeticSummatory zetaBinomialHalf (N / d) /
          selbergDelangeHalfScale N‖ ≤ squarefreeConvolutionHalfTanneryBound C d := by
  rcases Finset.mem_Icc.mp hdmem with ⟨hd, _hdN⟩
  rw [norm_squareCorrection_hyperbola hdmem, squarefreeConvolutionHalfTanneryBound,
    norm_LSeriesTerm_squareCorrection_three_quarters hd]
  have hratio := zetaBinomialHalf_moving_ratio_le hC hglobal hdmem
  calc
    ‖squareDilatedMoebiusBinomialHalf d‖ *
        (‖arithmeticSummatory zetaBinomialHalf (N / d)‖ *
          Real.sqrt (Real.log N) / N) ≤
      ‖squareDilatedMoebiusBinomialHalf d‖ *
        (2 * max C 1 / (d : ℝ) ^ ((3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
    _ = 2 * max C 1 *
        (‖squareDilatedMoebiusBinomialHalf d‖ /
          (d : ℝ) ^ ((3 : ℝ) / 4)) := by ring

/-- The undilated Kato conclusion supplies the concrete summable majorant required by moving
Tannery.  The majorant is the correction's absolute Dirichlet term on `Re s = 3/4`, times one
global constant. -/
theorem exists_squarefreeConvolutionHalf_tannery_majorant
    (hbase : ZetaBinomialHalfKatoInversion) :
    ∃ bound : ℕ → ℝ,
      (∀ d, 0 ≤ bound d) ∧ Summable bound ∧
      ∀ N d : ℕ, d ∈ Finset.Icc 1 N →
        ‖squareDilatedMoebiusBinomialHalf d *
            arithmeticSummatory zetaBinomialHalf (N / d) /
              selbergDelangeHalfScale N‖ ≤ bound d := by
  obtain ⟨C, hC, hglobal⟩ := exists_zetaBinomialHalf_summatory_bound hbase
  refine ⟨squarefreeConvolutionHalfTanneryBound C, ?_,
    summable_squarefreeConvolutionHalfTanneryBound C, ?_⟩
  · intro d
    exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_right C 1)))
      (norm_nonneg _)
  · intro N d hdmem
    exact squareCorrection_hyperbola_le_tanneryBound hC hglobal hdmem

/-- **Concrete signed Selberg--Delange assembly.**  The one undilated positive zeta-half limit
supplies every fixed dilation and a summable majorant for the hyperbola array.  The signed
squarefree half then has the asserted main term.  No positivity assumption is made on the
correction. -/
theorem tendsto_squarefreeConvolutionHalf_selbergDelange
    (hbase : ZetaBinomialHalfKatoInversion) :
    Tendsto
      (fun N ↦ arithmeticSummatory squarefreeConvolutionHalf N /
        selbergDelangeHalfScale N)
      atTop
      (𝓝 (((1 / Real.sqrt Real.pi : ℝ) : ℂ) *
        LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ))) := by
  have hWI := zetaBinomialHalfWienerIkehara_of_katoInversion hbase
  obtain ⟨bound, hboundNonneg, hboundSummable, hdominated⟩ :=
    exists_squarefreeConvolutionHalf_tannery_majorant hbase
  rw [squarefreeConvolutionHalf_eq_zetaBinomialHalf_mul_squareCorrection, mul_comm]
  exact tendsto_arithmeticSummatory_mul_div_of_dominated_LSeries
    squareDilatedMoebiusBinomialHalf zetaBinomialHalf selbergDelangeHalfScale
      ((1 / Real.sqrt Real.pi : ℝ) : ℂ) bound hboundNonneg hboundSummable hWI hdominated

/-- Explicit-constant form of the concrete signed Selberg--Delange assembly. -/
theorem tendsto_squarefreeConvolutionHalf_selbergDelange_explicit
    (hbase : ZetaBinomialHalfKatoInversion) :
    Tendsto
      (fun N ↦ arithmeticSummatory squarefreeConvolutionHalf N /
        selbergDelangeHalfScale N)
      atTop
      (𝓝 (((1 / (Real.sqrt Real.pi *
        Real.sqrt (riemannZeta (2 : ℂ)).re) : ℝ) : ℝ) : ℂ)) := by
  have h := tendsto_squarefreeConvolutionHalf_selbergDelange hbase
  rw [LSeries_squareDilatedMoebiusBinomialHalf_one_eq_inv_sqrt_zeta_two] at h
  convert h using 1
  push_cast
  rw [one_div, one_div, one_div, mul_inv]

end RHTower
