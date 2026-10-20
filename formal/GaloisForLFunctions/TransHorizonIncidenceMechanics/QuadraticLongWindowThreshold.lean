import GaloisForLFunctions.TransHorizonIncidenceMechanics.GlobalRenormalizedDefectSignAtLargeHorizons
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusResponseWhiteNoiseLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPrimeHorizonCrossoverScale
import GaloisForLFunctions.BezoutValuationIncidence.QuadraticOrderWindowDirichletAndDissipation
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusGradientCoercivityAndRenormalizedDefect
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory

/-!
# The long-window regime starts at the quadratic scale

The long-window law bounds the renormalized defect on a window of length `M` by
`2 D̃_N(M) ≤ 4 H² - (M - 10 N²) V`, with harmonic sum `H`, non-harmonic period variance `V`, and the
quadratic window constant `10 N²` (the window observability constant has exact order `N²`). For the
Möbius weight the harmonic sum is bounded, `|m(N)| ≤ 1` (the floor identity `Σ μ(d) ⌊N/d⌋ = 1`),
and the terminal prime of Bertrand's band gives `V ≥ 1/(2N)`. Hence at **every** horizon `N ≥ 2`

`2 D̃_N(M; μ) ≤ 4 - (M - 10 N²)/(2N)`, and `D̃_N(M; μ) ≤ 0` for `M ≥ 10 N² + 8 N`:

the explicit long-window threshold is quadratic in the horizon, not quintic. At large horizons the
white-noise floor `V ≥ 1/288` makes the dissipation slope horizon-uniform,
`2 D̃_N(M; μ) ≤ 4 - (M - 10 N²)/288`, and together with the polynomial-window regime on `[2N, N³]` the
defect is **strictly negative at every prefix `M ≥ 2N`**. For the damped weight
`c_ε(d) = μ(d) d^{-ε}` the same law holds at every horizon with `|H_ε(N)| ≤ 3` and threshold
`10 N² + 72 N^{1+2ε}`.
-/

open Finset Filter ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem prefixDefect_eq_window (N M : ℕ) (c : ℕ → ℝ) :
    shortWindowRenormalizedDefect N 0 M c = sieveRenormalizedPrefixDefect N M c := by
  unfold shortWindowRenormalizedDefect
  simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]

/-- `|m(N)| = |Σ_{d ≤ N} μ(d)/d| ≤ 1`. -/
theorem abs_finiteHarmonicSum_moebiusReal_le_one (N : ℕ) :
    |finiteHarmonicSum N moebiusReal| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [finiteHarmonicSum]
  · exact RHTower.abs_sum_moebius_div_le_one N hN

/-! ### The Möbius weight at every horizon -/

/-- **Quadratic long-window law.** For `N ≥ 2` and `M ≥ 10 N²`,
`2 D̃_N(M; μ) ≤ 4 - (M - 10 N²)/(2N)`. -/
theorem two_mul_moebius_defect_le_quadratic_window {N M : ℕ} (hN : 2 ≤ N)
    (hM : 10 * (N : ℝ) ^ 2 ≤ M) :
    2 * sieveRenormalizedPrefixDefect N M moebiusReal ≤
      4 - ((M : ℝ) - 10 * (N : ℝ) ^ 2) / (2 * N) := by
  have hw := two_mul_shortWindowRenormalizedDefect_le_ten_mul_sq hN 0 M moebiusReal
  rw [prefixDefect_eq_window] at hw
  have hH : finiteHarmonicSum N moebiusReal ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_finiteHarmonicSum_moebiusReal_le_one N)
  obtain ⟨p, hp⟩ := exists_mem_sievePrimeTail hN
  obtain ⟨hpI, hpp, -⟩ := mem_filter.mp hp
  obtain ⟨hp2, hpN⟩ := mem_Icc.mp hpI
  have hμ : moebiusReal p = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime hpp]; norm_num
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpNR : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hmode : 1 / (2 * (N : ℝ)) ≤ (p.totient : ℝ) * (moebiusReal p / (p : ℝ)) ^ 2 := by
    rw [Nat.totient_prime hpp, hμ, Nat.cast_sub (by omega), div_pow, neg_one_sq, Nat.cast_one]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hV := hmode.trans (primeTail_mode_le_sieveVariance hp moebiusReal)
  have hgap0 : 0 ≤ (M : ℝ) - 10 * (N : ℝ) ^ 2 := by linarith
  have hcomp : ((M : ℝ) - 10 * (N : ℝ) ^ 2) / (2 * N) ≤
      ((M : ℝ) - 10 * (N : ℝ) ^ 2) * sieveVariance N moebiusReal := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hV hgap0
  linarith

/-- **Quadratic threshold at every horizon.** For `N ≥ 2`, `D̃_N(M; μ) ≤ 0` once `M ≥ 10 N² + 8 N`. -/
theorem moebius_defect_nonpos_of_quadratic_window {N M : ℕ} (hN : 2 ≤ N)
    (hM : 10 * (N : ℝ) ^ 2 + 8 * N ≤ M) :
    sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := two_mul_moebius_defect_le_quadratic_window hN (by linarith)
  have hq : 4 ≤ ((M : ℝ) - 10 * (N : ℝ) ^ 2) / (2 * N) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

/-! ### Horizon-uniform slope at large horizons -/

/-- **Uniform long-window slope.** Eventually in the horizon, for every `M ≥ 10 N²`,
`2 D̃_N(M; μ) ≤ 4 - (M - 10 N²)/288`. -/
theorem eventually_two_mul_moebius_defect_le_uniform_slope :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, 10 * (N : ℝ) ^ 2 ≤ M →
      2 * sieveRenormalizedPrefixDefect N M moebiusReal ≤ 4 - ((M : ℝ) - 10 * (N : ℝ) ^ 2) / 288 := by
  filter_upwards [eventually_periodCovariance_moebius_zero_ge, eventually_ge_atTop 2]
    with N hvar hN M hM
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal] at hvar
  simp_rw [ramanujanLagWeight_zero_left] at hvar
  have hV : 1 / 288 ≤ sieveVariance N moebiusReal := hvar
  have hw := two_mul_shortWindowRenormalizedDefect_le_ten_mul_sq hN 0 M moebiusReal
  rw [prefixDefect_eq_window] at hw
  have hH : finiteHarmonicSum N moebiusReal ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_finiteHarmonicSum_moebiusReal_le_one N)
  have hgap0 : 0 ≤ (M : ℝ) - 10 * (N : ℝ) ^ 2 := by linarith
  have hcomp : ((M : ℝ) - 10 * (N : ℝ) ^ 2) / 288 ≤
      ((M : ℝ) - 10 * (N : ℝ) ^ 2) * sieveVariance N moebiusReal := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hV hgap0
  linarith

/-- **Strict global sign.** Eventually in the horizon, `D̃_N(M; μ) < 0` at every prefix `M ≥ 2N`: the
polynomial-window regime covers `[2N, N³]` and the uniform long-window slope covers `M > 10 N² + 1152`. -/
theorem eventually_moebius_defect_neg_all :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, 2 * N ≤ M → sieveRenormalizedPrefixDefect N M moebiusReal < 0 := by
  filter_upwards [eventually_moebiusRenormalizedDefect_polynomial_cofinal_bound 1,
    eventually_two_mul_moebius_defect_le_uniform_slope, eventually_ge_atTop 1200] with N hpoly hlong hN M hM
  have hNR : (1200 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hw : M ≤ N ^ 3
  · have h := hpoly M (mem_Icc.mpr ⟨hM, by simpa using hw⟩)
    have : -(N : ℝ) / (2 * Real.pi ^ 2) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  · have hM3 : (N : ℝ) ^ 3 ≤ M := by exact_mod_cast (show N ^ 3 ≤ M by omega)
    have hcube : 10 * (N : ℝ) ^ 2 + 1153 ≤ (N : ℝ) ^ 3 := by nlinarith
    have h := hlong M (by linarith)
    linarith

/-! ### The damped weight at every horizon -/

private theorem pmPowerDampedDivisorDensity_re_le_one {ε : ℝ} (hε : 0 < ε) :
    (RHTower.pmPowerDampedDivisorDensity ε).re ≤ 1 := by
  refine le_of_tendsto (RHTower.tendsto_pmPowerDampedDivisorSum_div_real hε) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [div_le_one (by linarith)]
  unfold RHTower.pmPowerDampedDivisorSum
  calc ∑ n ∈ Icc 1 ⌊x⌋₊, RHTower.pmPowerDampedDivisorCoeff ε n ≤ ∑ _n ∈ Icc 1 ⌊x⌋₊, (1 : ℝ) :=
        sum_le_sum fun n _ => RHTower.pmPowerDampedDivisorCoeff_le_one hε.le n
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le (by linarith)

/-- The damped harmonic sum is bounded: `|H_ε(N)| ≤ 3`. -/
theorem abs_finiteHarmonicSum_pmPowerDamped_le_three {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    |finiteHarmonicSum N (pmPowerDampedRealWeight ε)| ≤ 3 := by
  have h := abs_pmPowerDampedDivisorDensity_re_sub_le hε (n := N) (η := 1)
    fun t _ => abs_finiteHarmonicSum_moebiusReal_le_one t
  have hr : ((N + 1 : ℕ) : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (by linarith)
  have hr0 : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hρ0 := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have hρ1 := pmPowerDampedDivisorDensity_re_le_one hε
  have h' := abs_le.mp h
  rw [abs_le]
  constructor <;> nlinarith [h'.1, h'.2]

/-- **Damped quadratic long-window law.** For `ε > 0`, `N ≥ 2` and `M ≥ 10 N²`,
`2 D̃_N(M; c_ε) ≤ 36 - (M - 10 N²) N^{-2ε}/(2N)`. -/
theorem two_mul_pmPowerDamped_defect_le_quadratic_window {ε : ℝ} (hε : 0 < ε) {N M : ℕ}
    (hN : 2 ≤ N) (hM : 10 * (N : ℝ) ^ 2 ≤ M) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
      36 - ((M : ℝ) - 10 * (N : ℝ) ^ 2) * ((N : ℝ) ^ (-(2 * ε)) / (2 * N)) := by
  have hw := two_mul_shortWindowRenormalizedDefect_le_ten_mul_sq hN 0 M (pmPowerDampedRealWeight ε)
  rw [prefixDefect_eq_window] at hw
  have hH : finiteHarmonicSum N (pmPowerDampedRealWeight ε) ^ 2 ≤ 9 := by
    have h := abs_finiteHarmonicSum_pmPowerDamped_le_three hε N
    rw [← sq_abs]; nlinarith [abs_nonneg (finiteHarmonicSum N (pmPowerDampedRealWeight ε))]
  obtain ⟨p, hp⟩ := exists_mem_sievePrimeTail hN
  obtain ⟨hpI, hpp, -⟩ := mem_filter.mp hp
  obtain ⟨hp2, hpN⟩ := mem_Icc.mp hpI
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  have hpNR : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hμ : moebiusReal p ^ 2 = 1 := by
    unfold moebiusReal; rw [moebius_apply_prime hpp]; norm_num
  have hpow : ((p : ℝ) ^ (-ε)) ^ 2 = (p : ℝ) ^ (-(2 * ε)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; push_cast; ring_nf
  have hNp : (N : ℝ) ^ (-(2 * ε)) ≤ (p : ℝ) ^ (-(2 * ε)) :=
    Real.rpow_le_rpow_of_nonpos hp0 hpNR (by linarith)
  have hNe : 0 ≤ (N : ℝ) ^ (-(2 * ε)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmode : (N : ℝ) ^ (-(2 * ε)) / (2 * N) ≤
      (p.totient : ℝ) * (pmPowerDampedRealWeight ε p / (p : ℝ)) ^ 2 := by
    rw [Nat.totient_prime hpp, Nat.cast_sub (by omega), Nat.cast_one, pmPowerDampedRealWeight,
      div_pow, mul_pow, hμ, one_mul, hpow]
    have h1 : 1 / (2 * (N : ℝ)) ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    calc (N : ℝ) ^ (-(2 * ε)) / (2 * N) = (N : ℝ) ^ (-(2 * ε)) * (1 / (2 * N)) := by ring
      _ ≤ (p : ℝ) ^ (-(2 * ε)) * (((p : ℝ) - 1) / (p : ℝ) ^ 2) :=
          mul_le_mul hNp h1 (by positivity) (Real.rpow_nonneg hp0.le _)
      _ = _ := by ring
  have hV := hmode.trans (primeTail_mode_le_sieveVariance hp (pmPowerDampedRealWeight ε))
  have hgap0 : 0 ≤ (M : ℝ) - 10 * (N : ℝ) ^ 2 := by linarith
  have hcomp := mul_le_mul_of_nonneg_left hV hgap0
  linarith

/-- **Damped quadratic threshold at every horizon.** For `ε > 0` and `N ≥ 2`, `D̃_N(M; c_ε) ≤ 0` once
`M ≥ 10 N² + 72 N^{1+2ε}`. -/
theorem pmPowerDamped_defect_nonpos_of_quadratic_window {ε : ℝ} (hε : 0 < ε) {N M : ℕ}
    (hN : 2 ≤ N) (hM : 10 * (N : ℝ) ^ 2 + 72 * (N : ℝ) ^ (1 + 2 * ε) ≤ M) :
    sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow0 : 0 ≤ (N : ℝ) ^ (1 + 2 * ε) := Real.rpow_nonneg hNpos.le _
  have h := two_mul_pmPowerDamped_defect_le_quadratic_window hε hN (by linarith)
  have hsplit : (N : ℝ) ^ (1 + 2 * ε) * (N : ℝ) ^ (-(2 * ε)) = N := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hNe : 0 ≤ (N : ℝ) ^ (-(2 * ε)) := Real.rpow_nonneg hNpos.le _
  have hq : 36 ≤ ((M : ℝ) - 10 * (N : ℝ) ^ 2) * ((N : ℝ) ^ (-(2 * ε)) / (2 * N)) := by
    calc (36 : ℝ) = 72 * ((N : ℝ) ^ (1 + 2 * ε) * (N : ℝ) ^ (-(2 * ε))) / (2 * N) := by
          rw [hsplit]; field_simp; ring
      _ = 72 * (N : ℝ) ^ (1 + 2 * ε) * ((N : ℝ) ^ (-(2 * ε)) / (2 * N)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
