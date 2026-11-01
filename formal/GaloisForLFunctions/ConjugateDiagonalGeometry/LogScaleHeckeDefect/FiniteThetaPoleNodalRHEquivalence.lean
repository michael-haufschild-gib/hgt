import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.DyadicPoleNodalRHEquivalence
import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaApertureMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.PolynomialThetaMetric

/-!
# Zero-Coordinate-Free Finite-Theta Pole-Nodal Equivalences for `RiemannHypothesis`

Combining the pole-nodal ordinate construction (`exists_poleNodal_ordinate_in_Icc`) with the
growing-aperture finite integer theta certificates (`exists_finiteThetaSource_aperture_error_bound`
and `exists_polynomialThetaSource_aperture_error_bound`) eliminates all spectral zero coordinates
from the dyadic log-scale `RiemannHypothesis` equivalence:

1. **Base bump twist compatibility and explicit aperture schedules**
   (`baseBumpTest`, `sourceTwist_baseBumpTest_eq`, `apertureStage`, `linearThetaStage`,
    `exists_uniform_aperture_heckeDefect_error_bounds`,
    `exists_linearThetaStage_polynomialReading_sub_heckeDefect_le`):
   `sourceTwist γ baseBumpTest = baseTwistTest γ` holds definitionally with support radius `1 / 4`.
   Both `apertureStage L T` (for arbitrary `L, T ∈ ℝ` and `γ ∈ [T, T + 1]`) and the linear stage
   `linearThetaStage γ = max 2 ⌈2(|γ| + 2)⌉₊` (for `γ ≥ 2` and `0 ≤ L ≤ 2 log γ`) satisfy the
   aperture inequalities `|γ| ≤ n / 2` and `1 / 4 + |L| ≤ 2 log(n + 1)`, yielding uniform stage
   error bounds and an `O(log γ / γ)` approximation of `heckeDefect` at `linearThetaStage γ`.

2. **Six-way zero-coordinate-free finite-theta equivalence for `RiemannHypothesis`**
   (`riemannHypothesis_finiteTheta_poleNodal_dyadic_tfae`):
   For every `c₀ > 0` and `α ≥ 0`, with `L_k(T) = 2^k c₀ log T`, `RiemannHypothesis` is
   unconditionally equivalent (`TFAE`) to:
   - the pole-nodal restricted `finiteThetaSourceMomentReading` criterion at `apertureStage`;
   - the pole-nodal restricted `polynomialThetaSourceMomentReading` criterion at `apertureStage`;
   - the stage-uniform full-aperture `finiteThetaSourceMomentReading` criterion;
   - the pure finite-theta existential unit-window criterion (`∃ γ ∈ [T, T + 1]`, eliminating both
     spectral zero coordinates and `primePolynomial`);
   - uniform `< ε` vanishing of `polynomialThetaSourceMomentReading` across the growing aperture.

3. **Anti-nodal exponential pole growth and sharpness of the pole-nodal locus**
   (`exists_tr_twist_baseBump_one_ne_zero_in_Ico`, `exists_poleAntinodal_ordinate_in_Icc`,
    `exists_antinodal_primePolynomial_exp_growth_of_riemannHypothesis`):
   Analytic continuation of the entire transform `z ↦ tr baseBump (1 - z I)` from `z = -I / 2`
   (`tr baseBump (1 / 2) = 1 ≠ 0`) forces nonvanishing on every nondegenerate interval `[a₀, b₀)`.
   The four-phase grid then produces anti-nodal ordinates `γ_anti ∈ [a₀, b₀]` where
   `2 Re((tr (twist γ_anti F_L) 1)²) ≥ c_anti exp L / L²`, forcing `(Π_{F_L}).re` and `‖Π_{F_L}‖`
   to grow exponentially as `exp L / L²` even under `RiemannHypothesis` while finite-theta moment
   readings remain bounded (`→ 0`).
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators Real ComplexConjugate ContDiff
open _root_.RHTower _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.ArithmeticOrientationGeometry
open ArithmeticPolarization SquareRootThreshold

/-! ## §1. Twist compatibility, explicit aperture schedules, and linear-prefix error bounds -/

/-- Untwisted `baseBump` packaged as a `CompactTest` for `sourceTwist`. -/
def baseBumpTest : CompactTest :=
  ⟨baseBump, contDiff_baseBump, hasCompactSupport_baseBump⟩

/-- `sourceTwist γ baseBumpTest` coincides definitionally with `baseTwistTest γ`. -/
theorem sourceTwist_baseBumpTest_eq (γ : ℝ) :
    sourceTwist γ baseBumpTest = baseTwistTest γ :=
  Subtype.ext rfl

theorem abs_le_quarter_of_baseBumpTest_ne_zero (u : ℝ) (hu : baseBumpTest.1 u ≠ 0) :
    |u| ≤ 1 / 4 := by
  by_contra hgt
  exact hu (baseBump_eq_zero_of_abs_ge (not_le.mp hgt).le)

/-- Explicit zero-coordinate-free aperture stage covering all `γ ∈ [T, T + 1]` at scale `L`. -/
def apertureStage (L T : ℝ) : ℕ :=
  max 1 (max ⌈2 * (|T| + 2)⌉₊ ⌈Real.exp ((|L| + 1 / 4) / 2)⌉₊)

/-- Linear integer-theta stage `n_lin(γ) = max 2 ⌈2(|γ| + 2)⌉₊`, sufficient for all logarithmic
scales `0 ≤ L ≤ 2 log γ` once `γ ≥ 1`. -/
def linearThetaStage (γ : ℝ) : ℕ :=
  max 2 ⌈2 * (|γ| + 2)⌉₊

theorem one_le_apertureStage (L T : ℝ) : 1 ≤ apertureStage L T :=
  le_max_left _ _

theorem apertureStage_admissible (L T : ℝ) {γ : ℝ} (hγ : γ ∈ Icc T (T + 1)) :
    |γ| ≤ (apertureStage L T : ℝ) / 2 ∧
      1 / 4 + (1 : ℝ) * |L| ≤ 2 * Real.log ((apertureStage L T : ℝ) + 1) := by
  have hγ_abs : |γ| ≤ |T| + 2 := by
    rw [abs_le]
    have hT := neg_abs_le T
    have hT' := le_abs_self T
    constructor <;> linarith [hγ.1, hγ.2]
  have hceil1 : 2 * (|T| + 2) ≤ (apertureStage L T : ℝ) := by
    have h1 : ⌈2 * (|T| + 2)⌉₊ ≤ apertureStage L T :=
      (le_max_left _ _).trans (le_max_right _ _)
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hceil2 : Real.exp ((|L| + 1 / 4) / 2) < (apertureStage L T : ℝ) + 1 := by
    have h1 : ⌈Real.exp ((|L| + 1 / 4) / 2)⌉₊ ≤ apertureStage L T :=
      (le_max_right _ _).trans (le_max_right _ _)
    have h2 : (⌈Real.exp ((|L| + 1 / 4) / 2)⌉₊ : ℝ) ≤ (apertureStage L T : ℝ) := by
      exact_mod_cast h1
    linarith [Nat.le_ceil (Real.exp ((|L| + 1 / 4) / 2))]
  refine ⟨by linarith, ?_⟩
  have hlog := Real.log_le_log (Real.exp_pos _) hceil2.le
  rw [Real.log_exp] at hlog
  linarith

theorem one_le_linearThetaStage (γ : ℝ) : 1 ≤ linearThetaStage γ :=
  le_trans (by norm_num) (le_max_left _ _)

theorem two_le_linearThetaStage (γ : ℝ) : 2 ≤ linearThetaStage γ :=
  le_max_left _ _

theorem linearThetaStage_mono {γ₁ γ₂ : ℝ} (h0 : 0 ≤ γ₁) (hle : γ₁ ≤ γ₂) :
    linearThetaStage γ₁ ≤ linearThetaStage γ₂ := by
  unfold linearThetaStage
  have habs1 : |γ₁| = γ₁ := abs_of_nonneg h0
  have habs2 : |γ₂| = γ₂ := abs_of_nonneg (h0.trans hle)
  rw [habs1, habs2]
  exact max_le_max le_rfl (Nat.ceil_le_ceil (by linarith))

theorem linearThetaStage_bounds {γ : ℝ} (hγ : 1 ≤ γ) :
    2 * γ + 4 ≤ (linearThetaStage γ : ℝ) ∧ (linearThetaStage γ : ℝ) ≤ 2 * γ + 5 := by
  have habs : |γ| = γ := abs_of_pos (by linarith)
  have h2_le : 2 ≤ ⌈2 * (|γ| + 2)⌉₊ := by
    rw [habs]
    have h6 : (2 : ℝ) ≤ 2 * (γ + 2) := by linarith
    exact_mod_cast h6.trans (Nat.le_ceil _)
  have heq : linearThetaStage γ = ⌈2 * (|γ| + 2)⌉₊ := max_eq_right h2_le
  rw [heq, habs]
  constructor
  · have h1 := Nat.le_ceil (2 * (γ + 2))
    linarith
  · have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * (γ + 2))
    linarith

/-- At linear stage `linearThetaStage γ`, every scale `0 ≤ L ≤ 2 log γ` (`γ ≥ 1`) satisfies the
full growing-aperture hypothesis `1 / 4 + |L| ≤ 2 log(linearThetaStage γ + 1)`. -/
theorem linearThetaStage_admissible {γ L : ℝ} (hγ : 1 ≤ γ) (hL0 : 0 ≤ L)
    (hL : L ≤ 2 * Real.log γ) :
    |γ| ≤ (linearThetaStage γ : ℝ) / 2 ∧
      1 / 4 + (1 : ℝ) * |L| ≤ 2 * Real.log ((linearThetaStage γ : ℝ) + 1) := by
  obtain ⟨hlo, _⟩ := linearThetaStage_bounds hγ
  have habs_γ : |γ| = γ := abs_of_pos (by linarith)
  have habs_L : |L| = L := abs_of_nonneg hL0
  refine ⟨by rw [habs_γ]; linarith, ?_⟩
  rw [one_mul, habs_L]
  have hexp_18 : Real.exp (1 / 8 : ℝ) ≤ 2 := by
    have hlog2 : (1 / 8 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      linarith
    calc Real.exp (1 / 8 : ℝ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hlog2
      _ = 2 := Real.exp_log zero_lt_two
  have hexp_bound : Real.exp ((1 / 4 + L) / 2) ≤ (linearThetaStage γ : ℝ) + 1 := by
    calc Real.exp ((1 / 4 + L) / 2)
        ≤ Real.exp (1 / 8 + Real.log γ) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (1 / 8) * Real.exp (Real.log γ) := Real.exp_add _ _
      _ = Real.exp (1 / 8) * γ := by rw [Real.exp_log (by linarith : 0 < γ)]
      _ ≤ 2 * γ := mul_le_mul_of_nonneg_right hexp_18 (by linarith)
      _ ≤ (linearThetaStage γ : ℝ) + 1 := by linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hexp_bound
  rw [Real.log_exp] at hlog
  linarith

/-- Any sequence `e : ℕ → ℝ` converging to `0` is uniformly bounded in absolute value across all
`n : ℕ`. -/
private theorem exists_forall_abs_le_of_tendsto_zero {e : ℕ → ℝ} (ht : Tendsto e atTop (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, |e n| ≤ M := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht 1 zero_lt_one
  let prefMax : ℝ := ∑ k ∈ Finset.range N, |e k|
  have hpref_nn : 0 ≤ prefMax := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨prefMax + 1, by linarith, fun n => ?_⟩
  by_cases hn : n < N
  · have hle : |e n| ≤ prefMax :=
      Finset.single_le_sum (f := fun k => |e k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr hn)
    linarith
  · have h1 := hN n (not_lt.mp hn)
    rw [Real.dist_eq, sub_zero] at h1
    linarith

/-- Uniform stage-independent error constant controlling both `finiteThetaSourceMomentReading` and
`polynomialThetaSourceMomentReading` against `heckeDefect (baseTwistTest γ) L` across all
admissible `(n, L, γ)`. -/
theorem exists_uniform_aperture_heckeDefect_error_bounds :
    ∃ E_unif : ℝ, 0 ≤ E_unif ∧
      ∀ n : ℕ, 1 ≤ n → ∀ L γ : ℝ,
        |γ| ≤ (n : ℝ) / 2 → 1 / 4 + |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
        |finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n -
            heckeDefect (baseTwistTest γ) L| ≤ E_unif ∧
          |polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n -
            heckeDefect (baseTwistTest γ) L| ≤ E_unif := by
  obtain ⟨B₁, hB₁, hb₁⟩ := exists_finiteThetaSource_aperture_error_bound
  obtain ⟨B₂, hB₂, hb₂⟩ := exists_polynomialThetaSource_aperture_error_bound
  have ht₁ : Tendsto (fun n : ℕ =>
      B₁ * Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) +
        40 * sourceReferenceTail n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_sourceApertureWindowError B₁).add (tendsto_sourceReferenceTail.const_mul 40)
  have ht₂ : Tendsto (fun n : ℕ =>
      B₂ / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_polynomialSourceWindowError B₂).add (tendsto_sourceReferenceTail.const_mul 40)
  obtain ⟨M₁, hM₁, hbd₁⟩ := exists_forall_abs_le_of_tendsto_zero ht₁
  obtain ⟨M₂, hM₂, hbd₂⟩ := exists_forall_abs_le_of_tendsto_zero ht₂
  set S₂ : ℝ := 4 * sourceTestSize baseBumpTest ^ 2
  have hS₂_nn : 0 ≤ S₂ := by dsimp [S₂]; positivity
  refine ⟨S₂ * (M₁ + M₂), mul_nonneg hS₂_nn (add_nonneg hM₁ hM₂),
    fun n hn L γ hγ hwin => ?_⟩
  have hwin' : (1 / 4 : ℝ) + ((1 : ℕ) : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    simpa only [Nat.cast_one, one_mul] using hwin
  have h1 := hb₁ n hn baseBumpTest (1 / 4) (by norm_num)
    abs_le_quarter_of_baseBumpTest_ne_zero 1 L γ hγ hwin'
  have h2 := hb₂ n hn baseBumpTest (1 / 4) (by norm_num)
    abs_le_quarter_of_baseBumpTest_ne_zero 1 L γ hγ hwin'
  have hsum_eq : (∑' ρ : zetaZeroConfig.carrier,
      zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) ^ 1) =
      heckeDefect (baseTwistTest γ) L := by
    simp only [pow_one, heckeDefect]
  rw [sourceTwist_baseBumpTest_eq, hsum_eq, pow_one, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    at h1 h2
  have he₁ : B₁ * Real.exp (-((n : ℝ) ^ 4) + 68 * (n : ℝ) ^ 2 + 66) +
      40 * sourceReferenceTail n ≤ M₁ := (le_abs_self _).trans (hbd₁ n)
  have he₂ : B₂ / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n ≤ M₂ :=
    (le_abs_self _).trans (hbd₂ n)
  constructor
  · calc |finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n -
            heckeDefect (baseTwistTest γ) L|
        ≤ sourceTestSize baseBumpTest ^ 2 * M₁ * 4 := by
          nlinarith [h1, he₁, sq_nonneg (sourceTestSize baseBumpTest)]
      _ ≤ S₂ * (M₁ + M₂) := by dsimp [S₂]; nlinarith [hS₂_nn, hM₂]
  · calc |polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n -
            heckeDefect (baseTwistTest γ) L|
        ≤ sourceTestSize baseBumpTest ^ 2 * M₂ * 4 := by
          nlinarith [h2, he₂, sq_nonneg (sourceTestSize baseBumpTest)]
      _ ≤ S₂ * (M₁ + M₂) := by dsimp [S₂]; nlinarith [hS₂_nn, hM₁]

/-- Quantitative `O(log γ / γ)` approximation of `heckeDefect` by `polynomialThetaSourceMomentReading`
along any stage `n ≥ linearThetaStage γ` with `(n : ℝ) ≤ 4 * γ + 9`, uniformly for `γ ≥ 2` and
`0 ≤ L ≤ 2 log γ`. -/
theorem exists_polynomialReading_sub_heckeDefect_le_log_div :
    ∃ C_lin : ℝ, 0 < C_lin ∧ ∀ (γ L : ℝ) (n : ℕ),
      2 ≤ γ → 0 ≤ L → L ≤ 2 * Real.log γ →
      linearThetaStage γ ≤ n → (n : ℝ) ≤ 4 * γ + 9 →
      |polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n -
          heckeDefect (baseTwistTest γ) L| ≤
        C_lin * Real.log γ / γ := by
  obtain ⟨B, hB, hb⟩ := exists_polynomialThetaSource_aperture_logarithmic_bound
  set S₂ : ℝ := 4 * sourceTestSize baseBumpTest ^ 2
  set C_const : ℝ := B + 320 * (|xiLineTwoLogDerivConstant| + Real.log 11) + 1
  set C_lin : ℝ := (S₂ + 1) * (2 * C_const + 320)
  have hC_pos : 0 < C_const := by
    have : 0 ≤ Real.log 11 := Real.log_nonneg (by norm_num)
    dsimp [C_const]; positivity
  have hClin_pos : 0 < C_lin := by
    have : 0 ≤ S₂ := by dsimp [S₂]; positivity
    dsimp [C_lin]; positivity
  refine ⟨C_lin, hClin_pos, fun γ L n hγ2 hL0 hL hn_lo hn_hi => ?_⟩
  have hγ1 : 1 ≤ γ := by linarith
  have hγ_pos : 0 < γ := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log γ := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log zero_lt_two hγ2
    linarith
  have hn1 : 1 ≤ n := (one_le_linearThetaStage γ).trans hn_lo
  obtain ⟨hadm_γ, hadm_L⟩ := linearThetaStage_admissible hγ1 hL0 hL
  have hn_cast_le : (linearThetaStage γ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_lo
  have hn_γ : |γ| ≤ (n : ℝ) / 2 := hadm_γ.trans (by linarith)
  have hn_win : (1 / 4 : ℝ) + ((1 : ℕ) : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    have hlog_mono := Real.log_le_log (by positivity : 0 < (linearThetaStage γ : ℝ) + 1)
      (by linarith : (linearThetaStage γ : ℝ) + 1 ≤ (n : ℝ) + 1)
    linarith [hadm_L]
  have hmain := hb n hn1 baseBumpTest (1 / 4) (by norm_num)
    abs_le_quarter_of_baseBumpTest_ne_zero 1 L γ hn_γ hn_win
  have hsum_eq : (∑' ρ : zetaZeroConfig.carrier,
      zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) ^ 1) =
      heckeDefect (baseTwistTest γ) L := by
    simp only [pow_one, heckeDefect]
  rw [sourceTwist_baseBumpTest_eq, hsum_eq, pow_one, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    at hmain
  obtain ⟨hlin_lo, _⟩ := linearThetaStage_bounds hγ1
  have hn_ge_2γ : 2 * γ ≤ (n : ℝ) := by linarith
  have hterm1 : B / ((n : ℝ) + 1) ^ 2 ≤ B / γ := by
    have hsq : γ ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_left hB hγ_pos hsq
  have hlog_n4 : Real.log ((n : ℝ) + 4) ≤ Real.log 11 + Real.log γ := by
    have hle : (n : ℝ) + 4 ≤ 11 * γ := by linarith
    calc Real.log ((n : ℝ) + 4)
        ≤ Real.log (11 * γ) := Real.log_le_log (by positivity) hle
      _ = Real.log 11 + Real.log γ := Real.log_mul (by norm_num) hγ_pos.ne'
  have h640_le : 640 / (n : ℝ) ≤ 320 / γ := by
    rw [div_le_div_iff₀ (by linarith) hγ_pos]
    linarith
  have hxi_nn : 0 ≤ |xiLineTwoLogDerivConstant| + Real.log ((n : ℝ) + 4) :=
    add_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith))
  have hterm2 : (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)) ≤
      (320 / γ) * (|xiLineTwoLogDerivConstant| + Real.log 11 + Real.log γ) := by
    have h1 : xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4) ≤
        |xiLineTwoLogDerivConstant| + Real.log ((n : ℝ) + 4) :=
      add_le_add (le_abs_self _) le_rfl
    have h2 : |xiLineTwoLogDerivConstant| + Real.log ((n : ℝ) + 4) ≤
        |xiLineTwoLogDerivConstant| + Real.log 11 + Real.log γ := by linarith
    calc (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))
        ≤ (640 / (n : ℝ)) * (|xiLineTwoLogDerivConstant| + Real.log ((n : ℝ) + 4)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (320 / γ) * (|xiLineTwoLogDerivConstant| + Real.log ((n : ℝ) + 4)) :=
          mul_le_mul_of_nonneg_right h640_le hxi_nn
      _ ≤ (320 / γ) * (|xiLineTwoLogDerivConstant| + Real.log 11 + Real.log γ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsum_terms : B / ((n : ℝ) + 1) ^ 2 +
      (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)) ≤
      (2 * C_const + 320) * Real.log γ / γ := by
    have h1_le : (1 : ℝ) ≤ 2 * Real.log γ := by linarith
    rw [le_div_iff₀ hγ_pos]
    have ht1 := (le_div_iff₀ hγ_pos).mp hterm1
    have ht2 : (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)) * γ ≤
        320 * (|xiLineTwoLogDerivConstant| + Real.log 11 + Real.log γ) := by
      have hm := mul_le_mul_of_nonneg_right hterm2 hγ_pos.le
      have hsimp : 320 / γ * (|xiLineTwoLogDerivConstant| + Real.log 11 + Real.log γ) * γ =
          320 * (|xiLineTwoLogDerivConstant| + Real.log 11 + Real.log γ) := by
        field_simp
      linarith
    have hc_mul : C_const * 1 ≤ C_const * (2 * Real.log γ) :=
      mul_le_mul_of_nonneg_left h1_le hC_pos.le
    dsimp [C_const] at hc_mul ⊢
    linarith
  have hS_le : 4 * sourceTestSize baseBumpTest ^ 2 ≤ S₂ + 1 := by dsimp [S₂]; linarith
  have hrhs_pos : 0 < (2 * C_const + 320) * Real.log γ / γ := by
    have : 0 < Real.log γ := by linarith
    positivity
  calc |polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n -
          heckeDefect (baseTwistTest γ) L|
      ≤ (4 * sourceTestSize baseBumpTest ^ 2) *
          (B / ((n : ℝ) + 1) ^ 2 +
            (640 / (n : ℝ)) * (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))) := by
        linarith [hmain]
    _ ≤ (4 * sourceTestSize baseBumpTest ^ 2) * ((2 * C_const + 320) * Real.log γ / γ) :=
        mul_le_mul_of_nonneg_left hsum_terms (by positivity)
    _ ≤ (S₂ + 1) * ((2 * C_const + 320) * Real.log γ / γ) :=
        mul_le_mul_of_nonneg_right hS_le hrhs_pos.le
    _ = C_lin * Real.log γ / γ := by dsimp [C_lin]; ring

/-- Specialization of `exists_polynomialReading_sub_heckeDefect_le_log_div` to `n = linearThetaStage γ`. -/
theorem exists_linearThetaStage_polynomialReading_sub_heckeDefect_le :
    ∃ C_lin : ℝ, 0 < C_lin ∧ ∀ γ L : ℝ,
      2 ≤ γ → 0 ≤ L → L ≤ 2 * Real.log γ →
      |polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 (linearThetaStage γ) -
          heckeDefect (baseTwistTest γ) L| ≤
        C_lin * Real.log γ / γ := by
  obtain ⟨C_lin, hC, hbd⟩ := exists_polynomialReading_sub_heckeDefect_le_log_div
  refine ⟨C_lin, hC, fun γ L hγ2 hL0 hL => hbd γ L (linearThetaStage γ) hγ2 hL0 hL le_rfl ?_⟩
  obtain ⟨_, hhi⟩ := linearThetaStage_bounds (by linarith : 1 ≤ γ)
  linarith

/-! ## §2. Six-way zero-coordinate-free finite-theta `TFAE` for `RiemannHypothesis` -/

/-- Pole-nodal restricted dyadic sufficiency: bounding `heckeDefect` on the pole-nodal locus
`((tr (twist γ F_{L_k T}) 1) ^ 2).re = 0` inside `[T, T + 1]` suffices for `RiemannHypothesis`. -/
theorem riemannHypothesis_of_poleNodal_dyadic_heckeDefect_le_primePolynomial {c₀ α : ℝ}
    (hc₀ : 0 < c₀) (hα : 0 ≤ α)
    (hhyp : ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
      ((tr (twist γ (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))) 1) ^ 2).re = 0 →
      heckeDefect (baseTwistTest γ) ((2 : ℝ) ^ k * c₀ * Real.log T) ≤
        α * ‖primePolynomial (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))
          ⌊Real.exp (2 * ((2 : ℝ) ^ k * c₀ * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖ + C) :
    RiemannHypothesis := by
  obtain ⟨C, hdyad⟩ := hhyp
  rw [CrossRouteReceiverBridges.riemannHypothesis_iff_zetaZeroConfig_onLine]
  by_contra hnot_on
  have hex_raw : ∃ ρ_raw ∈ zetaZeroConfig.carrier, ρ_raw.re ≠ 1 / 2 := by
    by_contra hall
    exact hnot_on fun ρ hρ => by_contra fun hne => hall ⟨ρ, hρ, hne⟩
  obtain ⟨ρ_raw, hρ_raw, hre_raw⟩ := hex_raw
  have hex_pos : ∃ ρ₀ ∈ zetaZeroConfig.carrier, ρ₀.re ≠ 1 / 2 ∧ 3 < ρ₀.im := by
    have habs := three_lt_abs_im_of_mem_zetaZeroConfig hρ_raw
    rcases le_or_gt 0 ρ_raw.im with him0 | him_neg
    · rw [abs_of_nonneg him0] at habs
      exact ⟨ρ_raw, hρ_raw, hre_raw, habs⟩
    · rw [abs_of_neg him_neg] at habs
      refine ⟨conj ρ_raw, conj_mem_zetaZeroConfig hρ_raw, ?_, ?_⟩
      · simpa only [Complex.conj_re] using hre_raw
      · simp only [Complex.conj_im]; linarith
  obtain ⟨ρ₀, hρ₀_mem, hρ₀_re, hρ₀_im3⟩ := hex_pos
  set δ₀ : ℝ := |ρ₀.re - 1 / 2|
  have hδ₀_pos : 0 < δ₀ := abs_pos.mpr (sub_ne_zero.mpr hρ₀_re)
  set T₀ : ℝ := ρ₀.im - 1 / 2
  have hT₀_ge2 : 2 ≤ T₀ := by dsimp [T₀]; linarith
  have hlogT₀_pos : 0 < Real.log T₀ := Real.log_pos (by linarith)
  obtain ⟨hxi₀, h0₀, h1₀⟩ :=
    CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ₀_mem
  have hρ₀_W : ρ₀ ∈ xiUnitWindowZeros T₀ := by
    rw [mem_xiUnitWindowZeros]
    exact ⟨(Set.Finite.mem_toFinset _).mpr
      ⟨⟨h0₀, h1₀, by linarith, by dsimp [T₀]; linarith⟩, hxi₀⟩, by dsimp [T₀]; linarith⟩
  have hord₀_ge1 : (1 : ℝ) ≤ ((analyticOrderAt xi ρ₀).toNat : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hxi₀)
  obtain ⟨a₀, b₀, η₀, hT₀_a₀, ha₀_b₀, hb₀_T₀1, hη₀_pos, hsep_all⟩ :=
    exists_zero_avoiding_subinterval_in_unitWindow T₀
  obtain ⟨L_min, hLmin1, hpole_nodal⟩ :=
    exists_poleNodal_ordinate_in_Icc (by linarith : 0 < a₀) ha₀_b₀
  obtain ⟨C_mu, hCmu, hmu_bd⟩ := exists_abs_re_archPart_sub_pole_heckeAvgBump_le
  obtain ⟨C_lor, hClor, hlor⟩ := exists_zetaZeroConfig_lorentz_le
  set C_arch_nodal : ℝ := C_mu + Real.log (3 + T₀)
  set C_lor_T₀ : ℝ := (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) * (C_lor * (1 + Real.log (T₀ + 5)))
  have hCarn_pos : 0 < C_arch_nodal := by
    have : 0 ≤ Real.log (3 + T₀) := Real.log_nonneg (by linarith)
    dsimp [C_arch_nodal]; linarith
  have hClorT_pos : 0 < C_lor_T₀ := by
    have : 0 ≤ Real.log (T₀ + 5) := Real.log_nonneg (by linarith)
    dsimp [C_lor_T₀]; positivity
  have htend_L : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * c₀ * Real.log T₀) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * (c₀ * Real.log T₀)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const
        (mul_pos hc₀ hlogT₀_pos)
    exact h1.congr fun k => (mul_assoc _ _ _).symm
  set M_rhs : ℝ := α * (C_arch_nodal + C_lor_T₀) + |C| + 1
  have hM_nn : 0 ≤ M_rhs := by
    dsimp [M_rhs]; nlinarith [hCarn_pos, hClorT_pos, abs_nonneg C]
  have hcos_pos := cos_quarter_sq_pos
  set L_target : ℝ := max L_min
    (max (Real.sqrt (α / (2 * η₀ ^ 2)) + 1)
      (Real.sqrt (M_rhs / (2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2)) + 1))
  obtain ⟨k, hk⟩ := (htend_L.eventually_ge_atTop L_target).exists
  set L_k : ℝ := (2 : ℝ) ^ k * c₀ * Real.log T₀
  have hLk_ge_target : L_target ≤ L_k := hk
  have hLk_ge_min : L_min ≤ L_k := (le_max_left _ _).trans hLk_ge_target
  have hLk_ge1 : 1 ≤ L_k := hLmin1.trans hLk_ge_min
  have hLk_pos : 0 < L_k := lt_of_lt_of_le one_pos hLk_ge1
  obtain ⟨γ_k, hγk_ab, hpole0⟩ := hpole_nodal L_k hLk_ge_min
  have hγk_Icc : γ_k ∈ Icc T₀ (T₀ + 1) := ⟨hT₀_a₀.trans hγk_ab.1, hγk_ab.2.trans hb₀_T₀1⟩
  have harch_k : |(archPart (heckeAvgBump L_k) (-γ_k / (2 * Real.pi))).re| ≤ C_arch_nodal := by
    have hsub := hmu_bd L_k γ_k hLk_ge1
    rw [hpole0, mul_zero, sub_zero] at hsub
    have habs_γk : |γ_k| = γ_k := abs_of_pos (by linarith [hγk_Icc.1])
    have hlog_le : Real.log (2 + |γ_k|) / (2 * L_k) ≤ Real.log (3 + T₀) := by
      rw [habs_γk]
      have h1 : Real.log (2 + γ_k) ≤ Real.log (3 + T₀) :=
        Real.log_le_log (by linarith [hγk_Icc.1]) (by linarith [hγk_Icc.2])
      exact (div_le_self (Real.log_nonneg (by linarith [hγk_Icc.1])) (by linarith)).trans h1
    dsimp [C_arch_nodal]; linarith
  have hcoll_k : collidedForm zetaZeroConfig (twist γ_k (heckeAvgBump L_k)) ≤
      C_lor_T₀ + (1 / (4 * η₀ ^ 2 * L_k ^ 2)) * heckeDefect (baseTwistTest γ_k) L_k := by
    have hs_coll := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L_k) γ_k)
      (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hLk_pos) γ_k)
    have hlor_sum := (hlor γ_k).1
    have hdef_sum := summable_heckeDefect (baseTwistTest γ_k) L_k
    set c₁ : ℝ := (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) / L_k ^ 2
    set c₂ : ℝ := 1 / (4 * η₀ ^ 2 * L_k ^ 2)
    have hptw : ∀ ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_k (heckeAvgBump L_k)) ρ) ≤
          c₁ * ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ_k - (ρ : ℂ).im) ^ 2))) +
            c₂ * (zetaWeight (baseTwistTest γ_k) ρ * depthKernel L_k (zetaDepth ρ)) := by
      intro ρ
      have hsep := hsep_all (ρ : ℂ) ρ.2 γ_k hγk_ab
      have hbd := normSq_tr_twist_heckeAvgBump_le_of_sep hLk_pos hη₀_pos γ_k ρ hsep
      have hm0 : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
      have hw_eq : zetaWeight (baseTwistTest γ_k) ρ =
          (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_k baseBump) ρ) := rfl
      rw [hw_eq, show c₁ = (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) / L_k ^ 2 from rfl,
        show c₂ = 1 / (4 * η₀ ^ 2 * L_k ^ 2) from rfl]
      calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_k (heckeAvgBump L_k)) ρ)
          ≤ (zetaZeroConfig.mult ρ : ℝ) *
              ((1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) / L_k ^ 2 * (1 / (1 + (γ_k - (ρ : ℂ).im) ^ 2)) +
                1 / (4 * η₀ ^ 2 * L_k ^ 2) *
                  (Complex.normSq (tr (twist γ_k baseBump) ρ) * depthKernel L_k (zetaDepth ρ))) :=
            mul_le_mul_of_nonneg_left hbd hm0
        _ = _ := by ring
    have htsum := hs_coll.tsum_le_tsum hptw ((hlor_sum.mul_left c₁).add (hdef_sum.mul_left c₂))
    rw [(hlor_sum.mul_left c₁).tsum_add (hdef_sum.mul_left c₂), tsum_mul_left, tsum_mul_left]
      at htsum
    have hlor_le : c₁ * (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ_k - (ρ : ℂ).im) ^ 2))) ≤ C_lor_T₀ := by
      have h1 : c₁ ≤ (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) := by
        dsimp [c₁]
        exact div_le_self (by positivity) (by nlinarith : 1 ≤ L_k ^ 2)
      have habs_γk : |γ_k| = γ_k := abs_of_pos (by linarith [hγk_Icc.1])
      have h2 : (∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ_k - (ρ : ℂ).im) ^ 2))) ≤
          C_lor * (1 + Real.log (T₀ + 5)) := by
        refine (hlor γ_k).2.trans (mul_le_mul_of_nonneg_left ?_ hClor.le)
        have : Real.log (|γ_k| + 4) ≤ Real.log (T₀ + 5) := by
          rw [habs_γk]
          exact Real.log_le_log (by linarith [hγk_Icc.1]) (by linarith [hγk_Icc.2])
        linarith
      dsimp [C_lor_T₀]
      exact mul_le_mul h1 h2
        (tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))
        (by positivity)
    have hcoll_def : (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_k (heckeAvgBump L_k)) ρ)) =
        collidedForm zetaZeroConfig (twist γ_k (heckeAvgBump L_k)) := rfl
    have hdef_eq : (∑' ρ : zetaZeroConfig.carrier,
        zetaWeight (baseTwistTest γ_k) ρ * depthKernel L_k (zetaDepth ρ)) =
        heckeDefect (baseTwistTest γ_k) L_k := rfl
    rw [hcoll_def, hdef_eq, show c₂ = 1 / (4 * η₀ ^ 2 * L_k ^ 2) from rfl] at htsum
    linarith [htsum, hlor_le]
  have hhyp_k := hdyad k T₀ hT₀_ge2 γ_k hγk_Icc hpole0
  have hpp_k := norm_primePolynomial_heckeAvgBump_le hLk_pos γ_k
  have hLk_abs : α / (4 * η₀ ^ 2 * L_k ^ 2) ≤ 1 / 2 := by
    have hge_sq : Real.sqrt (α / (2 * η₀ ^ 2)) < L_k := by
      have := (le_max_left _ _).trans ((le_max_right _ _).trans hLk_ge_target)
      linarith
    have hsq : α / (2 * η₀ ^ 2) ≤ L_k ^ 2 := by
      have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hge_sq.le 2
      rwa [Real.sq_sqrt (by positivity)] at h1
    rw [div_le_div_iff₀ (by positivity) zero_lt_two]
    have := (div_le_iff₀ (by positivity : 0 < 2 * η₀ ^ 2)).mp hsq
    linarith
  set E_k := heckeDefect (baseTwistTest γ_k) L_k
  have hEk_nn : 0 ≤ E_k := heckeDefect_nonneg _ _
  have hEk_upper : (1 / 2) * E_k ≤ α * (C_arch_nodal + C_lor_T₀) + |C| := by
    have hpp_tot : ‖primePolynomial (heckeAvgBump L_k)
        ⌊Real.exp (2 * (L_k + 1 / 4))⌋₊ (-γ_k / (2 * Real.pi))‖ ≤
        C_arch_nodal + C_lor_T₀ + (1 / (4 * η₀ ^ 2 * L_k ^ 2)) * E_k := by
      linarith [hpp_k, harch_k, hcoll_k]
    have h1 : E_k ≤ α * (C_arch_nodal + C_lor_T₀ + (1 / (4 * η₀ ^ 2 * L_k ^ 2)) * E_k) + |C| :=
      hhyp_k.trans (add_le_add (mul_le_mul_of_nonneg_left hpp_tot hα) (le_abs_self C))
    have h2 : α * ((1 / (4 * η₀ ^ 2 * L_k ^ 2)) * E_k) ≤ (1 / 2) * E_k := by
      rw [← mul_assoc, mul_one_div]
      exact mul_le_mul_of_nonneg_right hLk_abs hEk_nn
    linarith
  have hEk_lower : 2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2 * L_k ^ 2 ≤ (1 / 2) * E_k := by
    have hunit := unitWindow_depthCharge_le_heckeDefect T₀ L_k hγk_Icc.1 hγk_Icc.2
    have hsingle : ((analyticOrderAt xi ρ₀).toNat : ℝ) * depthKernel L_k (ρ₀.re - 1 / 2) ≤
        ∑ ρ ∈ xiUnitWindowZeros T₀,
          ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L_k (ρ.re - 1 / 2) :=
      Finset.single_le_sum
        (f := fun ρ => ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L_k (ρ.re - 1 / 2))
        (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)) hρ₀_W
    have hquad : 4 * L_k ^ 2 * δ₀ ^ 2 ≤ depthKernel L_k (ρ₀.re - 1 / 2) := by
      have h1 := quadratic_le_depthKernel L_k (ρ₀.re - 1 / 2)
      have h2 : δ₀ ^ 2 = (ρ₀.re - 1 / 2) ^ 2 := sq_abs _
      rwa [← h2] at h1
    have hdk_le_ord : depthKernel L_k (ρ₀.re - 1 / 2) ≤
        ((analyticOrderAt xi ρ₀).toNat : ℝ) * depthKernel L_k (ρ₀.re - 1 / 2) :=
      le_mul_of_one_le_left (depthKernel_nonneg _ _) hord₀_ge1
    have hchain : Real.cos (1 / 4 : ℝ) ^ 2 * (4 * L_k ^ 2 * δ₀ ^ 2) ≤ E_k := by
      calc Real.cos (1 / 4 : ℝ) ^ 2 * (4 * L_k ^ 2 * δ₀ ^ 2)
          ≤ Real.cos (1 / 4 : ℝ) ^ 2 *
              ∑ ρ ∈ xiUnitWindowZeros T₀,
                ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L_k (ρ.re - 1 / 2) :=
            mul_le_mul_of_nonneg_left (hquad.trans (hdk_le_ord.trans hsingle)) hcos_pos.le
        _ ≤ E_k := hunit
    linarith
  have hLk_grow : M_rhs < 2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2 * L_k ^ 2 := by
    have hgt_sq : Real.sqrt (M_rhs / (2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2)) < L_k := by
      have := (le_max_right _ _).trans ((le_max_right _ _).trans hLk_ge_target)
      linarith
    have hsq : M_rhs / (2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2) < L_k ^ 2 := by
      have h1 := pow_lt_pow_left₀ hgt_sq (Real.sqrt_nonneg _) (by norm_num : 2 ≠ 0)
      rwa [Real.sq_sqrt (div_nonneg hM_nn (by positivity))] at h1
    have hmul := (div_lt_iff₀ (by positivity : 0 < 2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2)).mp hsq
    linarith
  dsimp [M_rhs] at hLk_grow
  linarith

/-- Existential unit-window boundedness of `heckeDefect` across dyadic scales `2^k c₀ log T`
forces `RiemannHypothesis`, without any `primePolynomial` term. -/
theorem riemannHypothesis_of_exists_unitWindow_dyadic_heckeDefect_le {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hhyp : ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T → ∃ γ ∈ Icc T (T + 1),
      heckeDefect (baseTwistTest γ) ((2 : ℝ) ^ k * c₀ * Real.log T) ≤ C) :
    RiemannHypothesis := by
  obtain ⟨C, hex⟩ := hhyp
  rw [CrossRouteReceiverBridges.riemannHypothesis_iff_zetaZeroConfig_onLine]
  by_contra hnot_on
  have hex_raw : ∃ ρ_raw ∈ zetaZeroConfig.carrier, ρ_raw.re ≠ 1 / 2 := by
    by_contra hall
    exact hnot_on fun ρ hρ => by_contra fun hne => hall ⟨ρ, hρ, hne⟩
  obtain ⟨ρ_raw, hρ_raw, hre_raw⟩ := hex_raw
  have hex_pos : ∃ ρ₀ ∈ zetaZeroConfig.carrier, ρ₀.re ≠ 1 / 2 ∧ 3 < ρ₀.im := by
    have habs := three_lt_abs_im_of_mem_zetaZeroConfig hρ_raw
    rcases le_or_gt 0 ρ_raw.im with him0 | him_neg
    · rw [abs_of_nonneg him0] at habs
      exact ⟨ρ_raw, hρ_raw, hre_raw, habs⟩
    · rw [abs_of_neg him_neg] at habs
      refine ⟨conj ρ_raw, conj_mem_zetaZeroConfig hρ_raw, ?_, ?_⟩
      · simpa only [Complex.conj_re] using hre_raw
      · simp only [Complex.conj_im]; linarith
  obtain ⟨ρ₀, hρ₀_mem, hρ₀_re, hρ₀_im3⟩ := hex_pos
  set δ₀ : ℝ := |ρ₀.re - 1 / 2|
  have hδ₀_pos : 0 < δ₀ := abs_pos.mpr (sub_ne_zero.mpr hρ₀_re)
  set T₀ : ℝ := ρ₀.im - 1 / 2
  have hT₀_ge2 : 2 ≤ T₀ := by dsimp [T₀]; linarith
  have hlogT₀_pos : 0 < Real.log T₀ := Real.log_pos (by linarith)
  obtain ⟨hxi₀, h0₀, h1₀⟩ :=
    CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ₀_mem
  have hρ₀_W : ρ₀ ∈ xiUnitWindowZeros T₀ := by
    rw [mem_xiUnitWindowZeros]
    exact ⟨(Set.Finite.mem_toFinset _).mpr
      ⟨⟨h0₀, h1₀, by linarith, by dsimp [T₀]; linarith⟩, hxi₀⟩, by dsimp [T₀]; linarith⟩
  have hord₀_ge1 : (1 : ℝ) ≤ ((analyticOrderAt xi ρ₀).toNat : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hxi₀)
  have hcos_pos := cos_quarter_sq_pos
  have htend_L : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * c₀ * Real.log T₀) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * (c₀ * Real.log T₀)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const
        (mul_pos hc₀ hlogT₀_pos)
    exact h1.congr fun k => (mul_assoc _ _ _).symm
  set L_target : ℝ :=
    Real.sqrt ((|C| + 1) / (4 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2)) + 1
  obtain ⟨k, hk⟩ := (htend_L.eventually_ge_atTop L_target).exists
  set L_k : ℝ := (2 : ℝ) ^ k * c₀ * Real.log T₀
  obtain ⟨γ_k, hγk_Icc, hEk_le⟩ := hex k T₀ hT₀_ge2
  have hunit := unitWindow_depthCharge_le_heckeDefect T₀ L_k hγk_Icc.1 hγk_Icc.2
  have hsingle : ((analyticOrderAt xi ρ₀).toNat : ℝ) * depthKernel L_k (ρ₀.re - 1 / 2) ≤
      ∑ ρ ∈ xiUnitWindowZeros T₀,
        ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L_k (ρ.re - 1 / 2) :=
    Finset.single_le_sum
      (f := fun ρ => ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L_k (ρ.re - 1 / 2))
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)) hρ₀_W
  have hquad : 4 * L_k ^ 2 * δ₀ ^ 2 ≤ depthKernel L_k (ρ₀.re - 1 / 2) := by
    have h1 := quadratic_le_depthKernel L_k (ρ₀.re - 1 / 2)
    have h2 : δ₀ ^ 2 = (ρ₀.re - 1 / 2) ^ 2 := sq_abs _
    rwa [← h2] at h1
  have hdk_le_ord : depthKernel L_k (ρ₀.re - 1 / 2) ≤
      ((analyticOrderAt xi ρ₀).toNat : ℝ) * depthKernel L_k (ρ₀.re - 1 / 2) :=
    le_mul_of_one_le_left (depthKernel_nonneg _ _) hord₀_ge1
  have hEk_lower : 4 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2 * L_k ^ 2 ≤
      heckeDefect (baseTwistTest γ_k) L_k := by
    calc 4 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2 * L_k ^ 2
        = Real.cos (1 / 4 : ℝ) ^ 2 * (4 * L_k ^ 2 * δ₀ ^ 2) := by ring
      _ ≤ Real.cos (1 / 4 : ℝ) ^ 2 *
            ∑ ρ ∈ xiUnitWindowZeros T₀,
              ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L_k (ρ.re - 1 / 2) :=
          mul_le_mul_of_nonneg_left (hquad.trans (hdk_le_ord.trans hsingle)) hcos_pos.le
      _ ≤ heckeDefect (baseTwistTest γ_k) L_k := hunit
  have hgt_sq : Real.sqrt ((|C| + 1) / (4 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2)) < L_k := by
    dsimp [L_target] at hk; linarith
  have hsq : (|C| + 1) / (4 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2) < L_k ^ 2 := by
    have h1 := pow_lt_pow_left₀ hgt_sq (Real.sqrt_nonneg _) (by norm_num : 2 ≠ 0)
    rwa [Real.sq_sqrt (div_nonneg (by positivity) (by positivity))] at h1
  have hmul := (div_lt_iff₀ (by positivity : 0 < 4 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2)).mp hsq
  linarith [le_abs_self C]

/-- **Six-Way Zero-Coordinate-Free Finite-Theta Pole-Nodal Equivalence for `RiemannHypothesis`
(`riemannHypothesis_finiteTheta_poleNodal_dyadic_tfae`).**
For every `c₀ > 0` and `α ≥ 0`, with `L_k(T) = 2^k c₀ log T`, `RiemannHypothesis` is
unconditionally equivalent to five purely source-side finite-theta criteria containing zero
spectral zero coordinates. -/
theorem riemannHypothesis_finiteTheta_poleNodal_dyadic_tfae {c₀ α : ℝ}
    (hc₀ : 0 < c₀) (hα : 0 ≤ α) :
    List.TFAE
      [ RiemannHypothesis,
        ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
          ((tr (twist γ (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))) 1) ^ 2).re = 0 →
          finiteThetaSourceMomentReading (baseTwistTest γ) ((2 : ℝ) ^ k * c₀ * Real.log T) 1
            (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T) ≤
            α * ‖primePolynomial (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))
              ⌊Real.exp (2 * ((2 : ℝ) ^ k * c₀ * Real.log T + 1 / 4))⌋₊
              (-γ / (2 * Real.pi))‖ + C,
        ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
          ((tr (twist γ (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))) 1) ^ 2).re = 0 →
          polynomialThetaSourceMomentReading (baseTwistTest γ) ((2 : ℝ) ^ k * c₀ * Real.log T) 1
            (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T) ≤
            α * ‖primePolynomial (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))
              ⌊Real.exp (2 * ((2 : ℝ) ^ k * c₀ * Real.log T + 1 / 4))⌋₊
              (-γ / (2 * Real.pi))‖ + C,
        ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T → ∀ γ ∈ Icc T (T + 1), ∀ n : ℕ, 1 ≤ n →
          |γ| ≤ (n : ℝ) / 2 →
          1 / 4 + |(2 : ℝ) ^ k * c₀ * Real.log T| ≤ 2 * Real.log ((n : ℝ) + 1) →
          finiteThetaSourceMomentReading (baseTwistTest γ) ((2 : ℝ) ^ k * c₀ * Real.log T) 1 n ≤
            α * ‖primePolynomial (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))
              ⌊Real.exp (2 * ((2 : ℝ) ^ k * c₀ * Real.log T + 1 / 4))⌋₊
              (-γ / (2 * Real.pi))‖ + C,
        ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T → ∃ γ ∈ Icc T (T + 1),
          finiteThetaSourceMomentReading (baseTwistTest γ) ((2 : ℝ) ^ k * c₀ * Real.log T) 1
            (apertureStage ((2 : ℝ) ^ k * c₀ * Real.log T) T) ≤ C,
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ L γ : ℝ,
          |γ| ≤ (n : ℝ) / 2 → 1 / 4 + |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
          polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n < ε ] := by
  obtain ⟨E_unif, hE_nn, hE_bd⟩ := exists_uniform_aperture_heckeDefect_error_bounds
  -- (1) → (4): RH ⇒ stage-uniform full-aperture `finiteThetaSourceMomentReading` bound
  tfae_have 1 → 4 := by
    intro hRH
    refine ⟨E_unif, fun k T _ γ _ n hn hγ hwin => ?_⟩
    have herr := (hE_bd n hn ((2 : ℝ) ^ k * c₀ * Real.log T) γ hγ hwin).1
    rw [heckeDefect_eq_zero_of_riemannHypothesis hRH, sub_zero] at herr
    have h1 := le_of_abs_le herr
    have hnn : 0 ≤ α * ‖primePolynomial (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))
        ⌊Real.exp (2 * ((2 : ℝ) ^ k * c₀ * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖ :=
      mul_nonneg hα (norm_nonneg _)
    linarith
  -- (4) → (2): specialize `n = apertureStage (L_k T) T` on the pole-nodal locus
  tfae_have 4 → 2 := by
    rintro ⟨C, h4⟩
    refine ⟨C, fun k T hT γ hγ _ => ?_⟩
    set L := (2 : ℝ) ^ k * c₀ * Real.log T
    obtain ⟨hγ_adm, hL_adm⟩ := apertureStage_admissible L T hγ
    rw [one_mul] at hL_adm
    exact h4 k T hT γ hγ (apertureStage L T) (one_le_apertureStage L T) hγ_adm hL_adm
  -- (2) → (3): transfer between `finiteThetaSourceMomentReading` and `polynomialThetaSourceMomentReading`
  tfae_have 2 → 3 := by
    rintro ⟨C, h2⟩
    refine ⟨C + 2 * E_unif, fun k T hT γ hγ hpole => ?_⟩
    set L := (2 : ℝ) ^ k * c₀ * Real.log T
    set n := apertureStage L T
    obtain ⟨hγ_adm, hL_adm⟩ := apertureStage_admissible L T hγ
    rw [one_mul] at hL_adm
    obtain ⟨herr_fin, herr_poly⟩ := hE_bd n (one_le_apertureStage L T) L γ hγ_adm hL_adm
    have hfin_ge : heckeDefect (baseTwistTest γ) L - E_unif ≤
        finiteThetaSourceMomentReading (baseTwistTest γ) L 1 n := by
      linarith [(abs_le.mp herr_fin).1]
    have hpoly_le : polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n ≤
        heckeDefect (baseTwistTest γ) L + E_unif := by
      linarith [(abs_le.mp herr_poly).2]
    linarith [h2 k T hT γ hγ hpole]
  -- (3) → (1): pole-nodal `polynomialThetaSourceMomentReading` criterion ⇒ `RiemannHypothesis`
  tfae_have 3 → 1 := by
    rintro ⟨C, h3⟩
    refine riemannHypothesis_of_poleNodal_dyadic_heckeDefect_le_primePolynomial hc₀ hα
      ⟨C + E_unif, fun k T hT γ hγ hpole => ?_⟩
    set L := (2 : ℝ) ^ k * c₀ * Real.log T
    set n := apertureStage L T
    obtain ⟨hγ_adm, hL_adm⟩ := apertureStage_admissible L T hγ
    rw [one_mul] at hL_adm
    have herr_poly := (hE_bd n (one_le_apertureStage L T) L γ hγ_adm hL_adm).2
    have hdef_le : heckeDefect (baseTwistTest γ) L ≤
        polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n + E_unif := by
      linarith [(abs_le.mp herr_poly).1]
    linarith [h3 k T hT γ hγ hpole]
  -- (1) → (5): RH ⇒ pure finite-theta existential unit-window criterion (witness `γ = T`)
  tfae_have 1 → 5 := by
    intro hRH
    refine ⟨E_unif, fun k T _ => ⟨T, ⟨le_rfl, by linarith⟩, ?_⟩⟩
    set L := (2 : ℝ) ^ k * c₀ * Real.log T
    obtain ⟨hγ_adm, hL_adm⟩ := apertureStage_admissible L T (γ := T) ⟨le_rfl, by linarith⟩
    rw [one_mul] at hL_adm
    have herr := (hE_bd (apertureStage L T) (one_le_apertureStage L T) L T hγ_adm hL_adm).1
    rw [heckeDefect_eq_zero_of_riemannHypothesis hRH, sub_zero] at herr
    exact le_of_abs_le herr
  -- (5) → (1): pure finite-theta existential unit-window criterion ⇒ `RiemannHypothesis`
  tfae_have 5 → 1 := by
    rintro ⟨C, h5⟩
    refine riemannHypothesis_of_exists_unitWindow_dyadic_heckeDefect_le hc₀
      ⟨C + E_unif, fun k T hT => ?_⟩
    obtain ⟨γ, hγ, hfin⟩ := h5 k T hT
    set L := (2 : ℝ) ^ k * c₀ * Real.log T
    obtain ⟨hγ_adm, hL_adm⟩ := apertureStage_admissible L T hγ
    rw [one_mul] at hL_adm
    have herr := (hE_bd (apertureStage L T) (one_le_apertureStage L T) L γ hγ_adm hL_adm).1
    exact ⟨γ, hγ, by linarith [(abs_le.mp herr).1]⟩
  -- (1) → (6): RH ⇒ uniform growing-aperture `< ε` vanishing of `polynomialThetaSourceMomentReading`
  tfae_have 1 → 6 := by
    intro hRH ε hε
    obtain ⟨B, hB, hb⟩ := exists_polynomialThetaSource_aperture_error_bound
    have ht : Tendsto (fun n : ℕ =>
        4 * sourceTestSize baseBumpTest ^ 2 *
          (B / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ =>
          B / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n) atTop (𝓝 0) := by
        simpa only [mul_zero, add_zero] using
          (tendsto_polynomialSourceWindowError B).add (tendsto_sourceReferenceTail.const_mul 40)
      simpa only [mul_zero] using h0.const_mul (4 * sourceTestSize baseBumpTest ^ 2)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht ε hε
    refine ⟨max 1 N, fun n hn L γ hγ hwin => ?_⟩
    have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
    have hnN : N ≤ n := (le_max_right _ _).trans hn
    have hwin' : (1 / 4 : ℝ) + ((1 : ℕ) : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) := by
      simpa only [Nat.cast_one, one_mul] using hwin
    have hbd := hb n hn1 baseBumpTest (1 / 4) (by norm_num)
      abs_le_quarter_of_baseBumpTest_ne_zero 1 L γ hγ hwin'
    have hsum_eq : (∑' ρ : zetaZeroConfig.carrier,
        zetaWeight (baseTwistTest γ) ρ * depthKernel L (zetaDepth ρ) ^ 1) =
        heckeDefect (baseTwistTest γ) L := by
      simp only [pow_one, heckeDefect]
    rw [sourceTwist_baseBumpTest_eq, hsum_eq, heckeDefect_eq_zero_of_riemannHypothesis hRH,
      sub_zero, pow_one, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)] at hbd
    have hnonneg : 0 ≤ 4 * sourceTestSize baseBumpTest ^ 2 *
        (B / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n) :=
      mul_nonneg (by positivity)
        (add_nonneg (div_nonneg hB (sq_nonneg _))
          (mul_nonneg (by norm_num) (sourceReferenceTail_nonneg n)))
    have hsmall := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hsmall
    have hle : polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n ≤
        4 * sourceTestSize baseBumpTest ^ 2 *
          (B / ((n : ℝ) + 1) ^ 2 + 40 * sourceReferenceTail n) := by
      linarith [le_abs_self (polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n)]
    exact hle.trans_lt hsmall
  -- (6) → (5): specialize `ε = 1` and transfer `polynomial` → `heckeDefect` → `finiteTheta`
  tfae_have 6 → 5 := by
    intro h6
    obtain ⟨N, hN⟩ := h6 1 zero_lt_one
    refine ⟨1 + 2 * E_unif, fun k T _ => ⟨T, ⟨le_rfl, by linarith⟩, ?_⟩⟩
    set L := (2 : ℝ) ^ k * c₀ * Real.log T
    set n₀ := apertureStage L T
    set n₁ := max N n₀
    obtain ⟨hγ0, hL0⟩ := apertureStage_admissible L T (γ := T) ⟨le_rfl, by linarith⟩
    rw [one_mul] at hL0
    have hn₀_le_n₁ : (n₀ : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast le_max_right N n₀
    have hn₁_1 : 1 ≤ n₁ := (one_le_apertureStage L T).trans (le_max_right N n₀)
    have hγ1 : |T| ≤ (n₁ : ℝ) / 2 := hγ0.trans (by linarith)
    have hL1 : 1 / 4 + |L| ≤ 2 * Real.log ((n₁ : ℝ) + 1) :=
      hL0.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) (by linarith)) zero_le_two)
    have hpoly_lt := hN n₁ (le_max_left N n₀) L T hγ1 hL1
    have herr_n₁ := (hE_bd n₁ hn₁_1 L T hγ1 hL1).2
    have herr_n₀ := (hE_bd n₀ (one_le_apertureStage L T) L T hγ0 hL0).1
    linarith [(abs_le.mp herr_n₁).1, (abs_le.mp herr_n₀).2]
  tfae_finish

/-! ## §3. Anti-nodal exponential pole growth and sharpness of the pole-nodal locus -/

/-- Analytic continuation nonvanishing: on every nondegenerate interval `[a₀, b₀)` (`a₀ < b₀`),
there exists `γ₁ ∈ Ico a₀ b₀` with `tr (twist γ₁ baseBump) 1 ≠ 0`. -/
theorem exists_tr_twist_baseBump_one_ne_zero_in_Ico {a₀ b₀ : ℝ} (hab : a₀ < b₀) :
    ∃ γ₁ ∈ Ico a₀ b₀, tr (twist γ₁ baseBump) 1 ≠ 0 := by
  by_contra hall
  push Not at hall
  let g : ℂ → ℂ := fun z => tr baseBump (1 - (a₀ : ℂ) * I - z * I)
  have htr_diff : Differentiable ℂ (tr baseBump) :=
    (RHTower.EvenSector.differentiable_paperFT_of_compact
      (contDiff_baseBump (n := ⊤)).continuous hasCompactSupport_baseBump).comp
      (by unfold gammaOf; fun_prop)
  have hg_diff : Differentiable ℂ g :=
    htr_diff.comp (by fun_prop)
  have hg_ana : AnalyticOnNhd ℂ g Set.univ := hg_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hseq_tend : Tendsto (fun n : ℕ => (((b₀ - a₀) / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1_shift : Tendsto ((fun k : ℕ => 1 / ((k : ℝ) + 1)) ∘ fun n : ℕ => n + 1) atTop (𝓝 (0 : ℝ)) :=
      h1.comp (tendsto_add_atTop_nat 1)
    have h2 := h1_shift.const_mul (b₀ - a₀)
    rw [mul_zero] at h2
    have h3 : Tendsto (fun n : ℕ => (b₀ - a₀) / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) :=
      h2.congr fun n => by dsimp only [Function.comp_def]; push_cast; ring
    have h4 : Tendsto (Complex.ofReal ∘ fun n : ℕ => (b₀ - a₀) / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℂ)) := by
      simpa only [Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp h3
    exact h4.congr fun _ => rfl
  have hpunc : Tendsto (fun n : ℕ => (((b₀ - a₀) / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop
      (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq_tend ?_
    filter_upwards with n
    rw [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
    have : 0 < b₀ - a₀ := sub_pos.mpr hab
    positivity
  have hg_seq_zero : ∀ n : ℕ, g (((b₀ - a₀) / ((n : ℝ) + 2) : ℝ) : ℂ) = 0 := by
    intro n
    set t : ℝ := (b₀ - a₀) / ((n : ℝ) + 2)
    have ht_pos : 0 < t := div_pos (sub_pos.mpr hab) (by positivity)
    have ht_lt : t < b₀ - a₀ := div_lt_self (sub_pos.mpr hab)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ) < (n : ℝ) + 2)
    have hmem : a₀ + t ∈ Ico a₀ b₀ := ⟨by linarith, by linarith⟩
    have hzero := hall (a₀ + t) hmem
    rw [tr_twist] at hzero
    have harg : (1 : ℂ) - ((a₀ + t : ℝ) : ℂ) * I = 1 - (a₀ : ℂ) * I - (t : ℂ) * I := by
      push_cast; ring
    rw [harg] at hzero
    exact hzero
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), g w = 0 :=
    hpunc.frequently (Frequently.of_forall hg_seq_zero)
  have hall_zero := hg_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (mem_univ (0 : ℂ)) hfreq
  have hz₀_zero : g (-(a₀ : ℂ) - I / 2) = 0 := hall_zero (mem_univ _)
  have hz₀_one : g (-(a₀ : ℂ) - I / 2) = 1 := by
    dsimp [g]
    have harg : (1 : ℂ) - (a₀ : ℂ) * I - (-(a₀ : ℂ) - I / 2) * I = 1 / 2 := by
      have hI2 : I * I = -1 := Complex.I_mul_I
      calc (1 : ℂ) - (a₀ : ℂ) * I - (-(a₀ : ℂ) - I / 2) * I
          = 1 + (I * I) / 2 := by ring
        _ = 1 / 2 := by rw [hI2]; norm_num
    rw [harg, tr_eq]
    have hint : (∫ u : ℝ, baseBump u * Complex.exp (((1 / 2 : ℂ) - 1 / 2) * (u : ℂ))) =
        ((∫ u : ℝ, baseBumpReal u : ℝ) : ℂ) := by
      simp only [sub_self, zero_mul, Complex.exp_zero, mul_one, baseBump]
      exact integral_ofReal
    rw [hint, integral_baseBumpReal, Complex.ofReal_one]
  exact zero_ne_one (hz₀_zero.symm.trans hz₀_one)

private theorem cos_and_sin_two_pi_mul_nat' :
    ∀ m : ℕ, Real.cos (2 * Real.pi * (m : ℝ)) = 1 ∧ Real.sin (2 * Real.pi * (m : ℝ)) = 0
  | 0 => by simp
  | m + 1 => by
      obtain ⟨hc, hs⟩ := cos_and_sin_two_pi_mul_nat' m
      have h : 2 * Real.pi * ((m + 1 : ℕ) : ℝ) = 2 * Real.pi * (m : ℝ) + 2 * Real.pi := by
        push_cast; ring
      rw [h, Real.cos_add_two_pi, Real.sin_add_two_pi]
      exact ⟨hc, hs⟩

/-- **Anti-nodal ordinate selection (`exists_poleAntinodal_ordinate_in_Icc`).**
On every nondegenerate positive interval `[a₀, b₀]` (`0 < a₀`, `a₀ < b₀`), there exist `c_anti > 0`
and `L_min ≥ 1` such that for every `L ≥ L_min`, there is an ordinate `γ_anti ∈ [a₀, b₀]` where
`2 * ((tr (twist γ_anti (heckeAvgBump L)) 1) ^ 2).re ≥ c_anti * exp L / L ^ 2`. -/
theorem exists_poleAntinodal_ordinate_in_Icc {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ < b₀) :
    ∃ c_anti L_min : ℝ, 0 < c_anti ∧ 1 ≤ L_min ∧ ∀ L : ℝ, L_min ≤ L →
      ∃ γ_anti ∈ Icc a₀ b₀,
        c_anti * Real.exp L / L ^ 2 ≤ 2 * ((tr (twist γ_anti (heckeAvgBump L)) 1) ^ 2).re := by
  obtain ⟨γ₁, hγ₁_mem, hb0⟩ := exists_tr_twist_baseBump_one_ne_zero_in_Ico hab
  have hγ₁_pos : 0 < γ₁ := lt_of_lt_of_le ha₀ hγ₁_mem.1
  let z : ℝ → ℂ := fun γ => (1 : ℂ) - 1 / 2 - (γ : ℂ) * I
  have hz_ne : ∀ γ : ℝ, 0 < γ → z γ ≠ 0 := by
    intro γ hγ hz0
    have him := congrArg Complex.im hz0
    simp [z] at him
    linarith
  let W : ℝ → ℂ := fun γ => (tr (twist γ baseBump) 1 / z γ) ^ 2
  have hW1_ne : W γ₁ ≠ 0 := pow_ne_zero 2 (div_ne_zero hb0 (hz_ne γ₁ hγ₁_pos))
  set r₁ : ℝ := ‖W γ₁‖
  have hr₁_pos : 0 < r₁ := norm_pos_iff.mpr hW1_ne
  have hcont_b : Continuous (fun γ : ℝ => tr (twist γ baseBump) 1) :=
    continuous_tr_twist (contDiff_baseBump (n := ⊤)).continuous hasCompactSupport_baseBump 1
  have hcont_z : Continuous z :=
    continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)
  have hW_contAt : ContinuousAt W γ₁ :=
    (hcont_b.continuousAt.div hcont_z.continuousAt (hz_ne γ₁ hγ₁_pos)).pow 2
  obtain ⟨δ_raw, hδ_raw_pos, hδ_raw⟩ :=
    Metric.continuousAt_iff.mp hW_contAt (r₁ / 8) (by positivity)
  set δ₁ : ℝ := min ((b₀ - γ₁) / 2) (δ_raw / 2)
  have hδ₁_pos : 0 < δ₁ := lt_min (by linarith [hγ₁_mem.2]) (by positivity)
  have hsub_Icc : Icc γ₁ (γ₁ + δ₁) ⊆ Icc a₀ b₀ := by
    intro γ hγ
    have hδ_le : δ₁ ≤ (b₀ - γ₁) / 2 := min_le_left _ _
    exact ⟨hγ₁_mem.1.trans hγ.1, by linarith [hγ.2, hγ₁_mem.2]⟩
  have hW_diff : ∀ γ ∈ Icc γ₁ (γ₁ + δ₁), ‖W γ - W γ₁‖ ≤ r₁ / 8 := by
    intro γ hγ
    have hlt : dist γ γ₁ < δ_raw := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hγ.1])]
      have : δ₁ ≤ δ_raw / 2 := min_le_right _ _
      linarith [hγ.2]
    exact dist_eq_norm (W γ) (W γ₁) ▸ (hδ_raw hlt).le
  have hW_norm : ∀ γ ∈ Icc γ₁ (γ₁ + δ₁), ‖W γ‖ ≤ 2 * r₁ := by
    intro γ hγ
    have hd := hW_diff γ hγ
    have htri := norm_add_le (W γ₁) (W γ - W γ₁)
    rw [add_sub_cancel] at htri
    change ‖W γ‖ ≤ r₁ + ‖W γ - W γ₁‖ at htri
    linarith [hr₁_pos]
  set L_min : ℝ := max 6 (4 * Real.pi / δ₁)
  refine ⟨r₁ / 8, L_min, by positivity, le_trans (by norm_num) (le_max_left _ _), fun L hL => ?_⟩
  have hL_ge6 : 6 ≤ L := (le_max_left _ _).trans hL
  have hL_δ : 4 * Real.pi / δ₁ ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  let Φ : ℝ → ℝ := fun γ =>
    Real.exp (-L) * (((2 * (L : ℂ)) * tr (twist γ (heckeAvgBump L)) 1) ^ 2).re
  set u₁ : ℝ := (W γ₁).re
  set v₁ : ℝ := (W γ₁).im
  have huv_sq : u₁ ^ 2 + v₁ ^ 2 = r₁ ^ 2 := by
    have := Complex.normSq_eq_norm_sq (W γ₁)
    rw [Complex.normSq_apply] at this
    dsimp [u₁, v₁, r₁]; linarith
  have hΦ_approx : ∀ γ ∈ Icc γ₁ (γ₁ + δ₁),
      |Φ γ - (u₁ * Real.cos (2 * γ * L) + v₁ * Real.sin (2 * γ * L))| ≤ r₁ / 4 := by
    intro γ hγ
    have hγ_pos : 0 < γ := lt_of_lt_of_le hγ₁_pos hγ.1
    have hzne := hz_ne γ hγ_pos
    have htr_eq : (2 * (L : ℂ)) * tr (twist γ (heckeAvgBump L)) 1 =
        (Complex.exp (z γ * (L : ℂ)) - Complex.exp (-(z γ * (L : ℂ)))) *
          (tr (twist γ baseBump) 1 / z γ) := by
      rw [tr_twist_heckeAvgBump_eq hLpos γ 1, intervalIntegral.integral_mul_const,
        show (1 : ℂ) - 1 / 2 - (γ : ℂ) * I = z γ from rfl,
        intervalIntegral_cexp_mul_eq_div hzne]
      have hL_ne_c : (L : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
      push_cast; field_simp
    set E_pos : ℂ := Complex.exp (((-(γ * L) : ℝ) : ℂ) * I)
    set E_neg : ℂ := Complex.exp (((γ * L : ℝ) : ℂ) * I)
    have hE_pos_norm : ‖E_pos‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hE_neg_norm : ‖E_neg‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hzL_pos : Complex.exp (z γ * (L : ℂ)) = ((Real.exp (L / 2) : ℝ) : ℂ) * E_pos := by
      have : z γ * (L : ℂ) = ((L / 2 : ℝ) : ℂ) + ((-(γ * L) : ℝ) : ℂ) * I := by
        dsimp [z]; push_cast; ring
      rw [this, Complex.exp_add, Complex.ofReal_exp]
    have hzL_neg : Complex.exp (-(z γ * (L : ℂ))) = ((Real.exp (-(L / 2)) : ℝ) : ℂ) * E_neg := by
      have : -(z γ * (L : ℂ)) = ((-(L / 2) : ℝ) : ℂ) + ((γ * L : ℝ) : ℂ) * I := by
        dsimp [z]; push_cast; ring
      rw [this, Complex.exp_add, Complex.ofReal_exp]
    have hsq_scaled : (((Real.exp (-L) : ℝ) : ℂ) *
        (((2 * (L : ℂ)) * tr (twist γ (heckeAvgBump L)) 1) ^ 2)) =
        E_pos ^ 2 * W γ₁ +
          (E_pos ^ 2 * (W γ - W γ₁) +
            (-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
              ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2) * W γ) := by
      rw [htr_eq, mul_pow, hzL_pos, hzL_neg]
      have he1 : Real.exp (-L) * (Real.exp (L / 2) * Real.exp (L / 2)) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, show -L + (L / 2 + L / 2) = 0 by ring, Real.exp_zero]
      have he2 : Real.exp (-L) * (Real.exp (L / 2) * Real.exp (-(L / 2))) = Real.exp (-L) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      have he3 : Real.exp (-L) * (Real.exp (-(L / 2)) * Real.exp (-(L / 2))) = Real.exp (-(2 * L)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      dsimp [W]
      have hstep : (((Real.exp (-L) : ℝ) : ℂ) *
          ((((Real.exp (L / 2) : ℝ) : ℂ) * E_pos - ((Real.exp (-(L / 2)) : ℝ) : ℂ) * E_neg) ^ 2)) =
          E_pos ^ 2 - 2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
            ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2 := by
        have hc1 : ((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (L / 2) : ℝ) : ℂ) * ((Real.exp (L / 2) : ℝ) : ℂ)) = 1 := by
          exact_mod_cast he1
        have hc2 : ((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (L / 2) : ℝ) : ℂ) * ((Real.exp (-(L / 2)) : ℝ) : ℂ)) =
            ((Real.exp (-L) : ℝ) : ℂ) := by
          exact_mod_cast he2
        have hc3 : ((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (-(L / 2)) : ℝ) : ℂ) * ((Real.exp (-(L / 2)) : ℝ) : ℂ)) =
            ((Real.exp (-(2 * L)) : ℝ) : ℂ) := by
          exact_mod_cast he3
        calc (((Real.exp (-L) : ℝ) : ℂ) *
              ((((Real.exp (L / 2) : ℝ) : ℂ) * E_pos - ((Real.exp (-(L / 2)) : ℝ) : ℂ) * E_neg) ^ 2))
            = (((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (L / 2) : ℝ) : ℂ) * ((Real.exp (L / 2) : ℝ) : ℂ))) * E_pos ^ 2 -
                2 * (((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (L / 2) : ℝ) : ℂ) * ((Real.exp (-(L / 2)) : ℝ) : ℂ))) *
                  (E_pos * E_neg) +
                (((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (-(L / 2)) : ℝ) : ℂ) * ((Real.exp (-(L / 2)) : ℝ) : ℂ))) *
                  E_neg ^ 2 := by ring
          _ = E_pos ^ 2 - 2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
                ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2 := by
              rw [hc1, hc2, hc3, one_mul]
      rw [← mul_assoc, hstep]; ring
    have hlead_re : (E_pos ^ 2 * W γ₁).re = u₁ * Real.cos (2 * γ * L) + v₁ * Real.sin (2 * γ * L) := by
      have hE2 : E_pos ^ 2 = Complex.exp (((-(2 * γ * L) : ℝ) : ℂ) * I) := by
        dsimp [E_pos]; rw [sq, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [hE2, Complex.exp_mul_I]
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
        Complex.I_re, Complex.I_im, Real.cos_neg, Real.sin_neg]
      dsimp [u₁, v₁]; ring
    set Rem : ℂ := E_pos ^ 2 * (W γ - W γ₁) +
      (-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
        ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2) * W γ
    have hΦ_diff : Φ γ - (u₁ * Real.cos (2 * γ * L) + v₁ * Real.sin (2 * γ * L)) = Rem.re := by
      have hΦ_eq : Φ γ = (((Real.exp (-L) : ℝ) : ℂ) *
          (((2 * (L : ℂ)) * tr (twist γ (heckeAvgBump L)) 1) ^ 2)).re := by
        dsimp [Φ]; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hΦ_eq, hsq_scaled, Complex.add_re, hlead_re]; ring
    rw [hΦ_diff]
    refine (Complex.abs_re_le_norm Rem).trans ?_
    have hexp_le : Real.exp (-L) ≤ 1 / 48 := by
      have h2_le_e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have h64 : (64 : ℝ) ≤ Real.exp L := by
        calc (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) := by norm_num
          _ ≤ (Real.exp 1) ^ (6 : ℕ) := pow_le_pow_left₀ zero_le_two h2_le_e 6
          _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ Real.exp L := Real.exp_le_exp.mpr hL_ge6
      rw [Real.exp_neg]
      exact (inv_anti₀ (by norm_num) h64).trans (by norm_num)
    have hexp2_le : Real.exp (-(2 * L)) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
    have hrem1 : ‖E_pos ^ 2 * (W γ - W γ₁)‖ ≤ r₁ / 8 := by
      rw [norm_mul, norm_pow, hE_pos_norm, one_pow, one_mul]; exact hW_diff γ hγ
    have hrem2 : ‖(-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
        ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2) * W γ‖ ≤ r₁ / 8 := by
      rw [norm_mul]
      have h1 : ‖-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
          ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2‖ ≤ 3 * Real.exp (-L) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_neg, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), norm_mul, hE_pos_norm, hE_neg_norm, mul_one, mul_one,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          norm_pow, hE_neg_norm, one_pow, mul_one]
        linarith
      calc ‖-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
            ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2‖ * ‖W γ‖
          ≤ (3 * Real.exp (-L)) * (2 * r₁) :=
            mul_le_mul h1 (hW_norm γ hγ) (norm_nonneg _) (by positivity)
        _ = 6 * r₁ * Real.exp (-L) := by ring
        _ ≤ 6 * r₁ * (1 / 48) := mul_le_mul_of_nonneg_left hexp_le (by positivity)
        _ = r₁ / 8 := by ring
    exact (norm_add_le _ _).trans ((add_le_add hrem1 hrem2).trans_eq (by ring))
  set m : ℕ := ⌈γ₁ * L / Real.pi⌉₊
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hm_ge : γ₁ * L / Real.pi ≤ (m : ℝ) := Nat.le_ceil _
  have hm_lt : (m : ℝ) < γ₁ * L / Real.pi + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hγ₁_pos.le hLpos.le) hπ_pos.le)
  have hθ_in_Icc : ∀ α_off : ℝ, 0 ≤ α_off → α_off ≤ 3 * Real.pi / 2 →
      (2 * Real.pi * (m : ℝ) + α_off) / (2 * L) ∈ Icc γ₁ (γ₁ + δ₁) := by
    intro α_off hα0 hα3
    constructor
    · rw [le_div_iff₀ (by positivity)]
      have := (div_le_iff₀ hπ_pos).mp hm_ge
      linarith
    · rw [div_le_iff₀ (by positivity)]
      have h2πm : 2 * Real.pi * (m : ℝ) < 2 * γ₁ * L + 2 * Real.pi := by
        have := (lt_div_iff₀' hπ_pos).mp (by linarith : (m : ℝ) - 1 < γ₁ * L / Real.pi)
        linarith
      have h4π_le : 4 * Real.pi ≤ L * δ₁ := (div_le_iff₀ hδ₁_pos).mp hL_δ
      nlinarith [hπ_pos]
  obtain ⟨hcos_m, hsin_m⟩ := cos_and_sin_two_pi_mul_nat' m
  let g_lead : ℝ → ℝ := fun θ => u₁ * Real.cos θ + v₁ * Real.sin θ
  have hg0 : g_lead (2 * Real.pi * (m : ℝ) + 0) = u₁ := by
    dsimp [g_lead]; rw [add_zero, hcos_m, hsin_m]; ring
  have hg1 : g_lead (2 * Real.pi * (m : ℝ) + Real.pi / 2) = v₁ := by
    dsimp [g_lead]
    rw [Real.cos_add, Real.sin_add, hcos_m, hsin_m, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hg2 : g_lead (2 * Real.pi * (m : ℝ) + Real.pi) = -u₁ := by
    dsimp [g_lead]
    rw [Real.cos_add, Real.sin_add, hcos_m, hsin_m, Real.cos_pi, Real.sin_pi]
    ring
  have hg3 : g_lead (2 * Real.pi * (m : ℝ) + 3 * Real.pi / 2) = -v₁ := by
    set θ₁ : ℝ := 2 * Real.pi * (m : ℝ) + Real.pi / 2
    have h32 : 2 * Real.pi * (m : ℝ) + 3 * Real.pi / 2 = θ₁ + Real.pi := by dsimp [θ₁]; ring
    rw [h32]
    dsimp [g_lead] at hg1 ⊢
    rw [Real.cos_add θ₁ Real.pi, Real.sin_add θ₁ Real.pi, Real.cos_pi, Real.sin_pi]
    linarith [hg1]
  have hmax_uv : r₁ / 2 ≤ |u₁| ∨ r₁ / 2 ≤ |v₁| := by
    by_contra hnot
    rw [not_or] at hnot
    have hu2 : u₁ ^ 2 < (r₁ / 2) ^ 2 := by
      rw [← sq_abs u₁]; exact pow_lt_pow_left₀ (not_le.mp hnot.1) (abs_nonneg _) (by norm_num)
    have hv2 : v₁ ^ 2 < (r₁ / 2) ^ 2 := by
      rw [← sq_abs v₁]; exact pow_lt_pow_left₀ (not_le.mp hnot.2) (abs_nonneg _) (by norm_num)
    nlinarith [huv_sq, hr₁_pos]
  have hex_pos : ∃ γ_pos ∈ Icc γ₁ (γ₁ + δ₁), r₁ / 2 ≤ g_lead (2 * γ_pos * L) := by
    have hmul_div : ∀ θ : ℝ, 2 * (θ / (2 * L)) * L = θ := fun θ => by
      have := hLpos.ne'; field_simp
    rcases hmax_uv with hu | hv
    · rcases le_or_gt 0 u₁ with hu0 | hu_neg
      · rw [abs_of_nonneg hu0] at hu
        exact ⟨(2 * Real.pi * (m : ℝ) + 0) / (2 * L), hθ_in_Icc 0 le_rfl (by positivity),
          by rw [hmul_div, hg0]; exact hu⟩
      · rw [abs_of_neg hu_neg] at hu
        exact ⟨(2 * Real.pi * (m : ℝ) + Real.pi) / (2 * L),
          hθ_in_Icc Real.pi hπ_pos.le (by linarith),
          by rw [hmul_div, hg2]; linarith⟩
    · rcases le_or_gt 0 v₁ with hv0 | hv_neg
      · rw [abs_of_nonneg hv0] at hv
        exact ⟨(2 * Real.pi * (m : ℝ) + Real.pi / 2) / (2 * L),
          hθ_in_Icc (Real.pi / 2) (by positivity) (by linarith),
          by rw [hmul_div, hg1]; exact hv⟩
      · rw [abs_of_neg hv_neg] at hv
        exact ⟨(2 * Real.pi * (m : ℝ) + 3 * Real.pi / 2) / (2 * L),
          hθ_in_Icc (3 * Real.pi / 2) (by positivity) le_rfl,
          by rw [hmul_div, hg3]; linarith⟩
  obtain ⟨γ_pos, hγp_mem, hlead_p⟩ := hex_pos
  have hΦ_ge : r₁ / 4 ≤ Φ γ_pos := by
    have happ := (abs_le.mp (hΦ_approx γ_pos hγp_mem)).1
    dsimp [g_lead] at hlead_p
    linarith
  have hΦ_unfold : Φ γ_pos =
      Real.exp (-L) * (4 * L ^ 2 * ((tr (twist γ_pos (heckeAvgBump L)) 1) ^ 2).re) := by
    dsimp [Φ]
    congr 1
    have hsq : ((2 * (L : ℂ)) * tr (twist γ_pos (heckeAvgBump L)) 1) ^ 2 =
        (((4 * L ^ 2 : ℝ) : ℂ)) * (tr (twist γ_pos (heckeAvgBump L)) 1) ^ 2 := by
      push_cast; ring
    rw [hsq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hΦ_unfold] at hΦ_ge
  refine ⟨γ_pos, hsub_Icc hγp_mem, ?_⟩
  rw [div_le_iff₀ (by positivity : 0 < L ^ 2)]
  have hm1 := mul_le_mul_of_nonneg_left hΦ_ge (Real.exp_pos L).le
  have hexp_cancel : Real.exp L *
      (Real.exp (-L) * (4 * L ^ 2 * ((tr (twist γ_pos (heckeAvgBump L)) 1) ^ 2).re)) =
      4 * L ^ 2 * ((tr (twist γ_pos (heckeAvgBump L)) 1) ^ 2).re := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [hexp_cancel] at hm1
  linarith

/-- **Sharpness of the Pole-Nodal Restriction under `RiemannHypothesis`
(`exists_antinodal_primePolynomial_exp_growth_of_riemannHypothesis`).**
Under `RiemannHypothesis`, on every unit window `[T, T + 1]` (`T ≥ 2`), there exist `c_T > 0` and
`L_T ≥ 1` such that for every `L ≥ L_T`, some `γ_anti ∈ [T, T + 1]` forces exponential growth
`c_T * exp L / L ^ 2 ≤ (primePolynomial (heckeAvgBump L) N*(L) (-γ_anti / 2π)).re` (and hence
`c_T * exp L / L ^ 2 ≤ ‖Π_{F_L}(-γ_anti / 2π)‖`), whereas `finiteThetaSourceMomentReading` remains
uniformly bounded across all `γ ∈ [T, T + 1]` and all `L`. -/
theorem exists_antinodal_primePolynomial_exp_growth_of_riemannHypothesis
    (hRH : RiemannHypothesis) {T : ℝ} (hT : 2 ≤ T) :
    ∃ c_T L_T E_T : ℝ, 0 < c_T ∧ 1 ≤ L_T ∧ 0 ≤ E_T ∧
      ∀ L : ℝ, L_T ≤ L →
        (∀ γ ∈ Icc T (T + 1),
          finiteThetaSourceMomentReading (baseTwistTest γ) L 1 (apertureStage L T) ≤ E_T) ∧
        (∃ γ_anti ∈ Icc T (T + 1),
          c_T * Real.exp L / L ^ 2 ≤
            (primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊
              (-γ_anti / (2 * Real.pi))).re ∧
          c_T * Real.exp L / L ^ 2 ≤
            ‖primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊
              (-γ_anti / (2 * Real.pi))‖) := by
  obtain ⟨E_unif, hE_nn, hE_bd⟩ := exists_uniform_aperture_heckeDefect_error_bounds
  obtain ⟨a₀, b₀, η₀, hT_a₀, ha₀_b₀, hb₀_T1, hη₀_pos, hsep_all⟩ :=
    exists_zero_avoiding_subinterval_in_unitWindow T
  obtain ⟨c_anti, L_min, hc_anti, hLmin1, hanti⟩ :=
    exists_poleAntinodal_ordinate_in_Icc (by linarith : 0 < a₀) ha₀_b₀
  obtain ⟨C_mu, hCmu, hmu_bd⟩ := exists_abs_re_archPart_sub_pole_heckeAvgBump_le
  obtain ⟨C_lor, hClor, hlor⟩ := exists_zetaZeroConfig_lorentz_le
  set M_err : ℝ := (C_mu + Real.log (3 + T)) +
    (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) * (C_lor * (1 + Real.log (T + 5))) + 1
  have hMerr_pos : 0 < M_err := by
    have : 0 ≤ Real.log (3 + T) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log (T + 5) := Real.log_nonneg (by linarith)
    dsimp [M_err]; positivity
  -- Since `exp L / L ^ 2 → ∞` as `L → ∞` (`exp L ≥ L^3 / 6` for `L ≥ 0`), choose `L_T` explicitly
  set L_T : ℝ := max L_min (12 * M_err / c_anti + 1)
  have hLT1 : 1 ≤ L_T := hLmin1.trans (le_max_left _ _)
  refine ⟨c_anti / 2, L_T, E_unif, by positivity, hLT1, hE_nn, fun L hL => ⟨?_, ?_⟩⟩
  · intro γ hγ
    obtain ⟨hγ_adm, hL_adm⟩ := apertureStage_admissible L T hγ
    rw [one_mul] at hL_adm
    have herr := (hE_bd (apertureStage L T) (one_le_apertureStage L T) L γ hγ_adm hL_adm).1
    rw [heckeDefect_eq_zero_of_riemannHypothesis hRH, sub_zero] at herr
    exact le_of_abs_le herr
  · have hL_ge_min : L_min ≤ L := (le_max_left _ _).trans hL
    have hL_ge1 : 1 ≤ L := hLT1.trans hL
    have hL_pos : 0 < L := lt_of_lt_of_le one_pos hL_ge1
    obtain ⟨γ_anti, hγ_ab, hpole_ge⟩ := hanti L hL_ge_min
    have hγ_Icc : γ_anti ∈ Icc T (T + 1) := ⟨hT_a₀.trans hγ_ab.1, hγ_ab.2.trans hb₀_T1⟩
    -- 1. Lower bound `(archPart (heckeAvgBump L) (-γ_anti / 2π)).re`
    have harch_ge : c_anti * Real.exp L / L ^ 2 - (C_mu + Real.log (3 + T)) ≤
        (archPart (heckeAvgBump L) (-γ_anti / (2 * Real.pi))).re := by
      have hsub := (abs_le.mp (hmu_bd L γ_anti hL_ge1)).1
      have habs_γ : |γ_anti| = γ_anti := abs_of_pos (by linarith [hγ_Icc.1])
      have hlog_le : Real.log (2 + |γ_anti|) / (2 * L) ≤ Real.log (3 + T) := by
        rw [habs_γ]
        have h1 : Real.log (2 + γ_anti) ≤ Real.log (3 + T) :=
          Real.log_le_log (by linarith [hγ_Icc.1]) (by linarith [hγ_Icc.2])
        exact (div_le_self (Real.log_nonneg (by linarith [hγ_Icc.1])) (by linarith)).trans h1
      linarith [hpole_ge]
    -- 2. Upper bound `|(zetaZeroConfig.W ...).re| ≤ collidedForm` under `RH` (`E_γ = 0`)
    have hW_abs : |(zetaZeroConfig.W (twist γ_anti (heckeAvgBump L))
        (twist γ_anti (heckeAvgBump L))).re| ≤
        (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) * (C_lor * (1 + Real.log (T + 5))) := by
      have hs_coll := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L) γ_anti)
        (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hL_pos) γ_anti)
      have hW_le := abs_re_W_le_collidedForm hs_coll
      have hlor_sum := (hlor γ_anti).1
      have hdef_sum := summable_heckeDefect (baseTwistTest γ_anti) L
      set c₁ : ℝ := (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2
      set c₂ : ℝ := 1 / (4 * η₀ ^ 2 * L ^ 2)
      have hptw : ∀ ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_anti (heckeAvgBump L)) ρ) ≤
            c₁ * ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ_anti - (ρ : ℂ).im) ^ 2))) +
              c₂ * (zetaWeight (baseTwistTest γ_anti) ρ * depthKernel L (zetaDepth ρ)) := by
        intro ρ
        have hsep := hsep_all (ρ : ℂ) ρ.2 γ_anti hγ_ab
        have hbd := normSq_tr_twist_heckeAvgBump_le_of_sep hL_pos hη₀_pos γ_anti ρ hsep
        have hm0 : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
        have hw_eq : zetaWeight (baseTwistTest γ_anti) ρ =
            (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_anti baseBump) ρ) := rfl
        rw [hw_eq, show c₁ = (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2 from rfl,
          show c₂ = 1 / (4 * η₀ ^ 2 * L ^ 2) from rfl]
        calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_anti (heckeAvgBump L)) ρ)
            ≤ (zetaZeroConfig.mult ρ : ℝ) *
                ((1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2 *
                    (1 / (1 + (γ_anti - (ρ : ℂ).im) ^ 2)) +
                  1 / (4 * η₀ ^ 2 * L ^ 2) *
                    (Complex.normSq (tr (twist γ_anti baseBump) ρ) *
                      depthKernel L (zetaDepth ρ))) :=
              mul_le_mul_of_nonneg_left hbd hm0
          _ = _ := by ring
      have htsum := hs_coll.tsum_le_tsum hptw ((hlor_sum.mul_left c₁).add (hdef_sum.mul_left c₂))
      rw [(hlor_sum.mul_left c₁).tsum_add (hdef_sum.mul_left c₂), tsum_mul_left, tsum_mul_left]
        at htsum
      have hcoll_def : (∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_anti (heckeAvgBump L)) ρ)) =
          collidedForm zetaZeroConfig (twist γ_anti (heckeAvgBump L)) := rfl
      have hdef_eq : (∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (baseTwistTest γ_anti) ρ * depthKernel L (zetaDepth ρ)) =
          heckeDefect (baseTwistTest γ_anti) L := rfl
      rw [hcoll_def, hdef_eq, heckeDefect_eq_zero_of_riemannHypothesis hRH, mul_zero, add_zero]
        at htsum
      have h1 : c₁ ≤ (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) := by
        dsimp [c₁]; exact div_le_self (by positivity) (by nlinarith : 1 ≤ L ^ 2)
      have habs_γ : |γ_anti| = γ_anti := abs_of_pos (by linarith [hγ_Icc.1])
      have h2 : (∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ_anti - (ρ : ℂ).im) ^ 2))) ≤
          C_lor * (1 + Real.log (T + 5)) := by
        refine (hlor γ_anti).2.trans (mul_le_mul_of_nonneg_left ?_ hClor.le)
        have : Real.log (|γ_anti| + 4) ≤ Real.log (T + 5) := by
          rw [habs_γ]
          exact Real.log_le_log (by linarith [hγ_Icc.1]) (by linarith [hγ_Icc.2])
        linarith
      exact hW_le.trans (htsum.trans (mul_le_mul h1 h2
        (tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))
        (by positivity)))
    -- 3. Combine explicit formula with `L ^ 3 / 6 ≤ exp L` (`Real.sum_le_exp_of_nonneg`)
    have hEF := re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial
      (contDiff_heckeAvgBump L) (tsupport_heckeAvgBump_subset hL_pos) (-γ_anti / (2 * Real.pi))
    rw [← twist_eq_heightShift γ_anti (heckeAvgBump L)] at hEF
    have hcubic : L ^ 3 / 6 ≤ Real.exp L := by
      have h4 := Real.sum_le_exp_of_nonneg hL_pos.le 4
      simp [Finset.sum_range_succ, Nat.factorial] at h4
      linarith [pow_nonneg hL_pos.le 2]
    have hexp_dom : M_err ≤ (c_anti / 2) * Real.exp L / L ^ 2 := by
      have hL_large : 12 * M_err / c_anti ≤ L := by
        have := (le_max_right _ _).trans hL; linarith
      have h1 := (div_le_iff₀ hc_anti).mp hL_large
      rw [le_div_iff₀ (by positivity : 0 < L ^ 2)]
      nlinarith [hcubic, hc_anti]
    have hre_ge : (c_anti / 2) * Real.exp L / L ^ 2 ≤
        (primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊
          (-γ_anti / (2 * Real.pi))).re := by
      have hW_hi := (abs_le.mp hW_abs).2
      have hsplit_c : c_anti * Real.exp L / L ^ 2 =
          2 * ((c_anti / 2) * Real.exp L / L ^ 2) := by ring
      dsimp [M_err] at hexp_dom
      linarith [hEF, harch_ge, hW_hi, hexp_dom, hsplit_c]
    refine ⟨γ_anti, hγ_Icc, hre_ge, ?_⟩
    exact hre_ge.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_uniform_aperture_heckeDefect_error_bounds
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_linearThetaStage_polynomialReading_sub_heckeDefect_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.riemannHypothesis_finiteTheta_poleNodal_dyadic_tfae
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_tr_twist_baseBump_one_ne_zero_in_Ico
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_poleAntinodal_ordinate_in_Icc
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_antinodal_primePolynomial_exp_growth_of_riemannHypothesis
