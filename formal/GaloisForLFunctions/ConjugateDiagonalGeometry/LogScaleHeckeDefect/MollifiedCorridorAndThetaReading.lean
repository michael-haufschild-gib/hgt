import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.FiniteStratumAndCorridorClassification
import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.FiniteThetaPoleNodalRHEquivalence
import GaloisForLFunctions.RHTower.SelbergNearLineCriticalGateDensity
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailSelberg
import GaloisForLFunctions.RHTower.ZetaRightZeroWeightedCount
import GaloisForLFunctions.BiScaleUncertainty.ZeroDensityFilteredCriticalDeficitLaw

/-!
# Three-Scale Sieve-Mollified Logarithmic Corridor Collapse and Polynomial-Theta Equivalence

This module attacks the bare prime-free logarithmic corridor charge
`unitWindowDepthCharge T (c * Real.log T)` together with `heckeDefect (baseTwistTest γ) (c * Real.log γ)`
and the linear-prefix finite-integer theta reading
`polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1 (linearThetaStage (2 * U))`
via multiplicative Selberg / Barban–Vehov sieve mollification, bypassing the `O(1 / log T)` linear
explicit-formula decoupling of `primePolynomial`:

1. **Symmetric-vs-Euler mollification obstruction** (`eulerFactor_verticalZeros_depthKernel_ge`):
   Every Dirichlet Euler factor `1 - m^{-s}` (`m ≥ 2`) has vertical zeros `s = i y` on `Re s = 0`
   in every interval of length `2π / log m` where `depthKernel (c log T) (Re s - 1/2) > T^c - 2`,
   obstructing naive two-sided Euler-product mollification prior to `lineReflect` folding.

2. **Three-scale sieve-mollified dyadic collapse up to `c < 22 / 51`**
   (`exists_dyadicMean_corridor_and_polynomialTheta_le_log`,
    `exists_dyadicMean_polynomialTheta_subpower_up_to_two_thirds`):
   Folding left-half zeros onto `Re ρ > 1/2` via `lineReflect` and coupling:
   - **Scale I** (`0 < δ_ρ < (51/50) / log S`): Selberg's twisted `Λ²` sieve mollifier of length
     `⌊V^{1/15}⌋` (`eventually_offLineMoment_le_selberg`);
   - **Scale II** (`(51/50) m / log S ≤ δ_ρ < (51/50)(m + 1) / log S`, `1 ≤ m < ⌊log S / 100⌋₊`):
     the two-length Barban–Vehov critical-gate mollifier of lengths `S^{23/50}, S^{47/100}`
     (`exists_selberg_criticalGate_nearLine_zeroDensity`, exponential rate `22/25`);
   - **Scale III** (`δ_ρ ≥ 1 / 200`): the hybrid Ingham–Guth–Maynard–DH zero-density theorem
     (`exists_sum_exp_foldedRe_deep_decay_up_to_two_thirds_log`)
   collapses the dyadic means of `unitWindowDepthCharge`, `heckeDefect`, and the linear-stage
   `polynomialThetaSourceMomentReading` to `O_c(log U)` for every `0 < c < 22 / 51` (with uniform
   quadratic scaling `K_c ≤ K_* c²` on `0 < c ≤ 1 / 5`), and to `O_{c, η}(U^η)` across `0 < c < 2 / 3`.

3. **Unconditional almost-all unit-window `(6/5) log(log T) / log T` corridor**
   (`eventually_volume_badLogLogCorridor_unitWindows_le`):
   All unit windows `[T, T + 1)` (`T ∈ [U, 2U]`) outside an exceptional set of Lebesgue measure
   `O(U / log(log U))` are completely free of zeros with `|Re ρ - 1/2| ≥ (6/5) log(log T) / log T`.

4. **Four-way `o(log U)` equivalence with `100%` critical-scale clustering**
   (`dyadicMean_corridor_and_polynomialTheta_littleO_log_tfae`):
   For every fixed `0 < c < 22 / 51`, `o(log U)` vanishing of the dyadic mean of
   `unitWindowDepthCharge`, `heckeDefect`, or `polynomialThetaSourceMomentReading` at
   `linearThetaStage (2 * U)` is unconditionally equivalent (`TFAE`) to
   `∀ κ > 0, offLineCountBeyond (κ / log V) V = o(V log V)`.
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators Real ComplexConjugate ContDiff ENNReal Laplacian
open _root_.RHTower _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open ArithmeticPolarization SquareRootThreshold

/-! ## §1. Symmetric-vs-Euler mollification obstruction on `Re s = 0` -/

/-- Every integer Euler factor `1 - m^{-s}` (`m ≥ 2`) vanishes on `Re s = 0` in every vertical
interval `[a, b]` of length `≥ 2π / log m`, carrying hyperbolic weight `depthKernel (c log T) (-1/2) > T^c - 2`. -/
theorem eulerFactor_verticalZeros_depthKernel_ge {m : ℕ} (hm : 2 ≤ m) {a b : ℝ}
    (hab : a + 2 * Real.pi / Real.log (m : ℝ) ≤ b) :
    ∃ y ∈ Icc a b,
      let s : ℂ := (y : ℂ) * I
      s.re = 0 ∧ 1 - (m : ℂ) ^ (-s) = 0 ∧
      ∀ (T c : ℝ), 1 ≤ T → 0 < c →
        T ^ c - 2 < depthKernel (c * Real.log T) (s.re - 1 / 2) := by
  have hm_gt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm_gt1
  have h2pi : 0 < 2 * Real.pi := by positivity
  set k : ℤ := ⌈a * Real.log (m : ℝ) / (2 * Real.pi)⌉
  set y : ℝ := 2 * Real.pi * (k : ℝ) / Real.log (m : ℝ)
  have hy_lo : a ≤ y := by
    have hk := Int.le_ceil (a * Real.log (m : ℝ) / (2 * Real.pi))
    have hk' := (div_le_iff₀ h2pi).mp hk
    dsimp [y]
    rw [le_div_iff₀ hlogm]
    linarith
  have hy_hi : y ≤ b := by
    have hk := Int.ceil_lt_add_one (a * Real.log (m : ℝ) / (2 * Real.pi))
    have hk' : (k : ℝ) * (2 * Real.pi) ≤ a * Real.log (m : ℝ) + 2 * Real.pi := by
      have h1 : (k : ℝ) - 1 ≤ a * Real.log (m : ℝ) / (2 * Real.pi) := by linarith
      have h2 := (le_div_iff₀ h2pi).mp h1
      linarith
    have hy_step : y ≤ a + 2 * Real.pi / Real.log (m : ℝ) := by
      dsimp [y]
      rw [← sub_nonneg]
      have hrew : a + 2 * Real.pi / Real.log (m : ℝ) - 2 * Real.pi * (k : ℝ) / Real.log (m : ℝ) =
          (a * Real.log (m : ℝ) + 2 * Real.pi - (k : ℝ) * (2 * Real.pi)) / Real.log (m : ℝ) := by
        field_simp
        ring
      rw [hrew]
      exact div_nonneg (by linarith) hlogm.le
    exact hy_step.trans hab
  refine ⟨y, ⟨hy_lo, hy_hi⟩, ?_⟩
  dsimp only
  have hs_re : ((y : ℂ) * I).re = 0 := by simp
  refine ⟨hs_re, ?_, fun T c hT1 hc => ?_⟩
  · have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast hm_pos.ne'
    rw [sub_eq_zero, eq_comm, Complex.cpow_def_of_ne_zero hm_ne]
    have hlog_c : Complex.log (m : ℂ) = ((Real.log (m : ℝ) : ℝ) : ℂ) := by
      rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_log hm_pos.le]
    have hy_mul : Real.log (m : ℝ) * y = 2 * Real.pi * (k : ℝ) := by
      dsimp [y]
      exact mul_div_cancel₀ _ hlogm.ne'
    have hy_mul_c : ((Real.log (m : ℝ) : ℝ) : ℂ) * (y : ℂ) = 2 * (Real.pi : ℂ) * (k : ℂ) := by
      exact_mod_cast hy_mul
    have hexp_arg : Complex.log (m : ℂ) * -((y : ℂ) * I) =
        -((k : ℂ) * (2 * (Real.pi : ℂ) * I)) := by
      rw [hlog_c]
      calc ((Real.log (m : ℝ) : ℝ) : ℂ) * -((y : ℂ) * I)
          = -((((Real.log (m : ℝ) : ℝ) : ℂ) * (y : ℂ)) * I) := by ring
        _ = -(2 * (Real.pi : ℂ) * (k : ℂ) * I) := by rw [hy_mul_c]
        _ = -((k : ℂ) * (2 * (Real.pi : ℂ) * I)) := by ring
    rw [hexp_arg, Complex.exp_neg, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, inv_one]
  · rw [hs_re, zero_sub]
    have hT_pos : 0 < T := by linarith
    set L : ℝ := c * Real.log T
    have hdk : depthKernel L (-1 / 2) = Real.exp L - 2 + Real.exp (-L) := by
      have h1 : depthKernel L (-1 / 2) = 4 * Real.sinh ((-1 / 2) * L) ^ 2 :=
        depthKernel_eq_four_sinh_sq L (-1 / 2)
      rw [h1, Real.sinh_eq]
      have he1 : Real.exp ((-1 / 2) * L) * Real.exp ((-1 / 2) * L) = Real.exp (-L) := by
        rw [← Real.exp_add]; congr 1; ring
      have he2 : Real.exp (-((-1 / 2) * L)) * Real.exp (-((-1 / 2) * L)) = Real.exp L := by
        rw [← Real.exp_add]; congr 1; ring
      have he3 : Real.exp ((-1 / 2) * L) * Real.exp (-((-1 / 2) * L)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith [he1, he2, he3]
    have hexpL : Real.exp L = T ^ c := by
      dsimp [L]
      rw [Real.rpow_def_of_pos hT_pos, mul_comm]
    have hexp_pos : 0 < Real.exp (-L) := Real.exp_pos _
    linarith

/-! ## §2. Elementary hyperbolic kernel estimates and scale-addition stability -/

private theorem sinh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 ≤ Real.exp x := Real.one_le_exp hx
  linarith

private theorem sinh_mono_nonneg {x y : ℝ} (_hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.sinh x ≤ Real.sinh y := by
  rw [Real.sinh_eq, Real.sinh_eq]
  have h1 : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
  have h2 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  linarith

private theorem cosh_mono_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.cosh x ≤ Real.cosh y := by
  rw [Real.cosh_eq, Real.cosh_eq]
  have h1 : Real.exp x - Real.exp y ≤ 0 := by linarith [Real.exp_le_exp.mpr hxy]
  have hprod : (Real.exp x - Real.exp y) * (1 - Real.exp (-(x + y))) ≤ 0 := by
    refine mul_nonpos_of_nonpos_of_nonneg h1 ?_
    have : Real.exp (-(x + y)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hexpand : (Real.exp x - Real.exp y) * (1 - Real.exp (-(x + y))) =
      (Real.exp x + Real.exp (-x)) - (Real.exp y + Real.exp (-y)) := by
    have hx_id : Real.exp x * Real.exp (-(x + y)) = Real.exp (-y) := by
      rw [← Real.exp_add]; congr 1; ring
    have hy_id : Real.exp y * Real.exp (-(x + y)) = Real.exp (-x) := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [hx_id, hy_id,
      show (Real.exp x - Real.exp y) * (1 - Real.exp (-(x + y))) =
        Real.exp x - Real.exp y - Real.exp x * Real.exp (-(x + y)) +
          Real.exp y * Real.exp (-(x + y)) by ring]
  linarith

/-- Elementary inequality `sinh x ≤ x * exp x` for `x ≥ 0`. -/
theorem sinh_le_mul_exp {x : ℝ} (_hx : 0 ≤ x) : Real.sinh x ≤ x * Real.exp x := by
  rw [Real.sinh_eq]
  have h1 := Real.add_one_le_exp (-(2 * x))
  have hm := mul_le_mul_of_nonneg_right h1 (Real.exp_pos x).le
  have hexp : Real.exp (-(2 * x)) * Real.exp x = Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at hm
  have hring : (-(2 * x) + 1) * Real.exp x = Real.exp x - 2 * x * Real.exp x := by ring
  linarith

private theorem cosh_le_two_mul_sinh_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Real.cosh x ≤ 2 * Real.sinh x := by
  rw [Real.cosh_eq, Real.sinh_eq]
  have h3 : (3 : ℝ) ≤ Real.exp (2 * x) := by
    calc (3 : ℝ) = 2 + 1 := by norm_num
      _ ≤ Real.exp 2 := Real.add_one_le_exp 2
      _ ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-x)).le
  have hexp : Real.exp (2 * x) * Real.exp (-x) = Real.exp x := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at hm
  linarith

theorem depthKernel_even_depth (L d : ℝ) : depthKernel L (-d) = depthKernel L d := by
  simp only [depthKernel, show 2 * (-d) * L = -(2 * d * L) by ring, Real.cosh_neg]

theorem depthKernel_abs_depth (L d : ℝ) : depthKernel L |d| = depthKernel L d := by
  rcases le_or_gt 0 d with hd | hd
  · rw [abs_of_nonneg hd]
  · rw [abs_of_neg hd, depthKernel_even_depth]

/-- Monotonicity of `depthKernel L d` with respect to scale `0 ≤ L₁ ≤ L₂`. -/
theorem depthKernel_mono_scale {L₁ L₂ : ℝ} (h0 : 0 ≤ L₁) (hle : L₁ ≤ L₂) (d : ℝ) :
    depthKernel L₁ d ≤ depthKernel L₂ d := by
  rw [← depthKernel_abs_depth L₁ d, ← depthKernel_abs_depth L₂ d,
    depthKernel_eq_four_sinh_sq, depthKernel_eq_four_sinh_sq]
  have hx0 : 0 ≤ |d| * L₁ := mul_nonneg (abs_nonneg d) h0
  have hxy : |d| * L₁ ≤ |d| * L₂ := mul_le_mul_of_nonneg_left hle (abs_nonneg d)
  have hsh := sinh_mono_nonneg hx0 hxy
  have hnn := sinh_nonneg_of_nonneg hx0
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hsh 2) (by norm_num)

/-- Quadratic-exponential upper bound `depthKernel L d ≤ 4 (L |d|)² exp(2 L |d|)` for `L ≥ 0`. -/
theorem depthKernel_le_four_sq_mul_exp {L d : ℝ} (hL : 0 ≤ L) :
    depthKernel L d ≤ 4 * (L * |d|) ^ 2 * Real.exp (2 * L * |d|) := by
  rw [← depthKernel_abs_depth L d, depthKernel_eq_four_sinh_sq]
  have hx0 : 0 ≤ |d| * L := mul_nonneg (abs_nonneg d) hL
  have hsh := sinh_le_mul_exp hx0
  have hnn := sinh_nonneg_of_nonneg hx0
  have hsq := pow_le_pow_left₀ hnn hsh 2
  calc 4 * Real.sinh (|d| * L) ^ 2
      ≤ 4 * ((|d| * L) * Real.exp (|d| * L)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 4 * (L * |d|) ^ 2 * (Real.exp (|d| * L) * Real.exp (|d| * L)) := by ring
    _ = 4 * (L * |d|) ^ 2 * Real.exp (2 * L * |d|) := by
        rw [← Real.exp_add]; congr 2; ring

/-- Pure exponential upper bound `depthKernel L d ≤ exp(2 L |d|)` for `L ≥ 0`. -/
theorem depthKernel_le_exp_two_mul {L d : ℝ} (hL : 0 ≤ L) :
    depthKernel L d ≤ Real.exp (2 * L * |d|) := by
  rw [← depthKernel_abs_depth L d, depthKernel_eq_four_sinh_sq, Real.sinh_eq]
  set x : ℝ := |d| * L
  have hx0 : 0 ≤ x := mul_nonneg (abs_nonneg d) hL
  have he_le1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1_le : 1 ≤ Real.exp x := Real.one_le_exp hx0
  have he_pos : 0 < Real.exp (-x) := Real.exp_pos _
  have hring : 4 * ((Real.exp x - Real.exp (-x)) / 2) ^ 2 =
      (Real.exp x - Real.exp (-x)) ^ 2 := by ring
  rw [hring]
  calc (Real.exp x - Real.exp (-x)) ^ 2
      ≤ (Real.exp x) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    _ = Real.exp (2 * L * |d|) := by
        rw [sq, ← Real.exp_add]; dsimp [x]; congr 1; ring

/-- Uniform additive scale stability: for `0 ≤ a ≤ L` and `|d| ≤ 1 / 2`,
`depthKernel (L + a) d ≤ (cosh(a / 2) + cosh 1 + 2 sinh(a / 2))² * depthKernel L d`. -/
theorem depthKernel_add_le_mul {L a d : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ L) (hd : |d| ≤ 1 / 2) :
    depthKernel (L + a) d ≤
      (Real.cosh (a / 2) + Real.cosh 1 + 2 * Real.sinh (a / 2)) ^ 2 * depthKernel L d := by
  have hL0 : 0 ≤ L := ha0.trans haL
  rw [← depthKernel_abs_depth (L + a) d, ← depthKernel_abs_depth L d,
    depthKernel_eq_four_sinh_sq, depthKernel_eq_four_sinh_sq]
  set x : ℝ := |d| * L
  set y : ℝ := |d| * a
  have hx0 : 0 ≤ x := mul_nonneg (abs_nonneg d) hL0
  have hy0 : 0 ≤ y := mul_nonneg (abs_nonneg d) ha0
  have hy_le_x : y ≤ x := mul_le_mul_of_nonneg_left haL (abs_nonneg d)
  have hy_le_a2 : y ≤ a / 2 := by
    dsimp [y]
    have := mul_le_mul_of_nonneg_right hd ha0
    linarith
  have hadd : |d| * (L + a) = x + y := by dsimp [x, y]; ring
  rw [hadd]
  set M : ℝ := Real.cosh (a / 2) + Real.cosh 1 + 2 * Real.sinh (a / 2)
  have hsh_x_nn : 0 ≤ Real.sinh x := sinh_nonneg_of_nonneg hx0
  have hsh_y_nn : 0 ≤ Real.sinh y := sinh_nonneg_of_nonneg hy0
  have hsh_a2_nn : 0 ≤ Real.sinh (a / 2) := sinh_nonneg_of_nonneg (by positivity)
  have hch_y : Real.cosh y ≤ Real.cosh (a / 2) := cosh_mono_nonneg hy0 hy_le_a2
  have hsh_sum : Real.sinh (x + y) ≤ M * Real.sinh x := by
    rw [Real.sinh_add]
    rcases le_or_gt x 1 with hx1 | hx1
    · have hsh_yx : Real.sinh y ≤ Real.sinh x := sinh_mono_nonneg hy0 hy_le_x
      have hch_x1 : Real.cosh x ≤ Real.cosh 1 := cosh_mono_nonneg hx0 hx1
      have h1 : Real.sinh x * Real.cosh y ≤ Real.cosh (a / 2) * Real.sinh x := by
        nlinarith [hch_y, hsh_x_nn]
      have h2 : Real.cosh x * Real.sinh y ≤ Real.cosh 1 * Real.sinh x :=
        mul_le_mul hch_x1 hsh_yx hsh_y_nn (Real.cosh_pos 1).le
      dsimp [M]
      nlinarith [hsh_a2_nn, hsh_x_nn]
    · have hch_x : Real.cosh x ≤ 2 * Real.sinh x := cosh_le_two_mul_sinh_of_one_le hx1.le
      have hsh_ya : Real.sinh y ≤ Real.sinh (a / 2) := sinh_mono_nonneg hy0 hy_le_a2
      have h1 : Real.sinh x * Real.cosh y ≤ Real.cosh (a / 2) * Real.sinh x := by
        nlinarith [hch_y, hsh_x_nn]
      have h2 : Real.cosh x * Real.sinh y ≤ (2 * Real.sinh (a / 2)) * Real.sinh x := by
        have hm := mul_le_mul hch_x hsh_ya hsh_y_nn (by positivity)
        linarith
      dsimp [M]
      have hch1 : 0 < Real.cosh 1 := Real.cosh_pos 1
      nlinarith [hch1, hsh_x_nn]
  have hsh_xy_nn : 0 ≤ Real.sinh (x + y) := sinh_nonneg_of_nonneg (by positivity)
  have hsq := pow_le_pow_left₀ hsh_xy_nn hsh_sum 2
  calc 4 * Real.sinh (x + y) ^ 2
      ≤ 4 * (M * Real.sinh x) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = M ^ 2 * (4 * Real.sinh x ^ 2) := by ring

private theorem one_le_log_of_four_le {V : ℝ} (hV : 4 ≤ V) : 1 ≤ Real.log V := by
  have h2 := Real.log_two_gt_d9
  have h4_eq : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
  have h4 : Real.log ((2 : ℝ) ^ (2 : ℕ)) ≤ Real.log V :=
    Real.log_le_log (by norm_num) (h4_eq.trans_le hV)
  rw [Real.log_pow] at h4; push_cast at h4; linarith

private theorem two_le_log_of_sixteen_le {V : ℝ} (hV : 16 ≤ V) : 2 ≤ Real.log V := by
  have h2 := Real.log_two_gt_d9
  have h16_eq : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
  have h16 : Real.log ((2 : ℝ) ^ (4 : ℕ)) ≤ Real.log V :=
    Real.log_le_log (by norm_num) (h16_eq.trans_le hV)
  rw [Real.log_pow] at h16; push_cast at h16; linarith

private theorem log_four_le_two : Real.log 4 ≤ 2 := by
  have h4_eq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [h4_eq, Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]

/-! ## §3. `lineReflect` shell folding, `XiZeroCopy` bridge, and short-shell bounds -/

/-- Strip zeros of `ξ` in the height shell `V₁ < Im z ≤ V₂` (`0 < Im z`). -/
def shellZeros (V₁ V₂ : ℝ) : Finset ℂ :=
  (stripFinsetPos V₂).filter (fun z => V₁ < z.im)

/-- Multiplicity-weighted hyperbolic depth sum across `shellZeros V₁ V₂`. -/
def shellDepthSum (V₁ V₂ L : ℝ) : ℝ :=
  ∑ z ∈ shellZeros V₁ V₂, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)

theorem shellDepthSum_nonneg (V₁ V₂ L : ℝ) : 0 ≤ shellDepthSum V₁ V₂ L :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)

theorem shellDepthSum_mono_scale {V₁ V₂ L₁ L₂ : ℝ} (h0 : 0 ≤ L₁) (hle : L₁ ≤ L₂) :
    shellDepthSum V₁ V₂ L₁ ≤ shellDepthSum V₁ V₂ L₂ :=
  Finset.sum_le_sum fun _ _ =>
    mul_le_mul_of_nonneg_left (depthKernel_mono_scale h0 hle _) (Nat.cast_nonneg _)

theorem shellZeros_disjoint_split {V₁ V₂ V₃ : ℝ} (h12 : V₁ ≤ V₂) (h23 : V₂ ≤ V₃) :
    shellZeros V₁ V₃ = shellZeros V₁ V₂ ∪ shellZeros V₂ V₃ ∧
      Disjoint (shellZeros V₁ V₂) (shellZeros V₂ V₃) := by
  classical
  refine ⟨?_, ?_⟩
  · ext z
    simp only [shellZeros, Finset.mem_union, Finset.mem_filter, mem_stripFinsetPos]
    constructor
    · rintro ⟨⟨h0, h1, him0, him3, hxi⟩, him1⟩
      rcases le_or_gt z.im V₂ with hle2 | hgt2
      · exact Or.inl ⟨⟨h0, h1, him0, hle2, hxi⟩, him1⟩
      · exact Or.inr ⟨⟨h0, h1, him0, him3, hxi⟩, hgt2⟩
    · rintro (⟨⟨h0, h1, him0, him2, hxi⟩, him1⟩ | ⟨⟨h0, h1, him0, him3, hxi⟩, him2⟩)
      · exact ⟨⟨h0, h1, him0, him2.trans h23, hxi⟩, him1⟩
      · exact ⟨⟨h0, h1, him0, him3, hxi⟩, lt_of_le_of_lt h12 him2⟩
  · rw [Finset.disjoint_left]
    intro z hz1 hz2
    have hle2 := (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz1).1).2.2.2.1
    have hgt2 := (Finset.mem_filter.mp hz2).2
    linarith

theorem shellDepthSum_split {V₁ V₂ V₃ : ℝ} (h12 : V₁ ≤ V₂) (h23 : V₂ ≤ V₃) (L : ℝ) :
    shellDepthSum V₁ V₃ L = shellDepthSum V₁ V₂ L + shellDepthSum V₂ V₃ L := by
  classical
  obtain ⟨hunion, hdisj⟩ := shellZeros_disjoint_split h12 h23
  unfold shellDepthSum
  rw [hunion, Finset.sum_union hdisj]

theorem lineReflect_mem_shellZeros {V₁ V₂ : ℝ} {z : ℂ} (hz : z ∈ shellZeros V₁ V₂) :
    lineReflect z ∈ shellZeros V₁ V₂ := by
  rw [shellZeros, Finset.mem_filter] at hz ⊢
  refine ⟨lineReflect_mem_stripFinsetPos hz.1, ?_⟩
  have him : (lineReflect z).im = z.im := by simp [lineReflect]
  rw [him]
  exact hz.2

/-- Critical-line reflection (`lineReflect`) folds `shellDepthSum` onto twice the right-half shell
`1 / 2 < z.re`. -/
theorem shellDepthSum_eq_two_mul_right (V₁ V₂ L : ℝ) :
    shellDepthSum V₁ V₂ L =
      2 * ∑ z ∈ (shellZeros V₁ V₂).filter (fun z => 1 / 2 < z.re),
        ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) := by
  classical
  set t := shellZeros V₁ V₂
  set f : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
  have hsplit1 := (Finset.sum_filter_add_sum_filter_not t (fun z => z.re = 1 / 2) f).symm
  have hsplit2 := (Finset.sum_filter_add_sum_filter_not
    (t.filter (fun z => ¬ z.re = 1 / 2)) (fun z => 1 / 2 < z.re) f).symm
  have honline : ∑ z ∈ t.filter (fun z => z.re = 1 / 2), f z = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    have hre := (Finset.mem_filter.mp hz).2
    dsimp [f]
    rw [hre, sub_self, depthKernel_zero_depth, mul_zero]
  have hR : (t.filter (fun z => ¬ z.re = 1 / 2)).filter (fun z => 1 / 2 < z.re) =
      t.filter (fun z => 1 / 2 < z.re) := by
    ext z
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ne_of_gt h.2⟩, h.2⟩⟩
  have hL_set : (t.filter (fun z => ¬ z.re = 1 / 2)).filter (fun z => ¬ 1 / 2 < z.re) =
      t.filter (fun z => z.re < 1 / 2) := by
    ext z
    simp only [Finset.mem_filter, not_lt]
    exact ⟨fun h => ⟨h.1.1, lt_of_le_of_ne h.2 h.1.2⟩, fun h => ⟨⟨h.1, ne_of_lt h.2⟩, h.2.le⟩⟩
  have hbij : ∑ z ∈ t.filter (fun z => z.re < 1 / 2), f z =
      ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), f z := by
    refine Finset.sum_nbij' lineReflect lineReflect ?_ ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨lineReflect_mem_shellZeros hz.1, ?_⟩
      rw [lineReflect_re]; linarith [hz.2]
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨lineReflect_mem_shellZeros hz.1, ?_⟩
      rw [lineReflect_re]; linarith [hz.2]
    · intro z _; exact lineReflect_involutive z
    · intro z _; exact lineReflect_involutive z
    · intro z _
      dsimp [f]
      rw [xi_orderAt_lineReflect, lineReflect_re, show 1 - z.re - 1 / 2 = -(z.re - 1 / 2) by ring,
        depthKernel_even_depth]
  change ∑ z ∈ t, f z = 2 * ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), f z
  rw [hsplit1, honline, zero_add, hsplit2, hR, hL_set, hbij, two_mul]

/-- Exact symmetry identity for counting zeros beyond symmetric threshold `|z.re - 1/2| ≥ b` (`b > 0`). -/
private theorem shellOrderSum_abs_ge_eq_two_mul_right (V₁ V₂ : ℝ) {b : ℝ} (hb : 0 < b) :
    (∑ z ∈ (shellZeros V₁ V₂).filter (fun z => b ≤ |z.re - 1 / 2|),
      ((analyticOrderAt xi z).toNat : ℝ)) =
      2 * ∑ z ∈ (shellZeros V₁ V₂).filter (fun z => 1 / 2 + b ≤ z.re),
        ((analyticOrderAt xi z).toNat : ℝ) := by
  classical
  set t := shellZeros V₁ V₂
  set m : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ)
  set A := t.filter (fun z => b ≤ |z.re - 1 / 2|)
  have hsplit := (Finset.sum_filter_add_sum_filter_not A (fun z => 1 / 2 ≤ z.re) m).symm
  have hR : A.filter (fun z => 1 / 2 ≤ z.re) = t.filter (fun z => 1 / 2 + b ≤ z.re) := by
    ext z
    simp only [A, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, habs⟩, hge⟩
      rw [abs_of_nonneg (by linarith)] at habs
      exact ⟨hz, by linarith⟩
    · rintro ⟨hz, hge⟩
      refine ⟨⟨hz, ?_⟩, by linarith⟩
      rw [abs_of_nonneg (by linarith)]; linarith
  have hL : A.filter (fun z => ¬ 1 / 2 ≤ z.re) = t.filter (fun z => z.re ≤ 1 / 2 - b) := by
    ext z
    simp only [A, Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hz, habs⟩, hlt⟩
      rw [abs_of_neg (by linarith)] at habs
      exact ⟨hz, by linarith⟩
    · rintro ⟨hz, hle⟩
      refine ⟨⟨hz, ?_⟩, by linarith⟩
      rw [abs_of_neg (by linarith)]; linarith
  have hbij : ∑ z ∈ t.filter (fun z => z.re ≤ 1 / 2 - b), m z =
      ∑ z ∈ t.filter (fun z => 1 / 2 + b ≤ z.re), m z := by
    refine Finset.sum_nbij' lineReflect lineReflect ?_ ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨lineReflect_mem_shellZeros hz.1, by rw [lineReflect_re]; linarith [hz.2]⟩
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨lineReflect_mem_shellZeros hz.1, by rw [lineReflect_re]; linarith [hz.2]⟩
    · intro z _; exact lineReflect_involutive z
    · intro z _; exact lineReflect_involutive z
    · intro z _; dsimp [m]; rw [xi_orderAt_lineReflect]
  change ∑ z ∈ A, m z = 2 * ∑ z ∈ t.filter (fun z => 1 / 2 + b ≤ z.re), m z
  rw [hsplit, hR, hL, hbij, two_mul]

private def toXiDivisorSupport (z : ℂ) (hz : xi z = 0) : XiDivisorSupport :=
  ⟨z, Function.mem_support.mpr (by
    rw [xi_divisor_apply_of_mem (Set.mem_univ z)]
    exact_mod_cast xi_order_toNat_ne_zero hz)⟩

private def liftToXiZeroCopy (S : Finset ℂ) (hS : ∀ z ∈ S, xi z = 0) : Finset XiZeroCopy :=
  S.attach.biUnion fun z =>
    (Finset.univ : Finset (Fin (Int.toNat (MeromorphicOn.divisor xi Set.univ
      (toXiDivisorSupport z.1 (hS z.1 z.2) : ℂ))))).image
      (fun i => (⟨toXiDivisorSupport z.1 (hS z.1 z.2), i⟩ : XiZeroCopy))

/-- Exact multiplicity-preserving lift of any finite set `S` of `ξ`-zeros to `Finset XiZeroCopy`. -/
private theorem sum_analyticOrder_eq_sum_liftToXiZeroCopy (S : Finset ℂ)
    (hS : ∀ z ∈ S, xi z = 0) (g : ℂ → ℝ) :
    ∑ z ∈ S, ((analyticOrderAt xi z).toNat : ℝ) * g z =
      ∑ q ∈ liftToXiZeroCopy S hS, g (q.1 : ℂ) := by
  classical
  unfold liftToXiZeroCopy
  have hdisj : Set.PairwiseDisjoint (S.attach : Set {z // z ∈ S})
      (fun z => (Finset.univ : Finset (Fin (Int.toNat (MeromorphicOn.divisor xi Set.univ
        (toXiDivisorSupport z.1 (hS z.1 z.2) : ℂ))))).image
        (fun i => (⟨toXiDivisorSupport z.1 (hS z.1 z.2), i⟩ : XiZeroCopy))) := by
    intro a _ b _ hab
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro q hqa hqb
    obtain ⟨ia, _, rfl⟩ := Finset.mem_image.mp hqa
    obtain ⟨ib, _, heq⟩ := Finset.mem_image.mp hqb
    have hval : a.1 = b.1 := congrArg (fun x : XiZeroCopy => (x.1 : ℂ)) heq.symm
    exact hab (Subtype.ext hval)
  rw [Finset.sum_biUnion hdisj, ← Finset.sum_attach S]
  refine Finset.sum_congr rfl fun z _ => ?_
  set ρ : XiDivisorSupport := toXiDivisorSupport z.1 (hS z.1 z.2)
  rw [Finset.sum_image fun _ _ _ _ hij => eq_of_heq (Sigma.mk.inj_iff.mp hij).2]
  have hconst : (∑ _i ∈ (Finset.univ : Finset (Fin (Int.toNat (MeromorphicOn.divisor xi Set.univ (ρ : ℂ))))),
      g (ρ : ℂ)) = (Int.toNat (MeromorphicOn.divisor xi Set.univ (ρ : ℂ)) : ℝ) * g (ρ : ℂ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst]
  have hρ_eq : (ρ : ℂ) = z.1 := rfl
  rw [hρ_eq, xi_divisor_apply_of_mem (Set.mem_univ z.1), Int.toNat_natCast]

private theorem mem_liftToXiZeroCopy_iff {S : Finset ℂ} {hS : ∀ z ∈ S, xi z = 0}
    {q : XiZeroCopy} :
    q ∈ liftToXiZeroCopy S hS → (q.1 : ℂ) ∈ S := by
  unfold liftToXiZeroCopy
  intro hq
  obtain ⟨z, _, hqi⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hqi
  exact z.2

/-- Total multiplicity on any short shell `V₂ - V₁ ≤ 2` (`0 ≤ V₁ ≤ V₂`) is `O(log(V₂ + 4))`. -/
theorem shortShell_orderSum_le_log {V₁ V₂ : ℝ} (hV₁ : 0 ≤ V₁) (h12 : V₁ ≤ V₂)
    (hlen : V₂ - V₁ ≤ 2) :
    ∑ z ∈ shellZeros V₁ V₂, ((analyticOrderAt xi z).toNat : ℝ) ≤
      16 * (|xiLineTwoLogDerivConstant| + Real.log (V₂ + 4)) := by
  have hxi : ∀ z ∈ shellZeros V₁ V₂, xi z = 0 := fun z hz =>
    (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1).2.2.2.2
  have hsum := sum_analyticOrder_eq_sum_liftToXiZeroCopy (shellZeros V₁ V₂) hxi (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at hsum
  rw [hsum]
  set mid : ℝ := (V₁ + V₂) / 2
  have hsub : (liftToXiZeroCopy (shellZeros V₁ V₂) hxi : Set XiZeroCopy) ⊆
      xiOrdinateWindow 1 mid := by
    intro q hq
    have hz : (q.1 : ℂ) ∈ shellZeros V₁ V₂ := mem_liftToXiZeroCopy_iff hq
    have him1 : V₁ < (q.1 : ℂ).im := (Finset.mem_filter.mp hz).2
    have him2 : (q.1 : ℂ).im ≤ V₂ := (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1).2.2.2.1
    rw [mem_xiOrdinateWindow_iff, abs_le]
    dsimp [mid]
    constructor <;> linarith
  have hncard := Set.ncard_le_ncard hsub (finite_xiOrdinateWindow 1 mid)
  rw [Set.ncard_coe_finset] at hncard
  have hcast : ((liftToXiZeroCopy (shellZeros V₁ V₂) hxi).card : ℝ) ≤
      ((xiOrdinateWindow 1 mid).ncard : ℝ) := by exact_mod_cast hncard
  have hwin := ncard_xiOrdinateWindow_one_le_log mid
  have habs_mid : |mid| ≤ V₂ := by
    rw [abs_of_nonneg (by dsimp [mid]; linarith)]
    dsimp [mid]; linarith
  have hlog_le : Real.log (|mid| + 4) ≤ Real.log (V₂ + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hconst_le : xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| := le_abs_self _
  linarith

/-- Shell-to-`windowZeros` comparison: every right-half zero in `shellZeros T₁ T₂` (`0 < T₁ ≤ T₂`)
with `1 / 2 + d ≤ z.re` lies in `(windowZeros T₁ T₂).filter (fun w => 1 / 2 + d ≤ w.re)` with the
same multiplicity. -/
private theorem shellRight_orderSum_le_windowZeros {T₁ T₂ d : ℝ} (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hd : 0 ≤ d) :
    (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re),
      ((analyticOrderAt xi z).toNat : ℝ)) ≤
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + d ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
  classical
  have hsub : (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re) ⊆
      (windowZeros T₁ T₂).filter (fun w => 1 / 2 + d ≤ w.re) := by
    intro z hz
    obtain ⟨hz_sh, hre_d⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz_pos, him1⟩ := Finset.mem_filter.mp hz_sh
    obtain ⟨h0, h1, _, him2, hxi⟩ := mem_stripFinsetPos.mp hz_pos
    rw [Finset.mem_filter, mem_windowZeros_iff hT₁ hT]
    refine ⟨⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, (xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mp hxi⟩,
      hre_d⟩
    · rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)]
      exact ⟨by linarith, by linarith⟩
    · rw [uIcc_of_le hT]
      exact ⟨him1.le, him2⟩
  calc ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re),
          ((analyticOrderAt xi z).toNat : ℝ)
      = ∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + d ≤ z.re),
          ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        obtain ⟨h0, h1, _, _, _⟩ :=
          mem_stripFinsetPos.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
        rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

/-! ## §4. Three-scale sieve-mollified shell collapse (`c' < 22 / 51`) and sub-power shell bound (`c' < 2 / 3`) -/

private theorem sum_range_pow_le_div {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∀ M : ℕ, ∑ j ∈ Finset.range M, r ^ j ≤ 1 / (1 - r)
  | 0 => by simp; exact div_nonneg zero_le_one (sub_nonneg.mpr hr1.le)
  | M + 1 => by
      rw [Finset.sum_range_succ']
      have ih := sum_range_pow_le_div hr0 hr1 M
      have hpos : 0 < 1 - r := by linarith
      calc ∑ k ∈ Finset.range M, r ^ (k + 1) + r ^ 0
          = r * (∑ k ∈ Finset.range M, r ^ k) + 1 := by
            rw [pow_zero, Finset.mul_sum]
            congr 1; refine Finset.sum_congr rfl fun k _ => pow_succ' r k
        _ ≤ r * (1 / (1 - r)) + 1 := add_le_add (mul_le_mul_of_nonneg_left ih hr0) le_rfl
        _ = 1 / (1 - r) := by field_simp; ring

private theorem slab_single_term_algebra {V S A K c' L_S lam r : ℝ} {m : ℕ}
    (hV_pos : 0 < V) (hS_pos : 0 < S) (hA : 0 < A) (hK : 0 ≤ K)
    (hc0 : 0 < c') (hc' : c' < 22 / 51) (hLS_eq : L_S = Real.log S) (hLS_pos : 0 < L_S)
    (hlam_eq : lam = (22 - 51 * c') / 25) (hr_eq : r = Real.exp (-(lam / 2)))
    (hm1 : 1 ≤ m) (hm_le_LS : (m : ℝ) ≤ L_S / 100) {W_m : ℝ}
    (hcount_m : W_m ≤ (L_S / (2 * Real.pi * (m : ℝ))) *
      (V * A * Real.exp (-(22 / 25 * (m : ℝ))) + K * L_S)) :
    (4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 *
      Real.exp ((51 / 25) * c' * ((m : ℝ) + 1))) * W_m ≤
      (64 * Real.exp 1 * A / lam) * c' ^ 2 * (V * L_S) * r ^ m +
        (16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 3 * S ^ (1 / 50 : ℝ) := by
  have hm1_r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hm_pos : 0 < (m : ℝ) := by linarith
  have hlam_pos : 0 < lam := by rw [hlam_eq]; linarith
  have hr_pos : 0 < r := by rw [hr_eq]; exact Real.exp_pos _
  have h51_50_sq : (4 : ℝ) * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 / (2 * Real.pi * (m : ℝ)) ≤
      16 * c' ^ 2 * (m : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hsq_m : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith [hm1_r]
    have h51 : (4 : ℝ) * (51 / 50) ^ 2 ≤ 6 := by norm_num
    have hlhs : 4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 =
        (4 * (51 / 50) ^ 2) * c' ^ 2 * ((m : ℝ) + 1) ^ 2 := by ring
    rw [hlhs]
    have hm_sq := mul_le_mul h51 hsq_m (sq_nonneg _) (by norm_num)
    have hm_c := mul_le_mul_of_nonneg_right hm_sq (sq_nonneg c')
    nlinarith [hm_c, sq_nonneg c', hm_pos]
  have hexp_prod : Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) * Real.exp (-(22 / 25 * (m : ℝ))) ≤
      Real.exp 1 * Real.exp (-(lam * (m : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [hlam_eq]; linarith
  have hm_exp : (m : ℝ) * Real.exp (-(lam * (m : ℝ))) ≤ (2 / lam) * r ^ m := by
    have h1 := Real.add_one_le_exp ((lam / 2) * (m : ℝ))
    have h2 : (lam / 2) * (m : ℝ) ≤ Real.exp ((lam / 2) * (m : ℝ)) := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(lam * (m : ℝ)))).le
    have hexp_half : Real.exp ((lam / 2) * (m : ℝ)) * Real.exp (-(lam * (m : ℝ))) = r ^ m := by
      rw [hr_eq, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 1; ring
    rw [hexp_half] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 / lam)
    have h5 : (2 / lam) * ((lam / 2) * (m : ℝ) * Real.exp (-(lam * (m : ℝ)))) =
        (m : ℝ) * Real.exp (-(lam * (m : ℝ))) := by
      calc (2 / lam) * ((lam / 2) * (m : ℝ) * Real.exp (-(lam * (m : ℝ))))
          = (m : ℝ) * Real.exp (-(lam * (m : ℝ))) * (lam / lam) := by ring
        _ = (m : ℝ) * Real.exp (-(lam * (m : ℝ))) := by rw [div_self hlam_pos.ne', mul_one]
    rwa [h5] at h4
  have hmain_part : (16 * c' ^ 2 * (m : ℝ)) * L_S *
      (Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) * (V * A * Real.exp (-(22 / 25 * (m : ℝ))))) ≤
      (64 * Real.exp 1 * A / lam) * c' ^ 2 * (V * L_S) * r ^ m := by
    have h1 : Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) * (V * A * Real.exp (-(22 / 25 * (m : ℝ)))) =
        V * A * (Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) * Real.exp (-(22 / 25 * (m : ℝ)))) := by
      ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hexp_prod (by positivity : 0 ≤ V * A)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (16 * c' ^ 2 * (m : ℝ)) * L_S)
    have h4 : (16 * c' ^ 2 * (m : ℝ)) * L_S * (V * A * (Real.exp 1 * Real.exp (-(lam * (m : ℝ))))) =
        (16 * Real.exp 1 * A * c' ^ 2 * (V * L_S)) * ((m : ℝ) * Real.exp (-(lam * (m : ℝ)))) := by
      ring
    rw [h4] at h3
    have h5 := h3.trans (mul_le_mul_of_nonneg_left hm_exp
      (by positivity : 0 ≤ 16 * Real.exp 1 * A * c' ^ 2 * (V * L_S)))
    have h6 : (16 * Real.exp 1 * A * c' ^ 2 * (V * L_S)) * ((2 / lam) * r ^ m) ≤
        (64 * Real.exp 1 * A / lam) * c' ^ 2 * (V * L_S) * r ^ m := by
      have h32 : (16 * Real.exp 1 * A * c' ^ 2 * (V * L_S)) * ((2 / lam) * r ^ m) =
          32 * (Real.exp 1 * A / lam * c' ^ 2 * (V * L_S) * r ^ m) := by ring
      have h64 : (64 * Real.exp 1 * A / lam) * c' ^ 2 * (V * L_S) * r ^ m =
          64 * (Real.exp 1 * A / lam * c' ^ 2 * (V * L_S) * r ^ m) := by ring
      have hnn : 0 ≤ Real.exp 1 * A / lam * c' ^ 2 * (V * L_S) * r ^ m := by positivity
      linarith
    exact h5.trans h6
  have herr_part : (16 * c' ^ 2 * (m : ℝ)) * L_S *
      (Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) * (K * L_S)) ≤
      (16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 3 * S ^ (1 / 50 : ℝ) := by
    have hm_le_L : (m : ℝ) ≤ L_S := by linarith
    have hexp_S : Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) ≤
        Real.exp 2 * S ^ (1 / 50 : ℝ) := by
      have harg : (51 / 25) * c' * ((m : ℝ) + 1) ≤ 2 + (1 / 50) * L_S := by
        have hc_half : (51 / 25) * c' ≤ 1 := by linarith
        have hm_100 : (51 / 25) * c' * (m : ℝ) ≤ 1 * (L_S / 100) :=
          mul_le_mul hc_half hm_le_LS hm_pos.le zero_le_one
        linarith
      calc Real.exp ((51 / 25) * c' * ((m : ℝ) + 1))
          ≤ Real.exp (2 + (1 / 50) * L_S) := Real.exp_le_exp.mpr harg
        _ = Real.exp 2 * Real.exp ((1 / 50) * L_S) := Real.exp_add _ _
        _ = Real.exp 2 * S ^ (1 / 50 : ℝ) := by
            rw [hLS_eq, Real.rpow_def_of_pos hS_pos, mul_comm]
    calc (16 * c' ^ 2 * (m : ℝ)) * L_S *
            (Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) * (K * L_S))
        ≤ (16 * c' ^ 2 * L_S) * L_S * ((Real.exp 2 * S ^ (1 / 50 : ℝ)) * (K * L_S)) := by
          refine mul_le_mul
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_le_L (by positivity))
              hLS_pos.le)
            (mul_le_mul_of_nonneg_right hexp_S (by positivity))
            (by positivity) (by positivity)
      _ = (16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 3 * S ^ (1 / 50 : ℝ) := by ring
  calc (4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 *
          Real.exp ((51 / 25) * c' * ((m : ℝ) + 1))) * W_m
      ≤ (4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 / (2 * Real.pi * (m : ℝ))) * L_S *
          (Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) *
            (V * A * Real.exp (-(22 / 25 * (m : ℝ))) + K * L_S)) := by
        have hm_w := mul_le_mul_of_nonneg_left hcount_m
          (by positivity : 0 ≤ 4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 *
            Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)))
        exact hm_w.trans_eq (by ring)
    _ ≤ (16 * c' ^ 2 * (m : ℝ)) * L_S *
          (Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) *
            (V * A * Real.exp (-(22 / 25 * (m : ℝ))) + K * L_S)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h51_50_sq hLS_pos.le)
          (by positivity)
    _ = (16 * c' ^ 2 * (m : ℝ)) * L_S *
          (Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) *
            (V * A * Real.exp (-(22 / 25 * (m : ℝ))))) +
        (16 * c' ^ 2 * (m : ℝ)) * L_S *
          (Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)) * (K * L_S)) := by ring
    _ ≤ _ := add_le_add hmain_part herr_part

/-- Master Scale-II Barban–Vehov slab summation starting at any integer slab `m₀ ≥ 1`:
bounds the intermediate near-line region `(51/50) m₀ / log S ≤ z.re - 1/2 < (51/50) N_S / log S`
by a geometric tail `r^{m₀} / (1 - r)` times `c'² * V * log S` plus `O(c'² (log S)⁴ S^{1/50})`. -/
private theorem scaleII_barbanVehov_slab_sum_le {V S A K c' L T₁ T₂ L_S lam r : ℝ} {N_S m₀ : ℕ}
    (hV4 : 4 ≤ V) (hS_eq : S = (3 / 2) * V) (hA : 0 < A) (hK : 0 ≤ K)
    (hc0 : 0 < c') (hc' : c' < 22 / 51) (hL0 : 0 ≤ L) (hL : L ≤ c' * L_S)
    (hT₁ : T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1))
    (hT₂ : T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3))
    (hLS_eq : L_S = Real.log S) (hNS_eq : N_S = ⌊L_S / 100⌋₊)
    (hlam_eq : lam = (22 - 51 * c') / 25) (hr_eq : r = Real.exp (-(lam / 2)))
    (hLS200 : 200 ≤ L_S)
    (hbv : ∀ a : ℝ, 1 ≤ a → a ≤ L_S / 100 →
      2 * Real.pi * ((a / L_S) *
        ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 51 / 50 * (a / L_S) ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
        (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L_S)
    (hm₀ : 1 ≤ m₀) :
    (∑ z ∈ (shellZeros T₁ T₂).filter (fun z =>
        (51 / 50) * ((m₀ : ℝ) / L_S) ≤ z.re - 1 / 2 ∧
          z.re - 1 / 2 < (51 / 50) * ((N_S : ℝ) / L_S)),
      ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)) ≤
      (64 * Real.exp 1 * A / (lam * (1 - r))) * c' ^ 2 * r ^ m₀ * (V * L_S) +
        (16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 4 * S ^ (1 / 50 : ℝ) := by
  classical
  have hV_pos : 0 < V := by linarith
  have hLS_pos : 0 < L_S := by linarith
  have hS_pos : 0 < S := by rw [hS_eq]; linarith
  have hT₁_pos : 0 < T₁ := by rw [hS_eq] at hT₁; linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by rw [hS_eq] at hT₁ hT₂; linarith [hT₁.2, hT₂.1]
  have hT_len : T₂ - T₁ ≤ V := by rw [hS_eq] at hT₁ hT₂; linarith [hT₁.1, hT₂.2]
  have hlam_pos : 0 < lam := by rw [hlam_eq]; linarith
  have hr_pos : 0 < r := by rw [hr_eq]; exact Real.exp_pos _
  have hr_lt1 : r < 1 := by rw [hr_eq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  let R_mid := (shellZeros T₁ T₂).filter (fun z =>
    (51 / 50) * ((m₀ : ℝ) / L_S) ≤ z.re - 1 / 2 ∧
      z.re - 1 / 2 < (51 / 50) * ((N_S : ℝ) / L_S))
  have hptw_slab : ∀ z ∈ R_mid,
      ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
        ∑ m ∈ Finset.Ico m₀ N_S,
          if (51 / 50) * ((m : ℝ) / L_S) ≤ z.re - 1 / 2 then
            ((analyticOrderAt xi z).toNat : ℝ) *
              (4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 *
                Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)))
          else 0 := by
    intro z hz
    obtain ⟨_, hlo_z, hhi_z⟩ := Finset.mem_filter.mp hz
    set δ : ℝ := z.re - 1 / 2
    set x_z : ℝ := (50 / 51) * L_S * δ
    have hx_ge : (m₀ : ℝ) ≤ x_z := by
      dsimp [x_z, δ]
      have hm1 := mul_le_mul_of_nonneg_left hlo_z (by positivity : 0 ≤ (50 / 51) * L_S)
      have hsimp : (50 / 51) * L_S * ((51 / 50) * ((m₀ : ℝ) / L_S)) = (m₀ : ℝ) := by
        calc (50 / 51) * L_S * ((51 / 50) * ((m₀ : ℝ) / L_S))
            = (m₀ : ℝ) * (L_S / L_S) := by ring
          _ = (m₀ : ℝ) := by rw [div_self hLS_pos.ne', mul_one]
      rwa [hsimp] at hm1
    have hx_lt : x_z < (N_S : ℝ) := by
      dsimp [x_z, δ]
      have hm1 := mul_lt_mul_of_pos_left hhi_z (by positivity : 0 < (50 / 51) * L_S)
      have hsimp : (50 / 51) * L_S * ((51 / 50) * ((N_S : ℝ) / L_S)) = (N_S : ℝ) := by
        calc (50 / 51) * L_S * ((51 / 50) * ((N_S : ℝ) / L_S))
            = (N_S : ℝ) * (L_S / L_S) := by ring
          _ = (N_S : ℝ) := by rw [div_self hLS_pos.ne', mul_one]
      rwa [hsimp] at hm1
    have hx_nn : 0 ≤ x_z := (Nat.cast_nonneg m₀).trans hx_ge
    set j : ℕ := ⌊x_z⌋₊
    have hj_lo : m₀ ≤ j := Nat.le_floor hx_ge
    have hj_hi : j < N_S := by
      have hj_le : (j : ℝ) ≤ x_z := Nat.floor_le hx_nn
      exact_mod_cast hj_le.trans_lt hx_lt
    have hj_mem : j ∈ Finset.Ico m₀ N_S := Finset.mem_Ico.mpr ⟨hj_lo, hj_hi⟩
    have hδ_lo : (51 / 50) * ((j : ℝ) / L_S) ≤ δ := by
      have hj_le : (j : ℝ) ≤ (50 / 51) * L_S * δ := Nat.floor_le hx_nn
      have hm1 := mul_le_mul_of_nonneg_left hj_le (by positivity : 0 ≤ (51 / 50) / L_S)
      have hsimp1 : ((51 / 50) / L_S) * ((50 / 51) * L_S * δ) = δ := by
        calc ((51 / 50) / L_S) * ((50 / 51) * L_S * δ) = δ * (L_S / L_S) := by ring
          _ = δ := by rw [div_self hLS_pos.ne', mul_one]
      have hsimp2 : ((51 / 50) / L_S) * (j : ℝ) = (51 / 50) * ((j : ℝ) / L_S) := by ring
      rwa [hsimp2, hsimp1] at hm1
    have hδ_hi : δ ≤ (51 / 50) * (((j : ℝ) + 1) / L_S) := by
      have hj_lt : (50 / 51) * L_S * δ ≤ (j : ℝ) + 1 := (Nat.lt_floor_add_one x_z).le
      have hm1 := mul_le_mul_of_nonneg_left hj_lt (by positivity : 0 ≤ (51 / 50) / L_S)
      have hsimp1 : ((51 / 50) / L_S) * ((50 / 51) * L_S * δ) = δ := by
        calc ((51 / 50) / L_S) * ((50 / 51) * L_S * δ) = δ * (L_S / L_S) := by ring
          _ = δ := by rw [div_self hLS_pos.ne', mul_one]
      have hsimp2 : ((51 / 50) / L_S) * ((j : ℝ) + 1) = (51 / 50) * (((j : ℝ) + 1) / L_S) := by ring
      rwa [hsimp1, hsimp2] at hm1
    have hδ_pos : 0 < δ := lt_of_lt_of_le (by positivity) hlo_z
    have hLδ : L * |δ| ≤ (51 / 50) * c' * ((j : ℝ) + 1) := by
      rw [abs_of_pos hδ_pos]
      calc L * δ ≤ (c' * L_S) * ((51 / 50) * (((j : ℝ) + 1) / L_S)) :=
            mul_le_mul hL hδ_hi hδ_pos.le (by positivity)
        _ = (51 / 50) * c' * ((j : ℝ) + 1) * (L_S / L_S) := by ring
        _ = (51 / 50) * c' * ((j : ℝ) + 1) := by rw [div_self hLS_pos.ne', mul_one]
    have hdk_j : depthKernel L δ ≤
        4 * ((51 / 50) * c' * ((j : ℝ) + 1)) ^ 2 *
          Real.exp ((51 / 25) * c' * ((j : ℝ) + 1)) := by
      refine (depthKernel_le_four_sq_mul_exp hL0).trans ?_
      have hsq : (L * |δ|) ^ 2 ≤ ((51 / 50) * c' * ((j : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hLδ 2
      have hexp : Real.exp (2 * L * |δ|) ≤ Real.exp ((51 / 25) * c' * ((j : ℝ) + 1)) :=
        Real.exp_le_exp.mpr (by linarith)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) hexp
        (Real.exp_pos _).le (by positivity)
    set f_term : ℕ → ℝ := fun m =>
      if (51 / 50) * ((m : ℝ) / L_S) ≤ δ then
        ((analyticOrderAt xi z).toNat : ℝ) *
          (4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 *
            Real.exp ((51 / 25) * c' * ((m : ℝ) + 1)))
      else 0
    have hfj : ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L δ ≤ f_term j := by
      dsimp [f_term]; rw [if_pos hδ_lo]
      exact mul_le_mul_of_nonneg_left hdk_j (Nat.cast_nonneg _)
    exact hfj.trans (Finset.single_le_sum (f := f_term)
      (fun m _ => by dsimp [f_term]; split_ifs <;> positivity) hj_mem)
  have hswap : (∑ z ∈ R_mid, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)) ≤
      ∑ m ∈ Finset.Ico m₀ N_S,
        (4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 *
          Real.exp ((51 / 25) * c' * ((m : ℝ) + 1))) *
          (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + (51 / 50) * ((m : ℝ) / L_S) ≤ z.re),
            ((analyticOrderAt xi z).toNat : ℝ)) := by
    refine (Finset.sum_le_sum hptw_slab).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun m _ => ?_
    set W_m : ℝ := 4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 *
      Real.exp ((51 / 25) * c' * ((m : ℝ) + 1))
    have hW_nn : 0 ≤ W_m := by dsimp [W_m]; positivity
    have h1 : (∑ z ∈ R_mid, if (51 / 50) * ((m : ℝ) / L_S) ≤ z.re - 1 / 2 then
          ((analyticOrderAt xi z).toNat : ℝ) * W_m else 0) =
        W_m * ∑ z ∈ R_mid.filter (fun z => (51 / 50) * ((m : ℝ) / L_S) ≤ z.re - 1 / 2),
          ((analyticOrderAt xi z).toNat : ℝ) := by
      rw [← Finset.sum_filter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => mul_comm _ _
    rw [h1]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_
      fun _ _ _ => Nat.cast_nonneg _) hW_nn
    intro z hz
    obtain ⟨hz_mid, hm_le⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz_mid).1, by linarith⟩
  have hslab_m : ∀ m ∈ Finset.Ico m₀ N_S,
      (4 * ((51 / 50) * c' * ((m : ℝ) + 1)) ^ 2 *
        Real.exp ((51 / 25) * c' * ((m : ℝ) + 1))) *
        (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => 1 / 2 + (51 / 50) * ((m : ℝ) / L_S) ≤ z.re),
          ((analyticOrderAt xi z).toNat : ℝ)) ≤
        (64 * Real.exp 1 * A / lam) * c' ^ 2 * (V * L_S) * r ^ m +
          (16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 3 * S ^ (1 / 50 : ℝ) := by
    intro m hm
    obtain ⟨hm_ge, hm_lt⟩ := Finset.mem_Ico.mp hm
    have hm1 : 1 ≤ m := hm₀.trans hm_ge
    have hm1_r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hm_pos : 0 < (m : ℝ) := by linarith
    have hm_le_LS : (m : ℝ) ≤ L_S / 100 := by
      have hlt_N : (m : ℝ) < (N_S : ℝ) := by exact_mod_cast hm_lt
      rw [hNS_eq] at hlt_N
      exact hlt_N.le.trans (Nat.floor_le (by positivity))
    have hbv_m := hbv (m : ℝ) hm1_r hm_le_LS
    have hsh_win := shellRight_orderSum_le_windowZeros
      (d := (51 / 50) * ((m : ℝ) / L_S)) hT₁_pos hT12 (by positivity)
    have hcount_m : (∑ z ∈ (shellZeros T₁ T₂).filter
          (fun z => 1 / 2 + (51 / 50) * ((m : ℝ) / L_S) ≤ z.re),
          ((analyticOrderAt xi z).toNat : ℝ)) ≤
        (L_S / (2 * Real.pi * (m : ℝ))) *
          (V * A * Real.exp (-(22 / 25 * (m : ℝ))) + K * L_S) := by
      have h1 := hbv_m.trans
        (add_le_add (mul_le_mul_of_nonneg_right hT_len (by positivity)) le_rfl)
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ L_S / (2 * Real.pi * (m : ℝ)))
      set W_z := ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 51 / 50 * ((m : ℝ) / L_S) ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ)
      have hcancel : (L_S / (2 * Real.pi * (m : ℝ))) * (2 * Real.pi * (((m : ℝ) / L_S) * W_z)) =
          W_z := by
        calc (L_S / (2 * Real.pi * (m : ℝ))) * (2 * Real.pi * (((m : ℝ) / L_S) * W_z))
            = W_z * ((2 * Real.pi * (m : ℝ)) / (2 * Real.pi * (m : ℝ))) * (L_S / L_S) := by ring
          _ = W_z := by rw [div_self (by positivity), div_self hLS_pos.ne', mul_one, mul_one]
      rw [hcancel, ← mul_assoc V A] at h2
      exact hsh_win.trans h2
    exact slab_single_term_algebra hV_pos hS_pos hA hK hc0 hc' hLS_eq hLS_pos hlam_eq hr_eq
      hm1 hm_le_LS hcount_m
  refine hswap.trans ((Finset.sum_le_sum hslab_m).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hgeom : ∑ m ∈ Finset.Ico m₀ N_S, r ^ m ≤ r ^ m₀ / (1 - r) := by
    by_cases hle : m₀ ≤ N_S
    · rw [Finset.sum_Ico_eq_sum_range]
      have hfactor : ∑ k ∈ Finset.range (N_S - m₀), r ^ (m₀ + k) =
          r ^ m₀ * ∑ k ∈ Finset.range (N_S - m₀), r ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => pow_add r m₀ k
      rw [hfactor, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (sum_range_pow_le_div hr_pos.le hr_lt1 _)
        (pow_nonneg hr_pos.le _)
    · rw [Finset.Ico_eq_empty hle, Finset.sum_empty]
      exact div_nonneg (pow_nonneg hr_pos.le _) (sub_nonneg.mpr hr_lt1.le)
  have hcard_le : ((Finset.Ico m₀ N_S).card : ℝ) ≤ L_S := by
    have h1 : (Finset.Ico m₀ N_S).card ≤ N_S := by rw [Nat.card_Ico]; omega
    have h2 : (N_S : ℝ) ≤ L_S / 100 := by rw [hNS_eq]; exact Nat.floor_le (by positivity)
    have h3 : ((Finset.Ico m₀ N_S).card : ℝ) ≤ (N_S : ℝ) := by exact_mod_cast h1
    linarith
  have hm_geom : (64 * Real.exp 1 * A / lam) * c' ^ 2 * (V * L_S) *
      (∑ m ∈ Finset.Ico m₀ N_S, r ^ m) ≤
      (64 * Real.exp 1 * A / (lam * (1 - r))) * c' ^ 2 * r ^ m₀ * (V * L_S) := by
    calc (64 * Real.exp 1 * A / lam) * c' ^ 2 * (V * L_S) * (∑ m ∈ Finset.Ico m₀ N_S, r ^ m)
        ≤ (64 * Real.exp 1 * A / lam) * c' ^ 2 * (V * L_S) * (r ^ m₀ / (1 - r)) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = (64 * Real.exp 1 * A / (lam * (1 - r))) * c' ^ 2 * r ^ m₀ * (V * L_S) := by
          rw [div_eq_mul_inv (64 * Real.exp 1 * A) (lam * (1 - r)), mul_inv,
            div_eq_mul_inv _ lam, div_eq_mul_inv _ (1 - r)]
          ring
  have hm_err : ((Finset.Ico m₀ N_S).card : ℝ) *
      ((16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 3 * S ^ (1 / 50 : ℝ)) ≤
      (16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 4 * S ^ (1 / 50 : ℝ) := by
    calc ((Finset.Ico m₀ N_S).card : ℝ) *
            ((16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 3 * S ^ (1 / 50 : ℝ))
        ≤ L_S * ((16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 3 * S ^ (1 / 50 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = (16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 4 * S ^ (1 / 50 : ℝ) := by ring
  exact add_le_add hm_geom hm_err

/-- Reusable short-shell `V^{3/4}` bound when `0 ≤ L ≤ (1 / 2) * Real.log V` (`16 ≤ V`). -/
private theorem shortCap_shellDepthSum_le_rpow {V W₁ W₂ L K_log3 : ℝ}
    (hV16 : 16 ≤ V) (hW₁ : 0 ≤ W₁) (h12 : W₁ ≤ W₂) (hlen : W₂ - W₁ ≤ 2) (hW₂ : W₂ ≤ 2 * V)
    (hL0 : 0 ≤ L) (hL : L ≤ (1 / 2) * Real.log V)
    (hlog3 : ∀ x : ℝ, 1 ≤ x → (1 + Real.log x) ^ 3 ≤ K_log3 * x ^ (1 / 4 : ℝ)) :
    shellDepthSum W₁ W₂ L ≤
      32 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) := by
  have hV_pos : 0 < V := by linarith
  have hlogV_ge2 : 2 ≤ Real.log V := two_le_log_of_sixteen_le hV16
  have hdk_cap : ∀ z : ℂ, |z.re - 1 / 2| ≤ 1 / 2 →
      depthKernel L (z.re - 1 / 2) ≤ (Real.log V) ^ 2 * V ^ (1 / 2 : ℝ) := by
    intro z hz
    have h1 := depthKernel_le_four_sq_mul_exp (d := z.re - 1 / 2) hL0
    have hLd : L * |z.re - 1 / 2| ≤ (1 / 2) * Real.log V := by
      nlinarith [hL, hz, abs_nonneg (z.re - 1 / 2), hlogV_ge2]
    have hsq : 4 * (L * |z.re - 1 / 2|) ^ 2 ≤ (Real.log V) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hLd 2
      linarith
    have hexp : Real.exp (2 * L * |z.re - 1 / 2|) ≤ V ^ (1 / 2 : ℝ) := by
      have h2Ld : 2 * L * |z.re - 1 / 2| ≤ (1 / 2) * Real.log V := by
        nlinarith [hL, hz, abs_nonneg (z.re - 1 / 2), hlogV_ge2]
      calc Real.exp (2 * L * |z.re - 1 / 2|)
          ≤ Real.exp ((1 / 2) * Real.log V) := Real.exp_le_exp.mpr h2Ld
        _ = V ^ (1 / 2 : ℝ) := by rw [Real.rpow_def_of_pos hV_pos, mul_comm]
    exact h1.trans (mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg _))
  have hord := (shortShell_orderSum_le_log hW₁ h12 hlen).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (Real.log_le_log (by linarith) (by linarith : W₂ + 4 ≤ 2 * V + 4))) (by norm_num))
  have hlog2V4 : Real.log (2 * V + 4) ≤ 3 + Real.log V := by
    calc Real.log (2 * V + 4) ≤ Real.log (4 * V) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 4 + Real.log V := Real.log_mul (by norm_num) hV_pos.ne'
      _ ≤ 3 + Real.log V := by linarith [log_four_le_two]
  have hsh_raw : shellDepthSum W₁ W₂ L ≤
      16 * (|xiLineTwoLogDerivConstant| + Real.log (2 * V + 4)) *
        ((Real.log V) ^ 2 * V ^ (1 / 2 : ℝ)) := by
    unfold shellDepthSum
    calc ∑ z ∈ shellZeros W₁ W₂, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
        ≤ ∑ z ∈ shellZeros W₁ W₂,
            ((analyticOrderAt xi z).toNat : ℝ) * ((Real.log V) ^ 2 * V ^ (1 / 2 : ℝ)) := by
          refine Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hdk_cap z ?_)
            (Nat.cast_nonneg _)
          obtain ⟨h0, h1, _, _, _⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1
          rw [abs_le]; constructor <;> linarith
      _ = (∑ z ∈ shellZeros W₁ W₂, ((analyticOrderAt xi z).toNat : ℝ)) *
            ((Real.log V) ^ 2 * V ^ (1 / 2 : ℝ)) := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hord (by positivity)
  have hfactor : (|xiLineTwoLogDerivConstant| + Real.log (2 * V + 4)) * (Real.log V) ^ 2 ≤
      2 * (|xiLineTwoLogDerivConstant| + 4) * (1 + Real.log V) ^ 3 := by
    nlinarith [abs_nonneg xiLineTwoLogDerivConstant, hlogV_ge2, hlog2V4]
  have hpow_le := hlog3 V (by linarith)
  have hV_add : V ^ (1 / 4 : ℝ) * V ^ (1 / 2 : ℝ) = V ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hV_pos]; norm_num
  calc shellDepthSum W₁ W₂ L
      ≤ 16 * ((|xiLineTwoLogDerivConstant| + Real.log (2 * V + 4)) * (Real.log V) ^ 2) *
          V ^ (1 / 2 : ℝ) := hsh_raw.trans_eq (by ring)
    _ ≤ 16 * (2 * (|xiLineTwoLogDerivConstant| + 4) * (K_log3 * V ^ (1 / 4 : ℝ))) *
          V ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (hfactor.trans (mul_le_mul_of_nonneg_left hpow_le (by positivity))) (by norm_num))
          (Real.rpow_nonneg hV_pos.le _)
    _ = 32 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 *
          (V ^ (1 / 4 : ℝ) * V ^ (1 / 2 : ℝ)) := by ring
    _ = 32 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) := by rw [hV_add]

/-- Scale-I near-line shell bound (`0 < z.re - 1/2 < (51/50) / L_S`) via Selberg's `Λ²` first moment. -/
private theorem scaleI_near_shell_sum_le {V T₁ T₂ L L_S c' : ℝ}
    (hV_pos : 0 < V) (hT₂2V : T₂ ≤ 2 * V)
    (hc0 : 0 < c') (hc' : c' < 22 / 51)
    (hLS_pos : 0 < L_S) (hLS_le : L_S ≤ 2 * Real.log V)
    (hL0 : 0 ≤ L) (hL_le_LS : L ≤ c' * L_S)
    (hm1_V : offLineMoment (2 * V) ≤ 17 / 100 * (2 * V)) :
    2 * (∑ z ∈ ((shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re)).filter
          (fun z => z.re - 1 / 2 < (51 / 50) * (1 / L_S)),
        ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)) ≤
      (16 * Real.exp 2) * c' ^ 2 * V * Real.log V := by
  classical
  let R₁ := ((shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re)).filter
    (fun z => z.re - 1 / 2 < (51 / 50) * (1 / L_S))
  have hptwI : ∀ z ∈ R₁,
      ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
        (8 * Real.exp 2 * c' ^ 2 * L_S) *
          (((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2)) := by
    intro z hz
    obtain ⟨hzR, hlt_b1⟩ := Finset.mem_filter.mp hz
    have hre_gt : 1 / 2 < z.re := (Finset.mem_filter.mp hzR).2
    set δ : ℝ := z.re - 1 / 2
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    have hLδ_c : L * δ ≤ (51 / 50) * c' := by
      calc L * δ ≤ (c' * L_S) * ((51 / 50) * (1 / L_S)) :=
            mul_le_mul hL_le_LS hlt_b1.le hδ_pos.le (by positivity)
        _ = (51 / 50) * c' * (L_S / L_S) := by ring
        _ = (51 / 50) * c' := by rw [div_self hLS_pos.ne', mul_one]
    have hLδ_lt1 : L * δ ≤ 1 := by linarith
    have hsq_le : (L * δ) ^ 2 ≤ (2 * c' ^ 2 * L_S) * δ := by
      have hprod : L * (L * δ) ≤ (c' * L_S) * ((51 / 50) * c') :=
        mul_le_mul hL_le_LS hLδ_c (mul_nonneg hL0 hδ_pos.le) (by positivity)
      have hm := mul_le_mul_of_nonneg_right hprod hδ_pos.le
      have hcoef : (c' * L_S) * ((51 / 50) * c') * δ ≤ (2 * c' ^ 2 * L_S) * δ := by
        have hnn : 0 ≤ c' ^ 2 * L_S * δ := by positivity
        nlinarith
      nlinarith
    have hdk_I : depthKernel L δ ≤ (8 * Real.exp 2 * c' ^ 2 * L_S) * δ := by
      have h1 := depthKernel_le_four_sq_mul_exp (d := δ) hL0
      rw [abs_of_pos hδ_pos] at h1
      have hexp_le : Real.exp (2 * L * δ) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
      have hm := mul_le_mul (mul_le_mul_of_nonneg_left hsq_le (by norm_num : (0 : ℝ) ≤ 4))
        hexp_le (Real.exp_pos _).le (by positivity)
      linarith
    exact (mul_le_mul_of_nonneg_left hdk_I (Nat.cast_nonneg _)).trans_eq (by ring)
  have hsub_box : R₁ ⊆ boxFinsetLe (2 * V) := by
    intro z hz
    obtain ⟨hzR, _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz_sh, hre_gt⟩ := Finset.mem_filter.mp hzR
    obtain ⟨_, hre_lt, him_pos, him_le, hxi⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1
    exact mem_boxFinsetLe.mpr ⟨hre_gt, hre_lt, him_pos.le, him_le.trans hT₂2V, hxi⟩
  have hsum_box : ∑ z ∈ R₁, (((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2)) ≤
      offLineMoment (2 * V) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub_box fun z hz _ => offLineMoment_term_nonneg hz
  have hsumI : ∑ z ∈ R₁, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      (8 * Real.exp 2 * c' ^ 2 * L_S) * offLineMoment (2 * V) := by
    refine (Finset.sum_le_sum hptwI).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum_box (by positivity)
  have hlogV_nn : 0 ≤ Real.log V := by
    have := offLineMoment_nonneg (2 * V)
    nlinarith [hLS_pos, hLS_le]
  calc 2 * ∑ z ∈ R₁, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
      ≤ 2 * ((8 * Real.exp 2 * c' ^ 2 * L_S) * offLineMoment (2 * V)) :=
        mul_le_mul_of_nonneg_left hsumI zero_le_two
    _ ≤ 2 * ((8 * Real.exp 2 * c' ^ 2 * (2 * Real.log V)) * (17 / 100 * (2 * V))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul
          (mul_le_mul_of_nonneg_left hLS_le (by positivity))
          hm1_V (offLineMoment_nonneg _) (by positivity)) zero_le_two
    _ = (544 / 50 : ℝ) * (Real.exp 2 * c' ^ 2 * V * Real.log V) := by ring
    _ ≤ 16 * (Real.exp 2 * c' ^ 2 * V * Real.log V) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (16 * Real.exp 2) * c' ^ 2 * V * Real.log V := by ring

/-- Scale-III deep shell bound (`1 / 2 + 1 / 200 ≤ z.re`) via `liftToXiZeroCopy`. -/
private theorem scaleIII_deep_shell_sum_le (R_deep : Finset ℂ) {V T₁ T₂ L C_deep γ₀ : ℝ}
    (hV_pos : 0 < V) (hVT₁ : V ≤ T₁) (hT₂2V : T₂ ≤ 2 * V) (hL0 : 0 ≤ L)
    (hsub : R_deep ⊆ shellZeros T₁ T₂)
    (hre : ∀ z ∈ R_deep, 1 / 2 + 1 / 200 ≤ z.re)
    (hdeep_V : ∀ G : Finset XiZeroCopy,
      (∀ q ∈ G, 1 / 2 + 1 / 200 ≤ foldedRe q ∧ V ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * V) →
      (1 / V) * ∑ q ∈ G, Real.exp (2 * L * (foldedRe q - 1 / 2)) ≤ C_deep * V ^ (-γ₀)) :
    2 * ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      2 * (C_deep * V ^ (1 - γ₀)) := by
  have hxi : ∀ z ∈ R_deep, xi z = 0 := fun z hz =>
    (mem_stripFinsetPos.mp (Finset.mem_filter.mp (hsub hz)).1).2.2.2.2
  have hptw : ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * Real.exp (2 * L * (z.re - 1 / 2)) := by
    refine Finset.sum_le_sum fun z hz => ?_
    have hge := hre z hz
    have hdk := depthKernel_le_exp_two_mul (d := z.re - 1 / 2) hL0
    rw [abs_of_pos (by linarith)] at hdk
    exact mul_le_mul_of_nonneg_left hdk (Nat.cast_nonneg _)
  have hfold_eq : ∑ q ∈ liftToXiZeroCopy R_deep hxi, Real.exp (2 * L * ((q.1 : ℂ).re - 1 / 2)) =
      ∑ q ∈ liftToXiZeroCopy R_deep hxi, Real.exp (2 * L * (foldedRe q - 1 / 2)) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hge := hre (q.1 : ℂ) (mem_liftToXiZeroCopy_iff hq)
    rw [show foldedRe q = (q.1 : ℂ).re from max_eq_left (by linarith)]
  have hG_cond : ∀ q ∈ liftToXiZeroCopy R_deep hxi,
      1 / 2 + 1 / 200 ≤ foldedRe q ∧ V ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * V := by
    intro q hq
    have hz_mem : (q.1 : ℂ) ∈ R_deep := mem_liftToXiZeroCopy_iff hq
    have hge := hre (q.1 : ℂ) hz_mem
    have hz_sh := hsub hz_mem
    have him1 : T₁ < (q.1 : ℂ).im := (Finset.mem_filter.mp hz_sh).2
    have him2 : (q.1 : ℂ).im ≤ T₂ := (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1).2.2.2.1
    rw [abs_of_pos (by linarith)]
    exact ⟨le_trans hge (le_max_left _ _), by linarith, by linarith⟩
  have hm_V := mul_le_mul_of_nonneg_left (hdeep_V (liftToXiZeroCopy R_deep hxi) hG_cond) hV_pos.le
  have hlhs : V * ((1 / V) * ∑ q ∈ liftToXiZeroCopy R_deep hxi,
      Real.exp (2 * L * (foldedRe q - 1 / 2))) =
      ∑ q ∈ liftToXiZeroCopy R_deep hxi, Real.exp (2 * L * (foldedRe q - 1 / 2)) := by
    field_simp
  have hrhs : V * (C_deep * V ^ (-γ₀)) = C_deep * V ^ (1 - γ₀) := by
    calc V * (C_deep * V ^ (-γ₀))
        = C_deep * (V ^ (1 : ℝ) * V ^ (-γ₀)) := by rw [Real.rpow_one]; ring
      _ = C_deep * V ^ (1 - γ₀) := by rw [← Real.rpow_add hV_pos]; ring_nf
  rw [hlhs, hrhs] at hm_V
  have hchain : ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      C_deep * V ^ (1 - γ₀) :=
    calc ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
        ≤ ∑ z ∈ R_deep, ((analyticOrderAt xi z).toNat : ℝ) * Real.exp (2 * L * (z.re - 1 / 2)) := hptw
      _ = ∑ q ∈ liftToXiZeroCopy R_deep hxi, Real.exp (2 * L * ((q.1 : ℂ).re - 1 / 2)) :=
          sum_analyticOrder_eq_sum_liftToXiZeroCopy R_deep hxi _
      _ = ∑ q ∈ liftToXiZeroCopy R_deep hxi, Real.exp (2 * L * (foldedRe q - 1 / 2)) := hfold_eq
      _ ≤ C_deep * V ^ (1 - γ₀) := hm_V
  exact mul_le_mul_of_nonneg_left hchain zero_le_two

/-- **Three-Scale Sieve-Mollified Shell Bound (`exists_shellDepthSum_le_mul_log`).**
For every `0 < c' < 22 / 51`, `shellDepthSum V (2 * V) L ≤ K_sh * V * Real.log V` uniformly for
all `0 ≤ L ≤ c' * Real.log V` eventually in `V`, with uniform quadratic small-`c'` constant
`K_sh ≤ K_univ * c' ^ 2` across `0 < c' ≤ 9 / 40`. -/
theorem exists_shellDepthSum_le_mul_log :
    ∃ K_univ : ℝ, 0 < K_univ ∧
      ∀ c' : ℝ, 0 < c' → c' < 22 / 51 →
        ∃ K_sh : ℝ, 0 < K_sh ∧ (c' ≤ 9 / 40 → K_sh ≤ K_univ * c' ^ 2) ∧
          ∀ᶠ V : ℝ in atTop, ∀ L : ℝ, 0 ≤ L → L ≤ c' * Real.log V →
            shellDepthSum V (2 * V) L ≤ K_sh * V * Real.log V := by
  obtain ⟨A, K, hA, hK, hbv_ev⟩ := exists_selberg_criticalGate_nearLine_zeroDensity
  set r_max : ℝ := Real.exp (-(1 / 5 : ℝ))
  have hr_max_lt1 : r_max < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  set K_I : ℝ := 16 * Real.exp 2
  set K_II_univ : ℝ := 2 * (2 * (64 * Real.exp 1 * A / ((2 / 5 : ℝ) * (1 - r_max))))
  set K_univ : ℝ := K_I + K_II_univ + 4
  have hKuniv_pos : 0 < K_univ := by dsimp [K_univ, K_I, K_II_univ]; positivity
  refine ⟨K_univ, hKuniv_pos, fun c' hc0 hc' => ?_⟩
  set lam : ℝ := (22 - 51 * c') / 25
  have hlam_pos : 0 < lam := by dsimp [lam]; linarith
  set r : ℝ := Real.exp (-(lam / 2))
  have hr_lt1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set K_II_c : ℝ := 4 * (64 * Real.exp 1 * A / (lam * (1 - r)))
  set K_sh : ℝ := (K_I + K_II_c + 4) * c' ^ 2
  have hKsh_pos : 0 < K_sh := by dsimp [K_sh, K_I, K_II_c]; positivity
  have hKsh_small : c' ≤ 9 / 40 → K_sh ≤ K_univ * c' ^ 2 := by
    intro hsmall
    have hlam_ge : (2 / 5 : ℝ) ≤ lam := by dsimp [lam]; linarith
    have hr_le : r ≤ r_max := Real.exp_le_exp.mpr (by linarith)
    have hden_ge : (2 / 5 : ℝ) * (1 - r_max) ≤ lam * (1 - r) :=
      mul_le_mul hlam_ge (by linarith) (by linarith) hlam_pos.le
    have hKII_le : K_II_c ≤ K_II_univ := by
      dsimp [K_II_c, K_II_univ]
      have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ 64 * Real.exp 1 * A)
        (by positivity) hden_ge
      linarith
    dsimp [K_sh, K_univ]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg c')
  obtain ⟨C_deep, hC_deep, T_deep, hT_deep, hdeep⟩ :=
    exists_sum_exp_foldedRe_deep_decay_up_to_two_thirds_log
      hc0.le (by linarith : c' < 2 / 3) (by norm_num : (0 : ℝ) < 1 / 200) (by norm_num)
  set γ₀ : ℝ := (4 / 3 - 2 * c') * (1 / 200) / 8
  have hγ₀_pos : 0 < γ₀ := by dsimp [γ₀]; linarith
  obtain ⟨K_log3, _, hlog3⟩ := exists_one_add_log_pow_le_rpow 3 (by positivity : (0 : ℝ) < 1 / 4)
  obtain ⟨K_log4, _, hlog4⟩ := exists_one_add_log_pow_le_rpow 4 (by positivity : (0 : ℝ) < 1 / 50)
  have htend_32 : Tendsto (fun V : ℝ => (3 / 2 : ℝ) * V) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have htend_2 : Tendsto (fun V : ℝ => (2 : ℝ) * V) atTop atTop :=
    tendsto_id.const_mul_atTop zero_lt_two
  have hev_cap : ∀ᶠ V : ℝ in atTop,
      64 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) ≤
        c' ^ 2 * V * Real.log V := by
    have ht : Tendsto (fun V : ℝ => V ^ (1 / 4 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop
      (64 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 / c' ^ 2 + 1),
      eventually_ge_atTop (4 : ℝ)] with V hV_rpow hV4
    have hV_pos : 0 < V := by linarith
    have hlog1 : 1 ≤ Real.log V := one_le_log_of_four_le hV4
    have hV_mul : V ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) = V := by
      rw [← Real.rpow_add hV_pos]; norm_num
    have hmul1 := (div_le_iff₀ (by positivity : 0 < c' ^ 2)).mp (by linarith :
      64 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 / c' ^ 2 ≤ V ^ (1 / 4 : ℝ))
    have hmul2 := mul_le_mul_of_nonneg_left hmul1 (Real.rpow_nonneg hV_pos.le (3 / 4))
    have hrew : V ^ (3 / 4 : ℝ) * (V ^ (1 / 4 : ℝ) * c' ^ 2) = c' ^ 2 * V := by
      calc V ^ (3 / 4 : ℝ) * (V ^ (1 / 4 : ℝ) * c' ^ 2)
          = c' ^ 2 * (V ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ)) := by ring
        _ = c' ^ 2 * V := by rw [hV_mul]
    rw [hrew] at hmul2
    exact hmul2.trans (le_mul_of_one_le_right (by positivity) hlog1)
  have hev_errII : ∀ᶠ V : ℝ in atTop,
      2 * ((16 * Real.exp 2 * K) * c' ^ 2 * K_log4 * ((3 / 2 : ℝ) * V) ^ (1 / 25 : ℝ)) ≤
        c' ^ 2 * V * Real.log V := by
    have ht : Tendsto (fun V : ℝ => V ^ (24 / 25 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop (64 * Real.exp 2 * K * K_log4 + 1),
      eventually_ge_atTop (4 : ℝ)] with V hV_rpow hV4
    have hV_pos : 0 < V := by linarith
    have hlog1 : 1 ≤ Real.log V := one_le_log_of_four_le hV4
    have h32_rpow : ((3 / 2 : ℝ) * V) ^ (1 / 25 : ℝ) ≤ 2 * V ^ (1 / 25 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hV_pos.le]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hV_pos.le _)
      calc (3 / 2 : ℝ) ^ (1 / 25 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            (Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)).trans
              (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num))
        _ = 2 := Real.rpow_one 2
    have hV_mul : V ^ (1 / 25 : ℝ) * V ^ (24 / 25 : ℝ) = V := by
      rw [← Real.rpow_add hV_pos]; norm_num
    have h1 : 2 * ((16 * Real.exp 2 * K) * c' ^ 2 * K_log4 * ((3 / 2 : ℝ) * V) ^ (1 / 25 : ℝ)) ≤
        c' ^ 2 * V ^ (1 / 25 : ℝ) * (64 * Real.exp 2 * K * K_log4) := by
      have hm := mul_le_mul_of_nonneg_left h32_rpow
        (by positivity : 0 ≤ 32 * Real.exp 2 * K * c' ^ 2 * K_log4)
      linarith
    have h2 : c' ^ 2 * V ^ (1 / 25 : ℝ) * (64 * Real.exp 2 * K * K_log4) ≤ c' ^ 2 * V := by
      calc c' ^ 2 * V ^ (1 / 25 : ℝ) * (64 * Real.exp 2 * K * K_log4)
          ≤ c' ^ 2 * V ^ (1 / 25 : ℝ) * V ^ (24 / 25 : ℝ) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = c' ^ 2 * (V ^ (1 / 25 : ℝ) * V ^ (24 / 25 : ℝ)) := by ring
        _ = c' ^ 2 * V := by rw [hV_mul]
    exact (h1.trans h2).trans (le_mul_of_one_le_right (by positivity) hlog1)
  have hev_deep : ∀ᶠ V : ℝ in atTop,
      2 * (C_deep * V ^ (1 - γ₀)) ≤ c' ^ 2 * V * Real.log V := by
    have ht : Tendsto (fun V : ℝ => V ^ γ₀) atTop atTop := tendsto_rpow_atTop hγ₀_pos
    filter_upwards [ht.eventually_ge_atTop (2 * C_deep / c' ^ 2 + 1),
      eventually_ge_atTop (4 : ℝ)] with V hV_rpow hV4
    have hV_pos : 0 < V := by linarith
    have hlog1 : 1 ≤ Real.log V := one_le_log_of_four_le hV4
    have hV_mul : V ^ (1 - γ₀) * V ^ γ₀ = V := by
      rw [← Real.rpow_add hV_pos]; ring_nf; exact Real.rpow_one V
    have hm1 := (div_le_iff₀ (by positivity : 0 < c' ^ 2)).mp
      (by linarith : 2 * C_deep / c' ^ 2 ≤ V ^ γ₀)
    have hm2 := mul_le_mul_of_nonneg_left hm1 (Real.rpow_nonneg hV_pos.le (1 - γ₀))
    have hrew : V ^ (1 - γ₀) * (V ^ γ₀ * c' ^ 2) = c' ^ 2 * V := by
      calc V ^ (1 - γ₀) * (V ^ γ₀ * c' ^ 2)
          = c' ^ 2 * (V ^ (1 - γ₀) * V ^ γ₀) := by ring
        _ = c' ^ 2 * V := by rw [hV_mul]
    rw [hrew] at hm2
    exact (by linarith : 2 * (C_deep * V ^ (1 - γ₀)) ≤ c' ^ 2 * V).trans
      (le_mul_of_one_le_right (by positivity) hlog1)
  refine ⟨K_sh, hKsh_pos, hKsh_small, ?_⟩
  filter_upwards [htend_32.eventually hbv_ev,
    htend_2.eventually ZetaGateProductAFE.eventually_offLineMoment_le_selberg,
    htend_32.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 200),
    eventually_ge_atTop (max 16 T_deep),
    hev_cap, hev_errII, hev_deep]
    with V hbv_V hm1_V hLS200 hV_max hcap_V herrII_V hdeep_V L hL0 hL
  have hV16 : 16 ≤ V := (le_max_left _ _).trans hV_max
  have hV_deep : T_deep ≤ V := (le_max_right _ _).trans hV_max
  have hV_pos : 0 < V := by linarith
  have hlogV_ge2 : 2 ≤ Real.log V := two_le_log_of_sixteen_le hV16
  set S : ℝ := (3 / 2) * V
  set L_S : ℝ := Real.log S
  have hLS_pos : 0 < L_S := by dsimp [L_S]; linarith
  have hLS_le_2logV : L_S ≤ 2 * Real.log V := by
    dsimp [L_S, S]
    have h1 : Real.log ((3 / 2) * V) ≤ Real.log (2 * V) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
    linarith [Real.log_two_lt_d9]
  have hL_le_LS : L ≤ c' * L_S :=
    hL.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log hV_pos (by dsimp [S]; linarith)) hc0.le)
  obtain ⟨T₁, hT₁, T₂, hT₂, hbv_S⟩ := hbv_V
  have hVT₁ : V ≤ T₁ := by dsimp [S] at hT₁; linarith [hT₁.1]
  have hT₁2 : T₁ ≤ T₂ := by dsimp [S] at hT₁ hT₂; linarith [hT₁.2, hT₂.1]
  have hT₂2V : T₂ ≤ 2 * V := by dsimp [S] at hT₂; linarith [hT₂.2]
  -- 1. End-caps `(V, T₁]` and `(T₂, 2 * V]`
  have hL_half : L ≤ (1 / 2) * Real.log V :=
    hL.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hcap_sum : shellDepthSum V T₁ L + shellDepthSum T₂ (2 * V) L ≤
      c' ^ 2 * V * Real.log V := by
    have hb1 := shortCap_shellDepthSum_le_rpow hV16 hV_pos.le hVT₁
      (by dsimp [S] at hT₁; linarith [hT₁.2]) (hT₁2.trans hT₂2V) hL0 hL_half hlog3
    have hb2 := shortCap_shellDepthSum_le_rpow hV16 (by linarith) hT₂2V
      (by dsimp [S] at hT₂; linarith [hT₂.1]) le_rfl hL0 hL_half hlog3
    calc shellDepthSum V T₁ L + shellDepthSum T₂ (2 * V) L
        ≤ 32 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) +
            32 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) :=
          add_le_add hb1 hb2
      _ = 64 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) := by ring
      _ ≤ c' ^ 2 * V * Real.log V := hcap_V
  -- 2. Partition `shellDepthSum T₁ T₂ L` into Scales I, II, III
  classical
  let R := (shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re)
  let N_S : ℕ := ⌊L_S / 100⌋₊
  let b₁ : ℝ := (51 / 50) * (1 / L_S)
  let b₂ : ℝ := (51 / 50) * ((N_S : ℝ) / L_S)
  let f_z : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
  have hpart1 := (Finset.sum_filter_add_sum_filter_not R (fun z => z.re - 1 / 2 < b₁) f_z).symm
  have hpart2 := (Finset.sum_filter_add_sum_filter_not
    (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)) (fun z => z.re - 1 / 2 < b₂) f_z).symm
  have hscaleI : 2 * ∑ z ∈ R.filter (fun z => z.re - 1 / 2 < b₁), f_z z ≤
      K_I * c' ^ 2 * V * Real.log V :=
    scaleI_near_shell_sum_le hV_pos hT₂2V hc0 hc' hLS_pos hLS_le_2logV hL0 hL_le_LS hm1_V
  have hscaleII : 2 * ∑ z ∈ (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter
        (fun z => z.re - 1 / 2 < b₂), f_z z ≤
      (K_II_c + 1) * c' ^ 2 * V * Real.log V := by
    have hR₂_eq : (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter (fun z => z.re - 1 / 2 < b₂) =
        (shellZeros T₁ T₂).filter (fun z =>
          (51 / 50) * (((1 : ℕ) : ℝ) / L_S) ≤ z.re - 1 / 2 ∧
            z.re - 1 / 2 < (51 / 50) * ((N_S : ℝ) / L_S)) := by
      ext z
      simp only [R, b₁, b₂, Finset.mem_filter, not_lt, Nat.cast_one]
      constructor
      · rintro ⟨⟨⟨hz_sh, _⟩, hge⟩, hlt⟩
        exact ⟨hz_sh, by simpa [one_div] using hge, hlt⟩
      · rintro ⟨hz_sh, hge, hlt⟩
        have hb1_pos : 0 < (51 / 50) * (1 / L_S) := by positivity
        exact ⟨⟨⟨hz_sh, by linarith⟩, by simpa [one_div] using hge⟩, hlt⟩
    rw [hR₂_eq]
    have hT₁_pos : 0 < T₁ := by linarith
    have hbv_win : ∀ a : ℝ, 1 ≤ a → a ≤ L_S / 100 →
        2 * Real.pi * ((a / L_S) *
          ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 51 / 50 * (a / L_S) ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
          (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * L_S :=
      fun a ha1 ha2 => hbv_S a ha1 ha2 (windowZeros T₁ T₂) (mem_windowZeros_iff hT₁_pos hT₁2)
    have hslab := scaleII_barbanVehov_slab_sum_le
      (by linarith : 4 ≤ V) rfl hA hK hc0 hc' hL0 hL_le_LS hT₁ hT₂ rfl rfl rfl rfl
      hLS200 hbv_win (le_rfl : 1 ≤ 1)
    have hr1_le : r ^ (1 : ℕ) ≤ 1 := by rw [pow_one]; exact hr_lt1.le
    have hmain_II : 2 * ((64 * Real.exp 1 * A / (lam * (1 - r))) * c' ^ 2 * r ^ (1 : ℕ) * (V * L_S)) ≤
        K_II_c * c' ^ 2 * V * Real.log V := by
      have hm1 : r ^ (1 : ℕ) * (V * L_S) ≤ 1 * (V * (2 * Real.log V)) :=
        mul_le_mul hr1_le (mul_le_mul_of_nonneg_left hLS_le_2logV hV_pos.le)
          (by positivity) zero_le_one
      have hm2 := mul_le_mul_of_nonneg_left hm1
        (by positivity : 0 ≤ 2 * ((64 * Real.exp 1 * A / (lam * (1 - r))) * c' ^ 2))
      dsimp [K_II_c]
      linarith
    have herr_II : 2 * ((16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 4 * S ^ (1 / 50 : ℝ)) ≤
        c' ^ 2 * V * Real.log V := by
      have hS_pos : 0 < S := by dsimp [S]; linarith
      have hLS4 : L_S ^ 4 ≤ K_log4 * S ^ (1 / 50 : ℝ) :=
        (pow_le_pow_left₀ hLS_pos.le (by linarith) 4).trans (hlog4 S (by dsimp [S]; linarith))
      have hS_add : S ^ (1 / 50 : ℝ) * S ^ (1 / 50 : ℝ) = S ^ (1 / 25 : ℝ) := by
        rw [← Real.rpow_add hS_pos]; norm_num
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLS4 (by positivity : 0 ≤ 2 * ((16 * Real.exp 2 * K) * c' ^ 2)))
        (Real.rpow_nonneg hS_pos.le (1 / 50))
      have hrew : 2 * ((16 * Real.exp 2 * K) * c' ^ 2) * (K_log4 * S ^ (1 / 50 : ℝ)) *
          S ^ (1 / 50 : ℝ) =
          2 * ((16 * Real.exp 2 * K) * c' ^ 2 * K_log4 * S ^ (1 / 25 : ℝ)) := by
        calc 2 * ((16 * Real.exp 2 * K) * c' ^ 2) * (K_log4 * S ^ (1 / 50 : ℝ)) *
                S ^ (1 / 50 : ℝ)
            = 2 * ((16 * Real.exp 2 * K) * c' ^ 2 * K_log4 *
                (S ^ (1 / 50 : ℝ) * S ^ (1 / 50 : ℝ))) := by ring
          _ = _ := by rw [hS_add]
      exact (hm.trans_eq hrew).trans herrII_V
    exact ((mul_le_mul_of_nonneg_left hslab zero_le_two).trans_eq (mul_add _ _ _)).trans
      ((add_le_add hmain_II herr_II).trans_eq (by ring))
  have hscaleIII : 2 * ∑ z ∈ (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter
        (fun z => ¬ z.re - 1 / 2 < b₂), f_z z ≤
      c' ^ 2 * V * Real.log V := by
    let R₃ := (R.filter (fun z => ¬ z.re - 1 / 2 < b₁)).filter (fun z => ¬ z.re - 1 / 2 < b₂)
    have hb₂_ge : (1 / 200 : ℝ) ≤ b₂ := by
      have hN_gt : L_S / 100 - 1 < (N_S : ℝ) := Nat.sub_one_lt_floor (L_S / 100)
      have hN_ge : L_S / 200 ≤ (N_S : ℝ) := by linarith [hLS200]
      have hm := mul_le_mul_of_nonneg_left hN_ge (by positivity : 0 ≤ (51 / 50) / L_S)
      have h1 : ((51 / 50) / L_S) * (L_S / 200) = 51 / 10000 := by
        calc ((51 / 50) / L_S) * (L_S / 200) = (51 / 10000) * (L_S / L_S) := by ring
          _ = 51 / 10000 := by rw [div_self hLS_pos.ne', mul_one]
      have h2 : ((51 / 50) / L_S) * (N_S : ℝ) = b₂ := by dsimp [b₂]; ring
      rw [h1, h2] at hm
      linarith
    have hsub₃ : R₃ ⊆ shellZeros T₁ T₂ := fun z hz =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1
    have hre₃ : ∀ z ∈ R₃, 1 / 2 + 1 / 200 ≤ z.re := fun z hz => by
      linarith [not_lt.mp (Finset.mem_filter.mp hz).2]
    exact (scaleIII_deep_shell_sum_le R₃ hV_pos hVT₁ hT₂2V hL0 hsub₃ hre₃
      (hdeep V hV_deep L hL0 hL)).trans hdeep_V
  have hmid_tot : shellDepthSum T₁ T₂ L ≤ (K_I + K_II_c + 2) * c' ^ 2 * V * Real.log V := by
    rw [shellDepthSum_eq_two_mul_right T₁ T₂ L]
    change 2 * ∑ z ∈ R, f_z z ≤ _
    rw [hpart1, hpart2, mul_add, mul_add]
    exact (add_le_add (add_le_add hscaleI hscaleII) hscaleIII).trans_eq (by ring)
  rw [shellDepthSum_split hVT₁ (hT₁2.trans hT₂2V), shellDepthSum_split hT₁2 hT₂2V]
  have hextra : 0 ≤ c' ^ 2 * V * Real.log V := by positivity
  calc shellDepthSum V T₁ L + (shellDepthSum T₁ T₂ L + shellDepthSum T₂ (2 * V) L)
      = (shellDepthSum V T₁ L + shellDepthSum T₂ (2 * V) L) + shellDepthSum T₁ T₂ L := by ring
    _ ≤ c' ^ 2 * V * Real.log V + (K_I + K_II_c + 2) * c' ^ 2 * V * Real.log V :=
        add_le_add hcap_sum hmid_tot
    _ = (K_I + K_II_c + 3) * (c' ^ 2 * V * Real.log V) := by ring
    _ ≤ (K_I + K_II_c + 4) * (c' ^ 2 * V * Real.log V) :=
        mul_le_mul_of_nonneg_right (by linarith) hextra
    _ = K_sh * V * Real.log V := by dsimp [K_sh]; ring

/-- **Sub-Power Shell Bound up to `c' < 2 / 3` (`exists_shellDepthSum_le_subpower`).**
For every `0 ≤ c' < 2 / 3` and every `η > 0`, `shellDepthSum V (2 * V) L ≤ C_sub * V ^ (1 + η)`
uniformly for all `0 ≤ L ≤ c' * Real.log V` eventually in `V`. -/
theorem exists_shellDepthSum_le_subpower {c' η : ℝ} (hc0 : 0 ≤ c') (hc' : c' < 2 / 3)
    (hη : 0 < η) :
    ∃ C_sub : ℝ, 0 < C_sub ∧ ∀ᶠ V : ℝ in atTop, ∀ L : ℝ, 0 ≤ L → L ≤ c' * Real.log V →
      shellDepthSum V (2 * V) L ≤ C_sub * V ^ (1 + η) := by
  obtain ⟨C, hC, T₀, hT₀, hsub⟩ :=
    exists_sum_exp_foldedRe_le_subpower_up_to_two_thirds_log hc0 hc' hη
  refine ⟨2 * C + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T₀] with V hV L hL0 hL
  have hV4 : 4 ≤ V := hT₀.trans hV
  have hV_pos : 0 < V := by linarith
  rw [shellDepthSum_eq_two_mul_right V (2 * V) L]
  classical
  let R := (shellZeros V (2 * V)).filter (fun z => 1 / 2 < z.re)
  have hxi : ∀ z ∈ R, xi z = 0 := fun z hz =>
    (mem_stripFinsetPos.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2.2.2.2
  have hptw : ∑ z ∈ R, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      ∑ z ∈ R, ((analyticOrderAt xi z).toNat : ℝ) * Real.exp (2 * L * (z.re - 1 / 2)) := by
    refine Finset.sum_le_sum fun z hz => ?_
    have hre : 1 / 2 < z.re := (Finset.mem_filter.mp hz).2
    have hdk := depthKernel_le_exp_two_mul (d := z.re - 1 / 2) hL0
    rw [abs_of_pos (by linarith)] at hdk
    exact mul_le_mul_of_nonneg_left hdk (Nat.cast_nonneg _)
  have hfold_eq : ∑ q ∈ liftToXiZeroCopy R hxi, Real.exp (2 * L * ((q.1 : ℂ).re - 1 / 2)) =
      ∑ q ∈ liftToXiZeroCopy R hxi, Real.exp (2 * L * (foldedRe q - 1 / 2)) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hre : 1 / 2 < (q.1 : ℂ).re := (Finset.mem_filter.mp (mem_liftToXiZeroCopy_iff hq)).2
    rw [show foldedRe q = (q.1 : ℂ).re from max_eq_left (by linarith)]
  have hG_cond : ∀ q ∈ liftToXiZeroCopy R hxi,
      V ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * V := by
    intro q hq
    have hz_sh : (q.1 : ℂ) ∈ shellZeros V (2 * V) :=
      (Finset.mem_filter.mp (mem_liftToXiZeroCopy_iff hq)).1
    have him1 : V < (q.1 : ℂ).im := (Finset.mem_filter.mp hz_sh).2
    have him2 : (q.1 : ℂ).im ≤ 2 * V :=
      (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1).2.2.2.1
    rw [abs_of_pos (by linarith)]
    exact ⟨him1.le, him2⟩
  have hb := mul_le_mul_of_nonneg_left (hsub V hV L hL0 hL (liftToXiZeroCopy R hxi) hG_cond) hV_pos.le
  have hlhs : V * ((1 / V) * ∑ q ∈ liftToXiZeroCopy R hxi,
      Real.exp (2 * L * (foldedRe q - 1 / 2))) =
      ∑ q ∈ liftToXiZeroCopy R hxi, Real.exp (2 * L * (foldedRe q - 1 / 2)) := by
    field_simp
  have hrhs : V * (C * V ^ η) = C * V ^ (1 + η) := by
    calc V * (C * V ^ η) = C * (V ^ (1 : ℝ) * V ^ η) := by rw [Real.rpow_one]; ring
      _ = C * V ^ (1 + η) := by rw [← Real.rpow_add hV_pos]
  rw [hlhs, hrhs] at hb
  have hchain : ∑ z ∈ R, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2) ≤
      C * V ^ (1 + η) :=
    calc ∑ z ∈ R, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
        ≤ ∑ z ∈ R, ((analyticOrderAt xi z).toNat : ℝ) * Real.exp (2 * L * (z.re - 1 / 2)) := hptw
      _ = ∑ q ∈ liftToXiZeroCopy R hxi, Real.exp (2 * L * ((q.1 : ℂ).re - 1 / 2)) :=
          sum_analyticOrder_eq_sum_liftToXiZeroCopy R hxi _
      _ = ∑ q ∈ liftToXiZeroCopy R hxi, Real.exp (2 * L * (foldedRe q - 1 / 2)) := hfold_eq
      _ ≤ C * V ^ (1 + η) := hb
  have hnn : 0 ≤ V ^ (1 + η) := Real.rpow_nonneg hV_pos.le _
  calc 2 * ∑ z ∈ R, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
      ≤ 2 * (C * V ^ (1 + η)) := mul_le_mul_of_nonneg_left hchain zero_le_two
    _ = (2 * C) * V ^ (1 + η) := by ring
    _ ≤ (2 * C + 1) * V ^ (1 + η) := mul_le_mul_of_nonneg_right (by linarith) hnn

/-! ## §5. Dyadic mean collapse of `unitWindowDepthCharge`, `heckeDefect`, and `polynomialThetaSourceMomentReading` -/

/-- Exact indicator decomposition of `unitWindowDepthCharge T (c * Real.log T)` across
`T ∈ Icc U (2 * U)` (`0 < U`). -/
private theorem unitWindowDepthCharge_eq_sum_indicator {U c T : ℝ} (hU : 0 < U)
    (hT : T ∈ Icc U (2 * U)) :
    unitWindowDepthCharge T (c * Real.log T) =
      ∑ z ∈ shellZeros (U - 1) (2 * U + 1),
        (Ioc (z.im - 1) z.im).indicator
          (fun t => ((analyticOrderAt xi z).toNat : ℝ) *
            depthKernel (c * Real.log t) (z.re - 1 / 2)) T := by
  classical
  have hmem : ∀ z : ℂ, z ∈ xiUnitWindowZeros T ↔
      z ∈ shellZeros (U - 1) (2 * U + 1) ∧ T ∈ Ioc (z.im - 1) z.im := by
    intro z
    rw [mem_xiUnitWindowZeros, shellZeros, Finset.mem_filter, mem_stripFinsetPos,
      Set.Finite.mem_toFinset, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h0, h1, _him0, hlt⟩, hxi⟩, hle⟩
      exact ⟨⟨⟨h0, h1, by linarith [hT.1, hle], by linarith [hT.2], hxi⟩, by linarith [hT.1]⟩,
        by linarith, hle⟩
    · rintro ⟨⟨⟨h0, h1, him0, _, hxi⟩, _⟩, hgt, hle⟩
      exact ⟨⟨⟨h0, h1, him0.le, by linarith⟩, hxi⟩, hle⟩
  unfold unitWindowDepthCharge
  have hfilt : xiUnitWindowZeros T =
      (shellZeros (U - 1) (2 * U + 1)).filter (fun z => T ∈ Ioc (z.im - 1) z.im) := by
    ext z; simp only [Finset.mem_filter]; exact hmem z
  rw [hfilt, Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hm : T ∈ Ioc (z.im - 1) z.im
  · rw [if_pos hm, Set.indicator_of_mem hm]
  · rw [if_neg hm, Set.indicator_of_notMem hm]

private theorem continuousOn_depthKernel_log {U : ℝ} (hU : 0 < U) (c d : ℝ) :
    ContinuousOn (fun t : ℝ => depthKernel (c * Real.log t) d) (Icc U (2 * U)) := by
  unfold depthKernel
  have hlog : ContinuousOn Real.log (Icc U (2 * U)) :=
    Real.continuousOn_log.mono fun t ht => (by linarith [ht.1] : 0 < t).ne'
  exact (continuousOn_const.mul (Real.continuous_cosh.comp_continuousOn
    (continuousOn_const.mul (continuousOn_const.mul hlog)))).sub continuousOn_const

/-- Integrability of `T ↦ unitWindowDepthCharge T (c * Real.log T)` on `Icc U (2 * U)` (`0 < U`). -/
theorem integrableOn_unitWindowDepthCharge_log_Icc {U : ℝ} (hU : 0 < U) (c : ℝ) :
    IntegrableOn (fun T : ℝ => unitWindowDepthCharge T (c * Real.log T)) (Icc U (2 * U)) volume := by
  have hint_sum : IntegrableOn
      (fun T : ℝ => ∑ z ∈ shellZeros (U - 1) (2 * U + 1),
        (Ioc (z.im - 1) z.im).indicator
          (fun t => ((analyticOrderAt xi z).toNat : ℝ) *
            depthKernel (c * Real.log t) (z.re - 1 / 2)) T)
      (Icc U (2 * U)) volume := by
    refine integrable_finsetSum _ fun z _ => ?_
    have hcont : ContinuousOn
        (fun t : ℝ => ((analyticOrderAt xi z).toNat : ℝ) *
          depthKernel (c * Real.log t) (z.re - 1 / 2)) (Icc U (2 * U)) :=
      continuousOn_const.mul (continuousOn_depthKernel_log hU c _)
    have hint_base : IntegrableOn
        (fun t : ℝ => ((analyticOrderAt xi z).toNat : ℝ) *
          depthKernel (c * Real.log t) (z.re - 1 / 2)) (Icc U (2 * U)) volume :=
      hcont.integrableOn_compact isCompact_Icc
    exact hint_base.indicator measurableSet_Ioc
  exact hint_sum.congr_fun (fun T hT => (unitWindowDepthCharge_eq_sum_indicator hU hT).symm)
    measurableSet_Icc

/-- Dyadic integral upper bound for `unitWindowDepthCharge`: for `1 ≤ U` and `0 ≤ c`,
`∫_U^{2U} unitWindowDepthCharge T (c log T) dT ≤ shellDepthSum (U - 1) (2U + 1) (c log (2U))`. -/
theorem dyadicIntegral_unitWindowDepthCharge_le_shellDepthSum {U c : ℝ} (hU : 1 ≤ U) (hc : 0 ≤ c) :
    (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) ≤
      shellDepthSum (U - 1) (2 * U + 1) (c * Real.log (2 * U)) := by
  have hU0 : 0 < U := by linarith
  let f_ind : ℂ → ℝ → ℝ := fun z T =>
    (Ioc (z.im - 1) z.im).indicator
      (fun t => ((analyticOrderAt xi z).toNat : ℝ) *
        depthKernel (c * Real.log t) (z.re - 1 / 2)) T
  have hint_ind : ∀ z ∈ shellZeros (U - 1) (2 * U + 1),
      IntegrableOn (f_ind z) (Icc U (2 * U)) volume := fun z _ =>
    ((continuousOn_const.mul (continuousOn_depthKernel_log hU0 c _)).integrableOn_compact
      isCompact_Icc).indicator measurableSet_Ioc
  have hcongr : (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) =
      ∫ T in Icc U (2 * U), ∑ z ∈ shellZeros (U - 1) (2 * U + 1), f_ind z T :=
    setIntegral_congr_fun measurableSet_Icc fun T hT =>
      unitWindowDepthCharge_eq_sum_indicator hU0 hT
  rw [hcongr, integral_finsetSum (s := shellZeros (U - 1) (2 * U + 1)) (f := f_ind) hint_ind]
  dsimp only [f_ind]
  unfold shellDepthSum
  refine Finset.sum_le_sum fun z _ => ?_
  rw [setIntegral_indicator measurableSet_Ioc]
  set M_z : ℝ := ((analyticOrderAt xi z).toNat : ℝ) *
    depthKernel (c * Real.log (2 * U)) (z.re - 1 / 2)
  have hM_nn : 0 ≤ M_z := mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)
  have hint_sub : IntegrableOn
      (fun t : ℝ => ((analyticOrderAt xi z).toNat : ℝ) *
        depthKernel (c * Real.log t) (z.re - 1 / 2))
      (Icc U (2 * U) ∩ Ioc (z.im - 1) z.im) volume :=
    ((continuousOn_const.mul (continuousOn_depthKernel_log hU0 c _)).integrableOn_compact
      isCompact_Icc).mono_set inter_subset_left
  have hvol_le : volume (Icc U (2 * U) ∩ Ioc (z.im - 1) z.im) ≤ ENNReal.ofReal 1 := by
    refine (measure_mono inter_subset_right).trans ?_
    rw [Real.volume_Ioc]
    exact le_of_eq (by ring_nf)
  have hreal_le : volume.real (Icc U (2 * U) ∩ Ioc (z.im - 1) z.im) ≤ 1 := by
    rw [Measure.real_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_le).trans (by simp)
  calc (∫ t in Icc U (2 * U) ∩ Ioc (z.im - 1) z.im,
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel (c * Real.log t) (z.re - 1 / 2))
      ≤ ∫ _t in Icc U (2 * U) ∩ Ioc (z.im - 1) z.im, M_z := by
        refine setIntegral_mono_on hint_sub (integrableOn_const (hs := hvol_le.trans_lt
          ENNReal.ofReal_lt_top |>.ne)) (measurableSet_Icc.inter measurableSet_Ioc) fun t ht => ?_
        have ht_lo : 1 ≤ t := hU.trans ht.1.1
        have hlog_nn : 0 ≤ c * Real.log t := mul_nonneg hc (Real.log_nonneg ht_lo)
        have hlog_le : c * Real.log t ≤ c * Real.log (2 * U) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) ht.1.2) hc
        exact mul_le_mul_of_nonneg_left (depthKernel_mono_scale hlog_nn hlog_le _)
          (Nat.cast_nonneg _)
    _ = volume.real (Icc U (2 * U) ∩ Ioc (z.im - 1) z.im) * M_z := by
        rw [setIntegral_const, smul_eq_mul]
    _ ≤ 1 * M_z := mul_le_mul_of_nonneg_right hreal_le hM_nn
    _ = M_z := one_mul M_z

/-- Dyadic integral lower bound for `unitWindowDepthCharge`: for `1 ≤ U` and `0 ≤ c`,
`shellDepthSum (U + 1) (2U) (c log U) ≤ ∫_U^{2U} unitWindowDepthCharge T (c log T) dT`. -/
theorem shellDepthSum_le_dyadicIntegral_unitWindowDepthCharge {U c : ℝ} (hU : 1 ≤ U) (hc : 0 ≤ c) :
    shellDepthSum (U + 1) (2 * U) (c * Real.log U) ≤
      ∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T) := by
  classical
  have hU0 : 0 < U := by linarith
  let f_ind : ℂ → ℝ → ℝ := fun z T =>
    (Ioc (z.im - 1) z.im).indicator
      (fun t => ((analyticOrderAt xi z).toNat : ℝ) *
        depthKernel (c * Real.log t) (z.re - 1 / 2)) T
  have hint_ind : ∀ z ∈ shellZeros (U - 1) (2 * U + 1),
      IntegrableOn (f_ind z) (Icc U (2 * U)) volume := fun z _ =>
    ((continuousOn_const.mul (continuousOn_depthKernel_log hU0 c _)).integrableOn_compact
      isCompact_Icc).indicator measurableSet_Ioc
  have hcongr : (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) =
      ∫ T in Icc U (2 * U), ∑ z ∈ shellZeros (U - 1) (2 * U + 1), f_ind z T :=
    setIntegral_congr_fun measurableSet_Icc fun T hT =>
      unitWindowDepthCharge_eq_sum_indicator hU0 hT
  rw [hcongr, integral_finsetSum (s := shellZeros (U - 1) (2 * U + 1)) (f := f_ind) hint_ind]
  dsimp only [f_ind]
  have hsub_sh : shellZeros (U + 1) (2 * U) ⊆ shellZeros (U - 1) (2 * U + 1) := by
    intro z hz
    obtain ⟨hz_pos, him1⟩ := Finset.mem_filter.mp hz
    obtain ⟨h0, h1, him0, him2, hxi⟩ := mem_stripFinsetPos.mp hz_pos
    exact Finset.mem_filter.mpr ⟨mem_stripFinsetPos.mpr ⟨h0, h1, him0, by linarith, hxi⟩,
      by linarith⟩
  have hnn_int : ∀ z ∈ shellZeros (U - 1) (2 * U + 1), z ∉ shellZeros (U + 1) (2 * U) →
      0 ≤ ∫ T in Icc U (2 * U), (Ioc (z.im - 1) z.im).indicator
        (fun t => ((analyticOrderAt xi z).toNat : ℝ) *
          depthKernel (c * Real.log t) (z.re - 1 / 2)) T := fun z _ _ =>
    setIntegral_nonneg measurableSet_Icc fun T _ =>
      Set.indicator_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)) T
  refine (Finset.sum_le_sum fun z hz => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub_sh hnn_int)
  obtain ⟨hz_pos, him_gt⟩ := Finset.mem_filter.mp hz
  have him_le : z.im ≤ 2 * U := (mem_stripFinsetPos.mp hz_pos).2.2.2.1
  have hinter : Icc U (2 * U) ∩ Ioc (z.im - 1) z.im = Ioc (z.im - 1) z.im :=
    inter_eq_right.mpr fun t ht => ⟨by linarith [ht.1], ht.2.trans him_le⟩
  rw [setIntegral_indicator measurableSet_Ioc, hinter]
  set m_z : ℝ := ((analyticOrderAt xi z).toNat : ℝ) *
    depthKernel (c * Real.log U) (z.re - 1 / 2)
  have hint_ioc : IntegrableOn
      (fun t : ℝ => ((analyticOrderAt xi z).toNat : ℝ) *
        depthKernel (c * Real.log t) (z.re - 1 / 2))
      (Ioc (z.im - 1) z.im) volume :=
    ((continuousOn_const.mul (continuousOn_depthKernel_log hU0 c _)).integrableOn_compact
      isCompact_Icc).mono_set fun t ht => ⟨by linarith [ht.1], ht.2.trans him_le⟩
  have hvol_ioc : volume (Ioc (z.im - 1) z.im) = ENNReal.ofReal 1 := by
    rw [Real.volume_Ioc]; ring_nf
  have hreal_ioc : volume.real (Ioc (z.im - 1) z.im) = 1 := by
    rw [Measure.real_def, hvol_ioc]; simp
  calc m_z = volume.real (Ioc (z.im - 1) z.im) * m_z := by rw [hreal_ioc, one_mul]
    _ = ∫ _t in Ioc (z.im - 1) z.im, m_z := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ t in Ioc (z.im - 1) z.im,
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel (c * Real.log t) (z.re - 1 / 2) := by
        refine setIntegral_mono_on (integrableOn_const (hs := by rw [hvol_ioc]; exact ENNReal.ofReal_ne_top))
          hint_ioc measurableSet_Ioc fun t ht => ?_
        have hlog_nn : 0 ≤ c * Real.log U := mul_nonneg hc (Real.log_nonneg hU)
        have hlog_le : c * Real.log U ≤ c * Real.log t :=
          mul_le_mul_of_nonneg_left (Real.log_le_log hU0 (by linarith [ht.1])) hc
        exact mul_le_mul_of_nonneg_left (depthKernel_mono_scale hlog_nn hlog_le _)
          (Nat.cast_nonneg _)

private theorem continuousOn_comp_log_pair {F : ℝ × ℝ → ℝ} (hF : Continuous F)
    {U : ℝ} (hU : 0 < U) (c : ℝ) :
    ContinuousOn (fun γ : ℝ => F (γ, c * Real.log γ)) (Icc U (2 * U)) := by
  have hlog : ContinuousOn Real.log (Icc U (2 * U)) :=
    Real.continuousOn_log.mono fun γ hγ => (by linarith [hγ.1] : 0 < γ).ne'
  have hpair : ContinuousOn (fun γ : ℝ => (γ, c * Real.log γ)) (Icc U (2 * U)) :=
    continuousOn_id.prodMk (continuousOn_const.mul hlog)
  exact hF.comp_continuousOn hpair

/-- Integrability of `γ ↦ heckeDefect (baseTwistTest γ) (c * Real.log γ)` on `Icc U (2 * U)`
(`0 < U`). -/
theorem integrableOn_heckeDefect_log_Icc {U : ℝ} (hU : 0 < U) (c : ℝ) :
    IntegrableOn (fun γ : ℝ => heckeDefect (baseTwistTest γ) (c * Real.log γ))
      (Icc U (2 * U)) volume :=
  (continuousOn_comp_log_pair (F := fun p => heckeDefect (baseTwistTest p.1) p.2)
    continuous_heckeDefect_pair hU c).integrableOn_compact isCompact_Icc

/-- Pointwise coercion of `unitWindowDepthCharge` into `heckeDefect` gives the immediate dyadic
integral lower bound on the exact same interval `[U, 2U]`. -/
theorem cos_sq_mul_dyadicIntegral_unitWindowDepthCharge_le_heckeDefect
    {U : ℝ} (hU : 0 < U) (c : ℝ) :
    Real.cos (1 / 4 : ℝ) ^ 2 *
      (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) ≤
      ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ) := by
  rw [← integral_const_mul]
  exact setIntegral_mono_on
    ((integrableOn_unitWindowDepthCharge_log_Icc hU c).const_mul _)
    (integrableOn_heckeDefect_log_Icc hU c)
    measurableSet_Icc fun γ _ =>
      unitWindow_depthCharge_le_heckeDefect γ (c * Real.log γ) le_rfl (by linarith)

/-- Local-shell + Paley–Wiener remote decomposition of the dyadic integral of `heckeDefect`:
for `4 ≤ U` and `0 ≤ c`, `∫_U^{2U} E_γ(c log γ) dγ` is bounded by `C_loc` times the three adjacent
dyadic shells `V ∈ {U/2, U, 2U}` at scale `c log (2U)` plus `C_rem * (2U)^c / U`. -/
theorem exists_dyadicIntegral_heckeDefect_le_threeShells :
    ∃ C_loc C_rem : ℝ, 0 < C_loc ∧ 0 < C_rem ∧
      ∀ U c : ℝ, 4 ≤ U → 0 ≤ c →
        (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) ≤
          C_loc * (shellDepthSum (U / 2) U (c * Real.log (2 * U)) +
            shellDepthSum U (2 * U) (c * Real.log (2 * U)) +
            shellDepthSum (2 * U) (4 * U) (c * Real.log (2 * U))) +
          C_rem * (2 * U) ^ c / U := by
  obtain ⟨C₁, hC₁, hpw₁⟩ := exists_norm_tr_twist_baseBump_le_pow 1
  obtain ⟨C₂, hC₂, hpw₂⟩ := exists_norm_tr_twist_baseBump_le_pow 2
  have hsum_lor : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    simpa only [zero_sub, neg_sq] using
      ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy
        (g := fun z : ℂ => 1 / (1 + (0 - z.im) ^ 2)) (fun _ => by positivity)
        (RHTower.summable_lorentzMassTerm 0)
  set L_mass : ℝ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))
  have hLmass_nn : 0 ≤ L_mass := tsum_nonneg fun _ => by positivity
  set M₀ : ℝ := max (2 * Real.exp (1 / 4)) (2 * C₁ ^ 2)
  have hM₀_pos : 0 < M₀ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set C_loc : ℝ := Real.pi * M₀ + 1
  set C_rem : ℝ := 16 * C₂ ^ 2 * L_mass + 1
  refine ⟨C_loc, C_rem, by positivity, by positivity, fun U c hU4 hc0 => ?_⟩
  classical
  have hU_pos : 0 < U := by linarith
  set L_max : ℝ := c * Real.log (2 * U)
  have hLmax_nn : 0 ≤ L_max := mul_nonneg hc0 (Real.log_nonneg (by linarith))
  -- Lift `shellZeros (U / 2) (4 * U)` into `zetaZeroConfig.carrier`
  have hmem_c : ∀ z ∈ shellZeros (U / 2) (4 * U), z ∈ zetaZeroConfig.carrier := by
    intro z hz
    obtain ⟨h0, h1, _, _, hxi⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1
    exact CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mpr
      ⟨hxi, h0, h1⟩
  let emb : {z // z ∈ shellZeros (U / 2) (4 * U)} → zetaZeroConfig.carrier :=
    fun z => ⟨z.1, hmem_c z.1 z.2⟩
  have hinj : Function.Injective emb := fun a b h =>
    Subtype.ext (congrArg (fun x : zetaZeroConfig.carrier => (x : ℂ)) h)
  let S_loc : Finset zetaZeroConfig.carrier := (shellZeros (U / 2) (4 * U)).attach.image emb
  -- Pointwise Lorentzian majorant on `Complex.normSq (tr (twist γ baseBump) ρ)`
  have hnsq_lor : ∀ (γ : ℝ) (ρ : zetaZeroConfig.carrier),
      Complex.normSq (tr (twist γ baseBump) ρ) ≤
        M₀ * (1 / (1 + ((ρ : ℂ).im - γ) ^ 2)) := by
    intro γ ρ
    have hstrip := abs_re_sub_half_le_of_zeroConfig zetaZeroConfig ρ
    by_cases hd : |(ρ : ℂ).im - γ| ≤ 1
    · have hb : Complex.normSq (tr (twist γ baseBump) ρ) ≤ Real.exp (1 / 4) := by
        rw [Complex.normSq_eq_norm_sq]
        refine (pow_le_pow_left₀ (norm_nonneg _)
          (norm_tr_twist_baseBump_le_exp γ hstrip) 2).trans_eq ?_
        rw [← Real.exp_nat_mul]; norm_num
      have hden : 1 + ((ρ : ℂ).im - γ) ^ 2 ≤ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hd 2
        rw [sq_abs] at this; linarith
      have hhalf : (1 / 2 : ℝ) ≤ 1 / (1 + ((ρ : ℂ).im - γ) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) hden
      have hM₀ : 2 * Real.exp (1 / 4) ≤ M₀ := le_max_left _ _
      calc Complex.normSq (tr (twist γ baseBump) ρ) ≤ Real.exp (1 / 4) := hb
        _ = (2 * Real.exp (1 / 4)) * (1 / 2) := by ring
        _ ≤ M₀ * (1 / (1 + ((ρ : ℂ).im - γ) ^ 2)) :=
            mul_le_mul hM₀ hhalf (by norm_num) (by positivity)
    · have hd' : 1 < |(ρ : ℂ).im - γ| := not_le.mp hd
      have hne : (ρ : ℂ).im ≠ γ := fun heq => by rw [heq, sub_self, abs_zero] at hd'; linarith
      have hpw := hpw₁ γ ρ hstrip hne
      rw [pow_one] at hpw
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hpw 2
      rw [← Complex.normSq_eq_norm_sq, div_pow, sq_abs] at hsq
      have hd_sq : 1 ≤ ((ρ : ℂ).im - γ) ^ 2 := by
        have := pow_le_pow_left₀ zero_le_one hd'.le 2
        simpa [sq_abs] using this
      have hfrac : 1 / ((ρ : ℂ).im - γ) ^ 2 ≤ 2 * (1 / (1 + ((ρ : ℂ).im - γ) ^ 2)) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have hM₀ : 2 * C₁ ^ 2 ≤ M₀ := le_max_right _ _
      calc Complex.normSq (tr (twist γ baseBump) ρ)
          ≤ C₁ ^ 2 * (1 / ((ρ : ℂ).im - γ) ^ 2) := by simpa [div_eq_mul_inv] using hsq
        _ ≤ C₁ ^ 2 * (2 * (1 / (1 + ((ρ : ℂ).im - γ) ^ 2))) :=
            mul_le_mul_of_nonneg_left hfrac (sq_nonneg C₁)
        _ ≤ M₀ * (1 / (1 + ((ρ : ℂ).im - γ) ^ 2)) := by
            have := mul_le_mul_of_nonneg_right hM₀
              (by positivity : 0 ≤ 1 / (1 + ((ρ : ℂ).im - γ) ^ 2))
            linarith
  -- Pointwise decomposition on `γ ∈ Icc U (2 * U)` into `S_loc` + `γ`-uniform remote tail
  have hptw_gamma : ∀ γ ∈ Icc U (2 * U),
      heckeDefect (baseTwistTest γ) (c * Real.log γ) ≤
        (∑ z ∈ shellZeros (U / 2) (4 * U),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2)))) +
        C_rem * (2 * U) ^ c / U ^ 2 := by
    intro γ hγ
    have hLγ_nn : 0 ≤ c * Real.log γ := mul_nonneg hc0 (Real.log_nonneg (by linarith [hγ.1]))
    have hLγ_le : c * Real.log γ ≤ L_max :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hγ.1]) hγ.2) hc0
    have hsum_split := ((summable_heckeDefect (baseTwistTest γ) (c * Real.log γ)).sum_add_tsum_compl
      (s := S_loc)).symm
    change (∑' ρ : zetaZeroConfig.carrier,
      zetaWeight (baseTwistTest γ) ρ * depthKernel (c * Real.log γ) (zetaDepth ρ)) ≤ _
    rw [hsum_split]
    -- Local sum bound
    have hloc_part : (∑ ρ ∈ S_loc,
          zetaWeight (baseTwistTest γ) ρ * depthKernel (c * Real.log γ) (zetaDepth ρ)) ≤
        ∑ z ∈ shellZeros (U / 2) (4 * U),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2))) := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h), ← Finset.sum_attach (shellZeros (U / 2) (4 * U))]
      refine Finset.sum_le_sum fun z _ => ?_
      obtain ⟨h0, h1, _, _, _⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp z.2).1
      have hmult : (zetaZeroConfig.mult z.1 : ℝ) = ((analyticOrderAt xi z.1).toNat : ℝ) := by
        change ((analyticOrderAt riemannZeta z.1).toNat : ℝ) = _
        exact congrArg (fun k : ℕ => (k : ℝ))
          (congrArg ENat.toNat (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩)).symm
      have hdk_le : depthKernel (c * Real.log γ) (zetaDepth (emb z)) ≤
          depthKernel L_max (z.1.re - 1 / 2) :=
        depthKernel_mono_scale hLγ_nn hLγ_le (z.1.re - 1 / 2)
      have hlor_z := hnsq_lor γ (emb z)
      dsimp only [zetaWeight, baseTwistTest, emb] at hlor_z ⊢
      rw [hmult]
      calc ((analyticOrderAt xi z.1).toNat : ℝ) * Complex.normSq (tr (twist γ baseBump) z.1) *
              depthKernel (c * Real.log γ) (zetaDepth (emb z))
          ≤ ((analyticOrderAt xi z.1).toNat : ℝ) * (M₀ * (1 / (1 + (z.1.im - γ) ^ 2))) *
              depthKernel L_max (z.1.re - 1 / 2) := by
            refine mul_le_mul
              (mul_le_mul_of_nonneg_left hlor_z (Nat.cast_nonneg _))
              hdk_le (depthKernel_nonneg _ _) (by positivity)
        _ = ((analyticOrderAt xi z.1).toNat : ℝ) * depthKernel L_max (z.1.re - 1 / 2) *
              (M₀ * (1 / (1 + (z.1.im - γ) ^ 2))) := by ring
    -- Remote tail (`ρ ∉ S_loc`): `K = 2` Paley–Wiener quartic decay
    have hrem_part : (∑' ρ : ((S_loc : Set zetaZeroConfig.carrier)ᶜ),
          zetaWeight (baseTwistTest γ) ρ.1 * depthKernel (c * Real.log γ) (zetaDepth ρ.1)) ≤
        C_rem * (2 * U) ^ c / U ^ 2 := by
      have hrem_ptw : ∀ ρ : ((S_loc : Set zetaZeroConfig.carrier)ᶜ),
          zetaWeight (baseTwistTest γ) ρ.1 * depthKernel (c * Real.log γ) (zetaDepth ρ.1) ≤
            (16 * C₂ ^ 2 * (2 * U) ^ c / U ^ 2) *
              ((zetaZeroConfig.mult ρ.1 : ℝ) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) := by
        intro ρ
        have hnot_sh : (ρ.1 : ℂ) ∉ shellZeros (U / 2) (4 * U) := by
          intro hsh
          exact ρ.2 (Finset.mem_image.mpr ⟨⟨(ρ.1 : ℂ), hsh⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)
        have hxi_01 := CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp ρ.1.2
        have him_out : (ρ.1 : ℂ).im ≤ U / 2 ∨ 4 * U < (ρ.1 : ℂ).im := by
          by_contra hmid
          push Not at hmid
          exact hnot_sh (Finset.mem_filter.mpr
            ⟨mem_stripFinsetPos.mpr ⟨hxi_01.2.1, hxi_01.2.2, by linarith [hmid.1], hmid.2, hxi_01.1⟩,
              hmid.1⟩)
        have hquartic : (1 / 16 : ℝ) * U ^ 2 * (1 + (ρ.1 : ℂ).im ^ 2) ≤ ((ρ.1 : ℂ).im - γ) ^ 4 := by
          have hnn_q : 0 ≤ U ^ 2 * (1 + (ρ.1 : ℂ).im ^ 2) := by positivity
          rcases him_out with hle_half | hgt_4U
          · rcases lt_or_ge ((ρ.1 : ℂ).im) 0 with hneg | hnn
            · have h1 : U ≤ γ - (ρ.1 : ℂ).im := by linarith [hγ.1]
              have h2 : -(ρ.1 : ℂ).im ≤ γ - (ρ.1 : ℂ).im := by linarith [hγ.1]
              have hsq1 : U ^ 2 ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith
              have hsq2 : 1 + (ρ.1 : ℂ).im ^ 2 ≤ 2 * ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith [hU4]
              have hm := mul_le_mul hsq1 hsq2 (by positivity) (sq_nonneg _)
              have hp4 : ((ρ.1 : ℂ).im - γ) ^ 2 * (2 * ((ρ.1 : ℂ).im - γ) ^ 2) =
                  2 * ((ρ.1 : ℂ).im - γ) ^ 4 := by ring
              linarith [hm, hp4, hnn_q]
            · have h1 : U / 2 ≤ γ - (ρ.1 : ℂ).im := by linarith [hγ.1]
              have hsq1 : U ^ 2 / 4 ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith
              have him_sq : 1 + (ρ.1 : ℂ).im ^ 2 ≤ U ^ 2 := by nlinarith [hU4]
              have hp4 : (U ^ 2 / 4) * (U ^ 2 / 4) ≤ ((ρ.1 : ℂ).im - γ) ^ 4 := by
                have hm := mul_le_mul hsq1 hsq1 (by positivity) (sq_nonneg _)
                linarith [show ((ρ.1 : ℂ).im - γ) ^ 2 * ((ρ.1 : ℂ).im - γ) ^ 2 =
                  ((ρ.1 : ℂ).im - γ) ^ 4 by ring]
              nlinarith [him_sq, hp4]
          · have h1 : (ρ.1 : ℂ).im / 2 ≤ (ρ.1 : ℂ).im - γ := by linarith [hγ.2]
            have h2 : 2 * U ≤ (ρ.1 : ℂ).im - γ := by linarith [hγ.2]
            have hsq1 : 4 * U ^ 2 ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by nlinarith
            have hsq2 : (1 / 8 : ℝ) * (1 + (ρ.1 : ℂ).im ^ 2) ≤ ((ρ.1 : ℂ).im - γ) ^ 2 := by
              nlinarith [hU4]
            have hm := mul_le_mul hsq1 hsq2 (by positivity) (sq_nonneg _)
            have hp4 : ((ρ.1 : ℂ).im - γ) ^ 2 * ((ρ.1 : ℂ).im - γ) ^ 2 =
                ((ρ.1 : ℂ).im - γ) ^ 4 := by ring
            linarith [hm, hp4, hnn_q]
        have hne_im : (ρ.1 : ℂ).im ≠ γ := by
          intro heq
          rw [heq, sub_self] at hquartic
          norm_num at hquartic
          nlinarith [sq_nonneg (ρ.1 : ℂ).im]
        have hstrip := abs_re_sub_half_le_of_zeroConfig zetaZeroConfig ρ.1
        have hpw := hpw₂ γ ρ.1 hstrip hne_im
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hpw 2
        rw [← Complex.normSq_eq_norm_sq, div_pow] at hsq
        have habs4 : |(ρ.1 : ℂ).im - γ| ^ 2 ^ 2 = ((ρ.1 : ℂ).im - γ) ^ 4 := by
          calc (|(ρ.1 : ℂ).im - γ| ^ 2) ^ 2 = (((ρ.1 : ℂ).im - γ) ^ 2) ^ 2 := by rw [sq_abs]
            _ = ((ρ.1 : ℂ).im - γ) ^ 4 := by ring
        rw [show (|(ρ.1 : ℂ).im - γ| ^ 2) ^ 2 = ((ρ.1 : ℂ).im - γ) ^ 4 from habs4] at hsq
        have hnsq_rem : Complex.normSq (tr (twist γ baseBump) ρ.1) ≤
            (16 * C₂ ^ 2 / U ^ 2) * (1 / (1 + (ρ.1 : ℂ).im ^ 2)) := by
          refine hsq.trans ?_
          have hdiv := div_le_div_of_nonneg_left (sq_nonneg C₂) (by positivity) hquartic
          refine hdiv.trans_eq ?_
          rw [mul_one_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
          ring
        have hdk_exp : depthKernel (c * Real.log γ) (zetaDepth ρ.1) ≤ (2 * U) ^ c := by
          calc depthKernel (c * Real.log γ) (zetaDepth ρ.1)
              ≤ depthKernel L_max (zetaDepth ρ.1) := depthKernel_mono_scale hLγ_nn hLγ_le _
            _ ≤ Real.exp L_max := depthKernel_le_exp_of_abs_le_half hLmax_nn hstrip
            _ = (2 * U) ^ c := by
                dsimp [L_max]; rw [Real.rpow_def_of_pos (by positivity), mul_comm]
        dsimp only [zetaWeight, baseTwistTest]
        calc (zetaZeroConfig.mult ρ.1 : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ.1) *
                depthKernel (c * Real.log γ) (zetaDepth ρ.1)
            ≤ (zetaZeroConfig.mult ρ.1 : ℝ) *
                ((16 * C₂ ^ 2 / U ^ 2) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) * (2 * U) ^ c :=
              mul_le_mul (mul_le_mul_of_nonneg_left hnsq_rem (Nat.cast_nonneg _)) hdk_exp
                (depthKernel_nonneg _ _) (by positivity)
          _ = (16 * C₂ ^ 2 * (2 * U) ^ c / U ^ 2) *
                ((zetaZeroConfig.mult ρ.1 : ℝ) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) := by ring
      have htsum1 := ((summable_heckeDefect (baseTwistTest γ) (c * Real.log γ)).subtype
        ((S_loc : Set zetaZeroConfig.carrier)ᶜ)).tsum_le_tsum hrem_ptw
        ((hsum_lor.subtype _).mul_left _)
      rw [tsum_mul_left] at htsum1
      have hsub_lor : (∑' ρ : ((S_loc : Set zetaZeroConfig.carrier)ᶜ),
          (zetaZeroConfig.mult ρ.1 : ℝ) * (1 / (1 + (ρ.1 : ℂ).im ^ 2))) ≤ L_mass := by
        have hsp := hsum_lor.sum_add_tsum_compl (s := S_loc)
        have hnn_s : 0 ≤ ∑ ρ ∈ S_loc,
            (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) :=
          Finset.sum_nonneg fun _ _ => by positivity
        dsimp only [L_mass]
        linarith [hsp, hnn_s]
      calc (∑' ρ : ((S_loc : Set zetaZeroConfig.carrier)ᶜ),
              zetaWeight (baseTwistTest γ) ρ.1 * depthKernel (c * Real.log γ) (zetaDepth ρ.1))
          ≤ (16 * C₂ ^ 2 * (2 * U) ^ c / U ^ 2) * L_mass :=
            htsum1.trans (mul_le_mul_of_nonneg_left hsub_lor (by positivity))
        _ ≤ C_rem * (2 * U) ^ c / U ^ 2 := by
            dsimp [C_rem]
            have hnn : 0 ≤ (2 * U) ^ c / U ^ 2 := by positivity
            have hrw : (16 * C₂ ^ 2 * (2 * U) ^ c / U ^ 2) * L_mass =
                (16 * C₂ ^ 2 * L_mass) * ((2 * U) ^ c / U ^ 2) := by ring
            have hrw2 : (16 * C₂ ^ 2 * L_mass + 1) * (2 * U) ^ c / U ^ 2 =
                (16 * C₂ ^ 2 * L_mass + 1) * ((2 * U) ^ c / U ^ 2) := by ring
            linarith
    exact add_le_add hloc_part hrem_part
  -- Integrate `hptw_gamma` over `γ ∈ Icc U (2 * U)`
  let g_loc : ℂ → ℝ → ℝ := fun z γ =>
    ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
      (M₀ * (1 / (1 + (z.im - γ) ^ 2)))
  have hg_int : ∀ z ∈ shellZeros (U / 2) (4 * U),
      IntegrableOn (g_loc z) (Icc U (2 * U)) volume := by
    intro z _
    have hcont : Continuous (g_loc z) :=
      continuous_const.mul (continuous_const.mul
        (continuous_const.div (by fun_prop) fun γ => by positivity))
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hsum_int : IntegrableOn
      (fun γ : ℝ => ∑ z ∈ shellZeros (U / 2) (4 * U), g_loc z γ)
      (Icc U (2 * U)) volume :=
    integrable_finsetSum _ hg_int
  have hconst_int : IntegrableOn
      (fun _ : ℝ => C_rem * (2 * U) ^ c / U ^ 2) (Icc U (2 * U)) volume :=
    integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hint_mono := setIntegral_mono_on (integrableOn_heckeDefect_log_Icc hU_pos c)
    (hsum_int.add hconst_int) measurableSet_Icc hptw_gamma
  rw [integral_add hsum_int hconst_int,
    integral_finsetSum (s := shellZeros (U / 2) (4 * U)) (f := g_loc) hg_int,
    setIntegral_const, smul_eq_mul] at hint_mono
  dsimp only [g_loc] at hint_mono
  have hvol_U : volume.real (Icc U (2 * U)) = U := by
    rw [Measure.real_def, Real.volume_Icc, show 2 * U - U = U by ring,
      ENNReal.toReal_ofReal hU_pos.le]
  rw [hvol_U] at hint_mono
  have hsum_lor_int : (∑ z ∈ shellZeros (U / 2) (4 * U),
        ∫ γ in Icc U (2 * U),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2)))) ≤
      C_loc * shellDepthSum (U / 2) (4 * U) L_max := by
    have h1 : ∀ z ∈ shellZeros (U / 2) (4 * U),
        (∫ γ in Icc U (2 * U),
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2)))) ≤
        (Real.pi * M₀) * (((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2)) := by
      intro z _
      have heq_fn : (fun γ : ℝ =>
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
            (M₀ * (1 / (1 + (z.im - γ) ^ 2)))) =
          fun γ : ℝ => (((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) * M₀) *
            (1 / (1 + (z.im - γ) ^ 2)) := by funext γ; ring
      rw [heq_fn, integral_const_mul]
      have hpi := integral_Icc_inv_one_add_sq_sub_le_pi U (2 * U) z.im
      have hm := mul_le_mul_of_nonneg_left hpi
        (by positivity : 0 ≤ ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) * M₀)
      linarith
    calc (∑ z ∈ shellZeros (U / 2) (4 * U),
            ∫ γ in Icc U (2 * U),
               ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L_max (z.re - 1 / 2) *
                (M₀ * (1 / (1 + (z.im - γ) ^ 2))))
        ≤ ∑ z ∈ shellZeros (U / 2) (4 * U),
            (Real.pi * M₀) * (((analyticOrderAt xi z).toNat : ℝ) *
              depthKernel L_max (z.re - 1 / 2)) := Finset.sum_le_sum h1
      _ = (Real.pi * M₀) * shellDepthSum (U / 2) (4 * U) L_max := by
          unfold shellDepthSum; rw [Finset.mul_sum]
      _ ≤ C_loc * shellDepthSum (U / 2) (4 * U) L_max :=
          mul_le_mul_of_nonneg_right (by dsimp [C_loc]; linarith) (shellDepthSum_nonneg _ _ _)
  have hsplit3 : shellDepthSum (U / 2) (4 * U) L_max =
      shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
        shellDepthSum (2 * U) (4 * U) L_max := by
    rw [shellDepthSum_split (by linarith : U / 2 ≤ U) (by linarith : U ≤ 4 * U),
      shellDepthSum_split (by linarith : U ≤ 2 * U) (by linarith : 2 * U ≤ 4 * U), add_assoc]
  have hrem_U : U * (C_rem * (2 * U) ^ c / U ^ 2) = C_rem * (2 * U) ^ c / U := by
    calc U * (C_rem * (2 * U) ^ c / U ^ 2)
        = (C_rem * (2 * U) ^ c / U) * (U / U) := by ring
      _ = C_rem * (2 * U) ^ c / U := by rw [div_self hU_pos.ne', mul_one]
  rw [hsplit3] at hsum_lor_int
  rw [hrem_U] at hint_mono
  exact hint_mono.trans (add_le_add hsum_lor_int le_rfl)

/-- Joint continuity of `(γ, L) ↦ polynomialThetaSourceMomentReading (baseTwistTest γ) L 1 n`
at any fixed stage `n : ℕ`. -/
theorem continuous_polynomialThetaSourceMomentReading_pair (n : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      polynomialThetaSourceMomentReading (baseTwistTest p.1) p.2 1 n) := by
  unfold polynomialThetaSourceMomentReading polynomialThetaSourceReading
  set k : Set ℂ := tsupport (stripSourceCutoff n)
  have hk : IsCompact k := hasCompactSupport_stripSourceCutoff n
  have hcurv_cont : Continuous (finiteThetaSourceCurvature
      (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n)) := by
    have heq : finiteThetaSourceCurvature
        (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n) =
        fun z : ℂ => (1 / 2 : ℝ) * Δ (finiteThetaSourcePotential
          (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n)) z := by
      funext z
      rw [laplacian_finiteThetaSourcePotential (polynomialSourceRegulator_pos n)]
      ring
    rw [heq]
    exact continuous_const.mul (continuous_test_laplacian
      (contDiff_finiteThetaSourcePotential (polynomialSourceRegulator_pos n) _))
  set F : (ℝ × ℝ) → ℂ → ℝ := fun p z =>
    stripSourceCutoff n z * sourceDepthKernel (baseTwistTest p.1) p.2 1 z *
      finiteThetaSourceCurvature (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n) z
  have hF_cont : Continuous F.uncurry := by
    have hcut : Continuous (fun q : (ℝ × ℝ) × ℂ => stripSourceCutoff n q.2) :=
      (contDiff_stripSourceCutoff n).continuous.comp continuous_snd
    have htr_c : Continuous (fun q : (ℝ × ℝ) × ℂ =>
        Complex.normSq (tr (baseTwistTest q.1.1).1 q.2)) := by
      have h1 : (fun q : (ℝ × ℝ) × ℂ => Complex.normSq (tr (baseTwistTest q.1.1).1 q.2)) =
          fun q : (ℝ × ℝ) × ℂ => Complex.normSq (tr baseBumpTest.1 (q.2 - (q.1.1 : ℂ) * I)) :=
        funext fun q => congrArg Complex.normSq (tr_twist q.1.1 baseBump q.2)
      rw [h1]
      exact Complex.continuous_normSq.comp ((contDiff_tr baseBumpTest).continuous.comp
        (continuous_snd.sub ((Complex.continuous_ofReal.comp
          (continuous_fst.comp continuous_fst)).mul continuous_const)))
    have hdk_c : Continuous (fun q : (ℝ × ℝ) × ℂ => depthKernel q.1.2 (q.2.re - 1 / 2) ^ 1) := by
      simp only [pow_one]
      unfold depthKernel
      exact (continuous_const.mul (Real.continuous_cosh.comp
        ((continuous_const.mul ((Complex.continuous_re.comp continuous_snd).sub
          continuous_const)).mul (continuous_snd.comp continuous_fst)))).sub continuous_const
    have hsdk : Continuous (fun q : (ℝ × ℝ) × ℂ =>
        sourceDepthKernel (baseTwistTest q.1.1) q.1.2 1 q.2) := htr_c.mul hdk_c
    exact (hcut.mul hsdk).mul (hcurv_cont.comp continuous_snd)
  have hint_cont : Continuous (fun p : ℝ × ℝ => ∫ z : ℂ, F p z) := by
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support hk hF_cont.continuousOn ?_
    intro p z _ hz
    dsimp [F]
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]
  exact continuous_const.mul hint_cont

/-- Integrability of `γ ↦ polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1 n`
on `Icc U (2 * U)` (`0 < U`). -/
theorem integrableOn_polynomialTheta_log_Icc {U : ℝ} (hU : 0 < U) (c : ℝ) (n : ℕ) :
    IntegrableOn (fun γ : ℝ =>
      polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1 n)
      (Icc U (2 * U)) volume :=
  (continuousOn_comp_log_pair
    (F := fun p => polynomialThetaSourceMomentReading (baseTwistTest p.1) p.2 1 n)
    (continuous_polynomialThetaSourceMomentReading_pair n) hU c).integrableOn_compact isCompact_Icc

/-- Uniform `O(log U)` dyadic-integral comparison between `polynomialThetaSourceMomentReading` at
`linearThetaStage (2 * U)` and `heckeDefect` across `0 ≤ c ≤ 2` and `U ≥ 4` (hence `O(log U / U)`
on the dyadic mean). -/
theorem exists_abs_dyadicIntegral_polynomialTheta_sub_heckeDefect_le :
    ∃ C_lin : ℝ, 0 < C_lin ∧ ∀ U c : ℝ, 4 ≤ U → 0 ≤ c → c ≤ 2 →
      |(∫ γ in Icc U (2 * U),
          polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
            (linearThetaStage (2 * U))) -
        ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)| ≤
      2 * C_lin * Real.log U := by
  obtain ⟨C_lin, hC_lin, hbd⟩ := exists_polynomialReading_sub_heckeDefect_le_log_div
  refine ⟨C_lin, hC_lin, fun U c hU4 hc0 hc2 => ?_⟩
  have hU_pos : 0 < U := by linarith
  set n_U : ℕ := linearThetaStage (2 * U)
  have hint1 := integrableOn_polynomialTheta_log_Icc hU_pos c n_U
  have hint2 := integrableOn_heckeDefect_log_Icc hU_pos c
  rw [← integral_sub hint1 hint2]
  have hptw : ∀ γ ∈ Icc U (2 * U),
      ‖polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1 n_U -
          heckeDefect (baseTwistTest γ) (c * Real.log γ)‖ ≤
        C_lin * Real.log (2 * U) / U := by
    intro γ hγ
    rw [Real.norm_eq_abs]
    have hγ2 : 2 ≤ γ := by linarith [hγ.1]
    have hL0 : 0 ≤ c * Real.log γ := mul_nonneg hc0 (Real.log_nonneg (by linarith))
    have hL2 : c * Real.log γ ≤ 2 * Real.log γ :=
      mul_le_mul_of_nonneg_right hc2 (Real.log_nonneg (by linarith))
    have hn_lo : linearThetaStage γ ≤ n_U := linearThetaStage_mono (by linarith) hγ.2
    have hn_hi : (n_U : ℝ) ≤ 4 * γ + 9 := by
      have hhi := (linearThetaStage_bounds (by linarith : 1 ≤ 2 * U)).2
      dsimp [n_U]; linarith [hγ.1]
    calc |polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1 n_U -
            heckeDefect (baseTwistTest γ) (c * Real.log γ)|
        ≤ C_lin * Real.log γ / γ := hbd γ (c * Real.log γ) n_U hγ2 hL0 hL2 hn_lo hn_hi
      _ ≤ C_lin * Real.log (2 * U) / U := by
          have hnum : C_lin * Real.log γ ≤ C_lin * Real.log (2 * U) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hγ.2) hC_lin.le
          exact (div_le_div_of_nonneg_right hnum (by linarith)).trans
            (div_le_div_of_nonneg_left
              (mul_nonneg hC_lin.le (Real.log_nonneg (by linarith))) hU_pos hγ.1)
  have hnorm_int := (norm_integral_le_integral_norm _).trans
    (setIntegral_mono_on (hint1.sub hint2).norm
      (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      measurableSet_Icc hptw)
  rw [Real.norm_eq_abs, setIntegral_const, smul_eq_mul] at hnorm_int
  have hvol_U : volume.real (Icc U (2 * U)) = U := by
    rw [Measure.real_def, Real.volume_Icc, show 2 * U - U = U by ring,
      ENNReal.toReal_ofReal hU_pos.le]
  rw [hvol_U] at hnorm_int
  have hlog2U : Real.log (2 * U) ≤ 2 * Real.log U := by
    rw [Real.log_mul zero_lt_two.ne' hU_pos.ne']
    linarith [one_le_log_of_four_le hU4, Real.log_two_lt_d9]
  have hcancel : U * (C_lin * Real.log (2 * U) / U) = C_lin * Real.log (2 * U) := by
    calc U * (C_lin * Real.log (2 * U) / U)
        = (C_lin * Real.log (2 * U)) * (U / U) := by ring
      _ = C_lin * Real.log (2 * U) := by rw [div_self hU_pos.ne', mul_one]
  calc |(∫ γ in Icc U (2 * U),
          polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1 n_U -
            heckeDefect (baseTwistTest γ) (c * Real.log γ))|
      ≤ U * (C_lin * Real.log (2 * U) / U) := hnorm_int
    _ = C_lin * Real.log (2 * U) := hcancel
    _ ≤ C_lin * (2 * Real.log U) := mul_le_mul_of_nonneg_left hlog2U hC_lin.le
    _ = 2 * C_lin * Real.log U := by ring

/-- Reusable short end-cap `U^{5/6}` bound for `shellDepthSum W₁ W₂ (c * Real.log (2 * U))`
whenever `16 ≤ U`, `0 ≤ W₁ ≤ W₂`, `W₂ - W₁ ≤ 2`, `W₂ ≤ 2 * U + 1`, and `0 ≤ c ≤ 2 / 3`. -/
private theorem shortEndCap_shellDepthSum_le_five_sixths {U W₁ W₂ c K_log1 : ℝ}
    (hU16 : 16 ≤ U) (hW₁ : 0 ≤ W₁) (h12 : W₁ ≤ W₂) (hlen : W₂ - W₁ ≤ 2) (hW₂ : W₂ ≤ 2 * U + 1)
    (hc0 : 0 ≤ c) (hc : c ≤ 2 / 3) (hK_log1 : 0 < K_log1)
    (hlog1 : ∀ x : ℝ, 1 ≤ x → (1 + Real.log x) ^ 1 ≤ K_log1 * x ^ (1 / 6 : ℝ)) :
    shellDepthSum W₁ W₂ (c * Real.log (2 * U)) ≤
      64 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) := by
  have hU_pos : 0 < U := by linarith
  have hLmax_nn : 0 ≤ c * Real.log (2 * U) := mul_nonneg hc0 (Real.log_nonneg (by linarith))
  have hdk_cap : ∀ z : ℂ, |z.re - 1 / 2| ≤ 1 / 2 →
      depthKernel (c * Real.log (2 * U)) (z.re - 1 / 2) ≤ 2 * U ^ (2 / 3 : ℝ) := by
    intro z hz
    refine (depthKernel_le_exp_of_abs_le_half hLmax_nn hz).trans ?_
    calc Real.exp (c * Real.log (2 * U))
        = (2 * U) ^ c := by rw [Real.rpow_def_of_pos (by positivity), mul_comm]
      _ ≤ (2 * U) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hc
      _ ≤ 2 * U ^ (2 / 3 : ℝ) := by
          rw [Real.mul_rpow zero_le_two hU_pos.le]
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hU_pos.le _)
          calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hord := shortShell_orderSum_le_log hW₁ h12 hlen
  have hlogW : Real.log (W₂ + 4) ≤ 4 + Real.log U := by
    calc Real.log (W₂ + 4) ≤ Real.log (4 * U) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 4 + Real.log U := Real.log_mul (by norm_num) hU_pos.ne'
      _ ≤ 4 + Real.log U := by linarith [log_four_le_two]
  unfold shellDepthSum
  have hsum_dk : ∑ z ∈ shellZeros W₁ W₂,
        ((analyticOrderAt xi z).toNat : ℝ) * depthKernel (c * Real.log (2 * U)) (z.re - 1 / 2) ≤
      (∑ z ∈ shellZeros W₁ W₂, ((analyticOrderAt xi z).toNat : ℝ)) * (2 * U ^ (2 / 3 : ℝ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hdk_cap z ?_)
      (Nat.cast_nonneg _)
    obtain ⟨h0, h1, _, _, _⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1
    rw [abs_le]; constructor <;> linarith
  have hlogU_nn : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  have hpoly1 : |xiLineTwoLogDerivConstant| + Real.log (W₂ + 4) ≤
      2 * (|xiLineTwoLogDerivConstant| + 5) * (1 + Real.log U) ^ 1 := by
    rw [pow_one]
    nlinarith [abs_nonneg xiLineTwoLogDerivConstant, hlogW, hlogU_nn]
  have hpow_le := hlog1 U (by linarith)
  have hU_add : U ^ (1 / 6 : ℝ) * U ^ (2 / 3 : ℝ) = U ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add hU_pos]; norm_num
  calc ∑ z ∈ shellZeros W₁ W₂,
          ((analyticOrderAt xi z).toNat : ℝ) * depthKernel (c * Real.log (2 * U)) (z.re - 1 / 2)
      ≤ 16 * (|xiLineTwoLogDerivConstant| + Real.log (W₂ + 4)) * (2 * U ^ (2 / 3 : ℝ)) :=
        hsum_dk.trans (mul_le_mul_of_nonneg_right hord (by positivity))
    _ ≤ 16 * (2 * (|xiLineTwoLogDerivConstant| + 5) * (K_log1 * U ^ (1 / 6 : ℝ))) *
          (2 * U ^ (2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hpoly1.trans (mul_le_mul_of_nonneg_left hpow_le (by positivity))) (by norm_num))
          (by positivity)
    _ = 64 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 *
          (U ^ (1 / 6 : ℝ) * U ^ (2 / 3 : ℝ)) := by ring
    _ = 64 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) := by rw [hU_add]

/-- **Three-Scale Sieve-Mollified Dyadic Mean Collapse (`exists_dyadicMean_corridor_and_polynomialTheta_le_log`).**
For every `0 < c < 22 / 51`, the dyadic means of `unitWindowDepthCharge T (c log T)`,
`heckeDefect (baseTwistTest γ) (c log γ)`, and `polynomialThetaSourceMomentReading` at the linear
integer-theta prefix `linearThetaStage (2 * U)` all collapse unconditionally to `O_c(log U)`
(with uniform quadratic small-`c` scaling `K_c ≤ K_star * c ^ 2` across `0 < c ≤ 1 / 5`). -/
theorem exists_dyadicMean_corridor_and_polynomialTheta_le_log :
    ∃ K_star : ℝ, 0 < K_star ∧
      ∀ c : ℝ, 0 < c → c < 22 / 51 →
        ∃ K_c : ℝ, 0 < K_c ∧ (c ≤ 1 / 5 → K_c ≤ K_star * c ^ 2) ∧
          ∀ᶠ U : ℝ in atTop,
            (1 / U) * (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) ≤
              K_c * Real.log U ∧
            (1 / U) * (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) ≤
              K_c * Real.log U ∧
            (1 / U) * (∫ γ in Icc U (2 * U),
              polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
                (linearThetaStage (2 * U))) ≤
              K_c * Real.log U := by
  obtain ⟨K_univ, hK_univ, hshell_univ⟩ := exists_shellDepthSum_le_mul_log
  obtain ⟨C_loc, C_rem, hC_loc, hC_rem, hhecke_3sh⟩ := exists_dyadicIntegral_heckeDefect_le_threeShells
  obtain ⟨C_lin, hC_lin, hpoly_diff⟩ := exists_abs_dyadicIntegral_polynomialTheta_sub_heckeDefect_le
  set K_star : ℝ := (C_loc + 1) * (8 * (121 / 100 : ℝ) * K_univ) + 4
  have hKstar_pos : 0 < K_star := by dsimp [K_star]; positivity
  refine ⟨K_star, hKstar_pos, fun c hc0 hc_hi => ?_⟩
  set c' : ℝ := min ((11 / 10 : ℝ) * c) ((c + 22 / 51) / 2)
  have hc_lt_c' : c < c' := lt_min (by linarith) (by linarith)
  have hc'_pos : 0 < c' := hc0.trans hc_lt_c'
  have hc'_lt : c' < 22 / 51 := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨K_sh, hK_sh, hK_sh_small, hev_sh⟩ := hshell_univ c' hc'_pos hc'_lt
  set K_c : ℝ := (C_loc + 1) * (8 * K_sh) + 3 * c ^ 2
  have hKc_pos : 0 < K_c := by dsimp [K_c]; positivity
  have hKc_small : c ≤ 1 / 5 → K_c ≤ K_star * c ^ 2 := by
    intro hc_le
    have hc'_le_940 : c' ≤ 9 / 40 :=
      (min_le_left _ _).trans (by linarith)
    have hc'_sq : c' ^ 2 ≤ (121 / 100 : ℝ) * c ^ 2 := by
      have h1 : c' ≤ (11 / 10 : ℝ) * c := min_le_left _ _
      have h2 := pow_le_pow_left₀ hc'_pos.le h1 2
      linarith
    have hk1 : K_sh ≤ K_univ * ((121 / 100 : ℝ) * c ^ 2) :=
      (hK_sh_small hc'_le_940).trans (mul_le_mul_of_nonneg_left hc'_sq hK_univ.le)
    have hk2 := mul_le_mul_of_nonneg_left hk1 (by positivity : 0 ≤ (C_loc + 1) * 8)
    dsimp [K_c, K_star]
    linarith [sq_nonneg c]
  refine ⟨K_c, hKc_pos, hKc_small, ?_⟩
  have ht_half : Tendsto (fun U : ℝ => U / 2) atTop atTop :=
    tendsto_id.atTop_mul_const (by norm_num)
  have ht_two : Tendsto (fun U : ℝ => 2 * U) atTop atTop :=
    tendsto_id.const_mul_atTop zero_lt_two
  obtain ⟨K_log1, hK_log1, hlog1⟩ := exists_one_add_log_pow_le_rpow 1 (by positivity : (0 : ℝ) < 1 / 6)
  -- Eventual smallness of short end-caps, remote `O(U^{c - 2})` tail, and `O(log U / U)` theta error
  have hev_capU : ∀ᶠ U : ℝ in atTop,
      128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) ≤
        c ^ 2 * U * Real.log U := by
    have ht : Tendsto (fun U : ℝ => U ^ (1 / 6 : ℝ)) atTop atTop := tendsto_rpow_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop
      (128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 / c ^ 2 + 1),
      eventually_ge_atTop (4 : ℝ)] with U hU_r hU4
    have hU_pos : 0 < U := by linarith
    have hlog1_U : 1 ≤ Real.log U := one_le_log_of_four_le hU4
    have hsplit : U ^ (5 / 6 : ℝ) * U ^ (1 / 6 : ℝ) = U := by
      rw [← Real.rpow_add hU_pos]; norm_num
    have hm1 := (div_le_iff₀ (by positivity : 0 < c ^ 2)).mp
      (by linarith : 128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 / c ^ 2 ≤ U ^ (1 / 6 : ℝ))
    have hm2 := mul_le_mul_of_nonneg_left hm1 (Real.rpow_nonneg hU_pos.le (5 / 6))
    have hrew : U ^ (5 / 6 : ℝ) * (U ^ (1 / 6 : ℝ) * c ^ 2) = c ^ 2 * U := by
      calc U ^ (5 / 6 : ℝ) * (U ^ (1 / 6 : ℝ) * c ^ 2)
          = c ^ 2 * (U ^ (5 / 6 : ℝ) * U ^ (1 / 6 : ℝ)) := by ring
        _ = c ^ 2 * U := by rw [hsplit]
    rw [hrew] at hm2
    exact hm2.trans (le_mul_of_one_le_right (by positivity) hlog1_U)
  set δ_c : ℝ := c' - c
  have hδc_pos : 0 < δ_c := sub_pos.mpr hc_lt_c'
  filter_upwards [ht_half.eventually hev_sh, hev_sh, ht_two.eventually hev_sh,
    Real.tendsto_log_atTop.eventually_ge_atTop ((c + c') * Real.log 2 / δ_c + 4),
    eventually_ge_atTop (max 16 (max (4 * C_rem / c ^ 2 + 1) (2 * C_lin / c ^ 2 + 1))),
    hev_capU]
    with U hsh_half hsh_U hsh_2U hlogU_big hU_big hcap_U
  have hU16 : 16 ≤ U := (le_max_left _ _).trans hU_big
  have hU_rem : 4 * C_rem / c ^ 2 + 1 ≤ U :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hU_big
  have hU_lin : 2 * C_lin / c ^ 2 + 1 ≤ U :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hU_big
  have hU_pos : 0 < U := by linarith
  have hlogU_ge4 : 4 ≤ Real.log U := by
    have : 0 ≤ (c + c') * Real.log 2 / δ_c := by positivity
    linarith
  set L_max : ℝ := c * Real.log (2 * U)
  have hLmax_nn : 0 ≤ L_max := mul_nonneg hc0.le (Real.log_nonneg (by linarith))
  -- Scale inequality `L_max = c log(2U) ≤ c' log(U / 2)`
  have hL_le_half : L_max ≤ c' * Real.log (U / 2) := by
    have hlog2U : Real.log (2 * U) = Real.log 2 + Real.log U :=
      Real.log_mul zero_lt_two.ne' hU_pos.ne'
    have hlogU2 : Real.log (U / 2) = Real.log U - Real.log 2 :=
      Real.log_div hU_pos.ne' zero_lt_two.ne'
    dsimp [L_max]
    rw [hlog2U, hlogU2]
    have hm := (div_le_iff₀ hδc_pos).mp
      (by linarith : (c + c') * Real.log 2 / δ_c ≤ Real.log U)
    dsimp [δ_c] at hm
    nlinarith
  have hL_le_U : L_max ≤ c' * Real.log U :=
    hL_le_half.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (by linarith)) hc'_pos.le)
  have hL_le_2U : L_max ≤ c' * Real.log (2 * U) :=
    hL_le_U.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log hU_pos (by linarith)) hc'_pos.le)
  -- Three adjacent dyadic shell bounds
  have hb_half : shellDepthSum (U / 2) U L_max ≤ K_sh * U * Real.log U := by
    have h1 := hsh_half L_max hLmax_nn hL_le_half
    rw [show 2 * (U / 2) = U by ring] at h1
    have hlog_le : Real.log (U / 2) ≤ Real.log U :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog_nn : 0 ≤ Real.log (U / 2) := Real.log_nonneg (by linarith)
    have hKU : K_sh * (U / 2) ≤ K_sh * U :=
      mul_le_mul_of_nonneg_left (by linarith) hK_sh.le
    exact h1.trans (mul_le_mul hKU hlog_le hlog_nn (by positivity))
  have hb_U : shellDepthSum U (2 * U) L_max ≤ K_sh * U * Real.log U :=
    hsh_U L_max hLmax_nn hL_le_U
  have hb_2U : shellDepthSum (2 * U) (4 * U) L_max ≤ 4 * K_sh * U * Real.log U := by
    have h1 := hsh_2U L_max hLmax_nn hL_le_2U
    rw [show 2 * (2 * U) = 4 * U by ring] at h1
    have hlog2U : Real.log (2 * U) ≤ 2 * Real.log U := by
      rw [Real.log_mul zero_lt_two.ne' hU_pos.ne']
      linarith [Real.log_two_lt_d9]
    calc shellDepthSum (2 * U) (4 * U) L_max
        ≤ K_sh * (2 * U) * Real.log (2 * U) := h1
      _ ≤ K_sh * (2 * U) * (2 * Real.log U) :=
          mul_le_mul_of_nonneg_left hlog2U (by positivity)
      _ = 4 * K_sh * U * Real.log U := by ring
  -- 1. Bound `∫_U^{2U} unitWindowDepthCharge`
  have huwd_raw : (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) ≤
      (K_sh + c ^ 2) * U * Real.log U := by
    have h1 := dyadicIntegral_unitWindowDepthCharge_le_shellDepthSum (by linarith : 1 ≤ U) hc0.le
    rw [shellDepthSum_split (by linarith : U - 1 ≤ U) (by linarith : U ≤ 2 * U + 1),
      shellDepthSum_split (by linarith : U ≤ 2 * U) (by linarith : 2 * U ≤ 2 * U + 1)] at h1
    have hc1 := shortEndCap_shellDepthSum_le_five_sixths hU16
      (by linarith : 0 ≤ U - 1) (by linarith) (by linarith) (by linarith)
      hc0.le (by linarith) hK_log1 hlog1
    have hc2 := shortEndCap_shellDepthSum_le_five_sixths hU16
      (by linarith : 0 ≤ 2 * U) (by linarith) (by linarith) le_rfl
      hc0.le (by linarith) hK_log1 hlog1
    have hcaps : shellDepthSum (U - 1) U L_max + shellDepthSum (2 * U) (2 * U + 1) L_max ≤
        c ^ 2 * U * Real.log U := by
      calc shellDepthSum (U - 1) U L_max + shellDepthSum (2 * U) (2 * U + 1) L_max
          ≤ 64 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) +
              64 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) :=
            add_le_add hc1 hc2
        _ = 128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) := by ring
        _ ≤ c ^ 2 * U * Real.log U := hcap_U
    calc (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T))
        ≤ shellDepthSum (U - 1) U L_max +
            (shellDepthSum U (2 * U) L_max + shellDepthSum (2 * U) (2 * U + 1) L_max) := h1
      _ = shellDepthSum U (2 * U) L_max +
            (shellDepthSum (U - 1) U L_max + shellDepthSum (2 * U) (2 * U + 1) L_max) := by ring
      _ ≤ K_sh * U * Real.log U + c ^ 2 * U * Real.log U := add_le_add hb_U hcaps
      _ = (K_sh + c ^ 2) * U * Real.log U := by ring
  -- 2. Bound `∫_U^{2U} heckeDefect`
  have hint_hd_raw : (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) ≤
      (C_loc * (6 * K_sh) + c ^ 2) * U * Real.log U := by
    have h3 := hhecke_3sh U c (by linarith) hc0.le
    have hrem_small : C_rem * (2 * U) ^ c / U ≤ c ^ 2 * U * Real.log U := by
      have h2U_c : (2 * U) ^ c ≤ 2 * U := by
        calc (2 * U) ^ c ≤ (2 * U) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = 2 * U := Real.rpow_one _
      have h1 : C_rem * (2 * U) ^ c / U ≤ 2 * C_rem := by
        rw [div_le_iff₀ hU_pos]; nlinarith [hC_rem]
      have h2 : 2 * C_rem ≤ c ^ 2 * U := by
        have hm := (div_le_iff₀ (by positivity : 0 < c ^ 2)).mp
          (by linarith : 4 * C_rem / c ^ 2 ≤ U)
        linarith
      exact (h1.trans h2).trans (le_mul_of_one_le_right (by positivity) (by linarith))
    have hsh_sum : shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
        shellDepthSum (2 * U) (4 * U) L_max ≤ (6 * K_sh) * (U * Real.log U) := by
      calc shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
              shellDepthSum (2 * U) (4 * U) L_max
          ≤ K_sh * U * Real.log U + K_sh * U * Real.log U + 4 * K_sh * U * Real.log U :=
            add_le_add (add_le_add hb_half hb_U) hb_2U
        _ = (6 * K_sh) * (U * Real.log U) := by ring
    calc (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ))
        ≤ C_loc * (shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
            shellDepthSum (2 * U) (4 * U) L_max) + C_rem * (2 * U) ^ c / U := h3
      _ ≤ C_loc * ((6 * K_sh) * (U * Real.log U)) + c ^ 2 * U * Real.log U :=
          add_le_add (mul_le_mul_of_nonneg_left hsh_sum hC_loc.le) hrem_small
      _ = (C_loc * (6 * K_sh) + c ^ 2) * U * Real.log U := by ring
  -- 3. Bound `∫_U^{2U} polynomialThetaSourceMomentReading`
  have hpoly_raw : (∫ γ in Icc U (2 * U),
      polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
        (linearThetaStage (2 * U))) ≤
      (C_loc * (6 * K_sh) + 2 * c ^ 2) * U * Real.log U := by
    have hdiff := (le_abs_self _).trans (hpoly_diff U c (by linarith) hc0.le (by linarith))
    have hlin_small : 2 * C_lin * Real.log U ≤ c ^ 2 * U * Real.log U := by
      have hm := (div_le_iff₀ (by positivity : 0 < c ^ 2)).mp
        (by linarith : 2 * C_lin / c ^ 2 ≤ U)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hsub_le : (∫ γ in Icc U (2 * U),
        polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
          (linearThetaStage (2 * U))) ≤
        (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) +
          2 * C_lin * Real.log U := sub_le_iff_le_add'.mp hdiff
    calc (∫ γ in Icc U (2 * U),
            polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
              (linearThetaStage (2 * U)))
        ≤ (C_loc * (6 * K_sh) + c ^ 2) * U * Real.log U + c ^ 2 * U * Real.log U :=
          hsub_le.trans (add_le_add hint_hd_raw hlin_small)
      _ = (C_loc * (6 * K_sh) + 2 * c ^ 2) * U * Real.log U := by ring
  have hdiv_U_log : ∀ M : ℝ, M ≤ K_c →
      (1 / U) * (M * U * Real.log U) ≤ K_c * Real.log U := by
    intro M hM
    have hsimp : (1 / U) * (M * U * Real.log U) = M * Real.log U := by
      calc (1 / U) * (M * U * Real.log U)
          = (M * Real.log U) * (U / U) := by ring
        _ = M * Real.log U := by rw [div_self hU_pos.ne', mul_one]
    rw [hsimp]
    exact mul_le_mul_of_nonneg_right hM (by linarith)
  have hCK_nn : 0 ≤ C_loc * K_sh := mul_nonneg hC_loc.le hK_sh.le
  have hM1 : K_sh + c ^ 2 ≤ K_c := by
    dsimp [K_c]; rw [add_mul, one_mul]; linarith [sq_nonneg c]
  have hM2 : C_loc * (6 * K_sh) + c ^ 2 ≤ K_c := by
    dsimp [K_c]; rw [add_mul, one_mul]; linarith [sq_nonneg c]
  have hM3 : C_loc * (6 * K_sh) + 2 * c ^ 2 ≤ K_c := by
    dsimp [K_c]; rw [add_mul, one_mul]; linarith [sq_nonneg c]
  exact ⟨(mul_le_mul_of_nonneg_left huwd_raw (by positivity)).trans (hdiv_U_log _ hM1),
    (mul_le_mul_of_nonneg_left hint_hd_raw (by positivity)).trans (hdiv_U_log _ hM2),
    (mul_le_mul_of_nonneg_left hpoly_raw (by positivity)).trans (hdiv_U_log _ hM3)⟩

/-- **Sub-Power Dyadic Mean Bound up to `c < 2 / 3` (`exists_dyadicMean_polynomialTheta_subpower_up_to_two_thirds`).**
Across the full Ingham–Guth–Maynard zero-density regime `0 < c < 2 / 3`, for every `η > 0`, the
dyadic means of `unitWindowDepthCharge`, `heckeDefect`, and the linear-stage
`polynomialThetaSourceMomentReading` are bounded by `O_{c, η}(U ^ η)`. -/
theorem exists_dyadicMean_polynomialTheta_subpower_up_to_two_thirds
    {c η : ℝ} (hc0 : 0 < c) (hc : c < 2 / 3) (hη : 0 < η) :
    ∃ C_sub : ℝ, 0 < C_sub ∧ ∀ᶠ U : ℝ in atTop,
      (1 / U) * (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) ≤
        C_sub * U ^ η ∧
      (1 / U) * (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) ≤
        C_sub * U ^ η ∧
      (1 / U) * (∫ γ in Icc U (2 * U),
        polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
          (linearThetaStage (2 * U))) ≤
        C_sub * U ^ η := by
  set c' : ℝ := (c + 2 / 3) / 2
  have hc_lt : c < c' := by dsimp [c']; linarith
  have hc'_lt : c' < 2 / 3 := by dsimp [c']; linarith
  obtain ⟨C_sh, hC_sh, hev_sh⟩ := exists_shellDepthSum_le_subpower (by linarith : 0 ≤ c') hc'_lt hη
  obtain ⟨C_loc, C_rem, hC_loc, hC_rem, hhecke_3sh⟩ := exists_dyadicIntegral_heckeDefect_le_threeShells
  obtain ⟨C_lin, hC_lin, hpoly_diff⟩ := exists_abs_dyadicIntegral_polynomialTheta_sub_heckeDefect_le
  obtain ⟨K_log1, hK_log1, hlog1⟩ := exists_one_add_log_pow_le_rpow 1 (by positivity : (0 : ℝ) < 1 / 6)
  set C_out : ℝ := (C_loc + 1) * ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) + 3
  refine ⟨C_out, by dsimp [C_out]; positivity, ?_⟩
  have ht_half : Tendsto (fun U : ℝ => U / 2) atTop atTop :=
    tendsto_id.atTop_mul_const (by norm_num)
  have ht_two : Tendsto (fun U : ℝ => 2 * U) atTop atTop :=
    tendsto_id.const_mul_atTop zero_lt_two
  set δ_c : ℝ := c' - c
  have hδc_pos : 0 < δ_c := sub_pos.mpr hc_lt
  have hev_cap_sub : ∀ᶠ U : ℝ in atTop,
      128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) ≤ U ^ (1 + η) := by
    have ht : Tendsto (fun U : ℝ => U ^ (1 / 6 + η)) atTop atTop :=
      tendsto_rpow_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop
      (128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 + 1),
      eventually_ge_atTop (4 : ℝ)] with U hUr hU4
    have hU_pos : 0 < U := by linarith
    have hm := mul_le_mul_of_nonneg_left
      (by linarith : 128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 ≤ U ^ (1 / 6 + η))
      (Real.rpow_nonneg hU_pos.le (5 / 6))
    have hrew : U ^ (5 / 6 : ℝ) * U ^ (1 / 6 + η) = U ^ (1 + η) := by
      rw [← Real.rpow_add hU_pos]; ring_nf
    calc 128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ)
        = U ^ (5 / 6 : ℝ) * (128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1) := by ring
      _ ≤ U ^ (5 / 6 : ℝ) * U ^ (1 / 6 + η) := hm
      _ = U ^ (1 + η) := hrew
  filter_upwards [ht_half.eventually hev_sh, hev_sh, ht_two.eventually hev_sh,
    Real.tendsto_log_atTop.eventually_ge_atTop ((c + c') * Real.log 2 / δ_c + 4),
    eventually_ge_atTop (max 16 (4 * C_rem + 1)),
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 5 / 6)).eventually_ge_atTop
      (2 * C_lin * K_log1 + 1),
    hev_cap_sub]
    with U hsh_half hsh_U hsh_2U hlogU_big hU_big hU_lin56 hcap_U
  have hU16 : 16 ≤ U := (le_max_left _ _).trans hU_big
  have hU_rem : 4 * C_rem + 1 ≤ U := (le_max_right _ _).trans hU_big
  have hU_pos : 0 < U := by linarith
  have hU1_eta : U ≤ U ^ (1 + η) := by
    calc U = U ^ (1 : ℝ) := (Real.rpow_one U).symm
      _ ≤ U ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  set L_max : ℝ := c * Real.log (2 * U)
  have hLmax_nn : 0 ≤ L_max := mul_nonneg hc0.le (Real.log_nonneg (by linarith))
  have hL_le_half : L_max ≤ c' * Real.log (U / 2) := by
    have hlog2U : Real.log (2 * U) = Real.log 2 + Real.log U :=
      Real.log_mul zero_lt_two.ne' hU_pos.ne'
    have hlogU2 : Real.log (U / 2) = Real.log U - Real.log 2 :=
      Real.log_div hU_pos.ne' zero_lt_two.ne'
    dsimp [L_max]; rw [hlog2U, hlogU2]
    have hm := (div_le_iff₀ hδc_pos).mp (by linarith : (c + c') * Real.log 2 / δ_c ≤ Real.log U)
    dsimp [δ_c] at hm; nlinarith
  have hL_le_U : L_max ≤ c' * Real.log U :=
    hL_le_half.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (by linarith)) (by linarith))
  have hL_le_2U : L_max ≤ c' * Real.log (2 * U) :=
    hL_le_U.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log hU_pos (by linarith)) (by linarith))
  have hb_half : shellDepthSum (U / 2) U L_max ≤ C_sh * U ^ (1 + η) := by
    have h1 := hsh_half L_max hLmax_nn hL_le_half
    rw [show 2 * (U / 2) = U by ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)) hC_sh.le)
  have hb_U : shellDepthSum U (2 * U) L_max ≤ C_sh * U ^ (1 + η) :=
    hsh_U L_max hLmax_nn hL_le_U
  have hb_2U : shellDepthSum (2 * U) (4 * U) L_max ≤ (2 : ℝ) ^ (1 + η) * C_sh * U ^ (1 + η) := by
    have h1 := hsh_2U L_max hLmax_nn hL_le_2U
    rw [show 2 * (2 * U) = 4 * U by ring, Real.mul_rpow zero_le_two hU_pos.le] at h1
    exact h1.trans_eq (by ring)
  -- 1. `unitWindowDepthCharge`
  have huwd_raw : (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) ≤
      (C_sh + 1) * U ^ (1 + η) := by
    have h1 := dyadicIntegral_unitWindowDepthCharge_le_shellDepthSum (by linarith : 1 ≤ U) hc0.le
    rw [shellDepthSum_split (by linarith : U - 1 ≤ U) (by linarith : U ≤ 2 * U + 1),
      shellDepthSum_split (by linarith : U ≤ 2 * U) (by linarith : 2 * U ≤ 2 * U + 1)] at h1
    have hc1 := shortEndCap_shellDepthSum_le_five_sixths hU16
      (by linarith : 0 ≤ U - 1) (by linarith) (by linarith) (by linarith)
      hc0.le hc.le hK_log1 hlog1
    have hc2 := shortEndCap_shellDepthSum_le_five_sixths hU16
      (by linarith : 0 ≤ 2 * U) (by linarith) (by linarith) le_rfl
      hc0.le hc.le hK_log1 hlog1
    have hcaps : shellDepthSum (U - 1) U L_max + shellDepthSum (2 * U) (2 * U + 1) L_max ≤
        U ^ (1 + η) := by
      calc shellDepthSum (U - 1) U L_max + shellDepthSum (2 * U) (2 * U + 1) L_max
          ≤ 64 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) +
              64 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) :=
            add_le_add hc1 hc2
        _ = 128 * (|xiLineTwoLogDerivConstant| + 5) * K_log1 * U ^ (5 / 6 : ℝ) := by ring
        _ ≤ U ^ (1 + η) := hcap_U
    calc (∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T))
        ≤ shellDepthSum (U - 1) U L_max +
            (shellDepthSum U (2 * U) L_max + shellDepthSum (2 * U) (2 * U + 1) L_max) := h1
      _ = shellDepthSum U (2 * U) L_max +
            (shellDepthSum (U - 1) U L_max + shellDepthSum (2 * U) (2 * U + 1) L_max) := by ring
      _ ≤ C_sh * U ^ (1 + η) + U ^ (1 + η) := add_le_add hb_U hcaps
      _ = (C_sh + 1) * U ^ (1 + η) := by ring
  -- 2. `heckeDefect`
  have hhd_raw : (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) ≤
      (C_loc * ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) + 1) * U ^ (1 + η) := by
    have h3 := hhecke_3sh U c (by linarith) hc0.le
    have hrem_small : C_rem * (2 * U) ^ c / U ≤ U ^ (1 + η) := by
      have h2U_c : (2 * U) ^ c ≤ 2 * U := by
        calc (2 * U) ^ c ≤ (2 * U) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = 2 * U := Real.rpow_one _
      have h1 : C_rem * (2 * U) ^ c / U ≤ 2 * C_rem := by
        rw [div_le_iff₀ hU_pos]; nlinarith [hC_rem]
      exact (h1.trans (by linarith)).trans hU1_eta
    have hsh_sum : shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
        shellDepthSum (2 * U) (4 * U) L_max ≤
        ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) * U ^ (1 + η) := by
      calc shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
              shellDepthSum (2 * U) (4 * U) L_max
          ≤ C_sh * U ^ (1 + η) + C_sh * U ^ (1 + η) + (2 : ℝ) ^ (1 + η) * C_sh * U ^ (1 + η) :=
            add_le_add (add_le_add hb_half hb_U) hb_2U
        _ = ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) * U ^ (1 + η) := by ring
    calc (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ))
        ≤ C_loc * (shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
            shellDepthSum (2 * U) (4 * U) L_max) + C_rem * (2 * U) ^ c / U := h3
      _ ≤ C_loc * (((2 + (2 : ℝ) ^ (1 + η)) * C_sh) * U ^ (1 + η)) + U ^ (1 + η) :=
          add_le_add (mul_le_mul_of_nonneg_left hsh_sum hC_loc.le) hrem_small
      _ = (C_loc * ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) + 1) * U ^ (1 + η) := by ring
  -- 3. `polynomialThetaSourceMomentReading`
  have hpoly_raw : (∫ γ in Icc U (2 * U),
      polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
        (linearThetaStage (2 * U))) ≤
      (C_loc * ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) + 2) * U ^ (1 + η) := by
    have hdiff := (le_abs_self _).trans (hpoly_diff U c (by linarith) hc0.le (by linarith))
    have hlin_small : 2 * C_lin * Real.log U ≤ U ^ (1 + η) := by
      have h1 : Real.log U ≤ K_log1 * U ^ (1 / 6 : ℝ) := by
        have := hlog1 U (by linarith)
        rw [pow_one] at this; linarith
      have hm1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * C_lin)
      have hm2 := mul_le_mul_of_nonneg_right
        (by linarith : 2 * C_lin * K_log1 ≤ U ^ (5 / 6 : ℝ))
        (Real.rpow_nonneg hU_pos.le (1 / 6))
      have hrew : U ^ (5 / 6 : ℝ) * U ^ (1 / 6 : ℝ) = U := by
        rw [← Real.rpow_add hU_pos]; norm_num
      calc 2 * C_lin * Real.log U
          ≤ 2 * C_lin * (K_log1 * U ^ (1 / 6 : ℝ)) := hm1
        _ = (2 * C_lin * K_log1) * U ^ (1 / 6 : ℝ) := by ring
        _ ≤ U ^ (5 / 6 : ℝ) * U ^ (1 / 6 : ℝ) := hm2
        _ = U := hrew
        _ ≤ U ^ (1 + η) := hU1_eta
    have hsub_le : (∫ γ in Icc U (2 * U),
        polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
          (linearThetaStage (2 * U))) ≤
        (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) +
          2 * C_lin * Real.log U := sub_le_iff_le_add'.mp hdiff
    calc (∫ γ in Icc U (2 * U),
            polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
              (linearThetaStage (2 * U)))
        ≤ (C_loc * ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) + 1) * U ^ (1 + η) + U ^ (1 + η) :=
          hsub_le.trans (add_le_add hhd_raw hlin_small)
      _ = (C_loc * ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) + 2) * U ^ (1 + η) := by ring
  have hdiv_U : ∀ M : ℝ, M ≤ C_out →
      (1 / U) * (M * U ^ (1 + η)) ≤ C_out * U ^ η := by
    intro M hM
    have hsplit : U ^ (1 + η) = U * U ^ η := by
      rw [Real.rpow_add hU_pos, Real.rpow_one]
    have hsimp : (1 / U) * (M * U ^ (1 + η)) = M * U ^ η := by
      rw [hsplit]
      calc (1 / U) * (M * (U * U ^ η))
          = (M * U ^ η) * (U / U) := by ring
        _ = M * U ^ η := by rw [div_self hU_pos.ne', mul_one]
    rw [hsimp]
    exact mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hU_pos.le _)
  have hrpow_nn : 0 ≤ (2 : ℝ) ^ (1 + η) := Real.rpow_nonneg zero_le_two _
  have hprod_nn : 0 ≤ C_loc * ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) := by positivity
  have h2_ge : C_sh ≤ (2 + (2 : ℝ) ^ (1 + η)) * C_sh :=
    le_mul_of_one_le_left hC_sh.le (by linarith)
  have hM1 : C_sh + 1 ≤ C_out := by
    dsimp [C_out]; rw [add_mul, one_mul]; linarith
  have hM2 : C_loc * ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) + 1 ≤ C_out := by
    dsimp [C_out]; rw [add_mul, one_mul]; linarith [le_trans hC_sh.le h2_ge]
  have hM3 : C_loc * ((2 + (2 : ℝ) ^ (1 + η)) * C_sh) + 2 ≤ C_out := by
    dsimp [C_out]; rw [add_mul, one_mul]; linarith [le_trans hC_sh.le h2_ge]
  exact ⟨(mul_le_mul_of_nonneg_left huwd_raw (by positivity)).trans (hdiv_U _ hM1),
    (mul_le_mul_of_nonneg_left hhd_raw (by positivity)).trans (hdiv_U _ hM2),
    (mul_le_mul_of_nonneg_left hpoly_raw (by positivity)).trans (hdiv_U _ hM3)⟩

/-! ## §6. Unconditional almost-all unit-window `(6/5) log(log T) / log T` zero-free corridor -/

/-- Pure scalar algebra converting the Barban–Vehov bound at `a_U = (25/22) * Real.log (Real.log U)`
into an upper bound on `2 * W_sum`. -/
private theorem barbanVehov_loglog_count_algebra {U A K L_S a_U T₁ T₂ W_sum : ℝ}
    (hU_pos : 0 < U) (hA : 0 < A) (hK : 0 ≤ K)
    (hlog50 : 50 ≤ Real.log U) (hll_pos : 0 < Real.log (Real.log U))
    (hLS_pos : 0 < L_S) (hLS_le_1add : L_S ≤ 1 + Real.log U) (hLS_le_2logU : L_S ≤ 2 * Real.log U)
    (ha_eq : a_U = (25 / 22 : ℝ) * Real.log (Real.log U)) (ha_lo : 1 ≤ a_U)
    (hlen : T₂ - T₁ ≤ U)
    (hbv : 2 * Real.pi * ((a_U / L_S) * W_sum) ≤
      (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a_U))) + K * L_S) :
    2 * W_sum ≤ (2 * A / 3) * U / Real.log (Real.log U) + 2 * K * (1 + Real.log U) ^ 3 := by
  have hexp_a : Real.exp (-(22 / 25 * a_U)) = (Real.log U)⁻¹ := by
    have harg : -(22 / 25 * a_U) = -Real.log (Real.log U) := by rw [ha_eq]; ring
    rw [harg, Real.exp_neg, Real.exp_log (by linarith : 0 < Real.log U)]
  rw [hexp_a] at hbv
  have hrhs_le : (T₂ - T₁) * (A * (Real.log U)⁻¹) + K * L_S ≤ U * A / Real.log U + K * L_S := by
    have h1 : (T₂ - T₁) * (A * (Real.log U)⁻¹) ≤ U * (A * (Real.log U)⁻¹) :=
      mul_le_mul_of_nonneg_right hlen (mul_nonneg hA.le (inv_nonneg.mpr (by linarith)))
    rw [show U * A / Real.log U = U * (A * (Real.log U)⁻¹) by ring]
    exact add_le_add h1 le_rfl
  have hbv' := hbv.trans hrhs_le
  have hden_pos : 0 < Real.pi * a_U := mul_pos Real.pi_pos (by linarith)
  have hm_div := mul_le_mul_of_nonneg_left hbv' (div_nonneg hLS_pos.le hden_pos.le)
  have hlhs_simp : (L_S / (Real.pi * a_U)) * (2 * Real.pi * ((a_U / L_S) * W_sum)) =
      2 * W_sum := by
    calc (L_S / (Real.pi * a_U)) * (2 * Real.pi * ((a_U / L_S) * W_sum))
        = (2 * W_sum) * ((Real.pi * a_U) / (Real.pi * a_U)) * (L_S / L_S) := by ring
      _ = 2 * W_sum := by rw [div_self hden_pos.ne', div_self hLS_pos.ne', mul_one, mul_one]
  rw [hlhs_simp, mul_add] at hm_div
  have hlogU_ne : Real.log U ≠ 0 := by linarith
  have hterm1 : (L_S / (Real.pi * a_U)) * (U * A / Real.log U) ≤
      (2 * A / 3) * U / Real.log (Real.log U) := by
    have hnum : L_S * (U * A / Real.log U) ≤ 2 * A * U := by
      calc L_S * (U * A / Real.log U)
          ≤ (2 * Real.log U) * (U * A / Real.log U) :=
            mul_le_mul_of_nonneg_right hLS_le_2logU
              (div_nonneg (mul_nonneg hU_pos.le hA.le) (by linarith))
        _ = (2 * A * U) * (Real.log U / Real.log U) := by ring
        _ = 2 * A * U := by rw [div_self hlogU_ne, mul_one]
    have hden_ge : 3 * Real.log (Real.log U) ≤ Real.pi * a_U := by
      have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
      have ha_ge : Real.log (Real.log U) ≤ a_U := by rw [ha_eq]; linarith
      exact mul_le_mul hpi3 ha_ge hll_pos.le Real.pi_pos.le
    calc (L_S / (Real.pi * a_U)) * (U * A / Real.log U)
        = (L_S * (U * A / Real.log U)) / (Real.pi * a_U) := by ring
      _ ≤ (2 * A * U) / (Real.pi * a_U) := div_le_div_of_nonneg_right hnum hden_pos.le
      _ ≤ (2 * A * U) / (3 * Real.log (Real.log U)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
      _ = (2 * A / 3) * U / Real.log (Real.log U) := by ring
  have hterm2 : (L_S / (Real.pi * a_U)) * (K * L_S) ≤ 2 * K * (1 + Real.log U) ^ 3 := by
    have hden1 : 1 ≤ Real.pi * a_U := by
      calc (1 : ℝ) ≤ 3 * 1 := by norm_num
        _ ≤ Real.pi * a_U := mul_le_mul Real.pi_gt_three.le ha_lo zero_le_one Real.pi_pos.le
    have h1 : (L_S / (Real.pi * a_U)) * (K * L_S) ≤ K * L_S ^ 2 := by
      rw [show (L_S / (Real.pi * a_U)) * (K * L_S) = (K * L_S ^ 2) / (Real.pi * a_U) by ring]
      exact div_le_self (by positivity) hden1
    have hsq : L_S ^ 2 ≤ (1 + Real.log U) ^ 3 := by
      have h2 : L_S ^ 2 ≤ (1 + Real.log U) ^ 2 := pow_le_pow_left₀ hLS_pos.le hLS_le_1add 2
      have h23 : (1 + Real.log U) ^ 2 ≤ (1 + Real.log U) ^ 3 :=
        pow_le_pow_right₀ (by linarith) (by omega)
      exact h2.trans h23
    calc (L_S / (Real.pi * a_U)) * (K * L_S)
        ≤ K * L_S ^ 2 := h1
      _ ≤ K * (1 + Real.log U) ^ 3 := mul_le_mul_of_nonneg_left hsq hK
      _ ≤ 2 * K * (1 + Real.log U) ^ 3 := by
          have : 0 ≤ K * (1 + Real.log U) ^ 3 := mul_nonneg hK (by positivity)
          linarith
  exact hm_div.trans (add_le_add hterm1 hterm2)

/-- **Unconditional Almost-All Unit-Window `(6/5) log(log T) / log T` Corridor
(`eventually_volume_badLogLogCorridor_unitWindows_le`).**
All unit windows `[T, T + 1)` (`T ∈ [U, 2U]`) outside an exceptional set of Lebesgue measure
`O(U / log(log U))` are completely free of zeros with `|Re ρ - 1/2| ≥ (6/5) log(log T) / log T`. -/
theorem eventually_volume_badLogLogCorridor_unitWindows_le :
    ∃ C_bad : ℝ, 0 < C_bad ∧ ∀ᶠ U : ℝ in atTop,
      volume {T ∈ Icc U (2 * U) |
        ∃ ρ ∈ xiUnitWindowZeros T,
          (6 / 5 : ℝ) * Real.log (Real.log T) / Real.log T ≤ |ρ.re - 1 / 2|} ≤
        ENNReal.ofReal (C_bad * U / Real.log (Real.log U)) := by
  obtain ⟨A, K, hA, hK, hbv_ev⟩ := exists_selberg_criticalGate_nearLine_zeroDensity
  obtain ⟨K_ll, hK_ll, hll⟩ := exists_one_add_log_pow_le_rpow 1 (by positivity : (0 : ℝ) < 1 / 2)
  obtain ⟨K_log4, hK_log4, hlog4⟩ := exists_one_add_log_pow_le_rpow 4 (by positivity : (0 : ℝ) < 1 / 2)
  set M_poly : ℝ := 2 * K + 32 * (|xiLineTwoLogDerivConstant| + 5)
  have hMpoly_pos : 0 < M_poly := by
    dsimp [M_poly]
    have := abs_nonneg xiLineTwoLogDerivConstant
    positivity
  set C_bad : ℝ := 2 * A / 3 + 2
  refine ⟨C_bad, by dsimp [C_bad]; positivity, ?_⟩
  have ht_32 : Tendsto (fun U : ℝ => (3 / 2 : ℝ) * U) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have ht_loglog : Tendsto (fun U : ℝ => Real.log (Real.log U)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ht_sqrt_log : Tendsto (fun U : ℝ => (Real.log U) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp Real.tendsto_log_atTop
  have hev_err_ll : ∀ᶠ U : ℝ in atTop,
      M_poly * (1 + Real.log U) ^ 3 ≤ U / Real.log (Real.log U) := by
    have ht_half : Tendsto (fun U : ℝ => U ^ (1 / 2 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by positivity)
    filter_upwards [ht_half.eventually_ge_atTop (M_poly * K_log4 + 1),
      Real.tendsto_log_atTop.eventually_ge_atTop 4,
      ht_loglog.eventually_ge_atTop 1,
      eventually_ge_atTop (16 : ℝ)] with U hUh hlog4_ge hll1 _
    have hU_pos : 0 < U := by linarith
    have hll_pos : 0 < Real.log (Real.log U) := by linarith
    rw [le_div_iff₀ hll_pos]
    have hll_le_log : Real.log (Real.log U) ≤ 1 + Real.log U := by
      have h := Real.add_one_le_exp (Real.log (Real.log U))
      rw [Real.exp_log (by linarith : 0 < Real.log U)] at h
      linarith
    have hpow4 : (1 + Real.log U) ^ 3 * Real.log (Real.log U) ≤ K_log4 * U ^ (1 / 2 : ℝ) := by
      calc (1 + Real.log U) ^ 3 * Real.log (Real.log U)
          ≤ (1 + Real.log U) ^ 3 * (1 + Real.log U) :=
            mul_le_mul_of_nonneg_left hll_le_log (by positivity)
        _ = (1 + Real.log U) ^ 4 := by ring
        _ ≤ K_log4 * U ^ (1 / 2 : ℝ) := hlog4 U (by linarith)
    have hm1 := mul_le_mul_of_nonneg_left hpow4 hMpoly_pos.le
    have hm2 := mul_le_mul_of_nonneg_right
      (by linarith : M_poly * K_log4 ≤ U ^ (1 / 2 : ℝ))
      (Real.rpow_nonneg hU_pos.le (1 / 2))
    have hU_sq : U ^ (1 / 2 : ℝ) * U ^ (1 / 2 : ℝ) = U := by
      rw [← Real.rpow_add hU_pos]; norm_num
    linarith [hm1, hm2, hU_sq]
  filter_upwards [ht_32.eventually hbv_ev,
    Real.tendsto_log_atTop.eventually_ge_atTop 50,
    ht_loglog.eventually_ge_atTop 1,
    ht_sqrt_log.eventually_ge_atTop ((25 / 22) * K_ll * 100 + 1),
    hev_err_ll,
    eventually_ge_atTop (16 : ℝ)]
    with U hbv_U hlog50 hll1 hsqrt_log herr_ll hU16
  classical
  have hU_pos : 0 < U := by linarith
  have hll_pos : 0 < Real.log (Real.log U) := by linarith
  set S : ℝ := (3 / 2 : ℝ) * U
  set L_S : ℝ := Real.log S
  have hlogU_le_LS : Real.log U ≤ L_S :=
    Real.log_le_log hU_pos (by dsimp [S]; linarith)
  have hLS_pos : 0 < L_S := by linarith
  have hLS_le_1add : L_S ≤ 1 + Real.log U := by
    dsimp [L_S, S]
    rw [Real.log_mul (by norm_num) hU_pos.ne']
    have h32 : Real.log (3 / 2 : ℝ) ≤ 1 := by
      have h1 : Real.log (3 / 2 : ℝ) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
      linarith [Real.log_two_lt_d9]
    linarith
  have hLS_le_2logU : L_S ≤ 2 * Real.log U := by linarith
  set a_U : ℝ := (25 / 22 : ℝ) * Real.log (Real.log U)
  have ha_lo : 1 ≤ a_U := by dsimp [a_U]; linarith
  have ha_hi : a_U ≤ L_S / 100 := by
    have h1 := hll (Real.log U) (by linarith)
    rw [pow_one] at h1
    have ha_le1 : a_U ≤ (25 / 22 : ℝ) * K_ll * (Real.log U) ^ (1 / 2 : ℝ) := by
      dsimp [a_U]; nlinarith
    have hm := mul_le_mul_of_nonneg_right
      (by linarith : (25 / 22 : ℝ) * K_ll * 100 ≤ (Real.log U) ^ (1 / 2 : ℝ))
      (Real.rpow_nonneg (by linarith : 0 ≤ Real.log U) (1 / 2))
    have hlog_sq : (Real.log U) ^ (1 / 2 : ℝ) * (Real.log U) ^ (1 / 2 : ℝ) = Real.log U := by
      rw [← Real.rpow_add (by linarith : 0 < Real.log U)]; norm_num
    rw [hlog_sq] at hm
    linarith
  set b_U : ℝ := (51 / 50 : ℝ) * (a_U / L_S)
  have hb_pos : 0 < b_U := by dsimp [b_U]; positivity
  set B_U : Finset ℂ :=
    (shellZeros (U - 1) (2 * U + 1)).filter (fun z => b_U ≤ |z.re - 1 / 2|)
  -- 1. Cover bad unit windows by unit intervals `[z.im - 1, z.im]` over `z ∈ B_U`
  have hcov : {T ∈ Icc U (2 * U) |
        ∃ ρ ∈ xiUnitWindowZeros T,
          (6 / 5 : ℝ) * Real.log (Real.log T) / Real.log T ≤ |ρ.re - 1 / 2|} ⊆
      ⋃ z ∈ B_U, Icc (z.im - 1) z.im := by
    rintro T ⟨hT, ρ, hρ_win, hρ_re⟩
    have hT_pos : 0 < T := by linarith [hT.1]
    have hlogT_ge : Real.log U ≤ Real.log T := Real.log_le_log hU_pos hT.1
    have hlogT_le : Real.log T ≤ (51 / 50 : ℝ) * Real.log U := by
      have h1 : Real.log T ≤ Real.log (2 * U) := Real.log_le_log hT_pos hT.2
      rw [Real.log_mul zero_lt_two.ne' hU_pos.ne'] at h1
      linarith [Real.log_two_lt_d9, hlog50]
    have hllT_ge : Real.log (Real.log U) ≤ Real.log (Real.log T) :=
      Real.log_le_log (by linarith) hlogT_ge
    have hb_le_T : b_U ≤ (6 / 5 : ℝ) * Real.log (Real.log T) / Real.log T := by
      have hb_eq : b_U = (51 / 44 : ℝ) * (Real.log (Real.log U) / L_S) := by
        dsimp [b_U, a_U]; ring
      rw [hb_eq]
      calc (51 / 44 : ℝ) * (Real.log (Real.log U) / L_S)
          ≤ (51 / 44 : ℝ) * (Real.log (Real.log U) / Real.log U) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_left hll_pos.le (by linarith) hlogU_le_LS) (by norm_num)
        _ ≤ (20 / 17 : ℝ) * (Real.log (Real.log U) / Real.log U) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = (6 / 5 : ℝ) * Real.log (Real.log U) / ((51 / 50 : ℝ) * Real.log U) := by ring
        _ ≤ (6 / 5 : ℝ) * Real.log (Real.log T) / ((51 / 50 : ℝ) * Real.log U) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hllT_ge (by norm_num)) (by positivity)
        _ ≤ (6 / 5 : ℝ) * Real.log (Real.log T) / Real.log T :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (by linarith)) (by linarith) hlogT_le
    rw [mem_xiUnitWindowZeros, Set.Finite.mem_toFinset] at hρ_win
    obtain ⟨⟨⟨h0, h1, _him0, him_lt⟩, hxi⟩, him_ge⟩ := hρ_win
    have hρ_B : ρ ∈ B_U := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨mem_stripFinsetPos.mpr ⟨h0, h1, by linarith [hT.1, him_ge],
        by linarith [hT.2], hxi⟩, by linarith [hT.1]⟩, hb_le_T.trans hρ_re⟩
    exact Set.mem_biUnion hρ_B ⟨by linarith, him_ge⟩
  -- 2. Bound `(B_U.card : ℝ)` via `exists_selberg_criticalGate_nearLine_zeroDensity` + end-caps
  obtain ⟨T₁, hT₁, T₂, hT₂, hbv_S⟩ := hbv_U
  have hT₁_lo : U < T₁ := by dsimp [S] at hT₁; linarith [hT₁.1]
  have hT₁_hi : T₁ < U + 1 := by dsimp [S] at hT₁; linarith [hT₁.2]
  have hT₂_lo : 2 * U - 1 < T₂ := by dsimp [S] at hT₂; linarith [hT₂.1]
  have hT₂_hi : T₂ < 2 * U := by dsimp [S] at hT₂; linarith [hT₂.2]
  have hT₁_pos : 0 < T₁ := by linarith
  have hT₁2 : T₁ ≤ T₂ := by linarith
  have hcard_le : (B_U.card : ℝ) ≤ C_bad * U / Real.log (Real.log U) := by
    have hcard_ord : (B_U.card : ℝ) ≤ ∑ z ∈ B_U, ((analyticOrderAt xi z).toNat : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun z hz => ?_
      have hxi : xi z = 0 :=
        (mem_stripFinsetPos.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).2.2.2.2
      have hpos : 1 ≤ (analyticOrderAt xi z).toNat :=
        Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hxi)
      exact_mod_cast hpos
    obtain ⟨hu1, hd1⟩ := shellZeros_disjoint_split (by linarith : U - 1 ≤ T₁)
      (by linarith : T₁ ≤ 2 * U + 1)
    obtain ⟨hu2, hd2⟩ := shellZeros_disjoint_split hT₁2 (by linarith : T₂ ≤ 2 * U + 1)
    have hsplit_B : ∑ z ∈ B_U, ((analyticOrderAt xi z).toNat : ℝ) =
        (∑ z ∈ (shellZeros (U - 1) T₁).filter (fun z => b_U ≤ |z.re - 1 / 2|),
          ((analyticOrderAt xi z).toNat : ℝ)) +
        (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => b_U ≤ |z.re - 1 / 2|),
          ((analyticOrderAt xi z).toNat : ℝ)) +
        (∑ z ∈ (shellZeros T₂ (2 * U + 1)).filter (fun z => b_U ≤ |z.re - 1 / 2|),
          ((analyticOrderAt xi z).toNat : ℝ)) := by
      dsimp [B_U]
      rw [hu1, Finset.filter_union,
        Finset.sum_union (hd1.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        hu2, Finset.filter_union,
        Finset.sum_union (hd2.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        add_assoc]
    have hcap_ord : ∀ W₁ W₂ : ℝ, 0 ≤ W₁ → W₁ ≤ W₂ → W₂ - W₁ ≤ 2 → W₂ ≤ 2 * U + 1 →
        (∑ z ∈ (shellZeros W₁ W₂).filter (fun z => b_U ≤ |z.re - 1 / 2|),
          ((analyticOrderAt xi z).toNat : ℝ)) ≤
          16 * (|xiLineTwoLogDerivConstant| + 5) * (1 + Real.log U) ^ 3 := by
      intro W₁ W₂ hW₁ h12 hlen hW₂
      have h1 : (∑ z ∈ (shellZeros W₁ W₂).filter (fun z => b_U ≤ |z.re - 1 / 2|),
            ((analyticOrderAt xi z).toNat : ℝ)) ≤
          ∑ z ∈ shellZeros W₁ W₂, ((analyticOrderAt xi z).toNat : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => Nat.cast_nonneg _
      have h2 := shortShell_orderSum_le_log hW₁ h12 hlen
      have hlogW : Real.log (W₂ + 4) ≤ 4 + Real.log U := by
        calc Real.log (W₂ + 4) ≤ Real.log (4 * U) :=
              Real.log_le_log (by linarith) (by linarith)
          _ = Real.log 4 + Real.log U := Real.log_mul (by norm_num) hU_pos.ne'
          _ ≤ 4 + Real.log U := by linarith [log_four_le_two]
      have h13 : 1 + Real.log U ≤ (1 + Real.log U) ^ 3 :=
        le_self_pow₀ (by linarith) (by norm_num)
      calc (∑ z ∈ (shellZeros W₁ W₂).filter (fun z => b_U ≤ |z.re - 1 / 2|),
              ((analyticOrderAt xi z).toNat : ℝ))
          ≤ 16 * (|xiLineTwoLogDerivConstant| + Real.log (W₂ + 4)) := h1.trans h2
        _ ≤ 16 * (|xiLineTwoLogDerivConstant| + (4 + Real.log U)) :=
            mul_le_mul_of_nonneg_left (add_le_add le_rfl hlogW) (by norm_num)
        _ ≤ 16 * ((|xiLineTwoLogDerivConstant| + 5) * (1 + Real.log U)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            rw [add_mul]
            have h1_le := le_mul_of_one_le_right (abs_nonneg xiLineTwoLogDerivConstant)
              (by linarith : 1 ≤ 1 + Real.log U)
            linarith
        _ ≤ 16 * ((|xiLineTwoLogDerivConstant| + 5) * (1 + Real.log U) ^ 3) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h13 (by positivity)) (by norm_num)
        _ = 16 * (|xiLineTwoLogDerivConstant| + 5) * (1 + Real.log U) ^ 3 := by ring
    have hcap1 := hcap_ord (U - 1) T₁ (by linarith) (by linarith) (by linarith) (by linarith)
    have hcap2 := hcap_ord T₂ (2 * U + 1) (by linarith) (by linarith) (by linarith) le_rfl
    -- Middle shell `(T₁, T₂]` via `shellOrderSum_abs_ge_eq_two_mul_right` + Barban–Vehov
    have hmid_le : (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => b_U ≤ |z.re - 1 / 2|),
          ((analyticOrderAt xi z).toNat : ℝ)) ≤
        (2 * A / 3) * U / Real.log (Real.log U) + 2 * K * (1 + Real.log U) ^ 3 := by
      rw [shellOrderSum_abs_ge_eq_two_mul_right T₁ T₂ hb_pos]
      have hsh_win := shellRight_orderSum_le_windowZeros hT₁_pos hT₁2 hb_pos.le
      have hbv_inst := hbv_S a_U ha_lo ha_hi (windowZeros T₁ T₂)
        (mem_windowZeros_iff hT₁_pos hT₁2)
      have h2W := barbanVehov_loglog_count_algebra hU_pos hA hK hlog50 hll_pos
        hLS_pos hLS_le_1add hLS_le_2logU rfl ha_lo (by linarith : T₂ - T₁ ≤ U) hbv_inst
      exact (mul_le_mul_of_nonneg_left hsh_win zero_le_two).trans h2W
    have htot_B : ∑ z ∈ B_U, ((analyticOrderAt xi z).toNat : ℝ) ≤
        (2 * A / 3) * U / Real.log (Real.log U) + M_poly * (1 + Real.log U) ^ 3 := by
      rw [hsplit_B]
      calc (∑ z ∈ (shellZeros (U - 1) T₁).filter (fun z => b_U ≤ |z.re - 1 / 2|),
              ((analyticOrderAt xi z).toNat : ℝ)) +
            (∑ z ∈ (shellZeros T₁ T₂).filter (fun z => b_U ≤ |z.re - 1 / 2|),
              ((analyticOrderAt xi z).toNat : ℝ)) +
            (∑ z ∈ (shellZeros T₂ (2 * U + 1)).filter (fun z => b_U ≤ |z.re - 1 / 2|),
              ((analyticOrderAt xi z).toNat : ℝ))
          ≤ 16 * (|xiLineTwoLogDerivConstant| + 5) * (1 + Real.log U) ^ 3 +
              ((2 * A / 3) * U / Real.log (Real.log U) + 2 * K * (1 + Real.log U) ^ 3) +
              16 * (|xiLineTwoLogDerivConstant| + 5) * (1 + Real.log U) ^ 3 :=
            add_le_add (add_le_add hcap1 hmid_le) hcap2
        _ = (2 * A / 3) * U / Real.log (Real.log U) + M_poly * (1 + Real.log U) ^ 3 := by
            dsimp [M_poly]; ring
    have hdiv_pos : 0 < U / Real.log (Real.log U) := by positivity
    calc (B_U.card : ℝ)
        ≤ (2 * A / 3) * U / Real.log (Real.log U) + M_poly * (1 + Real.log U) ^ 3 :=
          hcard_ord.trans htot_B
      _ ≤ (2 * A / 3) * U / Real.log (Real.log U) + U / Real.log (Real.log U) :=
          add_le_add le_rfl herr_ll
      _ ≤ C_bad * U / Real.log (Real.log U) := by
          dsimp [C_bad]
          rw [show (2 * A / 3) * U / Real.log (Real.log U) + U / Real.log (Real.log U) =
              (2 * A / 3 + 1) * (U / Real.log (Real.log U)) by ring,
            show (2 * A / 3 + 2) * U / Real.log (Real.log U) =
              (2 * A / 3 + 2) * (U / Real.log (Real.log U)) by ring]
          linarith
  -- 3. Subadditivity of Lebesgue measure across `z ∈ B_U`
  calc volume {T ∈ Icc U (2 * U) |
          ∃ ρ ∈ xiUnitWindowZeros T,
            (6 / 5 : ℝ) * Real.log (Real.log T) / Real.log T ≤ |ρ.re - 1 / 2|}
      ≤ volume (⋃ z ∈ B_U, Icc (z.im - 1) z.im) := measure_mono hcov
    _ ≤ ∑ z ∈ B_U, volume (Icc (z.im - 1) z.im) := measure_biUnion_finset_le B_U _
    _ = ∑ _z ∈ B_U, ENNReal.ofReal 1 := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Real.volume_Icc]; ring_nf
    _ = ENNReal.ofReal (B_U.card : ℝ) := by
        rw [Finset.sum_const, ENNReal.ofReal_one, nsmul_one, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C_bad * U / Real.log (Real.log U)) :=
        ENNReal.ofReal_le_ofReal hcard_le

/-! ## §7. Four-way `o(log U)` equivalence with Levinson–Montgomery `100%` critical-scale clustering -/

private theorem finset_sum_biUnion_le {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (t : ι → Finset α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      have hunion : ∑ a ∈ t i ∪ s.biUnion t, f a ≤
          ∑ a ∈ t i, f a + ∑ a ∈ s.biUnion t, f a := by
        have h := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
        have hnn : 0 ≤ ∑ a ∈ t i ∩ s.biUnion t, f a := Finset.sum_nonneg fun a _ => hf a
        linarith
      exact hunion.trans (add_le_add le_rfl ih)

/-- Elementary `O(V log V)` bound on the total zero multiplicity in `stripFinsetPos V` (`2 ≤ V`),
obtained by covering `(0, V]` with `⌈V⌉₊` unit shells and summing `shortShell_orderSum_le_log`. -/
private theorem stripFinsetPos_orderSum_le_mul_log {V : ℝ} (hV : 2 ≤ V) :
    ∑ z ∈ stripFinsetPos V, ((analyticOrderAt xi z).toNat : ℝ) ≤
      32 * (2 * |xiLineTwoLogDerivConstant| + 5) * V * Real.log V := by
  classical
  have hV_pos : 0 < V := by linarith
  have hlogV_half : (1 / 2 : ℝ) ≤ Real.log V := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log zero_lt_two hV
    linarith
  set n : ℕ := ⌈V⌉₊
  have hn_lt : (n : ℝ) < V + 1 := Nat.ceil_lt_add_one hV_pos.le
  have hn_le_2V : (n : ℝ) ≤ 2 * V := by linarith
  have hsub : stripFinsetPos V ⊆
      (Finset.range n).biUnion (fun k => shellZeros (k : ℝ) ((k : ℝ) + 1)) := by
    intro z hz
    obtain ⟨h0, h1, him0, himV, hxi⟩ := mem_stripFinsetPos.mp hz
    set m : ℕ := ⌈z.im⌉₊
    have hm_pos : 1 ≤ m := Nat.ceil_pos.mpr him0
    have hm_le : m ≤ n := Nat.ceil_mono himV
    set k : ℕ := m - 1
    have hk_lt : k < n := by omega
    have hkm : (k : ℝ) + 1 = (m : ℝ) := by
      have : k + 1 = m := by omega
      exact_mod_cast this
    have him_le : z.im ≤ (k : ℝ) + 1 := by rw [hkm]; exact Nat.le_ceil z.im
    have him_gt : (k : ℝ) < z.im := by
      have hlt : (m : ℝ) < z.im + 1 := Nat.ceil_lt_add_one him0.le
      linarith
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk_lt,
      Finset.mem_filter.mpr ⟨mem_stripFinsetPos.mpr ⟨h0, h1, him0, him_le, hxi⟩, him_gt⟩⟩
  have hterm_le : ∀ k ∈ Finset.range n,
      (∑ z ∈ shellZeros (k : ℝ) ((k : ℝ) + 1), ((analyticOrderAt xi z).toNat : ℝ)) ≤
        16 * (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V := by
    intro k hk
    have hk_lt : k < n := Finset.mem_range.mp hk
    have hk1_le : (k : ℝ) + 1 ≤ (n : ℝ) := by
      have : k + 1 ≤ n := by omega
      exact_mod_cast this
    have hord := shortShell_orderSum_le_log (Nat.cast_nonneg k) (by linarith) (by linarith)
    have hlog_k : Real.log ((k : ℝ) + 1 + 4) ≤ 5 * Real.log V := by
      have hle4V : (k : ℝ) + 1 + 4 ≤ 4 * V := by linarith
      calc Real.log ((k : ℝ) + 1 + 4)
          ≤ Real.log (4 * V) := Real.log_le_log (by positivity) hle4V
        _ = Real.log 4 + Real.log V := Real.log_mul (by norm_num) hV_pos.ne'
        _ ≤ 2 + Real.log V := by
            have : Real.log ((2 : ℝ) ^ (2 : ℕ)) ≤ 2 := by
              rw [Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
            norm_num at this; linarith
        _ ≤ 5 * Real.log V := by linarith [hlogV_half]
    nlinarith [hord, hlog_k, hlogV_half, abs_nonneg xiLineTwoLogDerivConstant]
  calc ∑ z ∈ stripFinsetPos V, ((analyticOrderAt xi z).toNat : ℝ)
      ≤ ∑ z ∈ (Finset.range n).biUnion (fun k => shellZeros (k : ℝ) ((k : ℝ) + 1)),
          ((analyticOrderAt xi z).toNat : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
    _ ≤ ∑ k ∈ Finset.range n,
          ∑ z ∈ shellZeros (k : ℝ) ((k : ℝ) + 1), ((analyticOrderAt xi z).toNat : ℝ) :=
        finset_sum_biUnion_le _ _ fun _ => Nat.cast_nonneg _
    _ ≤ ∑ _k ∈ Finset.range n,
          16 * (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V :=
        Finset.sum_le_sum hterm_le
    _ = (n : ℝ) * (16 * (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 * V) * (16 * (2 * |xiLineTwoLogDerivConstant| + 5) * Real.log V) :=
        mul_le_mul_of_nonneg_right hn_le_2V (by positivity)
    _ = 32 * (2 * |xiLineTwoLogDerivConstant| + 5) * V * Real.log V := by ring

/-- Under `100%` critical-scale clustering (`∀ κ > 0, offLineCountBeyond (κ / log V) V = o(V log V)`),
for every `0 < c' < 22 / 51`, `shellDepthSum V (2 * V) (c' * Real.log V) = o(V log V)` as `V → ∞`. -/
private theorem tendsto_shellDepthSum_div_mul_log_zero_of_countBeyond
    {c' : ℝ} (hc0 : 0 < c') (hc' : c' < 22 / 51)
    (h4 : ∀ κ : ℝ, 0 < κ →
      Tendsto (fun V : ℝ => offLineCountBeyond (κ / Real.log V) V / (V * Real.log V))
        atTop (𝓝 0)) :
    Tendsto (fun V : ℝ => shellDepthSum V (2 * V) (c' * Real.log V) / (V * Real.log V))
      atTop (𝓝 0) := by
  obtain ⟨A, K, hA, hK, hbv_ev⟩ := exists_selberg_criticalGate_nearLine_zeroDensity
  obtain ⟨C_deep, hC_deep, T_deep, hT_deep, hdeep⟩ :=
    exists_sum_exp_foldedRe_deep_decay_up_to_two_thirds_log
      hc0.le (by linarith : c' < 2 / 3) (by norm_num : (0 : ℝ) < 1 / 200) (by norm_num)
  set γ₀ : ℝ := (4 / 3 - 2 * c') * (1 / 200) / 8
  have hγ₀_pos : 0 < γ₀ := by dsimp [γ₀]; linarith
  obtain ⟨K_log3, _, hlog3⟩ := exists_one_add_log_pow_le_rpow 3 (by positivity : (0 : ℝ) < 1 / 4)
  obtain ⟨K_log4, _, hlog4⟩ := exists_one_add_log_pow_le_rpow 4 (by positivity : (0 : ℝ) < 1 / 50)
  set lam : ℝ := (22 - 51 * c') / 25
  have hlam_pos : 0 < lam := by dsimp [lam]; linarith
  set r : ℝ := Real.exp (-(lam / 2))
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set C_II : ℝ := 4 * (64 * Real.exp 1 * A / (lam * (1 - r))) * c' ^ 2
  have hCII_pos : 0 < C_II := by
    have : 0 < 1 - r := by linarith
    dsimp [C_II]; positivity
  set C_tot : ℝ := 32 * (2 * |xiLineTwoLogDerivConstant| + 5)
  have hCtot_pos : 0 < C_tot := by
    dsimp [C_tot]; have := abs_nonneg xiLineTwoLogDerivConstant; positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- 1. Choose Scale-II starting slab `m₀ ≥ 1` with `C_II * r ^ m₀ ≤ ε / 10`
  set M_tar : ℝ := (10 * C_II + 1) / ε
  have hMtar_pos : 0 < M_tar := by dsimp [M_tar]; positivity
  set m₀ : ℕ := max 1 ⌈(2 / lam) * max 0 (Real.log M_tar)⌉₊
  have hm₀_1 : 1 ≤ m₀ := le_max_left _ _
  have hCII_tail : C_II * r ^ m₀ ≤ ε / 10 := by
    have hm_ge : (2 / lam) * Real.log M_tar ≤ (m₀ : ℝ) := by
      calc (2 / lam) * Real.log M_tar
          ≤ (2 / lam) * max 0 (Real.log M_tar) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
        _ ≤ (⌈(2 / lam) * max 0 (Real.log M_tar)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (m₀ : ℝ) := by exact_mod_cast le_max_right 1 _
    have hexp_le : r ^ m₀ ≤ M_tar⁻¹ := by
      dsimp [r]
      rw [← Real.exp_nat_mul]
      have harg : (m₀ : ℝ) * -(lam / 2) ≤ -Real.log M_tar := by
        have hm := (div_le_iff₀ hlam_pos).mp
          (by rw [show 2 * Real.log M_tar / lam = (2 / lam) * Real.log M_tar by ring]; exact hm_ge)
        linarith
      calc Real.exp ((m₀ : ℝ) * -(lam / 2))
          ≤ Real.exp (-Real.log M_tar) := Real.exp_le_exp.mpr harg
        _ = M_tar⁻¹ := by rw [Real.exp_neg, Real.exp_log hMtar_pos]
    calc C_II * r ^ m₀ ≤ C_II * M_tar⁻¹ := mul_le_mul_of_nonneg_left hexp_le hCII_pos.le
      _ = C_II * ε / (10 * C_II + 1) := by dsimp [M_tar]; field_simp; ring
      _ ≤ ε / 10 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
  -- 2. Choose ultra-near micro-threshold `κ₀ ∈ (0, 1]`
  set κ₀ : ℝ := min 1 (ε / (320 * Real.exp 2 * C_tot + 1))
  have hκ₀_pos : 0 < κ₀ := lt_min zero_lt_one (by positivity)
  have hκ₀_le1 : κ₀ ≤ 1 := min_le_left _ _
  have hκ₀_tiny : 32 * Real.exp 2 * C_tot * κ₀ ≤ ε / 10 := by
    have h1 : κ₀ ≤ ε / (320 * Real.exp 2 * C_tot + 1) := min_le_right _ _
    have hm := (le_div_iff₀ (by positivity : 0 < 320 * Real.exp 2 * C_tot + 1)).mp h1
    linarith [mul_nonneg hκ₀_pos.le (by positivity : (0 : ℝ) ≤ 1)]
  -- 3. Bridge weight `M_br := exp((51 / 25) * c' * m₀)` and `h4` at `2 * V`
  set M_br : ℝ := Real.exp ((51 / 25 : ℝ) * c' * (m₀ : ℝ))
  have hMbr_pos : 0 < M_br := Real.exp_pos _
  have ht_32 : Tendsto (fun V : ℝ => (3 / 2 : ℝ) * V) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have ht_2 : Tendsto (fun V : ℝ => 2 * V) atTop atTop :=
    tendsto_id.const_mul_atTop zero_lt_two
  have hev_br : ∀ᶠ V : ℝ in atTop,
      2 * M_br * offLineCountBeyond (κ₀ / Real.log (2 * V)) (2 * V) ≤
        (ε / 10) * V * Real.log V := by
    have ht_cnt := (h4 κ₀ hκ₀_pos).comp ht_2
    have hlt := (Metric.tendsto_atTop.mp ht_cnt) (ε / (80 * M_br + 1)) (by positivity)
    obtain ⟨V_br, hV_br⟩ := hlt
    filter_upwards [eventually_ge_atTop (max 16 V_br)] with V hV
    have hV16 : 16 ≤ V := (le_max_left _ _).trans hV
    have hV_pos : 0 < V := by linarith
    have hd := hV_br V ((le_max_right _ _).trans hV)
    dsimp only [Function.comp_def] at hd
    have hcnt_nn : 0 ≤ offLineCountBeyond (κ₀ / Real.log (2 * V)) (2 * V) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hden_pos : 0 < (2 * V) * Real.log (2 * V) :=
      mul_pos (by positivity) (Real.log_pos (by linarith))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hcnt_nn hden_pos.le)] at hd
    have hm1 := (div_lt_iff₀ hden_pos).mp hd
    have hlog2V : Real.log (2 * V) ≤ 2 * Real.log V := by
      rw [Real.log_mul zero_lt_two.ne' hV_pos.ne']
      have h2 : Real.log ((2 : ℝ) ^ (2 : ℕ)) ≤ Real.log V :=
        Real.log_le_log (by norm_num) (by norm_num at *; linarith)
      rw [Real.log_pow] at h2; push_cast at h2; linarith [Real.log_two_gt_d9]
    have hden_le : (2 * V) * Real.log (2 * V) ≤ 4 * V * Real.log V := by
      have := mul_le_mul_of_nonneg_left hlog2V (by positivity : 0 ≤ 2 * V)
      linarith
    have hcnt_le : offLineCountBeyond (κ₀ / Real.log (2 * V)) (2 * V) ≤
        (ε / (80 * M_br + 1)) * (4 * V * Real.log V) :=
      hm1.le.trans (mul_le_mul_of_nonneg_left hden_le (by positivity))
    have hm2 := mul_le_mul_of_nonneg_left hcnt_le (by positivity : 0 ≤ 2 * M_br)
    have hcoef : 2 * M_br * (ε / (80 * M_br + 1)) * 4 ≤ ε / 10 := by
      rw [show 2 * M_br * (ε / (80 * M_br + 1)) * 4 = 8 * M_br * ε / (80 * M_br + 1) by ring,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hm3 := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg hV_pos.le (Real.log_nonneg (by linarith)))
    linarith [hm2, hm3]
  -- 4. Sublinear absorptions for end-caps, Scale II polylog error, and Scale III deep tail
  have hev_cap : ∀ᶠ V : ℝ in atTop,
      64 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) ≤
        (ε / 10) * V * Real.log V := by
    have ht : Tendsto (fun V : ℝ => V ^ (1 / 4 : ℝ)) atTop atTop := tendsto_rpow_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop
      (640 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 / ε + 1),
      eventually_ge_atTop (4 : ℝ)] with V hVr hV4
    have hV_pos : 0 < V := by linarith
    have hlog1 : 1 ≤ Real.log V := by
      have := Real.log_two_gt_d9
      have := Real.log_le_log zero_lt_two (by linarith : (2 : ℝ) ≤ V)
      linarith
    have hsplit : V = V ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hV_pos]; norm_num
    have hm1 := (div_le_iff₀ hε).mp
      (by linarith : 640 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 / ε ≤ V ^ (1 / 4 : ℝ))
    have hm2 := mul_le_mul_of_nonneg_left hm1 (Real.rpow_nonneg hV_pos.le (3 / 4))
    have hrew : V ^ (3 / 4 : ℝ) * (V ^ (1 / 4 : ℝ) * ε) = ε * V := by rw [hsplit]; ring
    rw [hrew] at hm2
    have h10 : 64 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) ≤ (ε / 10) * V := by
      linarith
    exact h10.trans (le_mul_of_one_le_right (by positivity) hlog1)
  have hev_errII : ∀ᶠ V : ℝ in atTop,
      2 * ((16 * Real.exp 2 * K) * c' ^ 2 * K_log4 * ((3 / 2 : ℝ) * V) ^ (1 / 25 : ℝ)) ≤
        (ε / 20) * V * Real.log V := by
    have ht : Tendsto (fun V : ℝ => V ^ (24 / 25 : ℝ)) atTop atTop := tendsto_rpow_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop
      (1280 * Real.exp 2 * K * c' ^ 2 * K_log4 / ε + 1),
      eventually_ge_atTop (4 : ℝ)] with V hVr hV4
    have hV_pos : 0 < V := by linarith
    have hlog1 : 1 ≤ Real.log V := by
      have := Real.log_two_gt_d9
      have := Real.log_le_log zero_lt_two (by linarith : (2 : ℝ) ≤ V)
      linarith
    have h32_rpow : ((3 / 2 : ℝ) * V) ^ (1 / 25 : ℝ) ≤ 2 * V ^ (1 / 25 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hV_pos.le]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hV_pos.le _)
      calc (3 / 2 : ℝ) ^ (1 / 25 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            (Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)).trans
              (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num))
        _ = 2 := Real.rpow_one 2
    have hsplit : V = V ^ (1 / 25 : ℝ) * V ^ (24 / 25 : ℝ) := by
      rw [← Real.rpow_add hV_pos]; norm_num
    have hm1 := (div_le_iff₀ hε).mp
      (by linarith : 1280 * Real.exp 2 * K * c' ^ 2 * K_log4 / ε ≤ V ^ (24 / 25 : ℝ))
    have hm2 := mul_le_mul_of_nonneg_left hm1 (Real.rpow_nonneg hV_pos.le (1 / 25))
    have hrew : V ^ (1 / 25 : ℝ) * (V ^ (24 / 25 : ℝ) * ε) = ε * V := by rw [hsplit]; ring
    rw [hrew] at hm2
    have hm3 := mul_le_mul_of_nonneg_left h32_rpow
      (by positivity : 0 ≤ 32 * Real.exp 2 * K * c' ^ 2 * K_log4)
    have h20 : 2 * ((16 * Real.exp 2 * K) * c' ^ 2 * K_log4 * ((3 / 2 : ℝ) * V) ^ (1 / 25 : ℝ)) ≤
        (ε / 20) * V := by linarith
    exact h20.trans (le_mul_of_one_le_right (by positivity) hlog1)
  have hev_deep : ∀ᶠ V : ℝ in atTop,
      2 * (C_deep * V ^ (1 - γ₀)) ≤ (ε / 20) * V * Real.log V := by
    have ht : Tendsto (fun V : ℝ => V ^ γ₀) atTop atTop := tendsto_rpow_atTop hγ₀_pos
    filter_upwards [ht.eventually_ge_atTop (40 * C_deep / ε + 1),
      eventually_ge_atTop (4 : ℝ)] with V hVr hV4
    have hV_pos : 0 < V := by linarith
    have hlog1 : 1 ≤ Real.log V := by
      have := Real.log_two_gt_d9
      have := Real.log_le_log zero_lt_two (by linarith : (2 : ℝ) ≤ V)
      linarith
    have hsplit : V = V ^ (1 - γ₀) * V ^ γ₀ := by
      rw [← Real.rpow_add hV_pos]; ring_nf
    have hm1 := (div_le_iff₀ hε).mp (by linarith : 40 * C_deep / ε ≤ V ^ γ₀)
    have hm2 := mul_le_mul_of_nonneg_left hm1 (Real.rpow_nonneg hV_pos.le (1 - γ₀))
    have hrew : V ^ (1 - γ₀) * (V ^ γ₀ * ε) = ε * V := by rw [hsplit]; ring
    rw [hrew] at hm2
    exact (by linarith : 2 * (C_deep * V ^ (1 - γ₀)) ≤ (ε / 20) * V).trans
      (le_mul_of_one_le_right (by positivity) hlog1)
  -- 5. Combine all eventual conditions
  have hev_all : ∀ᶠ V : ℝ in atTop,
      shellDepthSum V (2 * V) (c' * Real.log V) / (V * Real.log V) ≤ ε / 2 ∧
        0 ≤ shellDepthSum V (2 * V) (c' * Real.log V) / (V * Real.log V) := by
    filter_upwards [ht_32.eventually hbv_ev,
      ht_32.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (max 200 (100 * (m₀ : ℝ) + 1))),
      eventually_ge_atTop (max 16 T_deep),
      hev_br, hev_cap, hev_errII, hev_deep]
      with V hbv_V hLS_big hV_max hbr_V hcap_V herrII_V hdeep_V
    have hV16 : 16 ≤ V := (le_max_left _ _).trans hV_max
    have hV_deep : T_deep ≤ V := (le_max_right _ _).trans hV_max
    have hV_pos : 0 < V := by linarith
    have hlogV_ge2 : 2 ≤ Real.log V := by
      have h2 := Real.log_two_gt_d9
      have h16 : Real.log ((2 : ℝ) ^ (4 : ℕ)) ≤ Real.log V :=
        Real.log_le_log (by norm_num) (by norm_num at *; linarith)
      rw [Real.log_pow] at h16; push_cast at h16; linarith
    set L : ℝ := c' * Real.log V
    have hL0 : 0 ≤ L := by dsimp [L]; positivity
    set S : ℝ := (3 / 2 : ℝ) * V
    set L_S : ℝ := Real.log S
    have hLS200 : 200 ≤ L_S := (le_max_left _ _).trans hLS_big
    have hLS_pos : 0 < L_S := by linarith
    have hLS_le_2logV : L_S ≤ 2 * Real.log V := by
      dsimp [L_S, S]
      have h1 : Real.log ((3 / 2) * V) ≤ Real.log (2 * V) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_mul zero_lt_two.ne' hV_pos.ne'] at h1
      linarith [Real.log_two_lt_d9]
    have hL_le_LS : L ≤ c' * L_S :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hV_pos (by dsimp [S]; linarith)) hc0.le
    obtain ⟨T₁, hT₁, T₂, hT₂, hbv_S⟩ := hbv_V
    have hVT₁ : V ≤ T₁ := by dsimp [S] at hT₁; linarith [hT₁.1]
    have hT₁2 : T₁ ≤ T₂ := by dsimp [S] at hT₁ hT₂; linarith [hT₁.2, hT₂.1]
    have hT₂2V : T₂ ≤ 2 * V := by dsimp [S] at hT₂; linarith [hT₂.2]
    -- End-cap bound `(V, T₁] ∪ (T₂, 2 * V]`
    have hcap_sum : shellDepthSum V T₁ L + shellDepthSum T₂ (2 * V) L ≤
        (ε / 10) * V * Real.log V := by
      have hdk_cap : ∀ z : ℂ, |z.re - 1 / 2| ≤ 1 / 2 →
          depthKernel L (z.re - 1 / 2) ≤ (Real.log V) ^ 2 * V ^ (1 / 2 : ℝ) := by
        intro z hz
        have h1 := depthKernel_le_four_sq_mul_exp (d := z.re - 1 / 2) hL0
        have hLd : L * |z.re - 1 / 2| ≤ (1 / 2) * Real.log V := by
          have hc_lt1 : c' ≤ 1 := by linarith
          have hL_log : L ≤ Real.log V := mul_le_of_le_one_left (by positivity) hc_lt1
          nlinarith [abs_nonneg (z.re - 1 / 2)]
        have hsq : 4 * (L * |z.re - 1 / 2|) ^ 2 ≤ (Real.log V) ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) hLd 2
          linarith
        have hexp : Real.exp (2 * L * |z.re - 1 / 2|) ≤ V ^ (1 / 2 : ℝ) := by
          have h2Ld : 2 * L * |z.re - 1 / 2| ≤ (1 / 2) * Real.log V := by
            dsimp [L]; nlinarith [hz, hlogV_ge2]
          calc Real.exp (2 * L * |z.re - 1 / 2|)
              ≤ Real.exp ((1 / 2) * Real.log V) := Real.exp_le_exp.mpr h2Ld
            _ = V ^ (1 / 2 : ℝ) := by rw [Real.rpow_def_of_pos hV_pos, mul_comm]
        exact h1.trans (mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg _))
      have hcap1_ord := shortShell_orderSum_le_log hV_pos.le hVT₁
        (by dsimp [S] at hT₁; linarith [hT₁.2])
      have hcap2_ord := shortShell_orderSum_le_log (by linarith) hT₂2V
        (by dsimp [S] at hT₂; linarith [hT₂.1])
      have hbound_shell : ∀ W₁ W₂ : ℝ,
          (∑ z ∈ shellZeros W₁ W₂, ((analyticOrderAt xi z).toNat : ℝ)) ≤
            16 * (|xiLineTwoLogDerivConstant| + Real.log (2 * V + 4)) →
          shellDepthSum W₁ W₂ L ≤
            16 * (|xiLineTwoLogDerivConstant| + Real.log (2 * V + 4)) *
              ((Real.log V) ^ 2 * V ^ (1 / 2 : ℝ)) := by
        intro W₁ W₂ hord
        unfold shellDepthSum
        calc ∑ z ∈ shellZeros W₁ W₂, ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
            ≤ ∑ z ∈ shellZeros W₁ W₂,
                ((analyticOrderAt xi z).toNat : ℝ) * ((Real.log V) ^ 2 * V ^ (1 / 2 : ℝ)) := by
              refine Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hdk_cap z ?_)
                (Nat.cast_nonneg _)
              obtain ⟨h0, h1, _, _, _⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1
              rw [abs_le]; constructor <;> linarith
          _ = (∑ z ∈ shellZeros W₁ W₂, ((analyticOrderAt xi z).toNat : ℝ)) *
                ((Real.log V) ^ 2 * V ^ (1 / 2 : ℝ)) := (Finset.sum_mul _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right hord (by positivity)
      have hlog2V4 : Real.log (2 * V + 4) ≤ 3 + Real.log V := by
        calc Real.log (2 * V + 4) ≤ Real.log (4 * V) :=
              Real.log_le_log (by positivity) (by linarith)
          _ = Real.log 4 + Real.log V := Real.log_mul (by norm_num) hV_pos.ne'
          _ ≤ 3 + Real.log V := by
              have : Real.log ((2 : ℝ) ^ (2 : ℕ)) ≤ 2 := by
                rw [Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
              norm_num at this; linarith
      have hb1 := hbound_shell V T₁ (hcap1_ord.trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (Real.log_le_log (by positivity) (by linarith))) (by norm_num)))
      have hb2 := hbound_shell T₂ (2 * V) hcap2_ord
      have hpoly : 32 * (|xiLineTwoLogDerivConstant| + Real.log (2 * V + 4)) *
          ((Real.log V) ^ 2 * V ^ (1 / 2 : ℝ)) ≤
          64 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) := by
        have hfactor : (|xiLineTwoLogDerivConstant| + Real.log (2 * V + 4)) * (Real.log V) ^ 2 ≤
            2 * (|xiLineTwoLogDerivConstant| + 4) * (1 + Real.log V) ^ 3 := by
          nlinarith [abs_nonneg xiLineTwoLogDerivConstant, hlogV_ge2, hlog2V4]
        have hpow_le := hlog3 V (by linarith)
        have hV_add : V ^ (1 / 4 : ℝ) * V ^ (1 / 2 : ℝ) = V ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hV_pos]; norm_num
        calc 32 * (|xiLineTwoLogDerivConstant| + Real.log (2 * V + 4)) *
                ((Real.log V) ^ 2 * V ^ (1 / 2 : ℝ))
            = 32 * ((|xiLineTwoLogDerivConstant| + Real.log (2 * V + 4)) * (Real.log V) ^ 2) *
                V ^ (1 / 2 : ℝ) := by ring
          _ ≤ 32 * (2 * (|xiLineTwoLogDerivConstant| + 4) * (K_log3 * V ^ (1 / 4 : ℝ))) *
                V ^ (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left
                  (hfactor.trans (mul_le_mul_of_nonneg_left hpow_le (by positivity))) (by norm_num))
                (Real.rpow_nonneg hV_pos.le _)
          _ = 64 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 *
                (V ^ (1 / 4 : ℝ) * V ^ (1 / 2 : ℝ)) := by ring
          _ = 64 * (|xiLineTwoLogDerivConstant| + 4) * K_log3 * V ^ (3 / 4 : ℝ) := by rw [hV_add]
      linarith [hb1, hb2, hpoly, hcap_V]
    -- Four-band split of `R = (shellZeros T₁ T₂).filter (1 / 2 < ·.re)`
    classical
    set R := (shellZeros T₁ T₂).filter (fun z => 1 / 2 < z.re)
    set N_S : ℕ := ⌊L_S / 100⌋₊
    set b₀ : ℝ := κ₀ / Real.log (2 * V)
    set b_m : ℝ := (51 / 50 : ℝ) * ((m₀ : ℝ) / L_S)
    set b₂ : ℝ := (51 / 50 : ℝ) * ((N_S : ℝ) / L_S)
    set f_z : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ) * depthKernel L (z.re - 1 / 2)
    have hp1 := (Finset.sum_filter_add_sum_filter_not R (fun z => z.re - 1 / 2 < b₀) f_z).symm
    have hp2 := (Finset.sum_filter_add_sum_filter_not
      (R.filter (fun z => ¬ z.re - 1 / 2 < b₀)) (fun z => z.re - 1 / 2 < b_m) f_z).symm
    have hp3 := (Finset.sum_filter_add_sum_filter_not
      ((R.filter (fun z => ¬ z.re - 1 / 2 < b₀)).filter (fun z => ¬ z.re - 1 / 2 < b_m))
      (fun z => z.re - 1 / 2 < b₂) f_z).symm
    -- Band A (`0 < δ < b₀`): `4 * e^2 * κ₀` pointwise against `stripFinsetPos (2 * V)`
    have hbandA : 2 * ∑ z ∈ R.filter (fun z => z.re - 1 / 2 < b₀), f_z z ≤
        (ε / 10) * V * Real.log V := by
      have hptwA : ∀ z ∈ R.filter (fun z => z.re - 1 / 2 < b₀),
          f_z z ≤ (4 * Real.exp 2 * κ₀) * ((analyticOrderAt xi z).toNat : ℝ) := by
        intro z hz
        obtain ⟨hzR, hlt⟩ := Finset.mem_filter.mp hz
        have hre_gt : 1 / 2 < z.re := (Finset.mem_filter.mp hzR).2
        set δ : ℝ := z.re - 1 / 2
        have hδ_pos : 0 < δ := by dsimp [δ]; linarith
        have hlog2V_pos : 0 < Real.log (2 * V) := Real.log_pos (by linarith)
        have hL_le_2V : L ≤ Real.log (2 * V) := by
          dsimp [L]
          calc c' * Real.log V ≤ 1 * Real.log (2 * V) :=
                mul_le_mul (by linarith) (Real.log_le_log hV_pos (by linarith))
                  (by positivity) zero_le_one
            _ = Real.log (2 * V) := one_mul _
        have hLδ_κ : L * δ ≤ κ₀ := by
          calc L * δ ≤ Real.log (2 * V) * (κ₀ / Real.log (2 * V)) :=
                mul_le_mul hL_le_2V hlt.le hδ_pos.le hlog2V_pos.le
            _ = κ₀ := by have := hlog2V_pos.ne'; field_simp
        have hLδ_1 : L * δ ≤ 1 := hLδ_κ.trans hκ₀_le1
        have hsq : (L * δ) ^ 2 ≤ κ₀ := by nlinarith [hLδ_κ, hκ₀_le1, mul_nonneg hL0 hδ_pos.le]
        have hdk := depthKernel_le_four_sq_mul_exp (d := δ) hL0
        rw [abs_of_pos hδ_pos] at hdk
        have hexp2 : Real.exp (2 * L * δ) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
        have hdk' : depthKernel L δ ≤ 4 * Real.exp 2 * κ₀ := by
          have hm := mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 4))
            hexp2 (Real.exp_pos _).le (by positivity)
          linarith [hdk, hm]
        dsimp [f_z]
        have hm := mul_le_mul_of_nonneg_left hdk' (Nat.cast_nonneg (analyticOrderAt xi z).toNat)
        linarith
      have hsub_strip : R.filter (fun z => z.re - 1 / 2 < b₀) ⊆ stripFinsetPos (2 * V) := by
        intro z hz
        obtain ⟨⟨hz_sh, _⟩, _⟩ :=
          Finset.mem_filter.mp hz |> fun h => ⟨Finset.mem_filter.mp h.1, h.2⟩
        obtain ⟨h0, h1, him0, him2, hxi⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1
        exact mem_stripFinsetPos.mpr ⟨h0, h1, him0, him2.trans hT₂2V, hxi⟩
      have hord_2V := stripFinsetPos_orderSum_le_mul_log (by linarith : 2 ≤ 2 * V)
      have hlog2V : Real.log (2 * V) ≤ 2 * Real.log V := by
        rw [Real.log_mul zero_lt_two.ne' hV_pos.ne']; linarith [Real.log_two_lt_d9]
      have hord_V : ∑ z ∈ R.filter (fun z => z.re - 1 / 2 < b₀),
          ((analyticOrderAt xi z).toNat : ℝ) ≤ 4 * C_tot * V * Real.log V := by
        calc ∑ z ∈ R.filter (fun z => z.re - 1 / 2 < b₀), ((analyticOrderAt xi z).toNat : ℝ)
            ≤ ∑ z ∈ stripFinsetPos (2 * V), ((analyticOrderAt xi z).toNat : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_strip fun _ _ _ => Nat.cast_nonneg _
          _ ≤ C_tot * (2 * V) * Real.log (2 * V) := hord_2V
          _ ≤ C_tot * (2 * V) * (2 * Real.log V) :=
              mul_le_mul_of_nonneg_left hlog2V (by positivity)
          _ = 4 * C_tot * V * Real.log V := by ring
      have hsumA : ∑ z ∈ R.filter (fun z => z.re - 1 / 2 < b₀), f_z z ≤
          (4 * Real.exp 2 * κ₀) * (4 * C_tot * V * Real.log V) := by
        refine (Finset.sum_le_sum hptwA).trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hord_V (by positivity)
      have hm1 := mul_le_mul_of_nonneg_left hsumA zero_le_two
      have hm2 := mul_le_mul_of_nonneg_right hκ₀_tiny
        (mul_nonneg hV_pos.le (Real.log_nonneg (by linarith)))
      linarith [hm1, hm2]
    -- Band B (`b₀ ≤ δ < b_m`): bounded by `2 * M_br * offLineCountBeyond b₀ (2 * V)`
    have hbandB : 2 * ∑ z ∈ (R.filter (fun z => ¬ z.re - 1 / 2 < b₀)).filter
          (fun z => z.re - 1 / 2 < b_m), f_z z ≤
        (ε / 10) * V * Real.log V := by
      set R_B := (R.filter (fun z => ¬ z.re - 1 / 2 < b₀)).filter (fun z => z.re - 1 / 2 < b_m)
      have hptwB : ∀ z ∈ R_B, f_z z ≤ M_br * ((analyticOrderAt xi z).toNat : ℝ) := by
        intro z hz
        obtain ⟨hz1, hlt_m⟩ := Finset.mem_filter.mp hz
        have hre_gt : 1 / 2 < z.re := (Finset.mem_filter.mp (Finset.mem_filter.mp hz1).1).2
        have hδ_pos : 0 < z.re - 1 / 2 := by linarith
        have hdk := depthKernel_le_exp_two_mul (d := z.re - 1 / 2) hL0
        rw [abs_of_pos hδ_pos] at hdk
        have h2Ld : 2 * L * (z.re - 1 / 2) ≤ (51 / 25 : ℝ) * c' * (m₀ : ℝ) := by
          calc 2 * L * (z.re - 1 / 2)
              ≤ 2 * (c' * L_S) * ((51 / 50 : ℝ) * ((m₀ : ℝ) / L_S)) := by
                have hm := mul_le_mul hL_le_LS hlt_m.le hδ_pos.le (by positivity)
                linarith
            _ = (51 / 25 : ℝ) * c' * (m₀ : ℝ) := by
                have : L_S ≠ 0 := hLS_pos.ne'; field_simp; ring
        have hdk' : depthKernel L (z.re - 1 / 2) ≤ M_br :=
          hdk.trans (Real.exp_le_exp.mpr h2Ld)
        dsimp [f_z]
        have hm := mul_le_mul_of_nonneg_left hdk' (Nat.cast_nonneg (analyticOrderAt xi z).toNat)
        linarith
      have hsub_cnt : R_B ⊆ (stripFinsetPos (2 * V)).filter (fun z => 1 / 2 + b₀ ≤ z.re) := by
        intro z hz
        obtain ⟨hz1, _⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzR, hge_b0⟩ := Finset.mem_filter.mp hz1
        have hz_sh := (Finset.mem_filter.mp hzR).1
        obtain ⟨h0, h1, him0, him2, hxi⟩ := mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1
        refine Finset.mem_filter.mpr
          ⟨mem_stripFinsetPos.mpr ⟨h0, h1, him0, him2.trans hT₂2V, hxi⟩, ?_⟩
        linarith [not_lt.mp hge_b0]
      have hsumB : ∑ z ∈ R_B, f_z z ≤ M_br * offLineCountBeyond b₀ (2 * V) := by
        refine (Finset.sum_le_sum hptwB).trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub_cnt fun _ _ _ => Nat.cast_nonneg _)
          hMbr_pos.le
      exact (mul_le_mul_of_nonneg_left hsumB zero_le_two).trans hbr_V
    -- Band C (`b_m ≤ δ < b₂`): `scaleII_barbanVehov_slab_sum_le` starting at `m₀`
    have hbandC : 2 * ∑ z ∈ ((R.filter (fun z => ¬ z.re - 1 / 2 < b₀)).filter
          (fun z => ¬ z.re - 1 / 2 < b_m)).filter (fun z => z.re - 1 / 2 < b₂), f_z z ≤
        (3 * ε / 20) * V * Real.log V := by
      set R_C := ((R.filter (fun z => ¬ z.re - 1 / 2 < b₀)).filter
        (fun z => ¬ z.re - 1 / 2 < b_m)).filter (fun z => z.re - 1 / 2 < b₂)
      have hsub_C : R_C ⊆ (shellZeros T₁ T₂).filter (fun z =>
          (51 / 50) * ((m₀ : ℝ) / L_S) ≤ z.re - 1 / 2 ∧
            z.re - 1 / 2 < (51 / 50) * ((N_S : ℝ) / L_S)) := by
        intro z hz
        obtain ⟨hz2, hlt2⟩ := Finset.mem_filter.mp hz
        obtain ⟨hz1, hge_m⟩ := Finset.mem_filter.mp hz2
        have hz_sh := (Finset.mem_filter.mp (Finset.mem_filter.mp hz1).1).1
        exact Finset.mem_filter.mpr ⟨hz_sh, not_lt.mp hge_m, hlt2⟩
      have hT₁_pos : 0 < T₁ := by linarith
      have hbv_win : ∀ a : ℝ, 1 ≤ a → a ≤ Real.log S / 100 →
          2 * Real.pi * ((a / Real.log S) *
            ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 51 / 50 * (a / Real.log S) ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
            (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * Real.log S :=
        fun a ha1 ha2 => hbv_S a ha1 ha2 (windowZeros T₁ T₂) (mem_windowZeros_iff hT₁_pos hT₁2)
      have hslab := (Finset.sum_le_sum_of_subset_of_nonneg hsub_C fun z _ _ =>
          mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)).trans
        (scaleII_barbanVehov_slab_sum_le (V := V) (S := S) (A := A) (K := K)
          (c' := c') (L := L) (T₁ := T₁) (T₂ := T₂) (m₀ := m₀)
          (by linarith) rfl hA hK hc0 hc' hL0 hL_le_LS hT₁ hT₂ hLS200 hbv_win hm₀_1)
      have hmain_C : 2 * ((64 * Real.exp 1 * A / (lam * (1 - r))) * c' ^ 2 * r ^ m₀ * (V * L_S)) ≤
          (ε / 10) * V * Real.log V := by
        have hm1 : V * L_S ≤ 2 * (V * Real.log V) := by nlinarith [hLS_le_2logV, hV_pos]
        have hm2 := mul_le_mul_of_nonneg_left hm1
          (by positivity : 0 ≤ 2 * ((64 * Real.exp 1 * A / (lam * (1 - r))) * c' ^ 2 * r ^ m₀))
        have hm3 := mul_le_mul_of_nonneg_right hCII_tail
          (mul_nonneg hV_pos.le (Real.log_nonneg (by linarith)))
        dsimp [C_II] at hm3
        linarith
      have herr_C : 2 * ((16 * Real.exp 2 * K) * c' ^ 2 * L_S ^ 4 * S ^ (1 / 50 : ℝ)) ≤
          (ε / 20) * V * Real.log V := by
        have hS_pos : 0 < S := by dsimp [S]; linarith
        have hLS4 : L_S ^ 4 ≤ K_log4 * S ^ (1 / 50 : ℝ) := by
          exact (pow_le_pow_left₀ hLS_pos.le (by linarith) 4).trans
            (hlog4 S (by dsimp [S]; linarith))
        have hS_add : S ^ (1 / 50 : ℝ) * S ^ (1 / 50 : ℝ) = S ^ (1 / 25 : ℝ) := by
          rw [← Real.rpow_add hS_pos]; norm_num
        have hm := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLS4 (by positivity : 0 ≤ 2 * ((16 * Real.exp 2 * K) * c' ^ 2)))
          (Real.rpow_nonneg hS_pos.le (1 / 50))
        have hrew : 2 * ((16 * Real.exp 2 * K) * c' ^ 2) * (K_log4 * S ^ (1 / 50 : ℝ)) *
            S ^ (1 / 50 : ℝ) =
            2 * ((16 * Real.exp 2 * K) * c' ^ 2 * K_log4 * S ^ (1 / 25 : ℝ)) := by
          calc 2 * ((16 * Real.exp 2 * K) * c' ^ 2) * (K_log4 * S ^ (1 / 50 : ℝ)) *
                  S ^ (1 / 50 : ℝ)
              = 2 * ((16 * Real.exp 2 * K) * c' ^ 2 * K_log4 *
                  (S ^ (1 / 50 : ℝ) * S ^ (1 / 50 : ℝ))) := by ring
            _ = _ := by rw [hS_add]
        exact (hm.trans_eq hrew).trans herrII_V
      have hslab2 := mul_le_mul_of_nonneg_left hslab zero_le_two
      linarith [hslab2, hmain_C, herr_C]
    -- Band D (`b₂ ≤ δ`, hence `1 / 200 ≤ δ`): Scale III deep decay
    have hbandD : 2 * ∑ z ∈ ((R.filter (fun z => ¬ z.re - 1 / 2 < b₀)).filter
          (fun z => ¬ z.re - 1 / 2 < b_m)).filter (fun z => ¬ z.re - 1 / 2 < b₂), f_z z ≤
        (ε / 20) * V * Real.log V := by
      set R_D := ((R.filter (fun z => ¬ z.re - 1 / 2 < b₀)).filter
        (fun z => ¬ z.re - 1 / 2 < b_m)).filter (fun z => ¬ z.re - 1 / 2 < b₂)
      have hb₂_ge : (1 / 200 : ℝ) ≤ b₂ := by
        have hN_gt : L_S / 100 - 1 < (N_S : ℝ) := Nat.sub_one_lt_floor (L_S / 100)
        have hN_ge : L_S / 200 ≤ (N_S : ℝ) := by linarith [hLS200]
        have hm := mul_le_mul_of_nonneg_left hN_ge (by positivity : 0 ≤ (51 / 50) / L_S)
        have h1 : ((51 / 50) / L_S) * (L_S / 200) = 51 / 10000 := by
          have : L_S ≠ 0 := hLS_pos.ne'; field_simp; ring
        have h2 : ((51 / 50) / L_S) * (N_S : ℝ) = b₂ := by dsimp [b₂]; ring
        rw [h1, h2] at hm; linarith
      have hxiD : ∀ z ∈ R_D, xi z = 0 := fun z hz => by
        have hz_sh := (Finset.mem_filter.mp (Finset.mem_filter.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1).1
        exact (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1).2.2.2.2
      have hptwD : ∑ z ∈ R_D, f_z z ≤
          ∑ z ∈ R_D, ((analyticOrderAt xi z).toNat : ℝ) * Real.exp (2 * L * (z.re - 1 / 2)) := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hge : b₂ ≤ z.re - 1 / 2 := not_lt.mp (Finset.mem_filter.mp hz).2
        have hdk := depthKernel_le_exp_two_mul (d := z.re - 1 / 2) hL0
        rw [abs_of_pos (by linarith)] at hdk
        exact mul_le_mul_of_nonneg_left hdk (Nat.cast_nonneg _)
      rw [sum_analyticOrder_eq_sum_liftToXiZeroCopy R_D hxiD] at hptwD
      have hG_cond : ∀ q ∈ liftToXiZeroCopy R_D hxiD,
          1 / 2 + 1 / 200 ≤ foldedRe q ∧ V ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * V := by
        intro q hq
        have hz : (q.1 : ℂ) ∈ R_D := mem_liftToXiZeroCopy_iff hq
        have hge : b₂ ≤ (q.1 : ℂ).re - 1 / 2 := not_lt.mp (Finset.mem_filter.mp hz).2
        have hz_sh : (q.1 : ℂ) ∈ shellZeros T₁ T₂ :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp
            (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1).1
        have him1 : T₁ < (q.1 : ℂ).im := (Finset.mem_filter.mp hz_sh).2
        have him2 : (q.1 : ℂ).im ≤ T₂ := (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz_sh).1).2.2.2.1
        rw [abs_of_pos (by linarith)]
        exact ⟨le_trans (by linarith) (le_max_left _ _), by linarith, by linarith⟩
      have hfold_eq : ∑ q ∈ liftToXiZeroCopy R_D hxiD, Real.exp (2 * L * ((q.1 : ℂ).re - 1 / 2)) =
          ∑ q ∈ liftToXiZeroCopy R_D hxiD, Real.exp (2 * L * (foldedRe q - 1 / 2)) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        have hge : b₂ ≤ (q.1 : ℂ).re - 1 / 2 :=
          not_lt.mp (Finset.mem_filter.mp (mem_liftToXiZeroCopy_iff hq)).2
        rw [show foldedRe q = (q.1 : ℂ).re from max_eq_left (by linarith)]
      rw [hfold_eq] at hptwD
      have hdeep_G := hdeep V hV_deep L hL0 le_rfl (liftToXiZeroCopy R_D hxiD) hG_cond
      have hm_V := mul_le_mul_of_nonneg_left hdeep_G hV_pos.le
      have hlhs : V * ((1 / V) * ∑ q ∈ liftToXiZeroCopy R_D hxiD,
          Real.exp (2 * L * (foldedRe q - 1 / 2))) =
          ∑ q ∈ liftToXiZeroCopy R_D hxiD, Real.exp (2 * L * (foldedRe q - 1 / 2)) := by
        field_simp
      have hrhs : V * (C_deep * V ^ (-γ₀)) = C_deep * V ^ (1 - γ₀) := by
        calc V * (C_deep * V ^ (-γ₀))
            = C_deep * (V ^ (1 : ℝ) * V ^ (-γ₀)) := by rw [Real.rpow_one]; ring
          _ = C_deep * V ^ (1 - γ₀) := by rw [← Real.rpow_add hV_pos]; ring_nf
      rw [hlhs, hrhs] at hm_V
      exact (mul_le_mul_of_nonneg_left (hptwD.trans hm_V) zero_le_two).trans hdeep_V
    -- Sum end-caps + Bands A, B, C, D and divide by `V * Real.log V`
    have hsh_tot : shellDepthSum V (2 * V) L ≤ (ε / 2) * (V * Real.log V) := by
      rw [shellDepthSum_split hVT₁ (hT₁2.trans hT₂2V), shellDepthSum_split hT₁2 hT₂2V,
        shellDepthSum_eq_two_mul_right T₁ T₂ L]
      change shellDepthSum V T₁ L + (2 * ∑ z ∈ R, f_z z + shellDepthSum T₂ (2 * V) L) ≤ _
      rw [hp1, hp2, hp3]
      linarith [hcap_sum, hbandA, hbandB, hbandC, hbandD]
    have hden_pos : 0 < V * Real.log V := mul_pos hV_pos (by linarith)
    exact ⟨(div_le_iff₀ hden_pos).mpr hsh_tot,
      div_nonneg (shellDepthSum_nonneg _ _ _) hden_pos.le⟩
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp hev_all
  refine ⟨V₀, fun V hV => ?_⟩
  obtain ⟨hle, hnn⟩ := hV₀ V hV
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-- **Four-Way `o(log U)` Equivalence with Levinson–Montgomery `100%` Critical-Scale Clustering
(`dyadicMean_corridor_and_polynomialTheta_littleO_log_tfae`).**
For every fixed `0 < c < 22 / 51`, `o(log U)` vanishing of the dyadic mean of
`unitWindowDepthCharge`, `heckeDefect`, or the linear-stage `polynomialThetaSourceMomentReading`
is unconditionally equivalent (`List.TFAE`) to `100%` critical-scale clustering
`∀ κ > 0, offLineCountBeyond (κ / log V) V = o(V log V)`. -/
theorem dyadicMean_corridor_and_polynomialTheta_littleO_log_tfae
    {c : ℝ} (hc0 : 0 < c) (hc : c < 22 / 51) :
    List.TFAE [
      Tendsto (fun U : ℝ =>
        ((1 / U) * ∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) / Real.log U)
        atTop (𝓝 0),
      Tendsto (fun U : ℝ =>
        ((1 / U) * ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) /
          Real.log U)
        atTop (𝓝 0),
      Tendsto (fun U : ℝ =>
        ((1 / U) * ∫ γ in Icc U (2 * U),
          polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
            (linearThetaStage (2 * U))) / Real.log U)
        atTop (𝓝 0),
      ∀ κ : ℝ, 0 < κ →
        Tendsto (fun V : ℝ => offLineCountBeyond (κ / Real.log V) V / (V * Real.log V))
          atTop (𝓝 0)
    ] := by
  obtain ⟨C_lin, hC_lin, hpoly_diff⟩ := exists_abs_dyadicIntegral_polynomialTheta_sub_heckeDefect_le
  -- Difference between `(3)` and `(2)` is `O(1 / U) → 0`
  have hdiff_tendsto : Tendsto (fun U : ℝ =>
      (((1 / U) * ∫ γ in Icc U (2 * U),
        polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
          (linearThetaStage (2 * U))) / Real.log U) -
      (((1 / U) * ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) /
        Real.log U)) atTop (𝓝 0) := by
    have hnorm_zero : Tendsto (fun U : ℝ => 2 * C_lin / U) atTop (𝓝 0) := by
      simpa only [mul_zero, div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 * C_lin)
    refine squeeze_zero_norm' ?_ hnorm_zero
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with U hU4
    have hU_pos : 0 < U := by linarith
    have hlog_pos : 0 < Real.log U := Real.log_pos (by linarith)
    rw [Real.norm_eq_abs]
    have hsub_eq : (((1 / U) * ∫ γ in Icc U (2 * U),
          polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
            (linearThetaStage (2 * U))) / Real.log U) -
        (((1 / U) * ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) /
          Real.log U) =
        ((∫ γ in Icc U (2 * U),
          polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
            (linearThetaStage (2 * U))) -
        ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) /
          (U * Real.log U) := by
      have : U ≠ 0 := hU_pos.ne'
      have : Real.log U ≠ 0 := hlog_pos.ne'
      field_simp
    rw [hsub_eq, abs_div, abs_of_pos (mul_pos hU_pos hlog_pos)]
    have hbd := hpoly_diff U c hU4 hc0.le (by linarith)
    calc |(∫ γ in Icc U (2 * U),
            polynomialThetaSourceMomentReading (baseTwistTest γ) (c * Real.log γ) 1
              (linearThetaStage (2 * U))) -
          ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)| /
            (U * Real.log U)
        ≤ (2 * C_lin * Real.log U) / (U * Real.log U) :=
          div_le_div_of_nonneg_right hbd (by positivity)
      _ = 2 * C_lin / U := by have := hlog_pos.ne'; field_simp
  -- (2) → (3)
  tfae_have 2 → 3 := by
    intro h2
    have hadd := hdiff_tendsto.add h2
    rw [add_zero] at hadd
    exact hadd.congr fun U => sub_add_cancel _ _
  -- (3) → (2)
  tfae_have 3 → 2 := by
    intro h3
    have hsub := h3.sub hdiff_tendsto
    rw [sub_zero] at hsub
    exact hsub.congr fun U => sub_sub_cancel _ _
  -- (2) → (1): pointwise coercivity `cos(1/4)^2 * unitWindowDepthCharge ≤ heckeDefect` on `[U, 2U]`
  tfae_have 2 → 1 := by
    intro h2
    have hcos_pos : 0 < Real.cos (1 / 4 : ℝ) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    have hcos_sq : 0 < Real.cos (1 / 4 : ℝ) ^ 2 := sq_pos_of_pos hcos_pos
    have hrhs : Tendsto (fun U : ℝ =>
        (1 / Real.cos (1 / 4 : ℝ) ^ 2) *
          (((1 / U) * ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) /
            Real.log U)) atTop (𝓝 0) := by
      simpa only [mul_zero] using h2.const_mul (1 / Real.cos (1 / 4 : ℝ) ^ 2)
    refine squeeze_zero' ?_ ?_ hrhs
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with U hU4
      have hU_pos : 0 < U := by linarith
      have hlog_pos : 0 < Real.log U := Real.log_pos (by linarith)
      have hint_nn : 0 ≤ ∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T) :=
        setIntegral_nonneg measurableSet_Icc fun T hT => by
          unfold unitWindowDepthCharge
          exact Finset.sum_nonneg fun _ _ =>
            mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)
      positivity
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with U hU4
      have hU_pos : 0 < U := by linarith
      have hlog_pos : 0 < Real.log U := Real.log_pos (by linarith)
      have hle := cos_sq_mul_dyadicIntegral_unitWindowDepthCharge_le_heckeDefect hU_pos c
      have hm := mul_le_mul_of_nonneg_left hle
        (by positivity : 0 ≤ (1 / Real.cos (1 / 4 : ℝ) ^ 2) * (1 / U) / Real.log U)
      have hlhs : ((1 / Real.cos (1 / 4 : ℝ) ^ 2) * (1 / U) / Real.log U) *
          (Real.cos (1 / 4 : ℝ) ^ 2 *
            ∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) =
          ((1 / U) * ∫ T in Icc U (2 * U), unitWindowDepthCharge T (c * Real.log T)) /
            Real.log U := by
        have : Real.cos (1 / 4 : ℝ) ^ 2 ≠ 0 := hcos_sq.ne'
        field_simp; ring
      have hrhs_eq : ((1 / Real.cos (1 / 4 : ℝ) ^ 2) * (1 / U) / Real.log U) *
          (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) =
          (1 / Real.cos (1 / 4 : ℝ) ^ 2) *
            (((1 / U) * ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) /
              Real.log U) := by ring
      rwa [hlhs, hrhs_eq] at hm
  -- (1) → (4): telescope `K` dyadic shells `U_j = V / 2^{j+1}` + `stripFinsetPos (V / 2^K)`
  tfae_have 1 → 4 := by
    intro h1 κ hκ
    set C_tot : ℝ := 32 * (2 * |xiLineTwoLogDerivConstant| + 5)
    have hCtot_pos : 0 < C_tot := by
      dsimp [C_tot]; have := abs_nonneg xiLineTwoLogDerivConstant; positivity
    set γ_κ : ℝ := 4 * Real.sinh (c * κ / 2) ^ 2
    have hsinh_pos : 0 < Real.sinh (c * κ / 2) := by
      rw [Real.sinh_eq]
      have hx : 0 < c * κ / 2 := by positivity
      have h1 : Real.exp (-(c * κ / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have h2 : 1 < Real.exp (c * κ / 2) := Real.one_lt_exp_iff.mpr hx
      linarith
    have hγκ_pos : 0 < γ_κ := by dsimp [γ_κ]; positivity
    -- Dyadic telescoping cover of `stripFinsetPos W`
    have hcov_dyadic : ∀ (m : ℕ) (W : ℝ),
        stripFinsetPos W ⊆ stripFinsetPos (W / (2 : ℝ) ^ m) ∪
          (Finset.range m).biUnion (fun j =>
            shellZeros (W / (2 : ℝ) ^ (j + 1)) (2 * (W / (2 : ℝ) ^ (j + 1)))) := by
      intro m W
      induction m with
      | zero => simp
      | succ m ih =>
          intro z hz
          rw [Finset.range_succ, Finset.biUnion_insert]
          rcases Finset.mem_union.mp (ih hz) with hbase | hbi
          · obtain ⟨h0, h1, him0, him_le, hxi⟩ := mem_stripFinsetPos.mp hbase
            rcases le_or_gt z.im (W / (2 : ℝ) ^ (m + 1)) with hle | hgt
            · exact Finset.mem_union.mpr (Or.inl
                (mem_stripFinsetPos.mpr ⟨h0, h1, him0, hle, hxi⟩))
            · refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl ?_)))
              have h2eq : 2 * (W / (2 : ℝ) ^ (m + 1)) = W / (2 : ℝ) ^ m := by
                rw [pow_succ', ← div_div, mul_div_cancel₀ _ zero_lt_two.ne']
              rw [h2eq]
              exact Finset.mem_filter.mpr ⟨hbase, hgt⟩
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hbi)))
    rw [Metric.tendsto_atTop]
    intro ε hε
    set K_sh : ℕ := max 1 (⌈8 * C_tot / ε⌉₊ + 1)
    have hK_pos : 1 ≤ K_sh := le_max_left _ _
    have hK_real_pos : (0 : ℝ) < (K_sh : ℝ) := by exact_mod_cast hK_pos
    have hbase_coef : C_tot / (2 : ℝ) ^ K_sh ≤ ε / 8 := by
      have h1 : 8 * C_tot / ε < (K_sh : ℝ) := by
        have hlt : (⌈8 * C_tot / ε⌉₊ : ℝ) < (⌈8 * C_tot / ε⌉₊ : ℝ) + 1 := by linarith
        have hle1 : 8 * C_tot / ε ≤ (⌈8 * C_tot / ε⌉₊ : ℝ) := Nat.le_ceil _
        have hle2 : (⌈8 * C_tot / ε⌉₊ : ℝ) + 1 ≤ (K_sh : ℝ) := by
          exact_mod_cast le_max_right 1 (⌈8 * C_tot / ε⌉₊ + 1)
        linarith
      have h2 : (K_sh : ℝ) < (2 : ℝ) ^ K_sh := by exact_mod_cast K_sh.lt_two_pow_self
      have hm := (div_lt_iff₀ hε).mp (h1.trans h2)
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    -- Finite intersection of `h1` across `j < K_sh`
    have hev_shells : ∀ m : ℕ, ∀ᶠ V : ℝ in atTop, ∀ j < m,
        (∫ T in Icc (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1))),
          unitWindowDepthCharge T (c * Real.log T)) ≤
          (γ_κ * ε / (8 * (K_sh : ℝ))) * V * Real.log V := by
      intro m
      induction m with
      | zero => exact Eventually.of_forall fun _ _ hj => absurd hj (Nat.not_lt_zero _)
      | succ m ih =>
          have ht_j : Tendsto (fun V : ℝ => V / (2 : ℝ) ^ (m + 1)) atTop atTop :=
            tendsto_id.atTop_mul_const (by positivity)
          have hm_lim := Metric.tendsto_atTop.mp (h1.comp ht_j)
            (γ_κ * ε / (8 * (K_sh : ℝ))) (by positivity)
          obtain ⟨V_m, hV_m⟩ := hm_lim
          filter_upwards [ih, eventually_ge_atTop (max V_m (4 * (2 : ℝ) ^ (m + 1)))]
            with V hih hVm j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · exact hih j hlt
          · set U_m : ℝ := V / (2 : ℝ) ^ (m + 1)
            have hUm_ge4 : 4 ≤ U_m := by
              dsimp [U_m]
              rw [le_div_iff₀ (by positivity)]
              exact (le_max_right _ _).trans hVm
            have hUm_pos : 0 < U_m := by linarith
            have hlogUm_pos : 0 < Real.log U_m := Real.log_pos (by linarith)
            have hd := hV_m V ((le_max_left _ _).trans hVm)
            dsimp only [Function.comp_def] at hd
            have hint_nn : 0 ≤ ∫ T in Icc U_m (2 * U_m), unitWindowDepthCharge T (c * Real.log T) :=
              setIntegral_nonneg measurableSet_Icc fun T _ =>
                Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hd
            have hm1 := (div_lt_iff₀ hlogUm_pos).mp hd
            have hm2 := mul_le_mul_of_nonneg_left hm1.le hUm_pos.le
            have hlhs : U_m * ((1 / U_m) * ∫ T in Icc U_m (2 * U_m),
                unitWindowDepthCharge T (c * Real.log T)) =
                ∫ T in Icc U_m (2 * U_m), unitWindowDepthCharge T (c * Real.log T) := by
              field_simp
            rw [hlhs] at hm2
            have hUm_le_V : U_m ≤ V := div_le_self (by positivity)
              (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
            have hlog_le : Real.log U_m ≤ Real.log V := Real.log_le_log hUm_pos hUm_le_V
            calc (∫ T in Icc U_m (2 * U_m), unitWindowDepthCharge T (c * Real.log T))
                ≤ U_m * (γ_κ * ε / (8 * (K_sh : ℝ)) * Real.log U_m) := hm2
              _ = (γ_κ * ε / (8 * (K_sh : ℝ))) * (U_m * Real.log U_m) := by ring
              _ ≤ (γ_κ * ε / (8 * (K_sh : ℝ))) * (V * Real.log V) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hUm_le_V hlog_le hlogUm_pos.le (by positivity)) (by positivity)
              _ = (γ_κ * ε / (8 * (K_sh : ℝ))) * V * Real.log V := by ring
    have hev_short : ∀ᶠ V : ℝ in atTop,
        (K_sh : ℝ) * (16 * (|xiLineTwoLogDerivConstant| + 4 + Real.log V)) ≤
          (ε / 8) * V * Real.log V := by
      filter_upwards [eventually_ge_atTop
        (8 * (K_sh : ℝ) * 16 * (|xiLineTwoLogDerivConstant| + 5) / ε + 4)] with V hV
      have hlog1 : 1 ≤ Real.log V := by
        have := Real.log_two_gt_d9
        have := Real.log_le_log zero_lt_two (by linarith : (2 : ℝ) ≤ V)
        linarith
      have h1 : |xiLineTwoLogDerivConstant| + 4 + Real.log V ≤
          (|xiLineTwoLogDerivConstant| + 5) * Real.log V := by
        nlinarith [abs_nonneg xiLineTwoLogDerivConstant, hlog1]
      have hm1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (K_sh : ℝ) * 16)
      have hm2 := (div_le_iff₀ hε).mp
        (by linarith : 8 * (K_sh : ℝ) * 16 * (|xiLineTwoLogDerivConstant| + 5) / ε ≤ V)
      have hm3 := mul_le_mul_of_nonneg_right hm2 (by positivity : 0 ≤ Real.log V)
      linarith [hm1, hm3]
    have hev_cnt : ∀ᶠ V : ℝ in atTop,
        offLineCountBeyond (κ / Real.log V) V / (V * Real.log V) ≤ ε / 2 ∧
          0 ≤ offLineCountBeyond (κ / Real.log V) V / (V * Real.log V) := by
      filter_upwards [hev_shells K_sh, hev_short,
        Real.tendsto_log_atTop.eventually_ge_atTop (2 * (K_sh : ℝ) * Real.log 2 + 4),
        eventually_ge_atTop (4 * (2 : ℝ) ^ K_sh)]
        with V hsh_V hshort_V hlog_big hV_pow
      classical
      have hpow_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ K_sh := one_le_pow₀ one_le_two
      have hV4 : 4 ≤ V := by nlinarith
      have hV_pos : 0 < V := by linarith
      have hlogV_pos : 0 < Real.log V := Real.log_pos (by linarith)
      set P : ℂ → Prop := fun z => 1 / 2 + κ / Real.log V ≤ z.re
      set m_ord : ℂ → ℝ := fun z => ((analyticOrderAt xi z).toNat : ℝ)
      -- Cover `(stripFinsetPos V).filter P` by base + `K_sh` filtered shells
      have hcov_P : (stripFinsetPos V).filter P ⊆
          (stripFinsetPos (V / (2 : ℝ) ^ K_sh)).filter P ∪
            (Finset.range K_sh).biUnion (fun j =>
              (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter P) := by
        intro z hz
        obtain ⟨hz_s, hp⟩ := Finset.mem_filter.mp hz
        rcases Finset.mem_union.mp (hcov_dyadic K_sh V hz_s) with hb | hbi
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hb, hp⟩))
        · obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hbi
          exact Finset.mem_union.mpr (Or.inr
            (Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hzj, hp⟩⟩))
      -- Bound base `(stripFinsetPos (V / 2^{K_sh})).filter P`
      have hbase_le : ∑ z ∈ (stripFinsetPos (V / (2 : ℝ) ^ K_sh)).filter P, m_ord z ≤
          (ε / 8) * V * Real.log V := by
        have hVK_ge4 : 4 ≤ V / (2 : ℝ) ^ K_sh :=
          (le_div_iff₀ (by positivity)).mpr hV_pow
        have hord := stripFinsetPos_orderSum_le_mul_log (by linarith : 2 ≤ V / (2 : ℝ) ^ K_sh)
        have hlog_le : Real.log (V / (2 : ℝ) ^ K_sh) ≤ Real.log V :=
          Real.log_le_log (by positivity) (div_le_self hV_pos.le hpow_ge1)
        calc ∑ z ∈ (stripFinsetPos (V / (2 : ℝ) ^ K_sh)).filter P, m_ord z
            ≤ ∑ z ∈ stripFinsetPos (V / (2 : ℝ) ^ K_sh), m_ord z :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun _ _ _ => Nat.cast_nonneg _
          _ ≤ C_tot * (V / (2 : ℝ) ^ K_sh) * Real.log (V / (2 : ℝ) ^ K_sh) := hord
          _ ≤ C_tot * (V / (2 : ℝ) ^ K_sh) * Real.log V :=
              mul_le_mul_of_nonneg_left hlog_le (by positivity)
          _ = (C_tot / (2 : ℝ) ^ K_sh) * (V * Real.log V) := by ring
          _ ≤ (ε / 8) * (V * Real.log V) :=
              mul_le_mul_of_nonneg_right hbase_coef (by positivity)
          _ = (ε / 8) * V * Real.log V := by ring
      -- Bound each shell `j ∈ Finset.range K_sh`
      have hshell_each : ∀ j ∈ Finset.range K_sh,
          ∑ z ∈ (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter P,
            m_ord z ≤
            16 * (|xiLineTwoLogDerivConstant| + 4 + Real.log V) +
              (ε / (8 * (K_sh : ℝ))) * V * Real.log V := by
        intro j hj
        have hj_lt : j < K_sh := Finset.mem_range.mp hj
        set U_j : ℝ := V / (2 : ℝ) ^ (j + 1)
        have hpow_le : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ K_sh :=
          pow_le_pow_right₀ one_le_two (by omega)
        have hUj_ge4 : 4 ≤ U_j := by
          dsimp [U_j]
          rw [le_div_iff₀ (by positivity)]
          exact (mul_le_mul_of_nonneg_left hpow_le (by norm_num)).trans hV_pow
        have hUj_le_V : U_j ≤ V :=
          div_le_self hV_pos.le (one_le_pow₀ one_le_two)
        obtain ⟨hu, hd⟩ := shellZeros_disjoint_split (by linarith : U_j ≤ U_j + 1)
          (by linarith : U_j + 1 ≤ 2 * U_j)
        rw [hu, Finset.filter_union,
          Finset.sum_union (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
        -- Short end-cap `(U_j, U_j + 1]`
        have hshort_j : ∑ z ∈ (shellZeros U_j (U_j + 1)).filter P, m_ord z ≤
            16 * (|xiLineTwoLogDerivConstant| + 4 + Real.log V) := by
          have h1 := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => Nat.cast_nonneg _).trans
            (shortShell_orderSum_le_log (by linarith) (by linarith) (by linarith))
          have hlog_j : Real.log (U_j + 1 + 4) ≤ 4 + Real.log V := by
            calc Real.log (U_j + 1 + 4) ≤ Real.log (4 * V) :=
                  Real.log_le_log (by positivity) (by linarith)
              _ = Real.log 4 + Real.log V := Real.log_mul (by norm_num) hV_pos.ne'
              _ ≤ 4 + Real.log V := by
                  have : Real.log ((2 : ℝ) ^ (2 : ℕ)) ≤ 2 := by
                    rw [Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
                  norm_num at this; linarith
          linarith
        -- Main sub-shell `(U_j + 1, 2 * U_j]` via `shellDepthSum_le_dyadicIntegral_unitWindowDepthCharge`
        have hmain_j : ∑ z ∈ (shellZeros (U_j + 1) (2 * U_j)).filter P, m_ord z ≤
            (ε / (8 * (K_sh : ℝ))) * V * Real.log V := by
          have hlogUj_half : (1 / 2 : ℝ) * Real.log V ≤ Real.log U_j := by
            dsimp [U_j]
            rw [Real.log_div hV_pos.ne' (by positivity), Real.log_pow]
            have hj1_le : ((j + 1 : ℕ) : ℝ) ≤ (K_sh : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ K_sh)
            have hm := mul_le_mul_of_nonneg_right hj1_le (Real.log_pos one_lt_two).le
            linarith [hlog_big]
          have hdk_ge : ∀ z ∈ (shellZeros (U_j + 1) (2 * U_j)).filter P,
              γ_κ ≤ depthKernel (c * Real.log U_j) (z.re - 1 / 2) := by
            intro z hz
            have hre_ge : 1 / 2 + κ / Real.log V ≤ z.re := (Finset.mem_filter.mp hz).2
            rw [depthKernel_eq_four_sinh_sq]
            have harg_ge : c * κ / 2 ≤ (z.re - 1 / 2) * (c * Real.log U_j) := by
              have h1 : κ / Real.log V ≤ z.re - 1 / 2 := by linarith
              have hm := mul_le_mul h1 hlogUj_half (by positivity) (by linarith)
              have hsimp : (κ / Real.log V) * ((1 / 2 : ℝ) * Real.log V) = κ / 2 := by
                have := hlogV_pos.ne'; field_simp; ring
              have hm' := mul_le_mul_of_nonneg_left hm hc0.le
              linarith [hm', show c * ((κ / Real.log V) * ((1 / 2 : ℝ) * Real.log V)) =
                c * (κ / 2) by rw [hsimp]]
            have hsh_ge := sinh_mono_nonneg (by positivity) harg_ge
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hsinh_pos.le hsh_ge 2) (by norm_num)
          have hsum_dk : γ_κ * ∑ z ∈ (shellZeros (U_j + 1) (2 * U_j)).filter P, m_ord z ≤
              shellDepthSum (U_j + 1) (2 * U_j) (c * Real.log U_j) := by
            rw [Finset.mul_sum]
            refine (Finset.sum_le_sum fun z hz => ?_).trans
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _))
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left (hdk_ge z hz) (Nat.cast_nonneg _)
          have hint_le := hsum_dk.trans
            (shellDepthSum_le_dyadicIntegral_unitWindowDepthCharge (by linarith) hc0.le)
          have hbd_j := hint_le.trans (hsh_V j hj_lt)
          have hm := (le_div_iff₀ hγκ_pos).mpr
            (by linarith [hbd_j] :
              (∑ z ∈ (shellZeros (U_j + 1) (2 * U_j)).filter P, m_ord z) * γ_κ ≤
                ((ε / (8 * (K_sh : ℝ))) * V * Real.log V) * γ_κ)
          rwa [mul_div_cancel_right₀ _ hγκ_pos.ne'] at hm
        exact add_le_add hshort_j hmain_j
      -- Sum base + `K_sh` shells
      have htot_cnt : offLineCountBeyond (κ / Real.log V) V ≤
          (ε / 2) * (V * Real.log V) := by
        unfold offLineCountBeyond
        have h1 : ∑ z ∈ (stripFinsetPos V).filter P, m_ord z ≤
            ∑ z ∈ (stripFinsetPos (V / (2 : ℝ) ^ K_sh)).filter P, m_ord z +
              ∑ j ∈ Finset.range K_sh,
                ∑ z ∈ (shellZeros (V / (2 : ℝ) ^ (j + 1))
                  (2 * (V / (2 : ℝ) ^ (j + 1)))).filter P, m_ord z := by
          refine (Finset.sum_le_sum_of_subset_of_nonneg hcov_P fun _ _ _ => Nat.cast_nonneg _).trans ?_
          have hu : ∑ z ∈ (stripFinsetPos (V / (2 : ℝ) ^ K_sh)).filter P ∪
                (Finset.range K_sh).biUnion (fun j =>
                  (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter P),
                m_ord z ≤
              ∑ z ∈ (stripFinsetPos (V / (2 : ℝ) ^ K_sh)).filter P, m_ord z +
                ∑ z ∈ (Finset.range K_sh).biUnion (fun j =>
                  (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter P),
                m_ord z := by
            have h := Finset.sum_union_inter
              (s₁ := (stripFinsetPos (V / (2 : ℝ) ^ K_sh)).filter P)
              (s₂ := (Finset.range K_sh).biUnion (fun j =>
                (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter P))
              (f := m_ord)
            have hnn : 0 ≤ ∑ z ∈ _ ∩ _, m_ord z := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
            linarith
          exact hu.trans (add_le_add le_rfl (finset_sum_biUnion_le _ _ fun _ => Nat.cast_nonneg _))
        have h2 : ∑ j ∈ Finset.range K_sh,
            ∑ z ∈ (shellZeros (V / (2 : ℝ) ^ (j + 1)) (2 * (V / (2 : ℝ) ^ (j + 1)))).filter P,
              m_ord z ≤
            (K_sh : ℝ) * (16 * (|xiLineTwoLogDerivConstant| + 4 + Real.log V)) +
              (ε / 8) * V * Real.log V := by
          calc ∑ j ∈ Finset.range K_sh, _
              ≤ ∑ _j ∈ Finset.range K_sh,
                  (16 * (|xiLineTwoLogDerivConstant| + 4 + Real.log V) +
                    (ε / (8 * (K_sh : ℝ))) * V * Real.log V) :=
                Finset.sum_le_sum hshell_each
            _ = (K_sh : ℝ) * (16 * (|xiLineTwoLogDerivConstant| + 4 + Real.log V) +
                  (ε / (8 * (K_sh : ℝ))) * V * Real.log V) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ = (K_sh : ℝ) * (16 * (|xiLineTwoLogDerivConstant| + 4 + Real.log V)) +
                  (ε / 8) * V * Real.log V := by
                have := hK_real_pos.ne'; field_simp; ring
        have hpos_VL : 0 ≤ V * Real.log V := by positivity
        linarith [h1, hbase_le, h2, hshort_V, hε]
      have hden_pos : 0 < V * Real.log V := mul_pos hV_pos hlogV_pos
      have hcnt_nn : 0 ≤ offLineCountBeyond (κ / Real.log V) V :=
        Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      exact ⟨(div_le_iff₀ hden_pos).mpr htot_cnt, div_nonneg hcnt_nn hden_pos.le⟩
    obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp hev_cnt
    refine ⟨V₀, fun V hV => ?_⟩
    obtain ⟨hle, hnn⟩ := hV₀ V hV
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith
  -- (4) → (2): apply `tendsto_shellDepthSum_div_mul_log_zero_of_countBeyond` across `U/2, U, 2U`
  tfae_have 4 → 2 := by
    intro h4
    set c' : ℝ := (c + 22 / 51) / 2
    have hc_lt : c < c' := by dsimp [c']; linarith
    have hc'_pos : 0 < c' := hc0.trans hc_lt
    have hc'_lt : c' < 22 / 51 := by dsimp [c']; linarith
    have hsh_zero := tendsto_shellDepthSum_div_mul_log_zero_of_countBeyond hc'_pos hc'_lt h4
    obtain ⟨C_loc, C_rem, hC_loc, hC_rem, hhecke_3sh⟩ := exists_dyadicIntegral_heckeDefect_le_threeShells
    set f : ℝ → ℝ := fun V => shellDepthSum V (2 * V) (c' * Real.log V) / (V * Real.log V)
    have ht_half : Tendsto (fun U : ℝ => U / 2) atTop atTop :=
      tendsto_id.atTop_mul_const (by norm_num)
    have ht_two : Tendsto (fun U : ℝ => 2 * U) atTop atTop :=
      tendsto_id.const_mul_atTop zero_lt_two
    have hf_half : Tendsto (fun U : ℝ => f (U / 2)) atTop (𝓝 0) := hsh_zero.comp ht_half
    have hf_2U : Tendsto (fun U : ℝ => f (2 * U)) atTop (𝓝 0) := hsh_zero.comp ht_two
    have hrem_zero : Tendsto (fun U : ℝ => 2 * C_rem / U) atTop (𝓝 0) := by
      simpa only [mul_zero, div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 * C_rem)
    have hrhs_zero : Tendsto (fun U : ℝ =>
        C_loc * (f (U / 2) + f U + 4 * f (2 * U)) + 2 * C_rem / U) atTop (𝓝 0) := by
      have hsum : Tendsto (fun U : ℝ => f (U / 2) + f U + 4 * f (2 * U)) atTop (𝓝 0) := by
        simpa only [add_zero, mul_zero] using (hf_half.add hsh_zero).add (hf_2U.const_mul 4)
      simpa only [mul_zero, add_zero] using (hsum.const_mul C_loc).add hrem_zero
    refine squeeze_zero' ?_ ?_ hrhs_zero
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with U hU4
      have hU_pos : 0 < U := by linarith
      have hlog_pos : 0 < Real.log U := Real.log_pos (by linarith)
      have hint_nn : 0 ≤ ∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ) :=
        setIntegral_nonneg measurableSet_Icc fun γ _ => heckeDefect_nonneg _ _
      positivity
    · set δ_c : ℝ := c' - c
      have hδc_pos : 0 < δ_c := sub_pos.mpr hc_lt
      filter_upwards [
        Real.tendsto_log_atTop.eventually_ge_atTop ((c + c') * Real.log 2 / δ_c + 4),
        eventually_ge_atTop (16 : ℝ)] with U hlogU_big hU16
      have hU_pos : 0 < U := by linarith
      have hlogU_ge4 : 4 ≤ Real.log U := by
        have : 0 ≤ (c + c') * Real.log 2 / δ_c := by positivity
        linarith
      have hlogU_pos : 0 < Real.log U := by linarith
      set L_max : ℝ := c * Real.log (2 * U)
      have hLmax_nn : 0 ≤ L_max := mul_nonneg hc0.le (Real.log_nonneg (by linarith))
      have hL_le_half : L_max ≤ c' * Real.log (U / 2) := by
        have hlog2U : Real.log (2 * U) = Real.log 2 + Real.log U :=
          Real.log_mul zero_lt_two.ne' hU_pos.ne'
        have hlogU2 : Real.log (U / 2) = Real.log U - Real.log 2 :=
          Real.log_div hU_pos.ne' zero_lt_two.ne'
        dsimp [L_max]; rw [hlog2U, hlogU2]
        have hm := (div_le_iff₀ hδc_pos).mp
          (by linarith : (c + c') * Real.log 2 / δ_c ≤ Real.log U)
        dsimp [δ_c] at hm; nlinarith
      have hL_le_U : L_max ≤ c' * Real.log U :=
        hL_le_half.trans (mul_le_mul_of_nonneg_left
          (Real.log_le_log (by positivity) (by linarith)) hc'_pos.le)
      have hL_le_2U : L_max ≤ c' * Real.log (2 * U) :=
        hL_le_U.trans (mul_le_mul_of_nonneg_left
          (Real.log_le_log hU_pos (by linarith)) hc'_pos.le)
      have hb_half : shellDepthSum (U / 2) U L_max ≤ f (U / 2) * (U * Real.log U) := by
        have hm1 := shellDepthSum_mono_scale hLmax_nn hL_le_half (V₁ := U / 2) (V₂ := U)
        have heq2 : 2 * (U / 2) = U := by ring
        have hden_half : 0 < (U / 2) * Real.log (U / 2) :=
          mul_pos (by positivity) (Real.log_pos (by linarith))
        have hf_eq : shellDepthSum (U / 2) U (c' * Real.log (U / 2)) =
            f (U / 2) * ((U / 2) * Real.log (U / 2)) := by
          dsimp [f]; rw [heq2, div_mul_cancel₀ _ hden_half.ne']
        have hf_nn : 0 ≤ f (U / 2) :=
          div_nonneg (shellDepthSum_nonneg _ _ _) hden_half.le
        have hUL : (U / 2) * Real.log (U / 2) ≤ U * Real.log U :=
          mul_le_mul (by linarith) (Real.log_le_log (by positivity) (by linarith))
            (Real.log_nonneg (by linarith)) hU_pos.le
        exact (hm1.trans_eq hf_eq).trans (mul_le_mul_of_nonneg_left hUL hf_nn)
      have hb_U : shellDepthSum U (2 * U) L_max ≤ f U * (U * Real.log U) := by
        have hm1 := shellDepthSum_mono_scale hLmax_nn hL_le_U (V₁ := U) (V₂ := 2 * U)
        have hden : 0 < U * Real.log U := mul_pos hU_pos hlogU_pos
        exact hm1.trans_eq (by dsimp [f]; rw [div_mul_cancel₀ _ hden.ne'])
      have hb_2U : shellDepthSum (2 * U) (4 * U) L_max ≤ 4 * f (2 * U) * (U * Real.log U) := by
        have hm1 := shellDepthSum_mono_scale hLmax_nn hL_le_2U (V₁ := 2 * U) (V₂ := 4 * U)
        have heq4 : 2 * (2 * U) = 4 * U := by ring
        have hden_2U : 0 < (2 * U) * Real.log (2 * U) :=
          mul_pos (by positivity) (Real.log_pos (by linarith))
        have hf_eq : shellDepthSum (2 * U) (4 * U) (c' * Real.log (2 * U)) =
            f (2 * U) * ((2 * U) * Real.log (2 * U)) := by
          dsimp [f]; rw [heq4, div_mul_cancel₀ _ hden_2U.ne']
        have hf_nn : 0 ≤ f (2 * U) :=
          div_nonneg (shellDepthSum_nonneg _ _ _) hden_2U.le
        have hlog2U : Real.log (2 * U) ≤ 2 * Real.log U := by
          rw [Real.log_mul zero_lt_two.ne' hU_pos.ne']; linarith [Real.log_two_lt_d9]
        have hUL : (2 * U) * Real.log (2 * U) ≤ 4 * (U * Real.log U) := by
          have := mul_le_mul_of_nonneg_left hlog2U (by positivity : 0 ≤ 2 * U)
          linarith
        calc shellDepthSum (2 * U) (4 * U) L_max
            ≤ f (2 * U) * ((2 * U) * Real.log (2 * U)) := hm1.trans_eq hf_eq
          _ ≤ f (2 * U) * (4 * (U * Real.log U)) := mul_le_mul_of_nonneg_left hUL hf_nn
          _ = 4 * f (2 * U) * (U * Real.log U) := by ring
      have h3 := hhecke_3sh U c (by linarith) hc0.le
      have h2U_c : (2 * U) ^ c ≤ 2 * U := by
        calc (2 * U) ^ c ≤ (2 * U) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = 2 * U := Real.rpow_one _
      have hrem_le : C_rem * (2 * U) ^ c / U ≤ (2 * C_rem / U) * (U * Real.log U) := by
        have h1 : C_rem * (2 * U) ^ c / U ≤ 2 * C_rem := by
          rw [div_le_iff₀ hU_pos]; nlinarith [hC_rem]
        have h2 : (2 * C_rem / U) * (U * Real.log U) = 2 * C_rem * Real.log U := by
          have := hU_pos.ne'; field_simp; ring
        rw [h2]
        exact h1.trans (le_mul_of_one_le_right (by positivity) (by linarith))
      have htot : (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) ≤
          (C_loc * (f (U / 2) + f U + 4 * f (2 * U)) + 2 * C_rem / U) * (U * Real.log U) := by
        have hsum_sh : shellDepthSum (U / 2) U L_max + shellDepthSum U (2 * U) L_max +
            shellDepthSum (2 * U) (4 * U) L_max ≤
            (f (U / 2) + f U + 4 * f (2 * U)) * (U * Real.log U) := by
          linarith [hb_half, hb_U, hb_2U]
        have hm_loc := mul_le_mul_of_nonneg_left hsum_sh hC_loc.le
        linarith [h3, hm_loc, hrem_le]
      have hden : 0 < U * Real.log U := mul_pos hU_pos hlogU_pos
      have hm := (div_le_iff₀ hden).mpr htot
      have hlhs : ((1 / U) * ∫ γ in Icc U (2 * U),
          heckeDefect (baseTwistTest γ) (c * Real.log γ)) / Real.log U =
          (∫ γ in Icc U (2 * U), heckeDefect (baseTwistTest γ) (c * Real.log γ)) /
            (U * Real.log U) := by
        have : U ≠ 0 := hU_pos.ne'
        have : Real.log U ≠ 0 := hlogU_pos.ne'
        field_simp
      rwa [hlhs]
  tfae_finish

#print axioms eulerFactor_verticalZeros_depthKernel_ge
#print axioms exists_dyadicMean_corridor_and_polynomialTheta_le_log
#print axioms exists_dyadicMean_polynomialTheta_subpower_up_to_two_thirds
#print axioms eventually_volume_badLogLogCorridor_unitWindows_le
#print axioms dyadicMean_corridor_and_polynomialTheta_littleO_log_tfae

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

end
