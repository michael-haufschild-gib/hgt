import GaloisForLFunctions.RHTower.MarkovOverCompletedPoissonCombAndSlopeGaugePBAP

/-!
# Origin Boundary Absorption (`n = 1`), Elimination of `atomPairRe`, and True Trapezoidal Coercivity on the Primitive Hyperplane and Odd Sector

This module resolves a structural puzzle in the Euler–Maclaurin / Lebesgue–Atom PBAP bridge from
Modules 35–41: why did every coercive lower bound carry a subtracted `- atomPairRe k_f` term?

## The Mathematical Discovery: The Missing `n = 1` Origin Term Absorbs `atomPairRe`

1. **Section 1 (The Missing `n = 1` Origin Boundary Term `ℓ_f(1) = 2 ∫ ‖f‖²`, Spectral Cosine
   Dominance `atomPairRe k_f ≤ 2 ∫ ‖f‖²`, and Exact Absorption of `atomPairRe`):**
   - The continuum pole integral `∫_1^∞ primeIntegrand k_f d(lebesguePart)` starts at `x = 1`
     (`u = log 1 = 0`), whereas the discrete integer counterterm `∑_{n ≥ 2} lam(n) logValue f n`
     starts at `n = 2`.
   - At the origin `x = 1` (`u = 0`), the autocorrelation `k_f = EF.weilTest f f` evaluates to the
     exact `L²` norm (`weilTest_zero_eq_integral_norm_sq`, `re_weilTest_zero_eq_integral_norm_sq`):
     `(EF.weilTest f f 0).re = ∫ u : ℝ, ‖f u‖ ^ 2`.
   - Consequently, the `n = 1` log-profile value is twice the `L²` norm
     (`logValue_one_eq_two_mul_integral_norm_sq`,
     `weilContinuumLogProfile_one_eq_two_mul_integral_norm_sq`):
     `weilContinuumLogProfile f 1 = logValue f 1 = 2 * ∫ u : ℝ, ‖f u‖ ^ 2`.
   - By Fourier inversion (`EF.k_add_k_neg`) and Plancherel (`integral_norm_sq_paperFT_eq`), for
     **every** shift `u₀ ∈ ℝ` and every `f : WeilTestFn`, we prove the **Spectral Dirichlet
     Difference Identity** (`two_mul_integral_norm_sq_sub_re_weilTest_pair_eq`):
     `2 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (k_f u₀ + k_f (-u₀)).re = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (1 - Real.cos (r * u₀))) ≥ 0`.
   - Specializing to `u₀ = 1 / 10000` proves `atomPairRe_weilTest_le_two_mul_integral_norm_sq`:
     `atomPairRe (EF.weilTest f.1 f.1) ≤ 2 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) = weilContinuumLogProfile f.1 1`.

2. **Section 2 (Telescoping `α`-Weighted Euler–Maclaurin Cell Quadrature
   `weightedCellQuadratureDefect α g N` and Exact Extraction of the `n = 1` Origin Boundary Term):**
   - For any weight `α ∈ ℝ`, we define the `α`-weighted cell quadrature defect on `[1, N]`:
     `weightedCellQuadratureDefect α g N := ∑ n ∈ Finset.Icc 2 N, ∫ x in (n - 1)..n, (g x - (α * g (n - 1) + (1 - α) * g n))`,
     with special cases `unitLeftCellDefect := weightedCellQuadratureDefect 1` (left-endpoint rule on
     each cell `[n - 1, n]`) and `trueTrapezoidalCellDefect := weightedCellQuadratureDefect (1 / 2)`
     (true trapezoidal rule on each cell `[n - 1, n]`).
   - Because `∑_{n = 2}^N (g(n - 1) - g(n)) = g(1) - g(N)` telescopes across `Finset.Icc 2 N`, we
     prove the universal decomposition
     (`rightCellQuadratureDefect_eq_alpha_boundary_add_weightedCellQuadratureDefect`):
     `rightCellQuadratureDefect g N = α * (g 1 - g N) + weightedCellQuadratureDefect α g N`.
   - For `g = weilContinuumLogProfile f.1` with `k_f(±log N) = 0`, `g(N) = 0` and
     `g(1) = 2 * ∫ ‖f.1‖²`, giving (`rightCellQuadratureDefect_weilContinuumLogProfile_eq_weighted`):
     `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = 2 * α * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + weightedCellQuadratureDefect α (weilContinuumLogProfile f.1) N`.

3. **Section 3 (Complete Elimination of `atomPairRe` and Upgraded Coercivity
   `(1 / 100 + 2 * (α * θ - 1)) * ∫ ‖F‖²` on the Full Cone, Primitive Hyperplane, and Odd Sector):**
   - Substituting the `n = 1` origin boundary extraction into the `θ`-slope gauge identity from
     `MarkovOverCompletedPoissonCombAndSlopeGaugePBAP.lean` shows that whenever `1 ≤ α * θ`:
     - At `α = 1, θ = 1` (left-endpoint quadrature at unit slope, even on the full cone!),
       `2 * α * θ = 2`, so the `n = 1` boundary term `+2 ∫ ‖f‖²` completely absorbs `- atomPairRe k_f`!
     - At `α = 1 / 2, θ ≥ 2` (**true trapezoidal quadrature** at over-completed slope `θ ≥ 2` on the
       primitive hyperplane and odd sector), `2 * α * θ = θ ≥ 2`, so the `n = 1` trapezoidal
       boundary term `+θ ∫ ‖F‖²` completely absorbs `- atomPairRe k_F` AND upgrades the `L²`
       coercivity constant from `1 / 100` to `1 / 100 + θ - 2`!
   - Combining with `Real.log N ≤ θ` and `0 ≤ iteratedForwardDiff m (logValue F)` on `[2, N]` yields
     an unconditional, `atomPairRe`-free, discrete-prime-free lower bound for `markovEnergy F` on
     the primitive hyperplane and odd sector purely in terms of `trueTrapezoidalCellDefect`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The Missing `n = 1` Origin Boundary Term `ℓ_f(1) = 2 ∫ ‖f‖²`, Spectral Cosine Dominance, and Exact Absorption of `atomPairRe` -/

/-- At the origin `0`, the autocorrelation `EF.weilTest f f 0` equals the `L²` norm squared
`((∫ u : ℝ, ‖f u‖ ^ 2 : ℝ) : ℂ)`. -/
theorem weilTest_zero_eq_integral_norm_sq (f : ℝ → ℂ) :
    EF.weilTest f f 0 = ((∫ u : ℝ, ‖f u‖ ^ 2 : ℝ) : ℂ) := by
  rw [WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The real part of `EF.weilTest f f 0` is `∫ u : ℝ, ‖f u‖ ^ 2`. -/
@[simp]
theorem re_weilTest_zero_eq_integral_norm_sq (f : ℝ → ℂ) :
    (EF.weilTest f f 0).re = ∫ u : ℝ, ‖f u‖ ^ 2 := by
  rw [weilTest_zero_eq_integral_norm_sq, Complex.ofReal_re]

/-- At `n = 1`, `logValue f 1` equals `2 * ∫ u : ℝ, ‖f u‖ ^ 2`. -/
theorem logValue_one_eq_two_mul_integral_norm_sq (f : ℝ → ℂ) :
    logValue f 1 = 2 * ∫ u : ℝ, ‖f u‖ ^ 2 := by
  unfold logValue
  simp only [Nat.cast_one, Real.log_one, neg_zero, Real.sqrt_one, div_one,
    Complex.add_re, re_weilTest_zero_eq_integral_norm_sq]
  ring

/-- At `x = 1`, the continuum log-profile `weilContinuumLogProfile f 1` equals
`2 * ∫ u : ℝ, ‖f u‖ ^ 2`. -/
theorem weilContinuumLogProfile_one_eq_two_mul_integral_norm_sq (f : ℝ → ℂ) :
    weilContinuumLogProfile f 1 = 2 * ∫ u : ℝ, ‖f u‖ ^ 2 := by
  have h := weilContinuumLogProfile_natCast_eq_logValue f 1
  simpa [logValue_one_eq_two_mul_integral_norm_sq] using h

/-- **Spectral Cosine Representation of Symmetric Autocorrelation Pairs**:
for every `f : WeilTestFn` and every shift `u₀ : ℝ`,
`(EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r * u₀))`. -/
theorem re_weilTest_add_neg_eq_spectral_cos (f : WeilTestFn) (u₀ : ℝ) :
    (EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re =
      (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r * u₀)) := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have hki : Integrable (EF.weilTest f.1 f.1) :=
    hkd.continuous.integrable_of_hasCompactSupport hkc
  have hFk : Integrable (𝓕 (EF.weilTest f.1 f.1)) :=
    EF.integrable_fourier_of_contDiff_two hkd hkc
  have hPn : ∀ r : ℝ, paperFT (EF.weilTest f.1 f.1) r = ((‖paperFT f.1 r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [EF.paperFT_weilTest f.2.1.continuous f.2.1.continuous f.2.2 f.2.2, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpair := EF.k_add_k_neg hkd.continuous hki hFk u₀
  have hint : (∫ r : ℝ, paperFT (EF.weilTest f.1 f.1) r * (Real.cos (r * u₀) : ℂ)) =
      ((∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * Real.cos (r * u₀) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hPn, Complex.ofReal_mul]
  have h1 : (1 / π : ℂ) = ((1 / (2 * π) * 2 : ℝ) : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
  rw [hpair, hint, h1, ← Complex.ofReal_mul, Complex.ofReal_re, mul_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  ring

/-- **Spectral Cosine Representation of `atomPairRe`**:
for every `f : WeilTestFn`,
`atomPairRe (EF.weilTest f.1 f.1) = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r / 10000))`. -/
theorem atomPairRe_weilTest_eq (f : WeilTestFn) :
    atomPairRe (EF.weilTest f.1 f.1) =
      (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r / 10000)) := by
  unfold atomPairRe
  rw [re_weilTest_add_neg_eq_spectral_cos f (1 / 10000)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [show r * (1 / 10000) = r / 10000 by ring]

/-- **Spectral Dirichlet Difference Identity**:
for every `f : WeilTestFn` and every shift `u₀ : ℝ`, the difference between the `n = 1` origin term
`2 * ∫ ‖f.1‖²` and the symmetric autocorrelation pair `(k_f(u₀) + k_f(-u₀)).re` equals the
nonnegative spectral integral
`(1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (1 - Real.cos (r * u₀)))`. -/
theorem two_mul_integral_norm_sq_sub_re_weilTest_pair_eq (f : WeilTestFn) (u₀ : ℝ) :
    2 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        (EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re =
      (1 / (2 * π)) *
        ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (1 - Real.cos (r * u₀))) := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have hFk : Integrable (𝓕 (EF.weilTest f.1 f.1)) :=
    EF.integrable_fourier_of_contDiff_two hkd hkc
  have hP : Integrable fun r : ℝ => paperFT (EF.weilTest f.1 f.1) r :=
    EF.integrable_paperFT_ofReal hFk
  have hPn : ∀ r : ℝ, paperFT (EF.weilTest f.1 f.1) r = ((‖paperFT f.1 r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [EF.paperFT_weilTest f.2.1.continuous f.2.1.continuous f.2.2 f.2.2, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 := by
    refine hP.norm.congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [hPn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcos : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r * u₀)) := by
    refine (hsq.mul_const 2).mono' ?_ (Eventually.of_forall fun r => ?_)
    · exact (hsq.aestronglyMeasurable.mul (by fun_prop))
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hle : |Real.cos (r * u₀)| ≤ 1 := Real.abs_cos_le_one (r * u₀)
      nlinarith [sq_nonneg ‖paperFT f.1 r‖]
  rw [← LebesgueAtomWeil.integral_norm_sq_paperFT_eq f.2.1 f.2.2,
    re_weilTest_add_neg_eq_spectral_cos f u₀]
  have h2 : 2 * ((1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2) =
      (1 / (2 * π)) * ∫ r : ℝ, (‖paperFT f.1 r‖ ^ 2 * 2) := by
    rw [integral_mul_const]
    ring
  rw [h2, ← mul_sub, ← integral_sub (hsq.mul_const 2) hcos]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  ring

/-- **Bochner / Spectral Dominance of Symmetric Autocorrelation Pairs by the Origin**:
for every `f : WeilTestFn` and every shift `u₀ : ℝ`,
`(EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem re_weilTest_add_neg_le_two_mul_integral_norm_sq (f : WeilTestFn) (u₀ : ℝ) :
    (EF.weilTest f.1 f.1 u₀ + EF.weilTest f.1 f.1 (-u₀)).re ≤
      2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have hdiff := two_mul_integral_norm_sq_sub_re_weilTest_pair_eq f u₀
  have hnonneg : 0 ≤ (1 / (2 * π)) *
      ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (1 - Real.cos (r * u₀))) := by
    refine mul_nonneg (by positivity) (integral_nonneg fun r => ?_)
    refine mul_nonneg (by positivity) ?_
    linarith [Real.cos_le_one (r * u₀)]
  linarith

/-- **Origin Dominance of `atomPairRe` (`atomPairRe k_f ≤ 2 ∫ ‖f‖² = ℓ_f(1)`)**:
for every `f : WeilTestFn`, `atomPairRe (EF.weilTest f.1 f.1) ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem atomPairRe_weilTest_le_two_mul_integral_norm_sq (f : WeilTestFn) :
    atomPairRe (EF.weilTest f.1 f.1) ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 :=
  re_weilTest_add_neg_le_two_mul_integral_norm_sq f (1 / 10000)

/-- Equivalently, `atomPairRe (EF.weilTest f.1 f.1) ≤ weilContinuumLogProfile f.1 1`. -/
theorem atomPairRe_weilTest_le_weilContinuumLogProfile_one (f : WeilTestFn) :
    atomPairRe (EF.weilTest f.1 f.1) ≤ weilContinuumLogProfile f.1 1 := by
  rw [weilContinuumLogProfile_one_eq_two_mul_integral_norm_sq]
  exact atomPairRe_weilTest_le_two_mul_integral_norm_sq f

/-- **Upgraded Coercivity of `lebesgueAtomWeilFunctional` with Origin Boundary Surplus**:
for every `f : WeilTestFn` and every weight `c ≥ 1`, adding `2 * c * ∫ ‖f.1‖² - atomPairRe k_f` to
`(lebesgueAtomWeilFunctional k_f).re` upgrades the coercivity constant from `1 / 100` to
`1 / 100 + 2 * (c - 1)` with no `- atomPairRe` term remaining:
`(1 / 100 + 2 * (c - 1)) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 ≤ (lebesgueAtomWeilFunctional k_f).re + 2 * c * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - atomPairRe k_f`. -/
theorem upgraded_l2_le_re_lebesgueAtomWeilFunctional_add_origin_sub_atomPairRe
    (f : WeilTestFn) {c : ℝ} (_hc : 1 ≤ c) :
    (1 / 100 + 2 * (c - 1)) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re +
        2 * c * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        atomPairRe (EF.weilTest f.1 f.1) := by
  have hcoerc := lebesgueAtomWeilFunctional_coercive f.2.1 f.2.2
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq f
  linarith

/-! ## Section 2: Telescoping `α`-Weighted Euler–Maclaurin Cell Quadrature and Exact Extraction of the `n = 1` Origin Boundary Term -/

/-- The **`α`-Weighted Euler–Maclaurin Unit-Cell Quadrature Defect** on `(1, N]`:
`∑_{n = 2}^N ∫_{n - 1}^n (g(x) - (α * g(n - 1) + (1 - α) * g(n))) dx`.
- At `α = 0`, this is `rightCellQuadratureDefect g N`.
- At `α = 1`, this is the pure left-endpoint cell defect `unitLeftCellDefect g N`.
- At `α = 1 / 2`, this is the true trapezoidal cell defect `trueTrapezoidalCellDefect g N`. -/
def weightedCellQuadratureDefect (α : ℝ) (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    ∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - (α * g ((n : ℝ) - 1) + (1 - α) * g (n : ℝ)))

/-- The **Unit-Cell Left-Endpoint Quadrature Defect** on `(1, N]`:
`∑_{n = 2}^N ∫_{n - 1}^n (g(x) - g(n - 1)) dx`. -/
def unitLeftCellDefect (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  weightedCellQuadratureDefect 1 g N

/-- The **True Trapezoidal Unit-Cell Quadrature Defect** on `(1, N]`:
`∑_{n = 2}^N ∫_{n - 1}^n (g(x) - (g(n - 1) + g(n)) / 2) dx`. -/
def trueTrapezoidalCellDefect (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  weightedCellQuadratureDefect (1 / 2) g N

@[simp]
theorem weightedCellQuadratureDefect_zero (g : ℝ → ℝ) (N : ℕ) :
    weightedCellQuadratureDefect 0 g N = rightCellQuadratureDefect g N := by
  unfold weightedCellQuadratureDefect rightCellQuadratureDefect
  simp

theorem unitLeftCellDefect_eq_sum_Icc (g : ℝ → ℝ) (N : ℕ) :
    unitLeftCellDefect g N =
      ∑ n ∈ Finset.Icc 2 N, ∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - g ((n : ℝ) - 1)) := by
  unfold unitLeftCellDefect weightedCellQuadratureDefect
  refine Finset.sum_congr rfl fun n _ => ?_
  exact intervalIntegral.integral_congr fun x _ => by ring

theorem trueTrapezoidalCellDefect_eq_sum_Icc (g : ℝ → ℝ) (N : ℕ) :
    trueTrapezoidalCellDefect g N =
      ∑ n ∈ Finset.Icc 2 N,
        ∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - (g ((n : ℝ) - 1) + g (n : ℝ)) / 2) := by
  unfold trueTrapezoidalCellDefect weightedCellQuadratureDefect
  refine Finset.sum_congr rfl fun n _ => ?_
  exact intervalIntegral.integral_congr fun x _ => by ring

/-- Universal telescoping sum `∑_{n = 2}^N (g(n - 1) - g(n)) = g(1) - g(N)` for `1 ≤ N`. -/
theorem sum_Icc_two_sub_succ (g : ℝ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, (g ((n : ℝ) - 1) - g (n : ℝ))) = g 1 - g (N : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => simp
  | succ k ih =>
    have hk1 : 1 ≤ 1 + k := by omega
    have h2 : 2 ≤ 1 + k + 1 := by omega
    have hsub : ((1 + k + 1 : ℕ) : ℝ) - 1 = ((1 + k : ℕ) : ℝ) := by push_cast; ring
    rw [show 1 + (k + 1) = 1 + k + 1 by omega, Finset.sum_Icc_succ_top h2, ih hk1, hsub]
    ring

/-- **Universal Telescoping Decomposition of `rightCellQuadratureDefect` into Boundary +
`weightedCellQuadratureDefect`**:
for every `g : ℝ → ℝ` continuous on `[1, ∞)`, every weight `α ∈ ℝ`, and every `1 ≤ N`,
`rightCellQuadratureDefect g N = α * (g 1 - g N) + weightedCellQuadratureDefect α g N`. -/
theorem rightCellQuadratureDefect_eq_alpha_boundary_add_weightedCellQuadratureDefect
    (α : ℝ) {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 1)) {N : ℕ} (hN : 1 ≤ N) :
    rightCellQuadratureDefect g N =
      α * (g 1 - g (N : ℝ)) + weightedCellQuadratureDefect α g N := by
  have hcell : ∀ n ∈ Finset.Icc 2 N,
      (∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - g (n : ℝ))) =
        α * (g ((n : ℝ) - 1) - g (n : ℝ)) +
          ∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - (α * g ((n : ℝ) - 1) + (1 - α) * g (n : ℝ))) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hI : IntervalIntegrable g volume ((n : ℝ) - 1) (n : ℝ) := by
      refine (hg.mono fun x hx => ?_).intervalIntegrable
      rw [uIcc_of_le (by linarith)] at hx
      rw [mem_Ici]
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      linarith [hx.1]
    rw [intervalIntegral.integral_sub hI intervalIntegrable_const,
      intervalIntegral.integral_sub hI intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_const]
    simp only [sub_sub_cancel, one_smul]
    ring
  unfold rightCellQuadratureDefect weightedCellQuadratureDefect
  rw [Finset.sum_congr rfl hcell, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_Icc_two_sub_succ g hN]

/-- **Exact Origin Boundary Extraction from `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`**:
for every `f : WeilTestFn`, weight `α ∈ ℝ`, and support cutoff `1 ≤ N` with
`EF.weilTest f.1 f.1 (±log N) = 0`, the boundary term `g(N) = 0` vanishes and `g(1) = 2 ∫ ‖f.1‖²`, so
`rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = 2 * α * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + weightedCellQuadratureDefect α (weilContinuumLogProfile f.1) N`. -/
theorem rightCellQuadratureDefect_weilContinuumLogProfile_eq_weighted
    (α : ℝ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0) :
    rightCellQuadratureDefect (weilContinuumLogProfile f.1) N =
      2 * α * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        weightedCellQuadratureDefect α (weilContinuumLogProfile f.1) N := by
  rw [rightCellQuadratureDefect_eq_alpha_boundary_add_weightedCellQuadratureDefect
    α (continuousOn_weilContinuumLogProfile f) hN1,
    weilContinuumLogProfile_one_eq_two_mul_integral_norm_sq,
    weilContinuumLogProfile_natCast_eq_logValue]
  have hlogN : logValue f.1 N = 0 := by
    simp [logValue, hN0.1, hN0.2]
  rw [hlogN, sub_zero]
  ring

/-- Special case `α = 1 / 2` (**True Trapezoidal Rule**):
`rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = (∫ u : ℝ, ‖f.1 u‖ ^ 2) + trueTrapezoidalCellDefect (weilContinuumLogProfile f.1) N`. -/
theorem rightCellQuadratureDefect_weilContinuumLogProfile_eq_trueTrapezoidal
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0) :
    rightCellQuadratureDefect (weilContinuumLogProfile f.1) N =
      (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        trueTrapezoidalCellDefect (weilContinuumLogProfile f.1) N := by
  have h := rightCellQuadratureDefect_weilContinuumLogProfile_eq_weighted (1 / 2) f hN1 hN0
  unfold trueTrapezoidalCellDefect
  linarith

/-- Special case `α = 1` (**Unit-Cell Left-Endpoint Rule**):
`rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = 2 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + unitLeftCellDefect (weilContinuumLogProfile f.1) N`. -/
theorem rightCellQuadratureDefect_weilContinuumLogProfile_eq_unitLeft
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0) :
    rightCellQuadratureDefect (weilContinuumLogProfile f.1) N =
      2 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        unitLeftCellDefect (weilContinuumLogProfile f.1) N := by
  have h := rightCellQuadratureDefect_weilContinuumLogProfile_eq_weighted 1 f hN1 hN0
  unfold unitLeftCellDefect
  linarith

/-! ## Section 3: Complete Elimination of `atomPairRe` and Upgraded Coercivity on the Full Cone, Primitive Hyperplane, and Odd Sector -/

/-- **Full-Cone Elimination of `atomPairRe` via Unit-Cell Left-Endpoint Quadrature (`α = 1, θ = 1`)**:
for every `f : WeilTestFn`, Cesàro order `m : ℕ`, fluctuation sequence `δ : ℕ → ℝ`, and cutoff
`1 ≤ N` with `EF.weilTest f.1 f.1 (±log x) = 0` for `x ≥ N`, the `n = 1` origin boundary term
`+2 ∫ ‖f.1‖²` completely absorbs `- atomPairRe k_f`, giving an `atomPairRe`-free coercive lower
bound on the **full Weil cone**:
`(1 / 100) * ∫ ‖f.1‖² + unitLeftCellDefect (weilContinuumLogProfile f.1) N - ∑ n ∈ Finset.Icc 2 N, countertermIteratedPrefixSum m δ n * iteratedForwardDiff m (logValue f.1) n ≤ (weilFullFunctional (unitStepCountertermWeight + δ) k_f).re`. -/
theorem one_hundredth_l2_add_unitLeftCellDefect_sub_iteratedCesaro_le_re_weilFullFunctional
    (m : ℕ) (δ : ℕ → ℝ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        unitLeftCellDefect (weilContinuumLogProfile f.1) N -
        ∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m δ n * iteratedForwardDiff m (logValue f.1) n ≤
      (weilFullFunctional (unitStepCountertermWeight + δ) (EF.weilTest f.1 f.1)).re := by
  have h1 := one_hundredth_l2_add_eulerMaclaurin_sub_iteratedCesaro_le_re_weilFullFunctional
    m δ f hN1 hN
  have h2 := rightCellQuadratureDefect_weilContinuumLogProfile_eq_unitLeft f hN1 hN0
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq f
  unfold atomPairRe at hatom
  linarith

/-- **Master `(α, θ)`-Gauge Decomposition of `markovCountertermEnergy` on the Primitive Hyperplane**:
for every order `m : ℕ`, counterterm sequence `lam : ℕ → ℝ`, quadrature weight `α : ℝ`, slope `θ : ℝ`,
real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, and support cutoff `1 ≤ N`,
`markovCountertermEnergy lam F = (lebesgueAtomWeilFunctional k_F).re + (2 * α * θ * ∫ ‖F‖² - atomPairRe k_F) + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 + θ * weightedCellQuadratureDefect α (weilContinuumLogProfile F) N - ∑ n ∈ Finset.Icc 2 N, countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n * iteratedForwardDiff m (logValue F) n`. -/
theorem markovCountertermEnergy_ofReal_eq_alpha_theta_gauge_sub_iteratedCesaro_of_cosh_zero
    (m : ℕ) (lam : ℕ → ℝ) (α θ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 =
      (lebesgueAtomWeilFunctional (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1)).re +
        (2 * α * θ * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) -
          atomPairRe (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1)) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 +
        θ * weightedCellQuadratureDefect α
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        ∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
            iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n := by
  have h1 := markovCountertermEnergy_ofReal_eq_theta_slope_sub_iteratedCesaro_of_cosh_zero
    m lam θ hf hfc hcosh hN1 hN
  have h2 := rightCellQuadratureDefect_weilContinuumLogProfile_eq_weighted
    α (realWeilTestFn f hf hfc) hN1 hN0
  have h2θ := congrArg (fun x => θ * x) h2
  linarith

/-- **`atomPairRe`-Free Upgraded Coercive Lower Bound on the Primitive Hyperplane (`1 ≤ α * θ`)**:
whenever `1 ≤ α * θ`, the `n = 1` origin boundary term `2 * α * θ * ∫ ‖F‖²` absorbs `atomPairRe k_F`
with surplus `2 * (α * θ - 1) * ∫ ‖F‖² ≥ 0`, upgrading the `L²` coercivity constant to
`1 / 100 + 2 * (α * θ - 1)` with no `- atomPairRe` term remaining:
`(1 / 100 + 2 * (α * θ - 1)) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 + θ * weightedCellQuadratureDefect α (weilContinuumLogProfile F) N - ∑ n ∈ Finset.Icc 2 N, countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n * iteratedForwardDiff m (logValue F) n ≤ markovCountertermEnergy lam F`. -/
theorem upgraded_l2_add_alpha_theta_gauge_sub_iteratedCesaro_le_markovCountertermEnergy_of_cosh_zero
    (m : ℕ) (lam : ℕ → ℝ) {α θ : ℝ} (hαθ : 1 ≤ α * θ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    (1 / 100 + 2 * (α * θ - 1)) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 +
        θ * weightedCellQuadratureDefect α
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        ∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
            iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n ≤
      markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have heq := markovCountertermEnergy_ofReal_eq_alpha_theta_gauge_sub_iteratedCesaro_of_cosh_zero
    m lam α θ hf hfc hcosh hN1 hN0 hN
  have hup := upgraded_l2_le_re_lebesgueAtomWeilFunctional_add_origin_sub_atomPairRe
    (realWeilTestFn f hf hfc) hαθ
  linarith

/-- **True Trapezoidal (`α = 1 / 2, θ ≥ 2`) `atomPairRe`-Free Coercive Lower Bound on the Primitive
Hyperplane**:
for every slope `θ ≥ 2`, the true trapezoidal `n = 1` boundary term `+θ ∫ ‖F‖²` absorbs
`atomPairRe k_F` with surplus `(θ - 2) ∫ ‖F‖² ≥ 0`, giving:
`(1 / 100 + θ - 2) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 + θ * trueTrapezoidalCellDefect (weilContinuumLogProfile F) N - ∑ n ∈ Finset.Icc 2 N, countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n * iteratedForwardDiff m (logValue F) n ≤ markovCountertermEnergy lam F`. -/
theorem trueTrapezoidal_upgraded_l2_sub_iteratedCesaro_le_markovCountertermEnergy_of_cosh_zero
    (m : ℕ) (lam : ℕ → ℝ) {θ : ℝ} (hθ : 2 ≤ θ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    (1 / 100 + θ - 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 +
        θ * trueTrapezoidalCellDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        ∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
            iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n ≤
      markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have h :=
    upgraded_l2_add_alpha_theta_gauge_sub_iteratedCesaro_le_markovCountertermEnergy_of_cosh_zero
      m lam (α := 1 / 2) (θ := θ) (by linarith) hf hfc hcosh hN1 hN0 hN
  unfold trueTrapezoidalCellDefect
  linarith

/-- **Unconditional `atomPairRe`-Free and Discrete-Prime-Free True Trapezoidal Lower Bound for
`markovEnergy` on the Primitive Hyperplane (`2 ≤ θ` and `Real.log N ≤ θ`)**:
when `2 ≤ θ`, `Real.log N ≤ θ`, and `0 ≤ iteratedForwardDiff m (logValue F) n` on `Finset.Icc 2 N`,
BOTH `- atomPairRe k_F` AND the discrete prime sum are completely eliminated:
`(1 / 100 + θ - 2) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 + θ * trueTrapezoidalCellDefect (weilContinuumLogProfile F) N ≤ markovEnergy F`. -/
theorem trueTrapezoidal_upgraded_l2_le_markovEnergy_of_cosh_zero
    (m : ℕ) {θ : ℝ} (hθ2 : 2 ≤ θ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N) (hθlog : Real.log N ≤ θ)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) :
    (1 / 100 + θ - 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 +
        θ * trueTrapezoidalCellDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
      markovEnergy (realWeilTestFn f hf hfc).1 := by
  rw [← markovCountertermEnergy_vonMangoldt_eq_markovEnergy]
  have hbase :=
    trueTrapezoidal_upgraded_l2_sub_iteratedCesaro_le_markovCountertermEnergy_of_cosh_zero
      m (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) hθ2 hf hfc hcosh hN1 hN0 hN
  have hsum_nonpos :
      (∑ n ∈ Finset.Icc 2 N,
        countertermIteratedPrefixSum m (vonMangoldtSlopeDefect θ) n *
          iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) ≤ 0 :=
    Finset.sum_nonpos fun n hn =>
      mul_nonpos_of_nonpos_of_nonneg
        (countertermIteratedPrefixSum_vonMangoldtSlopeDefect_nonpos_of_log_le m hθlog hn)
        (hdiff n hn)
  unfold vonMangoldtSlopeDefect at hsum_nonpos
  linarith

/-- **Unconditional `atomPairRe`-Free and Discrete-Prime-Free True Trapezoidal Lower Bound for
`markovEnergy` on the Odd Sector (`2 ≤ θ` and `Real.log N ≤ θ`)**:
for any odd real test `f ∈ C²_c(ℝ)`, cutoff `1 ≤ N`, Cesàro order `m : ℕ` with
`0 ≤ iteratedForwardDiff m (logValue F) n` on `Finset.Icc 2 N`, and slope `θ ≥ max(2, log N)`,
`(1 / 100 + θ - 2) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 + θ * trueTrapezoidalCellDefect (weilContinuumLogProfile F) N ≤ markovEnergy F`. -/
theorem trueTrapezoidal_upgraded_l2_le_markovEnergy_of_odd
    (m : ℕ) {θ : ℝ} (hθ2 : 2 ≤ θ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) {N : ℕ} (hN1 : 1 ≤ N) (hθlog : Real.log N ≤ θ)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) :
    (1 / 100 + θ - 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 +
        θ * trueTrapezoidalCellDefect
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
      markovEnergy (realWeilTestFn f hf hfc).1 :=
  trueTrapezoidal_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ2 hf hfc (coshHalfMoment_eq_zero_of_odd hodd) hN1 hθlog hN0 hN hdiff

/-- **`atomPairRe`-Free `(α, θ)`-Gauge Sufficiency for `0 ≤ markovCountertermEnergy` on the
Primitive Hyperplane**:
if `1 ≤ α * θ` and the `m`-th Cesàro sum minus `θ * weightedCellQuadratureDefect α` is bounded by
the upgraded triple-coercive budget
`(1 / 100 + 2 * (α * θ - 1)) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2`,
then `0 ≤ markovCountertermEnergy lam F`. -/
theorem markovCountertermEnergy_nonneg_of_alpha_theta_gauge_le_upgraded_coercive_of_cosh_zero
    (m : ℕ) (lam : ℕ → ℝ) {α θ : ℝ} (hαθ : 1 ≤ α * θ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdom : (∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
            iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) -
        θ * weightedCellQuadratureDefect α
          (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
      (1 / 100 + 2 * (α * θ - 1)) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
          (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2) :
    0 ≤ markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have h :=
    upgraded_l2_add_alpha_theta_gauge_sub_iteratedCesaro_le_markovCountertermEnergy_of_cosh_zero
      m lam hαθ hf hfc hcosh hN1 hN0 hN
  linarith

/-- **Unconditional `RiemannHypothesis` from `atomPairRe`-Free `(α, θ)`-Gauge Domination on the Odd
Sector**:
if for every odd real test `f ∈ C²_c(ℝ)` there exist a counterterm `lam : ℕ → ℝ` dominating `Λ` on
`f`, a cutoff `1 ≤ N`, a Cesàro order `m : ℕ`, and gauge parameters `α, θ : ℝ` with `1 ≤ α * θ`
satisfying the `atomPairRe`-free upgraded coercive budget, then `RiemannHypothesis` holds
unconditionally. -/
theorem riemannHypothesis_of_forall_odd_exists_alpha_theta_gauge_dom
    (h : ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = -f x) →
      ∃ (lam : ℕ → ℝ) (N : ℕ) (m : ℕ) (α θ : ℝ), 1 ≤ N ∧ 1 ≤ α * θ ∧
        (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
          EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0) ∧
        (∀ x : ℝ, (N : ℝ) < x →
          EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
            EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1
              (-Real.log x) = 0) ∧
        (∑ n ∈ Finset.Icc 2 N,
            countertermIteratedPrefixSum m (shiftedDefectWeight lam θ) n *
              iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) -
          θ * weightedCellQuadratureDefect α
            (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N ≤
        (1 / 100 + 2 * (α * θ - 1)) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          (θ - 1) * bochnerResolventEnergy (EF.weilTest (realWeilTestFn f hf hfc).1
            (realWeilTestFn f hf hfc).1) +
          2 * θ * sinhHalfMoment f ^ 2 ∧
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (realWeilTestFn f hf hfc) ≤
          primeBlindCounterterm lam (realWeilTestFn f hf hfc)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_odd_exists_counterterm_markov_nonneg fun f hf hfc hodd => ?_
  obtain ⟨lam, N, m, α, θ, hN1, hαθ, hN0, hN, hdom, hle⟩ := h f hf hfc hodd
  exact ⟨lam,
    markovCountertermEnergy_nonneg_of_alpha_theta_gauge_le_upgraded_coercive_of_cosh_zero
      m lam hαθ hf hfc (coshHalfMoment_eq_zero_of_odd hodd) hN1 hN0 hN hdom,
    hle⟩

end RHTower

end
