import GaloisForLFunctions.RHTower.AllIntegerPoissonCountertermAndBochnerPBAPBridge
import GaloisForLFunctions.RHTower.WeilMarkovPrimitiveHyperplane

/-!
# Euler–Maclaurin Counterterm Cell Quadrature, One-Sided PBAP Monotonicity, and the Markov Odd / Primitive-Hyperplane Bridge

Building on `AllIntegerPoissonCountertermAndBochnerPBAPBridge`, `WeilMarkovOddPositivity`, and
`WeilMarkovPrimitiveHyperplane`, this module develops the continuous-to-discrete Euler–Maclaurin
cell-quadrature bridge for the unit-step Poisson comb, connects all-integer counterterm families to
the one-sided Weil cones (`PositiveOnNonposCone` and `PositiveOnNonnegCone`), and integrates the
pole-free archimedean-minus-prime form (`markovEnergy`) on odd tests and the primitive hyperplane:

1. **Section 1 (The Continuous Log-Profile `weilContinuumLogProfile`, Real-Space Exponential
   Evaluation of `lebesguePart`, and Continuous-Cutoff Vanishing):**
   - We define `weilContinuumLogProfile f x = (primeIntegrand (EF.weilTest f f) x).re` and prove
     that it interpolates the discrete sequence `logValue f n` at every natural number
     (`weilContinuumLogProfile_natCast_eq_logValue`).
   - We prove that for any continuous compactly supported `k : ℝ → ℂ`, the continuum pole integral
     `∫ x, primeIntegrand k x ∂lebesguePart` equals the real-space exponential pairing
     `∫ u : ℝ, (Real.exp (|u| / 2) : ℂ) * k u` (`integral_primeIntegrand_lebesguePart_eq_exp_abs`,
     `re_integral_primeIntegrand_lebesguePart_eq_exp_abs`), while the pole-minus-continuum residual
     equals `∫ u : ℝ, Real.exp (-|u| / 2) * (k u).re` (`re_paperFT_pole_sub_lebesguePart_eq_exp_neg_abs`).
   - We establish continuous-cutoff vanishing (`exists_weilTest_real_log_eq_zero`) and continuity on
     `Ici 1` (`continuousOn_primeIntegrand`, `continuousOn_weilContinuumLogProfile`).

2. **Section 2 (Finite-Cutoff Interval Reduction on `(1, N]` and Exact Euler–Maclaurin Unit-Cell
   Quadrature Identities for `unitStepCountertermWeight`):**
   - For any cutoff `R ≥ 1` beyond which `k(±log x) = 0`, we reduce the `lebesguePart` integral to
     the finite interval integral `∫ x in (1 : ℝ)..R, primeIntegrand k x`
     (`integral_primeIntegrand_lebesguePart_eq_intervalIntegral`,
     `re_integral_primeIntegrand_lebesguePart_eq_intervalIntegral`).
   - Splitting `(1, N]` and `(1, N + 1]` into unit cells `[n - 1, n]` and `[n, n + 1]` for
     `n ∈ Finset.Icc 2 N` and pairing each cell against the node `weilContinuumLogProfile f.1 n = logValue f.1 n`
     of `primeBlindCounterterm unitStepCountertermWeight f`, we prove the exact right-endpoint,
     left-endpoint, and trapezoidal Euler–Maclaurin cell-quadrature identities
     (`re_integral_lebesguePart_sub_unitStep_eq_rightCellQuadratureDefect`,
     `re_integral_lebesguePart_sub_unitStep_eq_leftCellQuadratureDefect`,
     `re_integral_lebesguePart_sub_unitStep_eq_trapezoidalCellQuadratureDefect`).

3. **Section 3 (Master Coercive Euler–Maclaurin + `m`-th Cesàro Decomposition for Counterterm-Completed
   Signed Tests):**
   - Combining Section 2 with the coercive `lebesgueAtomWeilFunctional` transfer identity and the
     boundary-free `m`-th order Cesàro summation-by-parts identity from
     `AllIntegerPoissonCountertermAndBochnerPBAPBridge`, we prove the exact decomposition and
     `(1 / 100) ∫ ‖f‖²` coercive lower bound for `(weilFullFunctional (unitStepCountertermWeight + δ)).re`
     and for the canonical Weil functional `(weilFullFunctional Λ).re` at every Cesàro order `m : ℕ`.

4. **Section 4 (One-Sided Cone Counterterm Monotonicity, Minorant/Majorant Comparison, and
   Mixture-Dependent One-Sided PBAP Bridges):**
   - We prove that on the nonpositive cone (`∀ n ≥ 2, c.sum (fun f t => t * logValue f.1 n) ≤ 0`),
     `(weilFullFunctional lam).re` is **monotone increasing** in `lam` (`sum_re_weilFullFunctional_le_of_nonposCone`,
     `positiveOnNonposCone_of_le`), whereas on the nonnegative cone it is **monotone decreasing** in
     `lam` (`sum_re_weilFullFunctional_le_of_nonnegCone`, `positiveOnNonnegCone_of_ge`).
   - We deduce mixture-dependent minorant/majorant sufficiency criteria for `PositiveOnNonposCone U`,
     `PositiveOnNonnegCone L`, and `RiemannHypothesis` (`riemannHypothesis_of_forall_exists_minorant_nonneg_on_nonposCone`,
     `riemannHypothesis_of_forall_exists_majorant_nonneg_on_nonnegCone`).

5. **Section 5 (The Markov Archimedean-Minus-Prime Form, Rank-2 `(1, 1)` Pole Signature
   `2 C(f)² - 2 S(f)²`, and Counterterm / Euler–Maclaurin Bridges on Odd Tests and the Primitive
   Hyperplane):**
   - We define `markovArchRe` and `markovCountertermEnergy lam f`, proving that in real space the
     `2 cosh((u-v)/2)` pole kernel cancels identically out of `weilArchRe`, leaving the pure Lévy
     jump form `A(0) ∫ f² + (jumpEnergy f).toReal - primeBlindCounterterm lam`
     (`markovCountertermEnergy_real_eq_levy_sub_counterterm`, `markovEnergy_real_eq_levy_sub_counterterm`).
   - We prove the exact rank-2 `(1, 1)` signature decomposition of `weilPoleTerm` on real tests:
     `(weilPoleTerm (EF.weilTest F F)).re = 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2`
     (`re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq`).
   - On the **primitive hyperplane** `coshHalfMoment f = 0` (`∫ f(x) cosh(x/2) dx = 0`) and on all
     **odd tests** (`f(-x) = -f(x)`), the positive square `2 C(f)²` vanishes and `markovCountertermEnergy lam`
     gains the nonnegative bonus square `+2 S(f)² = 2 (∫ f(x) sinh(x/2) dx)² ≥ 0` over
     `(weilFullFunctional lam).re`, yielding strengthened coercive Euler–Maclaurin + `m`-th Cesàro +
     sinh-moment lower bounds and direct counterterm criteria for `RiemannHypothesis` via
     `riemannHypothesis_iff_forall_odd_markovEnergy_nonneg` and
     `riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg`.
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

/-! ## Section 1: The Continuous Log-Profile `weilContinuumLogProfile`, Real-Space Exponential Evaluation of `lebesguePart`, and Continuous-Cutoff Vanishing -/

/-- The continuous multiplicative log-profile `(primeIntegrand (EF.weilTest f f) x).re`, which
interpolates `logValue f n` at every integer `n : ℕ`. -/
def weilContinuumLogProfile (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (primeIntegrand (EF.weilTest f f) x).re

/-- Explicit formula for `weilContinuumLogProfile`:
`weilContinuumLogProfile f x = (EF.weilTest f f (Real.log x) + EF.weilTest f f (-Real.log x)).re / Real.sqrt x`. -/
theorem weilContinuumLogProfile_eq (f : ℝ → ℂ) (x : ℝ) :
    weilContinuumLogProfile f x =
      (EF.weilTest f f (Real.log x) + EF.weilTest f f (-Real.log x)).re / Real.sqrt x := by
  unfold weilContinuumLogProfile primeIntegrand
  rw [Complex.re_ofReal_mul, div_eq_inv_mul]

/-- **Exact Integer Interpolation**: at every natural number `n : ℕ`, `weilContinuumLogProfile f n`
equals the discrete Weil coefficient `logValue f n`. -/
@[simp]
theorem weilContinuumLogProfile_natCast_eq_logValue (f : ℝ → ℂ) (n : ℕ) :
    weilContinuumLogProfile f (n : ℝ) = logValue f n := by
  rw [weilContinuumLogProfile_eq, logValue]

/-- If `k (Real.log x) = 0` and `k (-Real.log x) = 0`, then `primeIntegrand k x = 0`. -/
theorem primeIntegrand_eq_zero_of_log_eq_zero {k : ℝ → ℂ} {x : ℝ}
    (hx : k (Real.log x) = 0 ∧ k (-Real.log x) = 0) :
    primeIntegrand k x = 0 := by
  rw [primeIntegrand, hx.1, hx.2, add_zero, mul_zero]

/-- If `EF.weilTest f f (Real.log x) = 0` and `EF.weilTest f f (-Real.log x) = 0`, then
`weilContinuumLogProfile f x = 0`. -/
theorem weilContinuumLogProfile_eq_zero_of_log_eq_zero {f : ℝ → ℂ} {x : ℝ}
    (hx : EF.weilTest f f (Real.log x) = 0 ∧ EF.weilTest f f (-Real.log x) = 0) :
    weilContinuumLogProfile f x = 0 := by
  rw [weilContinuumLogProfile, primeIntegrand_eq_zero_of_log_eq_zero hx, Complex.zero_re]

/-- For every `f : WeilTestFn`, there exists an integer cutoff `N ≥ 2` such that for all real
`x > N`, `EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0`. -/
theorem exists_weilTest_real_log_eq_zero (f : WeilTestFn) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0 := by
  obtain ⟨A, hA⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
  have hf : ∀ u, f.1 u ≠ 0 → |u| ≤ A := fun u hu => by
    have := hA (subset_tsupport _ hu)
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  have hk := weilTest_support_abs_le hf hf
  refine ⟨max 2 ⌈Real.exp (A + A)⌉₊, le_max_left 2 _, fun x hx => ?_⟩
  have hx' : (⌈Real.exp (A + A)⌉₊ : ℝ) < x :=
    lt_of_le_of_lt (Nat.cast_le.mpr (le_max_right 2 _)) hx
  have hexp : Real.exp (A + A) < x := (Nat.le_ceil (Real.exp (A + A))).trans_lt hx'
  have hpos : 0 < x := (Real.exp_pos _).trans hexp
  have hlog : A + A < Real.log x := (Real.lt_log_iff_exp_lt hpos).mpr hexp
  constructor
  · by_contra h
    linarith [hk _ h, le_abs_self (Real.log x)]
  · by_contra h
    have := hk _ h
    rw [abs_neg] at this
    linarith [le_abs_self (Real.log x)]

/-- If `k : ℝ → ℂ` is continuous, then `primeIntegrand k` is continuous on `Ici 1`. -/
theorem continuousOn_primeIntegrand {k : ℝ → ℂ} (hk : Continuous k) :
    ContinuousOn (primeIntegrand k) (Ici 1) := by
  unfold primeIntegrand
  have hlog : ContinuousOn Real.log (Ici 1) :=
    Real.continuousOn_log.mono fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
  have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Ici 1) :=
    (Real.continuous_sqrt.continuousOn).inv₀ fun x hx =>
      ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hx))
  exact (Complex.continuous_ofReal.comp_continuousOn hinv).mul
    ((hk.comp_continuousOn hlog).add (hk.comp_continuousOn hlog.neg))

/-- For any `f : WeilTestFn`, `weilContinuumLogProfile f.1` is continuous on `Ici 1`. -/
theorem continuousOn_weilContinuumLogProfile (f : WeilTestFn) :
    ContinuousOn (weilContinuumLogProfile f.1) (Ici 1) := by
  unfold weilContinuumLogProfile
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  exact Complex.continuous_re.comp_continuousOn (continuousOn_primeIntegrand hkd.continuous)

/-- **Real-Space Exponential Evaluation of the Continuum `lebesguePart` Integral**:
for any continuous compactly supported `k : ℝ → ℂ`,
`∫ x, primeIntegrand k x ∂lebesguePart = ∫ u : ℝ, (Real.exp (|u| / 2) : ℂ) * k u`. -/
theorem integral_primeIntegrand_lebesguePart_eq_exp_abs {k : ℝ → ℂ} (hk : Continuous k)
    (hkc : HasCompactSupport k) :
    ∫ x, primeIntegrand k x ∂lebesguePart =
      ∫ u : ℝ, (Real.exp (|u| / 2) : ℂ) * k u := by
  set F : ℝ → ℂ := fun u => (Real.exp (|u| / 2) : ℂ) * k u with hF
  have hFi : Integrable F :=
    ((by fun_prop : Continuous fun u : ℝ => (Real.exp (|u| / 2) : ℂ)).mul
      hk).integrable_of_hasCompactSupport hkc.mul_left
  rw [integral_lebesguePart]
  have hsplit : ∫ u in Ioi (0 : ℝ), (Real.exp (u / 2) : ℂ) * (k u + k (-u)) =
      (∫ u in Ioi (0 : ℝ), F u) + ∫ u in Ioi (0 : ℝ), F (-u) := by
    rw [← integral_add hFi.integrableOn hFi.comp_neg.integrableOn]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : 0 < u := hu
    simp only [hF, abs_neg, abs_of_pos hu']
    ring
  rw [hsplit, integral_comp_neg_Ioi, neg_zero, add_comm,
    ← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hFi.integrableOn
      hFi.integrableOn, Iic_union_Ioi, setIntegral_univ]

/-- Real part of `integral_primeIntegrand_lebesguePart_eq_exp_abs`:
for any continuous compactly supported `k : ℝ → ℂ`,
`(∫ x, primeIntegrand k x ∂lebesguePart).re = ∫ u : ℝ, Real.exp (|u| / 2) * (k u).re`. -/
theorem re_integral_primeIntegrand_lebesguePart_eq_exp_abs {k : ℝ → ℂ} (hk : Continuous k)
    (hkc : HasCompactSupport k) :
    (∫ x, primeIntegrand k x ∂lebesguePart).re =
      ∫ u : ℝ, Real.exp (|u| / 2) * (k u).re := by
  rw [integral_primeIntegrand_lebesguePart_eq_exp_abs hk hkc]
  have hFi : Integrable fun u : ℝ => (Real.exp (|u| / 2) : ℂ) * k u :=
    ((by fun_prop : Continuous fun u : ℝ => (Real.exp (|u| / 2) : ℂ)).mul
      hk).integrable_of_hasCompactSupport hkc.mul_left
  have hre := integral_re hFi
  change ∫ u : ℝ, ((Real.exp (|u| / 2) : ℂ) * k u).re =
    (∫ u : ℝ, (Real.exp (|u| / 2) : ℂ) * k u).re at hre
  rw [← hre]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  exact Complex.re_ofReal_mul (Real.exp (|u| / 2)) (k u)

/-- Real part of `pole_sub_lebesgue_eq`:
for any continuous compactly supported `k : ℝ → ℂ`,
`(paperFT k (I / 2) + paperFT k (-I / 2) - ∫ x, primeIntegrand k x ∂lebesguePart).re = ∫ u : ℝ, Real.exp (-|u| / 2) * (k u).re`. -/
theorem re_paperFT_pole_sub_lebesguePart_eq_exp_neg_abs {k : ℝ → ℂ} (hk : Continuous k)
    (hkc : HasCompactSupport k) :
    (paperFT k (I / 2) + paperFT k (-I / 2) - ∫ x, primeIntegrand k x ∂lebesguePart).re =
      ∫ u : ℝ, Real.exp (-|u| / 2) * (k u).re := by
  rw [pole_sub_lebesgue_eq hk hkc]
  have hFi : Integrable fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) * k u :=
    ((by fun_prop : Continuous fun u : ℝ => (Real.exp (-|u| / 2) : ℂ)).mul
      hk).integrable_of_hasCompactSupport hkc.mul_left
  have hre := integral_re hFi
  change ∫ u : ℝ, ((Real.exp (-|u| / 2) : ℂ) * k u).re =
    (∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * k u).re at hre
  rw [← hre]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  exact Complex.re_ofReal_mul (Real.exp (-|u| / 2)) (k u)

/-! ## Section 2: Finite-Cutoff Interval Reduction on `(1, N]` and Exact Euler–Maclaurin Unit-Cell Quadrature Identities -/

/-- **Finite-Cutoff Interval Integral Reduction for `lebesguePart`**:
if `1 ≤ R` and `k (Real.log x) = 0 ∧ k (-Real.log x) = 0` for all `x > R`, then the integral of
`primeIntegrand k` over `lebesguePart = volume.restrict (Ioi 1)` equals the finite interval
integral `∫ x in (1 : ℝ)..R, primeIntegrand k x`. -/
theorem integral_primeIntegrand_lebesguePart_eq_intervalIntegral {k : ℝ → ℂ} {R : ℝ}
    (hR1 : 1 ≤ R)
    (hR : ∀ x : ℝ, R < x → k (Real.log x) = 0 ∧ k (-Real.log x) = 0) :
    ∫ x, primeIntegrand k x ∂lebesguePart = ∫ x in (1 : ℝ)..R, primeIntegrand k x := by
  rw [lebesguePart, intervalIntegral.integral_of_le hR1]
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    Ioc_subset_Ioi_self (Eventually.of_forall fun x hx => ?_)
  have hxR : R < x := by
    rcases hx with ⟨hx1, hx2⟩
    by_contra hle
    exact hx2 ⟨hx1, not_lt.mp hle⟩
  exact primeIntegrand_eq_zero_of_log_eq_zero (hR x hxR)

/-- **Real-Part Finite-Cutoff Interval Integral Reduction for `lebesguePart`**:
for any `f : WeilTestFn` and `1 ≤ R` such that `EF.weilTest f.1 f.1` vanishes at `±log x` for all
`x > R`, `(∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart).re` equals the real interval
integral `∫ x in (1 : ℝ)..R, weilContinuumLogProfile f.1 x`. -/
theorem re_integral_primeIntegrand_lebesguePart_eq_intervalIntegral (f : WeilTestFn) {R : ℝ}
    (hR1 : 1 ≤ R)
    (hR : ∀ x : ℝ, R < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart).re =
      ∫ x in (1 : ℝ)..R, weilContinuumLogProfile f.1 x := by
  rw [integral_primeIntegrand_lebesguePart_eq_intervalIntegral hR1 hR,
    intervalIntegral.integral_of_le hR1, intervalIntegral.integral_of_le hR1]
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hcont : ContinuousOn (primeIntegrand (EF.weilTest f.1 f.1)) (Icc 1 R) :=
    (continuousOn_primeIntegrand hkd.continuous).mono fun x hx => hx.1
  have hint : IntegrableOn (primeIntegrand (EF.weilTest f.1 f.1)) (Ioc 1 R) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  exact (integral_re hint).symm

/-- Adjacent unit-cell decomposition of `∫ x in (1 : ℝ)..(N : ℝ), g x` into the sum over
`n ∈ Finset.Icc 2 N` of `∫ x in ((n : ℝ) - 1)..(n : ℝ), g x`. -/
theorem intervalIntegral_one_natCast_eq_sum_Icc {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 1))
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..(N : ℝ), g x) =
      ∑ n ∈ Finset.Icc 2 N, ∫ x in ((n : ℝ) - 1)..(n : ℝ), g x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => simp
  | succ k ih =>
    have hk1 : 1 ≤ 1 + k := by omega
    have h2 : 2 ≤ 1 + k + 1 := by omega
    have hI1 : IntervalIntegrable g volume (1 : ℝ) ((1 + k : ℕ) : ℝ) := by
      refine (hg.mono fun x hx => ?_).intervalIntegrable
      rw [uIcc_of_le (by exact_mod_cast hk1)] at hx
      exact hx.1
    have hI2 : IntervalIntegrable g volume ((1 + k : ℕ) : ℝ) ((1 + k + 1 : ℕ) : ℝ) := by
      refine (hg.mono fun x hx => ?_).intervalIntegrable
      rw [uIcc_of_le (by exact_mod_cast Nat.le_succ (1 + k))] at hx
      exact le_trans (by exact_mod_cast hk1) hx.1
    rw [show 1 + (k + 1) = 1 + k + 1 by omega, Finset.sum_Icc_succ_top h2, ← ih hk1,
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    congr 2
    push_cast
    ring

/-- Adjacent unit-cell decomposition of `∫ x in (1 : ℝ)..((N : ℝ) + 1), g x` into the initial cell
`∫_1^2 g` plus the sum over `n ∈ Finset.Icc 2 N` of `∫ x in (n : ℝ)..((n : ℝ) + 1), g x`. -/
theorem intervalIntegral_one_natCast_succ_eq_sum_Icc {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 1))
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..((N : ℝ) + 1), g x) =
      (∫ x in (1 : ℝ)..(2 : ℝ), g x) +
        ∑ n ∈ Finset.Icc 2 N, ∫ x in (n : ℝ)..((n : ℝ) + 1), g x := by
  have hN1 : 1 ≤ N + 1 := by omega
  have h1 := intervalIntegral_one_natCast_eq_sum_Icc hg hN1
  rw [Nat.cast_add, Nat.cast_one] at h1
  rw [h1]
  have hbij : (∑ n ∈ Finset.Icc 2 (N + 1), ∫ x in ((n : ℝ) - 1)..(n : ℝ), g x) =
      ∑ m ∈ Finset.Icc 1 N, ∫ x in (m : ℝ)..((m : ℝ) + 1), g x := by
    refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro a ha b hb hab
      rw [Finset.mem_Icc] at ha hb
      omega
    · intro m hm
      rw [Finset.mem_Icc] at hm
      refine ⟨m + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : 1 ≤ n := by omega
      rw [Nat.cast_sub hn1, Nat.cast_one, sub_add_cancel]
  rw [hbij, ← Finset.insert_Icc_succ_left_eq_Icc hN,
    Finset.sum_insert (by simp)]
  norm_num

/-- Explicit finite-cutoff formula for the unit-step Poisson comb counterterm:
`primeBlindCounterterm unitStepCountertermWeight f = ∑ n ∈ Finset.Icc 2 N, logValue f.1 n`. -/
theorem primeBlindCounterterm_unitStep_eq_sum_Icc (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm unitStepCountertermWeight f =
      ∑ n ∈ Finset.Icc 2 N, logValue f.1 n := by
  rw [primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight f hN]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  simp [unitStepCountertermWeight, hn.1]

/-- The **Right-Endpoint Euler–Maclaurin Cell Quadrature Defect** on `(1, N]`:
`∑_{n = 2}^N ∫_{n - 1}^n (g(x) - g(n)) dx`. -/
def rightCellQuadratureDefect (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, ∫ x in ((n : ℝ) - 1)..(n : ℝ), (g x - g (n : ℝ))

/-- The **Left-Endpoint Euler–Maclaurin Cell Quadrature Defect** on `(1, N + 1]`:
`∫_1^2 g(x) dx + ∑_{n = 2}^N ∫_n^{n + 1} (g(x) - g(n)) dx`. -/
def leftCellQuadratureDefect (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∫ x in (1 : ℝ)..(2 : ℝ), g x) +
    ∑ n ∈ Finset.Icc 2 N, ∫ x in (n : ℝ)..((n : ℝ) + 1), (g x - g (n : ℝ))

/-- The **Trapezoidal Euler–Maclaurin Cell Quadrature Defect**:
the symmetric average `(1 / 2) * (rightCellQuadratureDefect g N + leftCellQuadratureDefect g N)`. -/
def trapezoidalCellQuadratureDefect (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  (1 / 2) * (rightCellQuadratureDefect g N + leftCellQuadratureDefect g N)

/-- **Universal Right-Endpoint Cell Quadrature Identity**:
for any `g : ℝ → ℝ` continuous on `Ici 1` and any `N ≥ 1`,
`(∫ x in 1..N, g x) - ∑_{n = 2}^N g(n) = rightCellQuadratureDefect g N`. -/
theorem intervalIntegral_sub_sum_eq_rightCellQuadratureDefect {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 1)) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..(N : ℝ), g x) - (∑ n ∈ Finset.Icc 2 N, g (n : ℝ)) =
      rightCellQuadratureDefect g N := by
  rw [intervalIntegral_one_natCast_eq_sum_Icc hg hN, rightCellQuadratureDefect,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hI : IntervalIntegrable g volume ((n : ℝ) - 1) (n : ℝ) := by
    refine (hg.mono fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    rw [mem_Ici]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    linarith [hx.1]
  rw [intervalIntegral.integral_sub hI intervalIntegrable_const,
    intervalIntegral.integral_const, sub_sub_cancel, one_smul]

/-- **Universal Left-Endpoint Cell Quadrature Identity**:
for any `g : ℝ → ℝ` continuous on `Ici 1` and any `N ≥ 1`,
`(∫ x in 1..(N + 1), g x) - ∑_{n = 2}^N g(n) = leftCellQuadratureDefect g N`. -/
theorem intervalIntegral_succ_sub_sum_eq_leftCellQuadratureDefect {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 1)) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..((N : ℝ) + 1), g x) - (∑ n ∈ Finset.Icc 2 N, g (n : ℝ)) =
      leftCellQuadratureDefect g N := by
  rw [intervalIntegral_one_natCast_succ_eq_sum_Icc hg hN, leftCellQuadratureDefect,
    add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hI : IntervalIntegrable g volume (n : ℝ) ((n : ℝ) + 1) := by
    refine (hg.mono fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    rw [mem_Ici]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    linarith [hx.1]
  rw [intervalIntegral.integral_sub hI intervalIntegrable_const,
    intervalIntegral.integral_const, add_sub_cancel_left, one_smul]

/-- **Exact Right-Endpoint Euler–Maclaurin Quadrature Identity for `unitStepCountertermWeight`**:
if `1 ≤ N` and `EF.weilTest f.1 f.1` vanishes at `±log x` for all `x > N`, then the continuum-minus-comb
difference `(∫ primeIntegrand k_f d(lebesguePart)).re - primeBlindCounterterm unitStepCountertermWeight f`
equals `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem re_integral_lebesguePart_sub_unitStep_eq_rightCellQuadratureDefect (f : WeilTestFn) {N : ℕ}
    (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart).re -
        primeBlindCounterterm unitStepCountertermWeight f =
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hNnat : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0 :=
    fun n hn => hN n (by exact_mod_cast hn)
  rw [re_integral_primeIntegrand_lebesguePart_eq_intervalIntegral f (by exact_mod_cast hN1) hN,
    primeBlindCounterterm_unitStep_eq_sum_Icc f hNnat]
  have hsum : (∑ n ∈ Finset.Icc 2 N, logValue f.1 n) =
      ∑ n ∈ Finset.Icc 2 N, weilContinuumLogProfile f.1 (n : ℝ) :=
    Finset.sum_congr rfl fun n _ => (weilContinuumLogProfile_natCast_eq_logValue f.1 n).symm
  rw [hsum]
  exact intervalIntegral_sub_sum_eq_rightCellQuadratureDefect
    (continuousOn_weilContinuumLogProfile f) hN1

/-- **Exact Left-Endpoint Euler–Maclaurin Quadrature Identity for `unitStepCountertermWeight`**:
if `1 ≤ N` and `EF.weilTest f.1 f.1` vanishes at `±log x` for all `x > N`, then the continuum-minus-comb
difference `(∫ primeIntegrand k_f d(lebesguePart)).re - primeBlindCounterterm unitStepCountertermWeight f`
equals `leftCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem re_integral_lebesguePart_sub_unitStep_eq_leftCellQuadratureDefect (f : WeilTestFn) {N : ℕ}
    (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart).re -
        primeBlindCounterterm unitStepCountertermWeight f =
      leftCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hNnat : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0 :=
    fun n hn => hN n (by exact_mod_cast hn)
  have hNsucc : ∀ x : ℝ, (N : ℝ) + 1 < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0 :=
    fun x hx => hN x (by linarith)
  have h1N1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  rw [re_integral_primeIntegrand_lebesguePart_eq_intervalIntegral f h1N1 hNsucc,
    primeBlindCounterterm_unitStep_eq_sum_Icc f hNnat]
  have hsum : (∑ n ∈ Finset.Icc 2 N, logValue f.1 n) =
      ∑ n ∈ Finset.Icc 2 N, weilContinuumLogProfile f.1 (n : ℝ) :=
    Finset.sum_congr rfl fun n _ => (weilContinuumLogProfile_natCast_eq_logValue f.1 n).symm
  rw [hsum]
  exact intervalIntegral_succ_sub_sum_eq_leftCellQuadratureDefect
    (continuousOn_weilContinuumLogProfile f) hN1

/-- **Exact Trapezoidal Euler–Maclaurin Quadrature Identity for `unitStepCountertermWeight`**:
if `1 ≤ N` and `EF.weilTest f.1 f.1` vanishes at `±log x` for all `x > N`, then the continuum-minus-comb
difference equals `trapezoidalCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem re_integral_lebesguePart_sub_unitStep_eq_trapezoidalCellQuadratureDefect (f : WeilTestFn)
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart).re -
        primeBlindCounterterm unitStepCountertermWeight f =
      trapezoidalCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  unfold trapezoidalCellQuadratureDefect
  rw [← re_integral_lebesguePart_sub_unitStep_eq_rightCellQuadratureDefect f hN1 hN,
    ← re_integral_lebesguePart_sub_unitStep_eq_leftCellQuadratureDefect f hN1 hN]
  ring

/-! ## Section 3: Master Coercive Euler–Maclaurin + `m`-th Cesàro Decomposition for Counterterm-Completed Signed Tests -/

/-- **Exact Euler–Maclaurin Decomposition of `(weilFullFunctional unitStepCountertermWeight).re`**:
for any `f : WeilTestFn` with cutoff `1 ≤ N`, the real part of the unit-step Poisson-comb Weil
functional equals the coercive `(lebesgueAtomWeilFunctional k_f).re` plus the unit-cell quadrature
defect `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N` minus the atom evaluation
`(k_f(1/10000) + k_f(-1/10000)).re`. -/
theorem re_weilFullFunctional_unitStep_eq_lebesgueAtom_add_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (weilFullFunctional unitStepCountertermWeight (EF.weilTest f.1 f.1)).re =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N -
        (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000))).re := by
  rw [re_weilFullFunctional_eq_re_lebesgueAtomWeilFunctional_add_sub_counterterm,
    Complex.sub_re]
  linarith [re_integral_lebesguePart_sub_unitStep_eq_rightCellQuadratureDefect f hN1 hN]

/-- **Master Euler–Maclaurin + `m`-th Order Cesàro Decomposition for `unitStepCountertermWeight + δ`**:
for every Cesàro order `m : ℕ`, every fluctuation sequence `δ : ℕ → ℝ`, and every `f : WeilTestFn`
with cutoff `1 ≤ N`, `(weilFullFunctional (unitStepCountertermWeight + δ) (EF.weilTest f.1 f.1)).re`
splits into:
1. the coercive Lebesgue–atom functional `(lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re`,
2. the unit-step Euler–Maclaurin cell quadrature defect `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`,
3. minus the atom term `(k_f(1/10000) + k_f(-1/10000)).re`,
4. minus the boundary-free `m`-th Cesàro sum of `δ` against `iteratedForwardDiff m (logValue f.1)`. -/
theorem re_weilFullFunctional_unitStep_add_fluctuation_eq_eulerMaclaurin_sub_iteratedCesaro
    (m : ℕ) (δ : ℕ → ℝ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (weilFullFunctional (unitStepCountertermWeight + δ) (EF.weilTest f.1 f.1)).re =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N -
        (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000))).re -
        ∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m δ n * iteratedForwardDiff m (logValue f.1) n := by
  have hNnat : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0 :=
    fun n hn => hN n (by exact_mod_cast hn)
  rw [re_weilFullFunctional_add_counterterm,
    re_weilFullFunctional_unitStep_eq_lebesgueAtom_add_rightCellQuadratureDefect f hN1 hN,
    primeBlindCounterterm_eq_sum_iteratedPrefix_mul_diff m δ f hNnat]

/-- **Canonical Weil Functional Euler–Maclaurin + `m`-th Order Cesàro Identity (`Λ = 1 + (Λ - 1)`)**:
specializing `δ = vonMangoldtDefectCountertermWeight` decomposes the canonical Weil functional
`(weilFullFunctional Λ (EF.weilTest f.1 f.1)).re` into the coercive `lebesgueAtomWeilFunctional`,
the unit-step Euler–Maclaurin cell quadrature defect, the atom term, and the `m`-th Cesàro sum of
`vonMangoldtDefectCountertermWeight`. -/
theorem re_weilFullFunctional_vonMangoldt_eq_eulerMaclaurin_sub_iteratedCesaro
    (m : ℕ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest f.1 f.1)).re =
      (lebesgueAtomWeilFunctional (EF.weilTest f.1 f.1)).re +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N -
        (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000))).re -
        ∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m vonMangoldtDefectCountertermWeight n *
            iteratedForwardDiff m (logValue f.1) n := by
  have heq : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
      unitStepCountertermWeight + vonMangoldtDefectCountertermWeight :=
    funext vonMangoldt_eq_unitStep_add_defect
  rw [heq]
  exact re_weilFullFunctional_unitStep_add_fluctuation_eq_eulerMaclaurin_sub_iteratedCesaro
    m vonMangoldtDefectCountertermWeight f hN1 hN

/-- **Master Coercive Euler–Maclaurin + `m`-th Cesàro Lower Bound for Counterterm-Completed Signed Tests**:
for every Cesàro order `m : ℕ`, every fluctuation sequence `δ : ℕ → ℝ`, and every signed test
`f : WeilTestFn` with cutoff `1 ≤ N`,
`(1 / 100) * ∫ ‖f‖² + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N - (k_f(1/10000) + k_f(-1/10000)).re - ∑_{n=2}^N (countertermIteratedPrefixSum m δ n) * (Δ^m (logValue f.1) n) ≤ (weilFullFunctional (unitStepCountertermWeight + δ) k_f).re`. -/
theorem one_hundredth_l2_add_eulerMaclaurin_sub_iteratedCesaro_le_re_weilFullFunctional
    (m : ℕ) (δ : ℕ → ℝ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N -
        (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000))).re -
        (∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m δ n * iteratedForwardDiff m (logValue f.1) n) ≤
      (weilFullFunctional (unitStepCountertermWeight + δ) (EF.weilTest f.1 f.1)).re := by
  have hcoerc := lebesgueAtomWeilFunctional_coercive f.2.1 f.2.2
  have hid := re_weilFullFunctional_unitStep_add_fluctuation_eq_eulerMaclaurin_sub_iteratedCesaro
    m δ f hN1 hN
  linarith

/-- **Master Coercive Euler–Maclaurin + `m`-th Cesàro Lower Bound for the Canonical Weil Functional**:
specializing `one_hundredth_l2_add_eulerMaclaurin_sub_iteratedCesaro_le_re_weilFullFunctional` to
`δ = vonMangoldtDefectCountertermWeight`. -/
theorem one_hundredth_l2_add_eulerMaclaurin_sub_iteratedCesaro_le_re_weilFullFunctional_vonMangoldt
    (m : ℕ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (1 / 100) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N -
        (EF.weilTest f.1 f.1 (1 / 10000) + EF.weilTest f.1 f.1 (-(1 / 10000))).re -
        (∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m vonMangoldtDefectCountertermWeight n *
            iteratedForwardDiff m (logValue f.1) n) ≤
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1 f.1)).re := by
  have heq : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
      unitStepCountertermWeight + vonMangoldtDefectCountertermWeight :=
    funext vonMangoldt_eq_unitStep_add_defect
  rw [heq]
  exact one_hundredth_l2_add_eulerMaclaurin_sub_iteratedCesaro_le_re_weilFullFunctional
    m vonMangoldtDefectCountertermWeight f hN1 hN

/-! ## Section 4: One-Sided Cone Counterterm Monotonicity, Minorant/Majorant Comparison, and Mixture-Dependent One-Sided PBAP Bridges -/

/-- Expansion of `c.sum (fun f t => t * primeBlindCounterterm lam f)` as the Finsupp sum over
`j : LogIndex` of `(linearCombination ℝ logVector c j) * lam j`. -/
theorem sum_primeBlindCounterterm_eq_finsuppSum (lam : ℕ → ℝ) (c : WeilTestFn →₀ ℝ) :
    (c.sum fun f t => t * primeBlindCounterterm lam f) =
      (linearCombination ℝ logVector c).sum fun j x => x * lam j := by
  rw [sum_primeBlindCounterterm_eq_linearCombination, linearCombination_apply]
  exact Finsupp.sum_congr fun j _ => by rw [smul_eq_mul]

/-- **Counterterm Monotonicity on the Nonpositive Cone**:
if a mixture `c : WeilTestFn →₀ ℝ` lies in the nonpositive cone
(`∀ n ≥ 2, (c.sum fun f t => t * logValue f.1 n) ≤ 0`) and `lam₂ n ≤ lam₁ n` for all `n ≥ 2`,
then `c.sum (fun f t => t * primeBlindCounterterm lam₁ f) ≤ c.sum (fun f t => t * primeBlindCounterterm lam₂ f)`. -/
theorem sum_primeBlindCounterterm_le_of_nonposCone {lam₁ lam₂ : ℕ → ℝ} {c : WeilTestFn →₀ ℝ}
    (hc_nonpos : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) ≤ 0)
    (hle : ∀ n : ℕ, 2 ≤ n → lam₂ n ≤ lam₁ n) :
    (c.sum fun f t => t * primeBlindCounterterm lam₁ f) ≤
      c.sum fun f t => t * primeBlindCounterterm lam₂ f := by
  rw [sum_primeBlindCounterterm_eq_finsuppSum, sum_primeBlindCounterterm_eq_finsuppSum]
  refine Finsupp.sum_le_sum fun j _ => ?_
  have hj0 : linearCombination ℝ logVector c j ≤ 0 := by
    rw [linearCombination_logVector_apply]
    exact hc_nonpos j.1 j.2
  exact mul_le_mul_of_nonpos_left (hle j.1 j.2) hj0

/-- **Weil Functional Monotonicity on the Nonpositive Cone**:
if `c` lies in the nonpositive cone (`∀ n ≥ 2, (c.sum fun f t => t * logValue f.1 n) ≤ 0`) and
`lam₁ n ≤ lam₂ n` for all `n ≥ 2`, then
`c.sum (fun f t => t * (weilFullFunctional lam₁ (EF.weilTest f.1 f.1)).re) ≤ c.sum (fun f t => t * (weilFullFunctional lam₂ (EF.weilTest f.1 f.1)).re)`. -/
theorem sum_re_weilFullFunctional_le_of_nonposCone {lam₁ lam₂ : ℕ → ℝ} {c : WeilTestFn →₀ ℝ}
    (hc_nonpos : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) ≤ 0)
    (hle : ∀ n : ℕ, 2 ≤ n → lam₁ n ≤ lam₂ n) :
    (c.sum fun f t => t * (weilFullFunctional lam₁ (EF.weilTest f.1 f.1)).re) ≤
      c.sum fun f t => t * (weilFullFunctional lam₂ (EF.weilTest f.1 f.1)).re := by
  rw [sum_re_weilFullFunctional_eq_sum_weilArchRe_sub_counterterm,
    sum_re_weilFullFunctional_eq_sum_weilArchRe_sub_counterterm]
  linarith [sum_primeBlindCounterterm_le_of_nonposCone hc_nonpos hle]

/-- **Upward Monotonicity of `PositiveOnNonposCone`**:
if `PositiveOnNonposCone lam₁` holds and `lam₁ n ≤ lam₂ n` for all `n ≥ 2`, then
`PositiveOnNonposCone lam₂` holds. -/
theorem positiveOnNonposCone_of_le {lam₁ lam₂ : ℕ → ℝ} (hpos : PositiveOnNonposCone lam₁)
    (hle : ∀ n : ℕ, 2 ≤ n → lam₁ n ≤ lam₂ n) :
    PositiveOnNonposCone lam₂ :=
  fun c hc hc_nonpos =>
    (hpos c hc hc_nonpos).trans (sum_re_weilFullFunctional_le_of_nonposCone hc_nonpos hle)

/-- Any majorant `U ≥ lam` of a full-cone Weil-positive weight `lam` satisfies
`PositiveOnNonposCone U`. -/
theorem positiveOnNonposCone_of_le_weilPositiveFull {lam U : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hle : ∀ n : ℕ, 2 ≤ n → lam n ≤ U n) :
    PositiveOnNonposCone U :=
  positiveOnNonposCone_of_le (fun c hc _ => sum_nonneg_of_weilPositiveFull hW c hc) hle

/-- **Counterterm Monotonicity on the Nonnegative Cone**:
if a mixture `c : WeilTestFn →₀ ℝ` lies in the nonnegative cone
(`∀ n ≥ 2, 0 ≤ c.sum fun f t => t * logValue f.1 n`) and `lam₁ n ≤ lam₂ n` for all `n ≥ 2`,
then `c.sum (fun f t => t * primeBlindCounterterm lam₁ f) ≤ c.sum (fun f t => t * primeBlindCounterterm lam₂ f)`. -/
theorem sum_primeBlindCounterterm_le_of_nonnegCone {lam₁ lam₂ : ℕ → ℝ} {c : WeilTestFn →₀ ℝ}
    (hc_nonneg : ∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1 n)
    (hle : ∀ n : ℕ, 2 ≤ n → lam₁ n ≤ lam₂ n) :
    (c.sum fun f t => t * primeBlindCounterterm lam₁ f) ≤
      c.sum fun f t => t * primeBlindCounterterm lam₂ f := by
  rw [sum_primeBlindCounterterm_eq_finsuppSum, sum_primeBlindCounterterm_eq_finsuppSum]
  refine Finsupp.sum_le_sum fun j _ => ?_
  have hj0 : 0 ≤ linearCombination ℝ logVector c j := by
    rw [linearCombination_logVector_apply]
    exact hc_nonneg j.1 j.2
  exact mul_le_mul_of_nonneg_left (hle j.1 j.2) hj0

/-- **Weil Functional Antitonicity on the Nonnegative Cone**:
if `c` lies in the nonnegative cone (`∀ n ≥ 2, 0 ≤ c.sum fun f t => t * logValue f.1 n`) and
`lam₂ n ≤ lam₁ n` for all `n ≥ 2`, then
`c.sum (fun f t => t * (weilFullFunctional lam₁ (EF.weilTest f.1 f.1)).re) ≤ c.sum (fun f t => t * (weilFullFunctional lam₂ (EF.weilTest f.1 f.1)).re)`. -/
theorem sum_re_weilFullFunctional_le_of_nonnegCone {lam₁ lam₂ : ℕ → ℝ} {c : WeilTestFn →₀ ℝ}
    (hc_nonneg : ∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1 n)
    (hle : ∀ n : ℕ, 2 ≤ n → lam₂ n ≤ lam₁ n) :
    (c.sum fun f t => t * (weilFullFunctional lam₁ (EF.weilTest f.1 f.1)).re) ≤
      c.sum fun f t => t * (weilFullFunctional lam₂ (EF.weilTest f.1 f.1)).re := by
  rw [sum_re_weilFullFunctional_eq_sum_weilArchRe_sub_counterterm,
    sum_re_weilFullFunctional_eq_sum_weilArchRe_sub_counterterm]
  linarith [sum_primeBlindCounterterm_le_of_nonnegCone hc_nonneg hle]

/-- **Downward Monotonicity of `PositiveOnNonnegCone`**:
if `PositiveOnNonnegCone lam₁` holds and `lam₂ n ≤ lam₁ n` for all `n ≥ 2`, then
`PositiveOnNonnegCone lam₂` holds. -/
theorem positiveOnNonnegCone_of_ge {lam₁ lam₂ : ℕ → ℝ} (hpos : PositiveOnNonnegCone lam₁)
    (hle : ∀ n : ℕ, 2 ≤ n → lam₂ n ≤ lam₁ n) :
    PositiveOnNonnegCone lam₂ :=
  fun c hc hc_nonneg =>
    (hpos c hc hc_nonneg).trans (sum_re_weilFullFunctional_le_of_nonnegCone hc_nonneg hle)

/-- Any minorant `L ≤ lam` of a full-cone Weil-positive weight `lam` satisfies
`PositiveOnNonnegCone L`. -/
theorem positiveOnNonnegCone_of_ge_weilPositiveFull {lam L : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hle : ∀ n : ℕ, 2 ≤ n → L n ≤ lam n) :
    PositiveOnNonnegCone L :=
  positiveOnNonnegCone_of_ge (fun c hc _ => sum_nonneg_of_weilPositiveFull hW c hc) hle

/-- **Mixture-Dependent Minorant Counterterm Sufficiency for `PositiveOnNonposCone U`**:
for any upper barrier `U : ℕ → ℝ`, if for each nonnegative mixture `c` in the nonpositive cone
there exists *some* minorant sequence `lam : ℕ → ℝ` (possibly depending on `c`) with
`∀ n ≥ 2, lam n ≤ U n` and `0 ≤ c.sum (fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re)`,
then `PositiveOnNonposCone U` holds unconditionally. -/
theorem positiveOnNonposCone_of_forall_exists_minorant_nonneg {U : ℕ → ℝ}
    (h : ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
      (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) ≤ 0) →
      ∃ lam : ℕ → ℝ, (∀ n : ℕ, 2 ≤ n → lam n ≤ U n) ∧
        0 ≤ c.sum fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re) :
    PositiveOnNonposCone U := by
  intro c hc hc_nonpos
  obtain ⟨lam, hle, hnn⟩ := h c hc hc_nonpos
  exact hnn.trans (sum_re_weilFullFunctional_le_of_nonposCone hc_nonpos hle)

/-- **Mixture-Dependent Minorant Counterterm Sufficiency for `RiemannHypothesis` (Nonpositive Cone)**:
if `U : ℕ → ℝ` has summable excess over `Λ` against `n^{-1/2}` and for each nonnegative mixture `c`
in the nonpositive cone there exists *some* minorant sequence `lam ≤ U` with nonnegative
counterterm-completed mixture energy, then `RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_exists_minorant_nonneg_on_nonposCone {U : ℕ → ℝ}
    (hU : Summable fun n => max (U n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 / Real.sqrt n)
    (h : ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
      (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) ≤ 0) →
      ∃ lam : ℕ → ℝ, (∀ n : ℕ, 2 ≤ n → lam n ≤ U n) ∧
        0 ≤ c.sum fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re) :
    RiemannHypothesis :=
  riemannHypothesis_of_positiveOnNonposCone hU
    (positiveOnNonposCone_of_forall_exists_minorant_nonneg h)

/-- **Mixture-Dependent Majorant Counterterm Sufficiency for `PositiveOnNonnegCone L`**:
for any lower barrier `L : ℕ → ℝ`, if for each nonnegative mixture `c` in the nonnegative cone
there exists *some* majorant sequence `lam : ℕ → ℝ` (possibly depending on `c`) with
`∀ n ≥ 2, L n ≤ lam n` and `0 ≤ c.sum (fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re)`,
then `PositiveOnNonnegCone L` holds unconditionally. -/
theorem positiveOnNonnegCone_of_forall_exists_majorant_nonneg {L : ℕ → ℝ}
    (h : ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
      (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1 n) →
      ∃ lam : ℕ → ℝ, (∀ n : ℕ, 2 ≤ n → L n ≤ lam n) ∧
        0 ≤ c.sum fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re) :
    PositiveOnNonnegCone L := by
  intro c hc hc_nonneg
  obtain ⟨lam, hle, hnn⟩ := h c hc hc_nonneg
  exact hnn.trans (sum_re_weilFullFunctional_le_of_nonnegCone hc_nonneg hle)

/-- **Mixture-Dependent Majorant Counterterm Sufficiency for `RiemannHypothesis` (Nonnegative Cone)**:
if `L : ℕ → ℝ` has summable deficit below `Λ` against `n^{-1/2}` and for each nonnegative mixture
`c` in the nonnegative cone there exists *some* majorant sequence `L ≤ lam` with nonnegative
counterterm-completed mixture energy, then `RiemannHypothesis` holds unconditionally. -/
theorem riemannHypothesis_of_forall_exists_majorant_nonneg_on_nonnegCone {L : ℕ → ℝ}
    (hL : Summable fun n => max ((ArithmeticFunction.vonMangoldt n : ℝ) - L n) 0 / Real.sqrt n)
    (h : ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
      (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1 n) →
      ∃ lam : ℕ → ℝ, (∀ n : ℕ, 2 ≤ n → L n ≤ lam n) ∧
        0 ≤ c.sum fun f t => t * (weilFullFunctional lam (EF.weilTest f.1 f.1)).re) :
    RiemannHypothesis :=
  riemannHypothesis_of_positiveOnNonnegCone hL
    (positiveOnNonnegCone_of_forall_exists_majorant_nonneg h)

/-! ## Section 5: The Markov Archimedean-Minus-Prime Form, Rank-2 `(1, 1)` Pole Signature `2 C(f)² - 2 S(f)²`, and Counterterm / Euler–Maclaurin Bridges on Odd Tests and the Primitive Hyperplane -/

/-- The pole-free archimedean functional `weilArchRe k - (weilPoleTerm k).re`, which equals
`((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)).re`. -/
def markovArchRe (k : ℝ → ℂ) : ℝ :=
  weilArchRe k - (weilPoleTerm k).re

/-- The general counterterm-completed pole-free (Markov) energy:
`markovCountertermEnergy lam f = (weilFullFunctional lam (EF.weilTest f f) - weilPoleTerm (EF.weilTest f f)).re`. -/
def markovCountertermEnergy (lam : ℕ → ℝ) (f : ℝ → ℂ) : ℝ :=
  (weilFullFunctional lam (EF.weilTest f f) - weilPoleTerm (EF.weilTest f f)).re

/-- At `lam = Λ`, `markovCountertermEnergy` is `markovEnergy`. -/
@[simp]
theorem markovCountertermEnergy_vonMangoldt_eq_markovEnergy (f : ℝ → ℂ) :
    markovCountertermEnergy (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f =
      markovEnergy f :=
  rfl

/-- `markovArchRe k` is the real part of the archimedean Gamma integral `(1 / (2 * π)) ∫ k̂(r) γ(r) dr`. -/
theorem markovArchRe_eq_re_archIntegral (k : ℝ → ℂ) :
    markovArchRe k =
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)).re := by
  unfold markovArchRe weilArchRe weilPoleTerm
  simp only [Complex.add_re]
  ring

/-- **Counterterm Decomposition of `markovCountertermEnergy`**:
for any `f : WeilTestFn` and any counterterm weight `lam : ℕ → ℝ`,
`markovCountertermEnergy lam f.1 = markovArchRe (EF.weilTest f.1 f.1) - primeBlindCounterterm lam f`. -/
theorem markovCountertermEnergy_eq_markovArchRe_sub_counterterm (lam : ℕ → ℝ) (f : WeilTestFn) :
    markovCountertermEnergy lam f.1 =
      markovArchRe (EF.weilTest f.1 f.1) - primeBlindCounterterm lam f := by
  unfold markovCountertermEnergy markovArchRe
  rw [Complex.sub_re, re_weilFullFunctional_eq_weilArchRe_sub_counterterm]
  ring

/-- Counterterm decomposition of `markovEnergy` on `f : WeilTestFn`. -/
theorem markovEnergy_eq_markovArchRe_sub_counterterm (f : WeilTestFn) :
    markovEnergy f.1 =
      markovArchRe (EF.weilTest f.1 f.1) -
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f :=
  markovCountertermEnergy_eq_markovArchRe_sub_counterterm _ f

/-- **All-Integer Counterterm Invariance of `markovCountertermEnergy` on the Prime-Blind Cone**:
for any prime-blind mixture `c : WeilTestFn →₀ ℝ` and any sequence `lam : ℕ → ℝ`, the mixture sum
of `markovCountertermEnergy lam` equals the mixture sum of `markovArchRe` (and in particular equals
the mixture sum of `markovEnergy`). -/
theorem sum_markovArchRe_eq_sum_markovCountertermEnergy_of_primeBlind (lam : ℕ → ℝ)
    {c : WeilTestFn →₀ ℝ}
    (hnull : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) :
    (c.sum fun f t => t * markovArchRe (EF.weilTest f.1 f.1)) =
      c.sum fun f t => t * markovCountertermEnergy lam f.1 := by
  have h1 : (c.sum fun f t => t * markovCountertermEnergy lam f.1) =
      (c.sum fun f t => t * markovArchRe (EF.weilTest f.1 f.1)) -
        (c.sum fun f t => t * primeBlindCounterterm lam f) := by
    rw [← Finsupp.sum_sub]
    refine Finsupp.sum_congr fun f _ => ?_
    rw [markovCountertermEnergy_eq_markovArchRe_sub_counterterm]
    ring
  rw [h1, sum_primeBlindCounterterm_eq_zero_of_primeBlind lam hnull, sub_zero]

/-- The even cosh moment `C(f) = ∫ x, f x * cosh(x / 2)` of a real test `f : ℝ → ℝ`. -/
def coshHalfMoment (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, f x * Real.cosh (x / 2)

/-- The odd sinh moment `S(f) = ∫ x, f x * sinh(x / 2)` of a real test `f : ℝ → ℝ`. -/
def sinhHalfMoment (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, f x * Real.sinh (x / 2)

/-- For any odd test `f : ℝ → ℝ`, `coshHalfMoment f = 0`. -/
theorem coshHalfMoment_eq_zero_of_odd {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) :
    coshHalfMoment f = 0 :=
  integral_mul_cosh_half_of_odd hodd

/-- Decomposition of the exponential moments `∫ f(x) e^{±x/2} dx` into `coshHalfMoment f ± sinhHalfMoment f`. -/
theorem integral_mul_exp_half_eq_cosh_add_sinh {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    (∫ x : ℝ, f x * Real.exp (x / 2)) = coshHalfMoment f + sinhHalfMoment f ∧
      (∫ x : ℝ, f x * Real.exp (-x / 2)) = coshHalfMoment f - sinhHalfMoment f := by
  have ic : Integrable fun x : ℝ => f x * Real.cosh (x / 2) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have is : Integrable fun x : ℝ => f x * Real.sinh (x / 2) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  unfold coshHalfMoment sinhHalfMoment
  constructor
  · rw [← integral_add ic is]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  · rw [← integral_sub ic is]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.cosh_eq, Real.sinh_eq, show -(x / 2) = -x / 2 by ring]
    ring

/-- **Exact Real-Space Pair-Integral Formula for `(weilPoleTerm (EF.weilTest F F)).re`**:
for any continuous compactly supported `f : ℝ → ℝ`,
`(weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re = 2 * ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)`. -/
theorem re_weilPoleTerm_ofReal_eq_two_mul_integral_cosh {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    (weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      2 * ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) := by
  set F : ℝ → ℂ := fun u => (f u : ℂ)
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf
  have hFcs : HasCompactSupport F := hfc.comp_left Complex.ofReal_zero
  rw [weilPoleTerm_weilTest_eq hFc hFcs, paperFT_ofReal_I_div_two f,
    paperFT_ofReal_neg_I_div_two f, Complex.conj_ofReal, Complex.conj_ofReal,
    integral_prod_cosh_eq hfc hf]
  have hcast :
      (((∫ u : ℝ, f u * Real.exp (-u / 2) : ℝ) : ℂ) *
          ((∫ u : ℝ, f u * Real.exp (u / 2) : ℝ) : ℂ) +
        ((∫ u : ℝ, f u * Real.exp (u / 2) : ℝ) : ℂ) *
          ((∫ u : ℝ, f u * Real.exp (-u / 2) : ℝ) : ℂ)) =
      ((2 * ((∫ u : ℝ, f u * Real.exp (u / 2)) * ∫ u : ℝ, f u * Real.exp (-u / 2)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

/-- **Exact Rank-2 `(1, 1)` Signature Decomposition of `weilPoleTerm` on Real Tests**:
for every continuous compactly supported `f : ℝ → ℝ`,
`(weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re = 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2`. -/
theorem re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    (weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 := by
  obtain ⟨hp, hm⟩ := integral_mul_exp_half_eq_cosh_add_sinh hf hfc
  rw [re_weilPoleTerm_ofReal_eq_two_mul_integral_cosh hf hfc,
    integral_prod_cosh_eq hfc hf, hp, hm]
  ring

/-- **Exact Real-Space Lévy Jump Identity for `markovArchRe` (Complete Pole Cancellation)**:
for every `f ∈ C²_c(ℝ)`, subtracting `weilPoleTerm` from `weilArchRe` cancels the growing
`2 cosh((u-v)/2)` pair integral identically, leaving
`markovArchRe (EF.weilTest F F) = EF.gammaBracket 0 * ∫ f² + (jumpEnergy f).toReal`. -/
theorem markovArchRe_ofReal_eq_levy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      EF.gammaBracket 0 * (∫ u : ℝ, f u ^ 2) + (jumpEnergy f).toReal := by
  unfold markovArchRe jumpEnergy
  rw [weilArchRe_eq_levy_pole hf hfc,
    re_weilPoleTerm_ofReal_eq_two_mul_integral_cosh hf.continuous hfc]
  ring

/-- **Exact Real-Space Lévy–Counterterm Identity for `markovCountertermEnergy` (No Pole Term)**:
for every real `f ∈ C²_c(ℝ)` and every counterterm sequence `lam : ℕ → ℝ`,
`markovCountertermEnergy lam F = EF.gammaBracket 0 * ∫ f² + (jumpEnergy f).toReal - primeBlindCounterterm lam (realWeilTestFn f hf hfc)`. -/
theorem markovCountertermEnergy_real_eq_levy_sub_counterterm (lam : ℕ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      EF.gammaBracket 0 * (∫ u : ℝ, f u ^ 2) + (jumpEnergy f).toReal -
        primeBlindCounterterm lam (realWeilTestFn f hf hfc) := by
  have h1 := markovCountertermEnergy_eq_markovArchRe_sub_counterterm lam (realWeilTestFn f hf hfc)
  change markovCountertermEnergy lam (fun u => (f u : ℂ)) =
    markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
      primeBlindCounterterm lam (realWeilTestFn f hf hfc) at h1
  rw [h1, markovArchRe_ofReal_eq_levy hf hfc]

/-- **Exact Real-Space Lévy–Counterterm Identity for `markovEnergy` (No Pole Term)**:
specializing `markovCountertermEnergy_real_eq_levy_sub_counterterm` to `Λ`. -/
theorem markovEnergy_real_eq_levy_sub_counterterm {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    markovEnergy (fun u => (f u : ℂ)) =
      EF.gammaBracket 0 * (∫ u : ℝ, f u ^ 2) + (jumpEnergy f).toReal -
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (realWeilTestFn f hf hfc) :=
  markovCountertermEnergy_real_eq_levy_sub_counterterm _ hf hfc

/-- **Signature `(1, 1)` Relation Between `markovCountertermEnergy` and `(weilFullFunctional lam).re`**:
for every real `f ∈ C²_c(ℝ)` and every counterterm `lam : ℕ → ℝ`,
`markovCountertermEnergy lam F = (weilFullFunctional lam (EF.weilTest F F)).re - 2 * coshHalfMoment f ^ 2 + 2 * sinhHalfMoment f ^ 2`. -/
theorem markovCountertermEnergy_real_eq_re_weilFullFunctional_sub_cosh_add_sinh (lam : ℕ → ℝ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re -
        2 * coshHalfMoment f ^ 2 + 2 * sinhHalfMoment f ^ 2 := by
  unfold markovCountertermEnergy
  rw [Complex.sub_re, re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hf.continuous hfc]
  ring

/-- **Primitive Hyperplane Identity (`coshHalfMoment f = 0`)**:
on the primitive hyperplane `∫ x, f x * cosh(x / 2) = 0`, the positive square `2 * coshHalfMoment f ^ 2`
vanishes and `markovCountertermEnergy lam F` equals `(weilFullFunctional lam (EF.weilTest F F)).re`
plus the nonnegative bonus square `2 * sinhHalfMoment f ^ 2`. -/
theorem markovCountertermEnergy_real_eq_re_weilFullFunctional_add_sinh_sq_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) :
    markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re +
        2 * sinhHalfMoment f ^ 2 := by
  rw [markovCountertermEnergy_real_eq_re_weilFullFunctional_sub_cosh_add_sinh lam hf hfc, hcosh]
  ring

/-- **Odd-Test Identity (`f (-x) = -f x`)**:
for every odd real test `f ∈ C²_c(ℝ)`, `markovCountertermEnergy lam F` equals
`(weilFullFunctional lam (EF.weilTest F F)).re + 2 * sinhHalfMoment f ^ 2`. -/
theorem markovCountertermEnergy_real_eq_re_weilFullFunctional_add_sinh_sq_of_odd
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) :
    markovCountertermEnergy lam (fun u => (f u : ℂ)) =
      (weilFullFunctional lam (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re +
        2 * sinhHalfMoment f ^ 2 :=
  markovCountertermEnergy_real_eq_re_weilFullFunctional_add_sinh_sq_of_cosh_zero lam hf hfc
    (coshHalfMoment_eq_zero_of_odd hodd)

/-- **Strengthened Coercive Euler–Maclaurin + `m`-th Cesàro + Sinh-Moment Lower Bound for
`markovCountertermEnergy` on the Primitive Hyperplane**:
for every real `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0` (and in particular
every odd test), `markovCountertermEnergy (unitStepCountertermWeight + δ)` dominates the coercive
Euler–Maclaurin + `m`-th Cesàro lower bound **plus** the nonnegative bonus square
`2 * sinhHalfMoment f ^ 2 ≥ 0`. -/
theorem one_hundredth_l2_add_sinh_sq_add_eulerMaclaurin_le_markovCountertermEnergy_of_cosh_zero
    (m : ℕ) (δ : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        2 * sinhHalfMoment f ^ 2 +
        rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N -
        (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (1 / 10000) +
          EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-(1 / 10000))).re -
        (∑ n ∈ Finset.Icc 2 N,
          countertermIteratedPrefixSum m δ n *
            iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) ≤
      markovCountertermEnergy (unitStepCountertermWeight + δ) (fun u => (f u : ℂ)) := by
  have h1 := one_hundredth_l2_add_eulerMaclaurin_sub_iteratedCesaro_le_re_weilFullFunctional
    m δ (realWeilTestFn f hf hfc) hN1 hN
  have h2 := markovCountertermEnergy_real_eq_re_weilFullFunctional_add_sinh_sq_of_cosh_zero
    (unitStepCountertermWeight + δ) hf hfc hcosh
  change _ ≤ (weilFullFunctional (unitStepCountertermWeight + δ)
    (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re at h1
  linarith

/-- **Counterterm Lévy–Jump Equivalence for `RiemannHypothesis` on Odd Tests**:
`RiemannHypothesis` holds if and only if for every odd real test `f ∈ C²_c(ℝ)`, the canonical prime
counterterm `primeBlindCounterterm Λ (realWeilTestFn f hf hfc)` is bounded above by the pole-free
Lévy jump energy `EF.gammaBracket 0 * ∫ f² + (jumpEnergy f).toReal`. -/
theorem riemannHypothesis_iff_forall_odd_counterterm_le_levy :
    RiemannHypothesis ↔ ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      (∀ x, f (-x) = -f x) →
      primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (realWeilTestFn f hf hfc) ≤
        EF.gammaBracket 0 * (∫ u : ℝ, f u ^ 2) + (jumpEnergy f).toReal := by
  rw [riemannHypothesis_iff_forall_odd_markovEnergy_nonneg]
  refine forall_congr' fun f => forall_congr' fun hf => forall_congr' fun hfc =>
    forall_congr' fun _ => ?_
  rw [markovEnergy_real_eq_levy_sub_counterterm hf hfc, sub_nonneg]

/-- **Counterterm Lévy–Jump Equivalence for `RiemannHypothesis` on the Primitive Hyperplane**:
`RiemannHypothesis` holds if and only if for every real test `f ∈ C²_c(ℝ)` on the primitive
hyperplane `coshHalfMoment f = 0`, the canonical prime counterterm
`primeBlindCounterterm Λ (realWeilTestFn f hf hfc)` is bounded above by the pole-free Lévy jump
energy `EF.gammaBracket 0 * ∫ f² + (jumpEnergy f).toReal`. -/
theorem riemannHypothesis_iff_forall_cosh_zero_counterterm_le_levy :
    RiemannHypothesis ↔ ∀ f : ℝ → ℝ, (hf : ContDiff ℝ 2 f) → (hfc : HasCompactSupport f) →
      coshHalfMoment f = 0 →
      primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (realWeilTestFn f hf hfc) ≤
        EF.gammaBracket 0 * (∫ u : ℝ, f u ^ 2) + (jumpEnergy f).toReal := by
  rw [riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg]
  refine forall_congr' fun f => forall_congr' fun hf => forall_congr' fun hfc =>
    forall_congr' fun _ => ?_
  rw [markovEnergy_real_eq_levy_sub_counterterm hf hfc, sub_nonneg]

end RHTower

end
