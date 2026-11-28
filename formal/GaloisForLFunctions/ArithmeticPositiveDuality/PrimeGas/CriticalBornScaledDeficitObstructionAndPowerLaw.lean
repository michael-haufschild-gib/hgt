import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBornFourierRigidity
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowPrimeReduction
import GaloisForLFunctions.ArithmeticPositiveDuality.ARationalPrimeBeurlingOneOff

/-!
# Polylogarithmic Zero-Blindness, Off-Critical Beurling Countermodels, Lossless Single-Mode Prime Reconstruction, and Power-Scaled Deficit Excess from `ζ(ρ) = 0`

For `0 < σ < 1 / 2`, `t ∈ ℝ`, and `k ∈ ℤ`, `bornCoefficient σ t k N` has limiting modulus
`bornLorentzianLimit σ t k = (1 - 2σ) / √((1 - 2σ)² + (k t)²)` and logarithmic dispersion deficit
`log(N + 2) · (bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖) → bornLogDispersionCoeff σ t k`.
This module establishes the obstruction to polylogarithmic deficit amplification and the exact
power-scaled laws under which `riemannZeta ρ = 0` (`0 < Re ρ < 1 / 2`, without assuming
`Re ρ = 1 / 2`) forces fixed positive excess above the critical-line limit at arbitrarily large
cutoffs:

1. **Pointwise logical barrier, all-order polylogarithmic zero-blindness, and the off-critical
   Beurling countermodel above height `184`**:
   - `zeta_zero_forces_superDispersion_iff_ne_zero` proves that forcing the `log(N + 2)`-scaled
     modulus deficit above `bornLogDispersionCoeff ρ.re ρ.im k₀ + c` (`c > 0`) along an unbounded
     cutoff sequence from `riemannZeta ρ = 0` is pointwise equivalent to `riemannZeta ρ ≠ 0`, and
     `unconditional_left_zero_exclusion_sub_farkas_and_low_height` discharges `riemannZeta ρ ≠ 0`
     unconditionally on `Re ρ < 2401 / 19200` and on `|Im ρ| ≤ 184`.
   - `subcritical_norm_deficit_sub_smooth_superPolyLog` and
     `subcritical_no_subseq_polyLog_smooth_deficit` prove that subtracting the zero-blind smooth
     modulus `‖smoothBornCoefficient σ t k N‖` and scaling by `(log(N + 2))^A` for any `A : ℕ`
     still converges to `0` unconditionally.
   - `beurling_countermodel_zero_above_184_yet_same_log_deficit` proves that for every `184 < |γ|`
     and `1 / 3 < μ < 1 / 2` (`0 < ν < 3μ - 1`), `overRegularZeta μ ν γ` has an actual off-critical
     zero at `(1 - μ) + iγ` (with `RationalPrimeOneOff` realizing `(3 / 5) ± iγ` as a convergent
     Euler product over rational primes), yet its `e^{-2μ u}`-weighted Born mode has the exact same
     logarithmic deficit limit `bornLogDispersionCoeff μ γ k`.

2. **Sharp `N = 3` finite-cutoff sub-unit rigidity and lossless single-mode prime reconstruction**:
   - `norm_bornCoefficient_two_eq_one_at_resonance` exhibits `t_res = 2π / (log 3 - log 2) ≠ 0`
     with `‖bornCoefficient σ t_res 1 2‖ = 1`, while `norm_bornCoefficient_lt_one_of_three_le`
     uses unique factorization of `{2, 3, 5}` to prove `‖bornCoefficient σ t k N‖ < 1` for all
     `N ≥ 3`, `σ ∈ ℝ`, `t ≠ 0`, `k ≠ 0`.
   - `bornStepExtraction_eq_and_prime_iff` and `reconstructedBornMass_and_theta_eq` reconstruct
     primality `(j + 3).Prime`, `bornMass σ N`, `Chebyshev.theta (N + 2)`, and
     `dyadicWeightedPrimeOnlyWindow N` purely from a single nonzero Fourier mode `k₀ ≠ 0`.

3. **Zero-forced power-scaled deficit and excess (`α ∈ (Re ρ, 1 / 2)`) vs. zero limit under RH**:
   - `zeta_zero_forces_single_mode_power_deficit_and_excess` proves from `riemannZeta ρ = 0`
     (`0 < Re ρ < 1 / 2`, without setting `Re ρ = 1 / 2`) that for every `k₀ ≠ 0`, every
     `α ∈ (Re ρ, 1 / 2)`, and every `c > 0`, the `(N + 2)^α`-scaled extracted deficit, excess, and
     dyadic single-mode window exceed `c` along unbounded cutoff sequences, whereas
     `rh_single_mode_power_deficit_tendsto_zero` and `rh_iff_fixed_point_single_mode_power_deficit`
     prove convergence to `0` under `RiemannHypothesis` and give a non-vacuous RH equivalence at
     any single fixed `(σ, t, k₀)` (`t ≠ 0`, `k₀ ≠ 0`).
   - `rh_quarter_bornCoefficient_sub_smooth_power_tendsto_zero` and
     `zeta_zero_forces_direct_bornCoefficient_sub_smooth_power_excess` establish the direct
     unreconstructed smooth-subtracted law: under `RiemannHypothesis` on `0 < σ ≤ 1 / 4`,
     `(N + 2)^α · ‖bornCoefficient σ t k N - smoothBornCoefficient σ t k N‖ → 0` for all `α < 1 / 2`,
     whereas any zero `riemannZeta ρ = 0` in `0 < Re ρ < 1 / 2` forces
     `(φ j + 2)^α · ‖bornCoefficient ρ.re ρ.im k₀ (φ j) - smoothBornCoefficient ρ.re ρ.im k₀ (φ j)‖ > c`
     along an unbounded cutoff sequence `φ → ∞` for every `k₀ ≠ 0`, `α ∈ (Re ρ, 1 / 2)`, and `c > 0`.
-/

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset MeasureTheory Real Set
open GaloisForLFunctions.HTGeometry
open scoped Topology BigOperators

attribute [-instance]
  GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.HeckeTauberian.instMeasurableSpace
  RCLike.toInnerProductSpaceReal

private theorem re_ofReal_add_ofReal_mul_I' (a b : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by simp

private theorem im_ofReal_add_ofReal_mul_I' (a b : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by simp

/-! ### Section 1: Pointwise logical barrier, all-order polylogarithmic zero-blindness, and the off-critical Beurling Born countermodel above height `184` -/

/-- **Pointwise logical equivalence at every subcritical abscissa (`0 < Re ρ < 1 / 2`):**
because `log(N + 2) · (bornLorentzianLimit ρ.re ρ.im k₀ - ‖bornCoefficient ρ.re ρ.im k₀ N‖)`
converges unconditionally to `bornLogDispersionCoeff ρ.re ρ.im k₀` (`subcritical_norm_bornCoefficient_log_deficit`),
forcing the `log`-scaled deficit above `bornLogDispersionCoeff ρ.re ρ.im k₀ + c` (`c > 0`) along
an unbounded cutoff sequence from `riemannZeta ρ = 0` is **pointwise equivalent** to `riemannZeta ρ ≠ 0`. -/
theorem zeta_zero_forces_superDispersion_iff_ne_zero {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1 / 2) (k₀ : ℤ) :
    (riemannZeta ρ = 0 →
      ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
        ∃ c : ℝ, 0 < c ∧
          ∀ᶠ j : ℕ in atTop,
            bornLogDispersionCoeff ρ.re ρ.im k₀ + c ≤
              Real.log ((φ j + 2 : ℕ) : ℝ) *
                (bornLorentzianLimit ρ.re ρ.im k₀ -
                  ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖)) ↔
      riemannZeta ρ ≠ 0 := by
  constructor
  · intro hforce hζ
    obtain ⟨φ, hφ, c, hc_pos, hev⟩ := hforce hζ
    have hC : bornLogDispersionCoeff ρ.re ρ.im k₀ < bornLogDispersionCoeff ρ.re ρ.im k₀ + c := by
      linarith only [hc_pos]
    refine subcritical_no_subseq_superDispersion_deficit hρ0 hρ1 ρ.im k₀ hC hφ ?_
    filter_upwards [hev] with j hj
    have hlog_pos : 0 < Real.log ((φ j + 2 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < φ j + 2))
    have hdiv : (bornLogDispersionCoeff ρ.re ρ.im k₀ + c) / Real.log ((φ j + 2 : ℕ) : ℝ) ≤
        bornLorentzianLimit ρ.re ρ.im k₀ - ‖bornCoefficient ρ.re ρ.im k₀ (φ j)‖ :=
      (div_le_iff₀' hlog_pos).mpr hj
    linarith only [hdiv]
  · intro hne hζ
    exact False.elim (hne hζ)

/-- **Unconditional exclusion of putative left-hand zeros on `(0, 2401 / 19200)` at all heights
and on `(0, 1 / 2)` through height `184`:** on both regions `riemannZeta ρ ≠ 0` holds
unconditionally. -/
theorem unconditional_left_zero_exclusion_sub_farkas_and_low_height {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1 / 2)
    (hreg : ρ.re < 2401 / 19200 ∨ |ρ.im| ≤ 184) :
    riemannZeta ρ ≠ 0 := by
  rcases hreg with hsub | hlow
  · exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_sub_farkas_left
      hρ0 hsub
  · exact (GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
      hρ0 (by linarith only [hρ1]) hρ1.ne hlow).1

/-- **All-order polylogarithmic zero-blindness of the modulus deficit (`0 < σ < 1 / 2`):**
for every `A : ℕ`, the difference between the true modulus deficit
`bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖` and the zero-blind smooth modulus deficit
`bornLorentzianLimit σ t k - ‖smoothBornCoefficient σ t k N‖` is `o((log(N + 2))^{-A})`. -/
theorem subcritical_norm_deficit_sub_smooth_superPolyLog {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) (t : ℝ) (k : ℤ) (A : ℕ) :
    Tendsto (fun N : ℕ =>
      (Real.log ((N + 2 : ℕ) : ℝ)) ^ A *
        |(bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖) -
          (bornLorentzianLimit σ t k - ‖smoothBornCoefficient σ t k N‖)|)
      atTop (𝓝 0) := by
  have hsup := subcritical_bornCoefficient_sub_smooth_superPolyLog hσ0 hσ1 t k A
  have hnn : ∀ᶠ N : ℕ in atTop,
      0 ≤ (Real.log ((N + 2 : ℕ) : ℝ)) ^ A *
        |(bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖) -
          (bornLorentzianLimit σ t k - ‖smoothBornCoefficient σ t k N‖)| := by
    filter_upwards [eventually_ge_atTop 0] with N _
    have hlog0 : 0 ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + 2))
    exact mul_nonneg (pow_nonneg hlog0 _) (abs_nonneg _)
  refine squeeze_zero' hnn ?_ hsup
  filter_upwards [eventually_ge_atTop 0] with N _
  have hlog0 : 0 ≤ (Real.log ((N + 2 : ℕ) : ℝ)) ^ A :=
    pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + 2))) _
  have htri : |(bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖) -
      (bornLorentzianLimit σ t k - ‖smoothBornCoefficient σ t k N‖)| ≤
      ‖bornCoefficient σ t k N - smoothBornCoefficient σ t k N‖ := by
    rw [show (bornLorentzianLimit σ t k - ‖bornCoefficient σ t k N‖) -
        (bornLorentzianLimit σ t k - ‖smoothBornCoefficient σ t k N‖) =
        ‖smoothBornCoefficient σ t k N‖ - ‖bornCoefficient σ t k N‖ by ring,
      abs_sub_comm]
    exact abs_norm_sub_norm_le _ _
  exact mul_le_mul_of_nonneg_left htri hlog0

/-- **All-order polylogarithmic cutoff barrier (`0 < σ < 1 / 2`):** subtracting the entire
infinite logarithmic asymptotic tower encoded in `‖smoothBornCoefficient σ t k‖` and scaling by
`(log(N + 2))^A` for **any** `A : ℕ` still cannot push the residual deficit above any fixed
`c > 0` along any unbounded cutoff sequence `φ : ℕ → ℕ`. -/
theorem subcritical_no_subseq_polyLog_smooth_deficit {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) (t : ℝ) (k : ℤ) (A : ℕ)
    {c : ℝ} (hc : 0 < c) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    ¬ (∀ᶠ j : ℕ in atTop,
        c ≤ (Real.log ((φ j + 2 : ℕ) : ℝ)) ^ A *
          (‖smoothBornCoefficient σ t k (φ j)‖ - ‖bornCoefficient σ t k (φ j)‖)) := by
  intro hev
  have hlim := (subcritical_norm_deficit_sub_smooth_superPolyLog hσ0 hσ1 t k A).comp hφ
  obtain ⟨j, hj_ge, hj_lt⟩ := (hev.and (hlim.eventually (gt_mem_nhds hc))).exists
  dsimp only [Function.comp_apply] at hj_lt
  have hlog0 : 0 ≤ (Real.log ((φ j + 2 : ℕ) : ℝ)) ^ A :=
    pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ φ j + 2))) _
  have hle_abs : (Real.log ((φ j + 2 : ℕ) : ℝ)) ^ A *
      (‖smoothBornCoefficient σ t k (φ j)‖ - ‖bornCoefficient σ t k (φ j)‖) ≤
      (Real.log ((φ j + 2 : ℕ) : ℝ)) ^ A *
        |(bornLorentzianLimit σ t k - ‖bornCoefficient σ t k (φ j)‖) -
          (bornLorentzianLimit σ t k - ‖smoothBornCoefficient σ t k (φ j)‖)| := by
    rw [show (bornLorentzianLimit σ t k - ‖bornCoefficient σ t k (φ j)‖) -
        (bornLorentzianLimit σ t k - ‖smoothBornCoefficient σ t k (φ j)‖) =
        ‖smoothBornCoefficient σ t k (φ j)‖ - ‖bornCoefficient σ t k (φ j)‖ by ring]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hlog0
  linarith only [hj_ge, hle_abs, hj_lt]

/-- Truncated logarithmic prime-Laplace transform `∫_1^U e^{-s u} w(u) du` of the continuous
Beurling one-off prime density `primeDensity μ ν γ`. -/
def beurlingPrimeSum (μ ν γ : ℝ) (s : ℂ) (U : ℝ) : ℂ :=
  ∫ u in (1 : ℝ)..U,
    Complex.exp (-(s * (u : ℂ))) * (_root_.RHTower.BeurlingOverRegularIntegers.primeDensity μ ν γ u : ℂ)

/-- The `k`-th Fourier mode of the `e^{-2μ u}`-weighted continuous Beurling prime ensemble at
clock `γ` and logarithmic cutoff `U = log X`. -/
def beurlingBornCoefficient (μ ν γ : ℝ) (k : ℤ) (U : ℝ) : ℂ :=
  beurlingPrimeSum μ ν γ (((2 * μ : ℝ) : ℂ) - (((k : ℝ) * γ : ℝ) : ℂ) * Complex.I) U /
    beurlingPrimeSum μ ν γ ((2 * μ : ℝ) : ℂ) U

private theorem continuousOn_beurlingPrimeIntegrand (μ ν γ : ℝ) (s : ℂ) {U : ℝ} :
    ContinuousOn (fun u : ℝ =>
      Complex.exp (-(s * (u : ℂ))) *
        (_root_.RHTower.BeurlingOverRegularIntegers.primeDensity μ ν γ u : ℂ)) (Icc 1 U) := by
  unfold _root_.RHTower.BeurlingOverRegularIntegers.primeDensity
    _root_.RHTower.BeurlingOverRegularIntegers.primeNumerator
  refine ContinuousOn.mul (by fun_prop) ?_
  have hnum : Continuous (fun u : ℝ =>
      ((Real.exp u - 2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u) +
        Real.exp (-((3 * μ - 1 - ν) * u)) + Real.exp (-((3 * μ - 1 + ν) * u)) -
          Real.exp (-((4 * μ - 1) * u)) : ℝ) : ℂ)) := by fun_prop
  have hden : ContinuousOn (fun u : ℝ => (u : ℂ)) (Icc 1 U) := by fun_prop
  refine (hnum.continuousOn.div hden fun u hu => ?_).congr fun u _ => ?_
  · exact Complex.ofReal_ne_zero.mpr (by linarith only [hu.1])
  · simp only [Pi.div_apply, Complex.ofReal_div]

private theorem exp_integral_div_cube_asymptotic {z : ℂ} (ha : 0 < z.re) :
    Tendsto (fun U : ℝ =>
      ‖∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖ *
        U ^ 2 / Real.exp (z.re * U)) atTop (𝓝 0) := by
  set a : ℝ := z.re with ha_def
  have hmaj : Tendsto (fun U : ℝ =>
      (1 / a) * (U ^ 2 * Real.exp (-(a / 2) * U)) + (8 / a) * (1 / U)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun U : ℝ => (1 / a) * (U ^ 2 * Real.exp (-(a / 2) * U))) atTop (𝓝 0) := by
      have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (a / 2) (half_pos ha)).const_mul (1 / a)
      rw [mul_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with U hU
      rw [Real.rpow_two, neg_mul]
    have h2 : Tendsto (fun U : ℝ => (8 / a) * (1 / U)) atTop (𝓝 0) := by
      have h0 := tendsto_inv_atTop_zero.const_mul (8 / a)
      rw [mul_zero] at h0
      exact h0.congr fun U => by rw [one_div]
    simpa only [add_zero] using h1.add h2
  have hnn : ∀ᶠ U : ℝ in atTop,
      0 ≤ ‖∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖ *
        U ^ 2 / Real.exp (a * U) := by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with U _
    exact div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (Real.exp_pos _).le
  refine squeeze_zero' hnn ?_ hmaj
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with U hU4
  have hU1 : 1 ≤ U := by linarith only [hU4]
  have hU_pos : 0 < U := by linarith only [hU4]
  have hhalf_ge1 : 1 ≤ U / 2 := by linarith only [hU4]
  have hhalf_le : U / 2 ≤ U := by linarith only [hU4]
  have hcont : ∀ b c : ℝ, 1 ≤ b → b ≤ c →
      IntervalIntegrable (fun u : ℝ => ‖Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖) volume b c := by
    intro b c hb hbc
    have hc_on : ContinuousOn (fun u : ℝ => Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3) (Icc b c) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu =>
        pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith only [hb, hu.1]))
    exact hc_on.norm.intervalIntegrable_of_Icc hbc
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont 1 (U / 2) le_rfl hhalf_ge1) (hcont (U / 2) U hhalf_ge1 hhalf_le)
  have hexp_int : ∀ b c : ℝ, b ≤ c →
      IntervalIntegrable (fun u : ℝ => Real.exp (a * u)) volume b c ∧
        (∫ u in b..c, Real.exp (a * u)) ≤ Real.exp (a * c) / a := by
    intro b c hbc
    have hi : IntervalIntegrable (fun u : ℝ => Real.exp (a * u)) volume b c :=
      (by fun_prop : Continuous fun u : ℝ => Real.exp (a * u)).intervalIntegrable b c
    refine ⟨hi, ?_⟩
    have hd : ∀ u ∈ Set.uIcc b c,
        HasDerivAt (fun y : ℝ => Real.exp (a * y) / a) (Real.exp (a * u)) u := by
      intro u _
      have h1 := ((hasDerivAt_id u).const_mul a).exp.div_const a
      refine h1.congr_deriv ?_
      dsimp only [id]
      rw [mul_one, mul_div_cancel_right₀ _ ha.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    have hb_pos : 0 ≤ Real.exp (a * b) / a := div_nonneg (Real.exp_pos _).le ha.le
    linarith only [hb_pos]
  have hnorm_eq : ∀ u : ℝ, 1 ≤ u →
      ‖Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖ = Real.exp (a * u) / u ^ 3 := by
    intro u hu1
    have hu0 : 0 ≤ u := by linarith only [hu1]
    have hre : (z * (u : ℂ)).re = a * u := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, ha_def]
    rw [norm_div, norm_pow, Complex.norm_exp, hre, Complex.norm_real, Real.norm_of_nonneg hu0]
  obtain ⟨hi_low, hle_low⟩ := hexp_int 1 (U / 2) hhalf_ge1
  obtain ⟨hi_high, hle_high⟩ := hexp_int (U / 2) U hhalf_le
  have hlow : (∫ u in (1 : ℝ)..(U / 2), ‖Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖) ≤
      Real.exp (a * (U / 2)) / a := by
    refine (intervalIntegral.integral_mono_on hhalf_ge1
      (hcont 1 (U / 2) le_rfl hhalf_ge1) hi_low fun u hu => ?_).trans hle_low
    rw [hnorm_eq u hu.1]
    exact div_le_self (Real.exp_pos _).le (one_le_pow₀ hu.1)
  have hhigh : (∫ u in (U / 2)..U, ‖Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖) ≤
      (8 / U ^ 3) * (Real.exp (a * U) / a) := by
    have hmono := intervalIntegral.integral_mono_on hhalf_le
      (hcont (U / 2) U hhalf_ge1 hhalf_le) (hi_high.const_mul (8 / U ^ 3)) fun u hu => by
        rw [hnorm_eq u (hhalf_ge1.trans hu.1)]
        have hpow : (U / 2) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by positivity) hu.1 3
        have hinv : 1 / u ^ 3 ≤ 8 / U ^ 3 := by
          have h1 := one_div_le_one_div_of_le (pow_pos (half_pos hU_pos) 3) hpow
          rwa [div_pow, show (2 : ℝ) ^ 3 = 8 by norm_num, one_div_div] at h1
        calc Real.exp (a * u) / u ^ 3 = (1 / u ^ 3) * Real.exp (a * u) := by ring
          _ ≤ (8 / U ^ 3) * Real.exp (a * u) :=
            mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hle_high (by positivity))
  have htot : ‖∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖ ≤
      Real.exp (a * (U / 2)) / a + (8 / U ^ 3) * (Real.exp (a * U) / a) := by
    calc ‖∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖
        ≤ ∫ u in (1 : ℝ)..U, ‖Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖ :=
          intervalIntegral.norm_integral_le_integral_norm hU1
      _ = _ := hsplit.symm
      _ ≤ _ := add_le_add hlow hhigh
  have hexp_div : Real.exp (a * (U / 2)) / Real.exp (a * U) = Real.exp (-(a / 2) * U) := by
    rw [← Real.exp_sub]; congr 1; ring
  have hU_div : U ^ 2 / U ^ 3 = 1 / U := by
    rw [pow_succ U 2, ← div_div, div_self (pow_pos hU_pos 2).ne']
  have hexp_ne : Real.exp (a * U) ≠ 0 := (Real.exp_pos _).ne'
  calc ‖∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖ * U ^ 2 / Real.exp (a * U)
      ≤ (Real.exp (a * (U / 2)) / a + (8 / U ^ 3) * (Real.exp (a * U) / a)) *
          (U ^ 2 / Real.exp (a * U)) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right htot (div_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    _ = (1 / a) * (U ^ 2 * (Real.exp (a * (U / 2)) / Real.exp (a * U))) +
          (8 / a) * (U ^ 2 / U ^ 3) * (Real.exp (a * U) / Real.exp (a * U)) := by ring
    _ = (1 / a) * (U ^ 2 * Real.exp (-(a / 2) * U)) + (8 / a) * (1 / U) := by
        rw [hexp_div, hU_div, div_self hexp_ne, mul_one]

private theorem tendsto_beurlingPrimeSum_div_main_sub_one {μ ν : ℝ}
    (hμ1 : 1 / 3 < μ) (hμ2 : μ < 1 / 2) (hν0 : 0 < ν) (hν1 : ν < 3 * μ - 1)
    (γ ω : ℝ) :
    let s : ℂ := ((2 * μ : ℝ) : ℂ) - (ω : ℂ) * Complex.I
    Tendsto (fun U : ℝ =>
      (U : ℂ) *
        ((beurlingPrimeSum μ ν γ s U /
          (Complex.exp ((1 - s) * (U : ℂ)) / ((1 - s) * (U : ℂ)))) - 1))
      atTop (𝓝 (1 / (1 - (((2 * μ : ℝ) : ℂ) - (ω : ℂ) * Complex.I)))) := by
  set s : ℂ := ((2 * μ : ℝ) : ℂ) - (ω : ℂ) * Complex.I with hs_def
  set z : ℂ := 1 - s with hz_def
  set a : ℝ := 1 - 2 * μ with ha_def
  have ha0 : 0 < a := by linarith only [ha_def, hμ2]
  have hz_eq : z = (a : ℂ) + (ω : ℂ) * Complex.I := by
    rw [hz_def, hs_def, ha_def]; push_cast; ring
  have hz_re : z.re = a := by rw [hz_eq, re_ofReal_add_ofReal_mul_I']
  have hz_ne : z ≠ 0 := by
    intro h0; have hr := congrArg Complex.re h0
    rw [hz_re, Complex.zero_re] at hr; exact ha0.ne' hr
  set η : ℝ := 3 * μ - 1 - ν with hη_def
  have hη_pos : 0 < η := by linarith only [hη_def, hν1]
  let tail : ℝ → ℂ := fun u =>
    Complex.exp (-(s * (u : ℂ))) *
      (((-2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u) +
        Real.exp (-((3 * μ - 1 - ν) * u)) + Real.exp (-((3 * μ - 1 + ν) * u)) -
          Real.exp (-((4 * μ - 1) * u))) / u : ℝ) : ℂ)
  let prim : ℝ → ℂ := fun u =>
    Complex.exp (z * (u : ℂ)) / (z * (u : ℂ)) +
      Complex.exp (z * (u : ℂ)) / (z ^ 2 * (u : ℂ) ^ 2)
  have hprim_deriv : ∀ u : ℝ, 1 ≤ u →
      HasDerivAt prim
        (Complex.exp (z * (u : ℂ)) / (u : ℂ) -
          (2 / z ^ 2) * (Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3)) u := by
    intro u hu1
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hu1])
    have hid_c : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u := by
      simpa only [id, Complex.real_smul, mul_one, one_smul] using
        (hasDerivAt_id u).smul_const (1 : ℂ)
    have hexp_d : HasDerivAt (fun y : ℝ => Complex.exp (z * (y : ℂ)))
        (Complex.exp (z * (u : ℂ)) * z) u := by
      simpa only [mul_one] using (hid_c.const_mul z).cexp
    have hu_d : HasDerivAt (fun y : ℝ => z * (y : ℂ)) z u := by
      simpa only [mul_one] using hid_c.const_mul z
    have hu2_d : HasDerivAt (fun y : ℝ => z ^ 2 * (y : ℂ) ^ 2) (z ^ 2 * (2 * (u : ℂ))) u := by
      have hp2 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) (2 * (u : ℂ) ^ 1 * 1) u := hid_c.pow 2
      simpa only [pow_one, mul_one] using hp2.const_mul (z ^ 2)
    have hd1 := hexp_d.div hu_d (mul_ne_zero hz_ne hu_ne)
    have hd2 := hexp_d.div hu2_d (mul_ne_zero (pow_ne_zero 2 hz_ne) (pow_ne_zero 2 hu_ne))
    refine (hd1.add hd2).congr_deriv ?_
    set E : ℂ := Complex.exp (z * (u : ℂ))
    set uc : ℂ := (u : ℂ)
    field_simp [hz_ne, hu_ne]
    ring
  set C_const : ℝ := ‖prim 1‖ + 5 / η
  have hmaj : Tendsto (fun U : ℝ =>
      ‖z‖ * C_const * (U ^ 2 * Real.exp (-a * U)) +
        ‖z‖ * ‖2 / z ^ 2‖ *
          (‖∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖ *
            U ^ 2 / Real.exp (z.re * U))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun U : ℝ => ‖z‖ * C_const * (U ^ 2 * Real.exp (-a * U))) atTop (𝓝 0) := by
      have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha0).const_mul (‖z‖ * C_const)
      rw [mul_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with U _
      rw [Real.rpow_two]
    have h2 := (exp_integral_div_cube_asymptotic (by rw [hz_re]; exact ha0)).const_mul
      (‖z‖ * ‖2 / z ^ 2‖)
    rw [mul_zero] at h2
    simpa only [add_zero] using h1.add h2
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (by filter_upwards [eventually_ge_atTop (4 : ℝ)] with U _; exact norm_nonneg _)
    ?_ hmaj
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with U hU4
  have hU1 : 1 ≤ U := by linarith only [hU4]
  have hU_pos : 0 < U := by linarith only [hU4]
  have hUc_ne : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU_pos.ne'
  have hI_main : IntervalIntegrable (fun u : ℝ => Complex.exp (z * (u : ℂ)) / (u : ℂ)) volume 1 U :=
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu =>
      Complex.ofReal_ne_zero.mpr (by linarith only [hu.1])).intervalIntegrable_of_Icc hU1
  have hI_cube : IntervalIntegrable (fun u : ℝ => Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3) volume 1 U :=
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu =>
      pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith only [hu.1]))).intervalIntegrable_of_Icc hU1
  have hI_tail : IntervalIntegrable tail volume 1 U := by
    refine (ContinuousOn.mul (by fun_prop) ?_).intervalIntegrable_of_Icc hU1
    have hn : Continuous (fun u : ℝ =>
        ((-2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u) +
          Real.exp (-((3 * μ - 1 - ν) * u)) + Real.exp (-((3 * μ - 1 + ν) * u)) -
            Real.exp (-((4 * μ - 1) * u)) : ℝ) : ℂ)) := by fun_prop
    refine (hn.continuousOn.div (by fun_prop) fun u hu =>
      Complex.ofReal_ne_zero.mpr (by linarith only [hu.1])).congr fun u _ => ?_
    simp only [Pi.div_apply, Complex.ofReal_div]
  have hsplit_sum : beurlingPrimeSum μ ν γ s U =
      (∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ)) + ∫ u in (1 : ℝ)..U, tail u := by
    rw [beurlingPrimeSum, ← intervalIntegral.integral_add hI_main hI_tail]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hU1] at hu
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith only [hu.1])
    dsimp only [tail]
    unfold _root_.RHTower.BeurlingOverRegularIntegers.primeDensity
      _root_.RHTower.BeurlingOverRegularIntegers.primeNumerator
    have hexp1 : Complex.exp (-(s * (u : ℂ))) * Complex.exp (u : ℂ) = Complex.exp (z * (u : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; rw [hz_def]; ring
    simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_exp]
    linear_combination hexp1 / (u : ℂ)
  have hibp : (∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ)) =
      prim U - prim 1 + (2 / z ^ 2) * ∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hprim_deriv u (by rw [Set.uIcc_of_le hU1] at hu; exact hu.1))
      (hI_main.sub (hI_cube.const_mul (2 / z ^ 2)))
    rw [intervalIntegral.integral_sub hI_main (hI_cube.const_mul (2 / z ^ 2)),
      intervalIntegral.integral_const_mul] at hftc
    linear_combination hftc
  have htail_bound : ‖∫ u in (1 : ℝ)..U, tail u‖ ≤ 5 / η := by
    have hmaj_int : IntervalIntegrable (fun u : ℝ => 5 * Real.exp (-η * u)) volume 1 U :=
      (by fun_prop : Continuous fun u : ℝ => 5 * Real.exp (-η * u)).intervalIntegrable 1 U
    have hd_eta : ∀ u ∈ Set.uIcc 1 U,
        HasDerivAt (fun y : ℝ => -(5 / η) * Real.exp (-η * y)) (5 * Real.exp (-η * u)) u := by
      intro u _
      have h1 := (((hasDerivAt_id u).const_mul (-η)).exp).const_mul (-(5 / η))
      refine h1.congr_deriv ?_
      dsimp only [id]
      field_simp [hη_pos.ne']
    have hint_val := intervalIntegral.integral_eq_sub_of_hasDerivAt hd_eta hmaj_int
    calc ‖∫ u in (1 : ℝ)..U, tail u‖
        ≤ ∫ u in (1 : ℝ)..U, ‖tail u‖ := intervalIntegral.norm_integral_le_integral_norm hU1
      _ ≤ ∫ u in (1 : ℝ)..U, 5 * Real.exp (-η * u) := by
          refine intervalIntegral.integral_mono_on hU1 hI_tail.norm hmaj_int fun u hu => ?_
          dsimp only [tail]
          have hu1' : 1 ≤ u := hu.1
          have hu_pos : 0 < u := by linarith only [hu1']
          have hs_re : (-(s * (u : ℂ))).re = -2 * μ * u := by
            rw [hs_def]
            simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
              Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
            ring
          rw [norm_mul, Complex.norm_exp, hs_re, Complex.norm_real, Real.norm_eq_abs, abs_div,
            abs_of_pos hu_pos]
          have hcos : |Real.cos (γ * u)| ≤ 1 := Real.abs_cos_le_one _
          have habs_num : |-2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u) +
              Real.exp (-((3 * μ - 1 - ν) * u)) + Real.exp (-((3 * μ - 1 + ν) * u)) -
                Real.exp (-((4 * μ - 1) * u))| ≤
              2 * Real.exp ((1 - μ) * u) + Real.exp (-((3 * μ - 1 - ν) * u)) +
                Real.exp (-((3 * μ - 1 + ν) * u)) + Real.exp (-((4 * μ - 1) * u)) := by
            have htri1 := abs_sub
              (-2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u) +
                Real.exp (-((3 * μ - 1 - ν) * u)) + Real.exp (-((3 * μ - 1 + ν) * u)))
              (Real.exp (-((4 * μ - 1) * u)))
            have htri2 := abs_add_le
              (-2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u) +
                Real.exp (-((3 * μ - 1 - ν) * u)))
              (Real.exp (-((3 * μ - 1 + ν) * u)))
            have htri3 := abs_add_le
              (-2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u))
              (Real.exp (-((3 * μ - 1 - ν) * u)))
            have h1 : |-2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u)| ≤
                2 * Real.exp ((1 - μ) * u) := by
              rw [abs_mul, abs_mul, show |(-2 : ℝ)| = 2 by norm_num,
                abs_of_pos (Real.exp_pos _)]
              nlinarith [Real.exp_pos ((1 - μ) * u), hcos]
            rw [abs_of_pos (Real.exp_pos _)] at htri1 htri2 htri3
            linarith only [htri1, htri2, htri3, h1]
          have hdiv_le : |-2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u) +
              Real.exp (-((3 * μ - 1 - ν) * u)) + Real.exp (-((3 * μ - 1 + ν) * u)) -
                Real.exp (-((4 * μ - 1) * u))| / u ≤
              2 * Real.exp ((1 - μ) * u) + Real.exp (-((3 * μ - 1 - ν) * u)) +
                Real.exp (-((3 * μ - 1 + ν) * u)) + Real.exp (-((4 * μ - 1) * u)) :=
            (div_le_self (abs_nonneg _) hu1').trans habs_num
          have he1 : Real.exp (-2 * μ * u) * Real.exp ((1 - μ) * u) ≤ Real.exp (-η * u) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by rw [hη_def]; nlinarith only [hν0, hu1'])
          have he2 : Real.exp (-2 * μ * u) * Real.exp (-((3 * μ - 1 - ν) * u)) ≤ Real.exp (-η * u) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by rw [hη_def]; nlinarith only [hμ1, hu1'])
          have he3 : Real.exp (-2 * μ * u) * Real.exp (-((3 * μ - 1 + ν) * u)) ≤ Real.exp (-η * u) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by rw [hη_def]; nlinarith only [hμ1, hν0, hu1'])
          have he4 : Real.exp (-2 * μ * u) * Real.exp (-((4 * μ - 1) * u)) ≤ Real.exp (-η * u) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by rw [hη_def]; nlinarith only [hμ1, hν0, hu1'])
          calc Real.exp (-2 * μ * u) *
                (|-2 * Real.exp ((1 - μ) * u) * Real.cos (γ * u) +
                  Real.exp (-((3 * μ - 1 - ν) * u)) + Real.exp (-((3 * μ - 1 + ν) * u)) -
                    Real.exp (-((4 * μ - 1) * u))| / u)
              ≤ Real.exp (-2 * μ * u) *
                  (2 * Real.exp ((1 - μ) * u) + Real.exp (-((3 * μ - 1 - ν) * u)) +
                    Real.exp (-((3 * μ - 1 + ν) * u)) + Real.exp (-((4 * μ - 1) * u))) :=
                mul_le_mul_of_nonneg_left hdiv_le (Real.exp_pos _).le
            _ = 2 * (Real.exp (-2 * μ * u) * Real.exp ((1 - μ) * u)) +
                  Real.exp (-2 * μ * u) * Real.exp (-((3 * μ - 1 - ν) * u)) +
                  Real.exp (-2 * μ * u) * Real.exp (-((3 * μ - 1 + ν) * u)) +
                  Real.exp (-2 * μ * u) * Real.exp (-((4 * μ - 1) * u)) := by ring
            _ ≤ 5 * Real.exp (-η * u) := by linarith only [he1, he2, he3, he4]
      _ = -(5 / η) * Real.exp (-η * U) - -(5 / η) * Real.exp (-η * 1) := hint_val
      _ ≤ 5 / η := by
          have h1 : 0 ≤ (5 / η) * Real.exp (-η * U) := by positivity
          have h2 : Real.exp (-η * 1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hη_pos])
          nlinarith only [h1, h2, div_pos (by norm_num : (0 : ℝ) < 5) hη_pos]
  set Rem : ℂ := -prim 1 + (2 / z ^ 2) * (∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3) +
    ∫ u in (1 : ℝ)..U, tail u
  set E_U : ℂ := Complex.exp (z * (U : ℂ))
  have hEU_ne : E_U ≠ 0 := Complex.exp_ne_zero _
  have halg : (U : ℂ) * ((beurlingPrimeSum μ ν γ s U / (E_U / (z * (U : ℂ)))) - 1) - 1 / z =
      Rem * (z * (U : ℂ) ^ 2 / E_U) := by
    have hbp : beurlingPrimeSum μ ν γ s U = E_U / (z * (U : ℂ)) + E_U / (z ^ 2 * (U : ℂ) ^ 2) + Rem := by
      rw [hsplit_sum, hibp]; dsimp only [prim, Rem, E_U]; ring
    rw [hbp]
    set uc : ℂ := (U : ℂ)
    field_simp [hz_ne, hUc_ne, hEU_ne]
    ring
  change ‖(U : ℂ) * ((beurlingPrimeSum μ ν γ s U / (E_U / (z * (U : ℂ)))) - 1) - 1 / z‖ ≤ _
  rw [halg, norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hU_pos.le]
  have hEU_norm : ‖E_U‖ = Real.exp (a * U) := by
    dsimp only [E_U]
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, hz_re]
  rw [hEU_norm]
  have hRem_le : ‖Rem‖ ≤ C_const +
      ‖2 / z ^ 2‖ * ‖∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖ := by
    dsimp only [Rem, C_const]
    have htri1 := norm_add_le
      (-prim 1 + (2 / z ^ 2) * ∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3)
      (∫ u in (1 : ℝ)..U, tail u)
    have htri2 := norm_add_le (-prim 1)
      ((2 / z ^ 2) * ∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3)
    rw [norm_neg, norm_mul] at htri2
    linarith only [htri1, htri2, htail_bound]
  have hexp_inv : U ^ 2 / Real.exp (a * U) = U ^ 2 * Real.exp (-a * U) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul]
  calc ‖Rem‖ * (‖z‖ * U ^ 2 / Real.exp (a * U))
      ≤ (C_const + ‖2 / z ^ 2‖ *
          ‖∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖) *
          (‖z‖ * U ^ 2 / Real.exp (a * U)) :=
        mul_le_mul_of_nonneg_right hRem_le (by positivity)
    _ = ‖z‖ * C_const * (U ^ 2 / Real.exp (a * U)) +
          ‖z‖ * ‖2 / z ^ 2‖ *
            (‖∫ u in (1 : ℝ)..U, Complex.exp (z * (u : ℂ)) / (u : ℂ) ^ 3‖ *
              U ^ 2 / Real.exp (a * U)) := by ring
    _ = _ := by rw [hexp_inv, hz_re]

/-- **Off-critical Beurling countermodel above height `184` (`1 / 3 < μ < 1 / 2`, e.g. `μ = 2 / 5`):**
for **every** height `γ` (`184 < |γ|`), `overRegularZeta μ ν γ` has a nonnegative prime density,
linear integer count `N(x) - ρ₀ x - C → 0`, and an **actual off-critical zero pair** at
`(1 - μ) ± iγ` (reflected left-hand abscissa `μ ∈ (1 / 3, 1 / 2)`), while
`RationalPrimeOneOff.exists_rational_prime_euler_one_off γ` realizes the `μ = 2 / 5` zero pair
`3 / 5 ± iγ` as a convergent Euler product over genuine rational primes; yet its `e^{-2μ u}`-weighted
Born Fourier mode `beurlingBornCoefficient μ ν γ k U` has the **exact same** logarithmic deficit
limit `bornLogDispersionCoeff μ γ k` as a zero-free model. -/
theorem beurling_countermodel_zero_above_184_yet_same_log_deficit {μ ν : ℝ}
    (hμ1 : 1 / 3 < μ) (hμ2 : μ < 1 / 2) (hν0 : 0 < ν) (hν1 : ν < 3 * μ - 1)
    {γ : ℝ} (_hγ : 184 < |γ|) (k : ℤ) :
    _root_.RHTower.BeurlingOverRegularIntegers.overRegularZeta μ ν γ
        (((1 - μ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) = 0 ∧
      (∃ q : ℕ → ℕ, (∀ m, (q m).Prime) ∧ ∃ F : ℂ → ℂ,
        (∀ s : ℂ, 1 < s.re →
          HasProd (fun m => (1 - Complex.exp (-(s * Real.log (q m))))⁻¹) (F s)) ∧
        DifferentiableOn ℂ F {s : ℂ | 17 / 30 < s.re ∧ s ≠ 1} ∧
        {s : ℂ | 17 / 30 < s.re ∧ s ≠ 1 ∧ F s = 0} =
          {(3 / 5 : ℂ) + (γ : ℂ) * Complex.I, (3 / 5 : ℂ) - (γ : ℂ) * Complex.I}) ∧
      Tendsto (fun U : ℝ =>
        U * (bornLorentzianLimit μ γ k - ‖beurlingBornCoefficient μ ν γ k U‖))
        atTop (𝓝 (bornLogDispersionCoeff μ γ k)) := by
  refine ⟨_root_.RHTower.BeurlingOverRegularIntegers.overRegularZeta_eq_zero μ ν γ,
    GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff.exists_rational_prime_euler_one_off γ,
    ?_⟩
  set a : ℝ := 1 - 2 * μ with ha_def
  set ω : ℝ := (k : ℝ) * γ with hω_def
  have ha0 : 0 < a := by linarith only [ha_def, hμ2]
  set s : ℂ := ((2 * μ : ℝ) : ℂ) - (ω : ℂ) * Complex.I
  set s₀ : ℂ := ((2 * μ : ℝ) : ℂ)
  have h1s : 1 - s = (a : ℂ) + (ω : ℂ) * Complex.I := by
    dsimp only [s]; rw [ha_def]; push_cast; ring
  have h1s0 : 1 - s₀ = (a : ℂ) := by
    dsimp only [s₀]; rw [ha_def]; push_cast; ring
  let M_num : ℝ → ℂ := fun U => Complex.exp ((1 - s) * (U : ℂ)) / ((1 - s) * (U : ℂ))
  let M_den : ℝ → ℂ := fun U => Complex.exp ((1 - s₀) * (U : ℂ)) / ((1 - s₀) * (U : ℂ))
  let Q_num : ℝ → ℂ := fun U => beurlingPrimeSum μ ν γ s U / M_num U
  let Q_den : ℝ → ℂ := fun U => beurlingPrimeSum μ ν γ s₀ U / M_den U
  let W : ℝ → ℂ := fun U => Q_num U / Q_den U
  have hQ_num_log : Tendsto (fun U : ℝ => (U : ℂ) * (Q_num U - 1)) atTop (𝓝 (1 / (1 - s))) :=
    tendsto_beurlingPrimeSum_div_main_sub_one hμ1 hμ2 hν0 hν1 γ ω
  have hQ_den_log : Tendsto (fun U : ℝ => (U : ℂ) * (Q_den U - 1)) atTop (𝓝 (1 / (1 - s₀))) := by
    have h0 := tendsto_beurlingPrimeSum_div_main_sub_one hμ1 hμ2 hν0 hν1 γ 0
    have hs0_eq : ((2 * μ : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * Complex.I = s₀ := by
      dsimp only [s₀]; simp
    change Tendsto (fun U : ℝ =>
      (U : ℂ) * ((beurlingPrimeSum μ ν γ (((2 * μ : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * Complex.I) U /
        (Complex.exp ((1 - (((2 * μ : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * Complex.I)) * (U : ℂ)) /
          ((1 - (((2 * μ : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * Complex.I)) * (U : ℂ)))) - 1))
      atTop (𝓝 (1 / (1 - (((2 * μ : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * Complex.I)))) at h0
    rwa [hs0_eq] at h0
  have hinv_U : Tendsto (fun U : ℝ => ((U : ℂ))⁻¹) atTop (𝓝 0) := by
    have hc := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    rw [Complex.ofReal_zero] at hc
    exact hc.congr fun U => by dsimp only [Function.comp_apply]; rw [Complex.ofReal_inv]
  have hQ_num_1 : Tendsto Q_num atTop (𝓝 1) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have hm := hQ_num_log.mul hinv_U
    rw [mul_zero] at hm
    refine hm.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    have hUc : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
    calc (U : ℂ) * (Q_num U - 1) * (U : ℂ)⁻¹
        = (Q_num U - 1) * ((U : ℂ) * (U : ℂ)⁻¹) := by ring
      _ = Q_num U - 1 := by rw [mul_inv_cancel₀ hUc, mul_one]
  have hQ_den_1 : Tendsto Q_den atTop (𝓝 1) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have hm := hQ_den_log.mul hinv_U
    rw [mul_zero] at hm
    refine hm.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    have hUc : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hU.ne'
    calc (U : ℂ) * (Q_den U - 1) * (U : ℂ)⁻¹
        = (Q_den U - 1) * ((U : ℂ) * (U : ℂ)⁻¹) := by ring
      _ = Q_den U - 1 := by rw [mul_inv_cancel₀ hUc, mul_one]
  set α : ℂ := 1 / (1 - s) - 1 / (1 - s₀)
  have hW_log : Tendsto (fun U : ℝ => (U : ℂ) * (W U - 1)) atTop (𝓝 α) := by
    have hq := (hQ_num_log.sub hQ_den_log).div hQ_den_1 one_ne_zero
    rw [div_one] at hq
    refine hq.congr' ?_
    filter_upwards [hQ_den_1.eventually_ne one_ne_zero] with U hQd_ne
    dsimp only [Pi.div_apply, W]
    set qn : ℂ := Q_num U
    set qd : ℂ := Q_den U
    field_simp [hQd_ne]; ring
  have hW_1 : Tendsto W atTop (𝓝 1) := by
    have h0 := hQ_num_1.div hQ_den_1 one_ne_zero
    rwa [div_one] at h0
  have hW_re_log : Tendsto (fun U : ℝ => U * (W U - 1).re) atTop (𝓝 α.re) := by
    have hr := (Complex.continuous_re.tendsto α).comp hW_log
    refine hr.congr fun U => ?_
    dsimp only [Function.comp_apply]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hW_sq_log : Tendsto (fun U : ℝ => U * ‖W U - 1‖ ^ 2) atTop (𝓝 0) := by
    have hn1 := hW_log.norm
    have hn2 : Tendsto (fun U : ℝ => ‖W U - 1‖) atTop (𝓝 0) := by
      have hs1 := (hW_1.sub (tendsto_const_nhds (x := (1 : ℂ)))).norm
      rwa [sub_self, norm_zero] at hs1
    have hm := hn1.mul hn2
    rw [mul_zero] at hm
    refine hm.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with U hU
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hU, sq, mul_assoc]
  have h1_normW : Tendsto (fun U : ℝ => U * (1 - ‖W U‖)) atTop (𝓝 (-α.re)) := by
    have hnum := ((hW_re_log.const_mul (-2)).sub hW_sq_log)
    have hden : Tendsto (fun U : ℝ => 1 + ‖W U‖) atTop (𝓝 2) := by
      have ha1 := (tendsto_const_nhds (x := (1 : ℝ))).add hW_1.norm
      rwa [norm_one, one_add_one_eq_two] at ha1
    have hq := hnum.div hden two_ne_zero
    rw [show (-2 * α.re - 0) / 2 = -α.re by ring] at hq
    refine hq.congr fun U => ?_
    dsimp only [Pi.div_apply]
    have hpos_den : 1 + ‖W U‖ ≠ 0 := by positivity
    have hsq_id : 1 - ‖W U‖ ^ 2 = -2 * (W U - 1).re - ‖W U - 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
      ring
    apply mul_right_cancel₀ hpos_den
    rw [div_mul_cancel₀ _ hpos_den]
    symm
    calc U * (1 - ‖W U‖) * (1 + ‖W U‖) = U * (1 - ‖W U‖ ^ 2) := by ring
      _ = U * (-2 * (W U - 1).re - ‖W U - 1‖ ^ 2) := by rw [hsq_id]
      _ = -2 * (U * (W U - 1).re) - U * ‖W U - 1‖ ^ 2 := by ring
  have hL_eq : ‖(a : ℂ) / (1 - s)‖ = bornLorentzianLimit μ γ k := by
    rw [h1s, norm_div, Complex.norm_real, Real.norm_of_nonneg ha0.le,
      Complex.norm_eq_sqrt_sq_add_sq, re_ofReal_add_ofReal_mul_I', im_ofReal_add_ofReal_mul_I',
      bornLorentzianLimit, ← ha_def, ← hω_def]
  have hα_re : bornLorentzianLimit μ γ k * (-α.re) = bornLogDispersionCoeff μ γ k := by
    have hα_calc : α.re = a / (a ^ 2 + ω ^ 2) - 1 / a := by
      dsimp only [α]
      rw [h1s, h1s0, Complex.sub_re]
      have h1 : (1 / ((a : ℂ) + (ω : ℂ) * Complex.I)).re = a / (a ^ 2 + ω ^ 2) := by
        rw [one_div, Complex.inv_re, Complex.normSq_apply, re_ofReal_add_ofReal_mul_I',
          im_ofReal_add_ofReal_mul_I']
        ring
      have h2 : (1 / (a : ℂ)).re = 1 / a := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      rw [h1, h2]
    rw [hα_calc, bornLorentzianLimit, bornLogDispersionCoeff, ← ha_def, ← hω_def]
    set S : ℝ := a ^ 2 + ω ^ 2 with hS_def
    have hS_pos : 0 < S := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha0) (sq_nonneg _)
    set R_sq : ℝ := Real.sqrt S
    have hR_ne : R_sq ≠ 0 := (Real.sqrt_pos.mpr hS_pos).ne'
    have hpow3 : R_sq ^ 3 = S * R_sq := by
      rw [pow_succ, show R_sq ^ 2 = S by exact Real.sq_sqrt hS_pos.le, mul_comm]
    rw [hpow3]
    field_simp [ha0.ne', hS_pos.ne', hR_ne]
    rw [hS_def]; ring
  rw [← hα_re]
  refine (h1_normW.const_mul (bornLorentzianLimit μ γ k)).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hQ_den_1.eventually_ne zero_ne_one.symm] with U hU1 hQd_ne0
  have hUc_ne : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hU1).ne'
  have h1s_ne : (1 : ℂ) - s ≠ 0 := by
    rw [h1s]; intro h0; have hr := congrArg Complex.re h0
    rw [re_ofReal_add_ofReal_mul_I', Complex.zero_re] at hr; exact ha0.ne' hr
  have h1s0_ne : (1 : ℂ) - s₀ ≠ 0 := by rw [h1s0]; exact Complex.ofReal_ne_zero.mpr ha0.ne'
  have hM_num_ne : M_num U ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero h1s_ne hUc_ne)
  have hM_den_ne : M_den U ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero h1s0_ne hUc_ne)
  have hbp_den_ne : beurlingPrimeSum μ ν γ s₀ U ≠ 0 := fun h0 => by
    apply hQd_ne0; dsimp only [Q_den]; rw [h0, zero_div]
  have hM_ratio_norm : ‖M_num U / M_den U‖ = bornLorentzianLimit μ γ k := by
    have hrat : M_num U / M_den U = ((a : ℂ) / (1 - s)) * Complex.exp ((ω * U : ℝ) * Complex.I) := by
      dsimp only [M_num, M_den]
      have hexp_split : Complex.exp ((1 - s) * (U : ℂ)) =
          Complex.exp ((1 - s₀) * (U : ℂ)) * Complex.exp ((ω * U : ℝ) * Complex.I) := by
        rw [← Complex.exp_add]; congr 1; rw [h1s, h1s0]; push_cast; ring
      rw [hexp_split, h1s0]
      set E0 : ℂ := Complex.exp ((a : ℂ) * (U : ℂ))
      have hE0_ne : E0 ≠ 0 := Complex.exp_ne_zero _
      set E_ph : ℂ := Complex.exp ((ω * U : ℝ) * Complex.I)
      set uc : ℂ := (U : ℂ)
      set wc : ℂ := 1 - s
      set ac : ℂ := (a : ℂ)
      have hac_ne : ac ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
      field_simp [h1s_ne, hac_ne, hUc_ne, hE0_ne]
    rw [hrat, norm_mul, hL_eq, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hbc_eq : beurlingBornCoefficient μ ν γ k U = (M_num U / M_den U) * W U := by
    rw [beurlingBornCoefficient]; dsimp only [W, Q_num, Q_den, s, s₀, ω]
    set bn : ℂ := beurlingPrimeSum μ ν γ (((2 * μ : ℝ) : ℂ) - (((k : ℝ) * γ : ℝ) : ℂ) * Complex.I) U
    set bd : ℂ := beurlingPrimeSum μ ν γ ((2 * μ : ℝ) : ℂ) U
    set mn : ℂ := M_num U
    set md : ℂ := M_den U
    field_simp [hM_num_ne, hM_den_ne, hbp_den_ne]
  have hbc_norm : ‖beurlingBornCoefficient μ ν γ k U‖ = bornLorentzianLimit μ γ k * ‖W U‖ := by
    rw [hbc_eq, norm_mul, hM_ratio_norm]
  rw [hbc_norm]
  ring

/-! ### Section 2: Sharp finite-cutoff sub-unit rigidity (`N = 3` sharp threshold) and lossless single-mode prime & mass reconstruction -/

/-- **Sharp resonance degeneration at `N = 2` (`primes 2 = {2, 3}`):** at the nonzero clock
`t_res = 2π / (log 3 - log 2) ≠ 0`, `‖bornCoefficient σ t_res 1 2‖ = 1` for every `σ ∈ ℝ`. -/
theorem norm_bornCoefficient_two_eq_one_at_resonance (σ : ℝ) :
    let t_res : ℝ := 2 * Real.pi / (Real.log 3 - Real.log 2)
    t_res ≠ 0 ∧ ‖bornCoefficient σ t_res 1 2‖ = 1 := by
  intro t_res
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hdiff_pos : 0 < Real.log 3 - Real.log 2 := sub_pos.mpr hlog23
  have ht_pos : 0 < t_res := div_pos (by positivity [Real.pi_pos]) hdiff_pos
  refine ⟨ht_pos.ne', ?_⟩
  have hprimes2 : primes 2 = {2, 3} := by
    ext p
    simp only [primes, Nat.mem_primesBelow, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hlt, hp⟩
      have hge2 := hp.two_le
      interval_cases p
      · left; rfl
      · right; rfl
      · exfalso; exact absurd hp (by decide)
    · rintro (rfl | rfl)
      · exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨by omega, Nat.prime_three⟩
  have hph_eq : (phase t_res 3 : ℂ) ^ (-(1 : ℤ)) = (phase t_res 2 : ℂ) ^ (-(1 : ℤ)) := by
    simp only [zpow_neg, zpow_one, phase, ← Circle.coe_inv, ← Circle.exp_neg, neg_neg]
    have h3 : t_res * Real.log 3 = t_res * Real.log 2 + 2 * Real.pi := by
      dsimp only [t_res]
      field_simp [hdiff_pos.ne']
      ring
    rw [Circle.coe_exp, Circle.coe_exp, Nat.cast_ofNat, Nat.cast_ofNat, h3,
      Complex.ofReal_add, add_mul, Complex.exp_add,
      show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * ↑Real.pi * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I, mul_one]
  have hbm_pos : 0 < bornMass σ 2 := by
    rw [bornMass, hprimes2, Finset.sum_pair (by decide)]
    exact add_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
  set u_ph : ℂ := (phase t_res 2 : ℂ) ^ (-(1 : ℤ))
  have hu_norm : ‖u_ph‖ = 1 := by
    dsimp only [u_ph]
    rw [norm_zpow, Circle.norm_coe, one_zpow]
  have hbc : bornCoefficient σ t_res 1 2 = u_ph := by
    have hw_ne : ((bornMass σ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbm_pos.ne'
    rw [bornCoefficient_eq_sum, hprimes2, Finset.sum_pair (by decide), hph_eq]
    change ((bornWeight σ 2 : ℂ) * u_ph + (bornWeight σ 3 : ℂ) * u_ph) / (bornMass σ 2 : ℂ) = u_ph
    have hbm_eq : ((bornMass σ 2 : ℝ) : ℂ) = (bornWeight σ 2 : ℂ) + (bornWeight σ 3 : ℂ) := by
      rw [bornMass, hprimes2, Finset.sum_pair (by decide), Complex.ofReal_add]
    rw [← add_mul, ← hbm_eq]
    exact mul_div_cancel_left₀ u_ph hw_ne
  rw [hbc, hu_norm]

private theorem int_abs_eq_nat (z : ℤ) :
    ∃ a : ℕ, (a : ℝ) = |(z : ℝ)| ∧ (z ≠ 0 → 1 ≤ a) := by
  rcases Int.eq_nat_or_neg z with ⟨a, rfl | rfl⟩
  · refine ⟨a, ?_, fun hz => by omega⟩
    push_cast
    exact (abs_of_nonneg (Nat.cast_nonneg a)).symm
  · refine ⟨a, ?_, fun hz => by omega⟩
    push_cast
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg a)]

private theorem not_phase_eq_three_and_five {t : ℝ} (ht : t ≠ 0) {k : ℤ} (hk : k ≠ 0) :
    ¬ ((phase t 2 : ℂ) ^ (-k) = (phase t 3 : ℂ) ^ (-k) ∧
       (phase t 2 : ℂ) ^ (-k) = (phase t 5 : ℂ) ^ (-k)) := by
  rintro ⟨h23, h25⟩
  set ω : ℝ := (k : ℝ) * t with hω_def
  have hω_ne : ω ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hk) ht
  have hph_exp : ∀ p : ℕ, (phase t p : ℂ) ^ (-k) = Complex.exp ((ω * Real.log p : ℝ) * Complex.I) := by
    intro p
    rw [phase, ← Circle.coe_zpow, ← Circle.exp_intCast_mul, Circle.coe_exp]
    congr 2
    rw [hω_def, Int.cast_neg]
    ring
  have hcos_one : ∀ q : ℕ, (phase t 2 : ℂ) ^ (-k) = (phase t q : ℂ) ^ (-k) →
      ∃ m : ℤ, (m : ℝ) * (2 * Real.pi) = ω * (Real.log (q : ℝ) - Real.log ((2 : ℕ) : ℝ)) := by
    intro q heq
    rw [hph_exp 2, hph_exp q] at heq
    have hdiv : Complex.exp ((ω * (Real.log (q : ℝ) - Real.log ((2 : ℕ) : ℝ)) : ℝ) * Complex.I) = 1 := by
      have h1 : Complex.exp ((ω * (Real.log (q : ℝ) - Real.log ((2 : ℕ) : ℝ)) : ℝ) * Complex.I) =
          Complex.exp ((ω * Real.log (q : ℝ) : ℝ) * Complex.I) /
            Complex.exp ((ω * Real.log ((2 : ℕ) : ℝ) : ℝ) * Complex.I) := by
        rw [← Complex.exp_sub]; congr 1; push_cast; ring
      rw [h1, ← heq, div_self (Complex.exp_ne_zero _)]
    have hre := congrArg Complex.re hdiv
    rw [Complex.exp_mul_I, Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
      Complex.sin_ofReal_re, Complex.I_re, mul_zero, Complex.sin_ofReal_im, Complex.I_im,
      mul_one, sub_zero, add_zero, Complex.one_re] at hre
    exact (Real.cos_eq_one_iff _).mp hre
  obtain ⟨m, hm⟩ := hcos_one 3 h23
  obtain ⟨n, hn⟩ := hcos_one 5 h25
  rw [Nat.cast_ofNat, Nat.cast_ofNat] at hm hn
  have hlog23 : 0 < Real.log 3 - Real.log 2 := sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))
  have hlog25 : 0 < Real.log 5 - Real.log 2 := sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))
  have h2pi_pos : 0 < 2 * Real.pi := by positivity [Real.pi_pos]
  have hm_ne : m ≠ 0 := by
    intro hm0; rw [hm0, Int.cast_zero, zero_mul] at hm
    exact (mul_ne_zero hω_ne hlog23.ne') hm.symm
  have hn_ne : n ≠ 0 := by
    intro hn0; rw [hn0, Int.cast_zero, zero_mul] at hn
    exact (mul_ne_zero hω_ne hlog25.ne') hn.symm
  obtain ⟨a, ha_abs, ha_ge⟩ := int_abs_eq_nat m
  obtain ⟨b, hb_abs, hb_ge⟩ := int_abs_eq_nat n
  have ha1 : 1 ≤ a := ha_ge hm_ne
  have hm_abs : (a : ℝ) * (2 * Real.pi) = |ω| * (Real.log 3 - Real.log 2) := by
    have h := congrArg abs hm
    rw [abs_mul, abs_of_pos h2pi_pos, abs_mul, abs_of_pos hlog23, ← ha_abs] at h
    exact h
  have hn_abs : (b : ℝ) * (2 * Real.pi) = |ω| * (Real.log 5 - Real.log 2) := by
    have h := congrArg abs hn
    rw [abs_mul, abs_of_pos h2pi_pos, abs_mul, abs_of_pos hlog25, ← hb_abs] at h
    exact h
  have hcross : (b : ℝ) * (Real.log 3 - Real.log 2) = (a : ℝ) * (Real.log 5 - Real.log 2) := by
    apply mul_right_cancel₀ h2pi_pos.ne'
    calc (b : ℝ) * (Real.log 3 - Real.log 2) * (2 * Real.pi)
        = ((b : ℝ) * (2 * Real.pi)) * (Real.log 3 - Real.log 2) := by ring
      _ = (|ω| * (Real.log 5 - Real.log 2)) * (Real.log 3 - Real.log 2) := by rw [hn_abs]
      _ = (|ω| * (Real.log 3 - Real.log 2)) * (Real.log 5 - Real.log 2) := by ring
      _ = ((a : ℝ) * (2 * Real.pi)) * (Real.log 5 - Real.log 2) := by rw [hm_abs]
      _ = (a : ℝ) * (Real.log 5 - Real.log 2) * (2 * Real.pi) := by ring
  have hlogs : (b : ℝ) * Real.log 3 + (a : ℝ) * Real.log 2 =
      (a : ℝ) * Real.log 5 + (b : ℝ) * Real.log 2 := by linarith only [hcross]
  have hexp_eq := congrArg Real.exp hlogs
  rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3),
    Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log (by norm_num : (0 : ℝ) < 5)] at hexp_eq
  have hnat_eq : 3 ^ b * 2 ^ a = 5 ^ a * 2 ^ b := by exact_mod_cast hexp_eq
  have hdvd5 : 5 ∣ 3 ^ b * 2 ^ a := by
    rw [hnat_eq]
    exact dvd_mul_of_dvd_left (dvd_pow_self 5 (by omega)) _
  rcases Nat.Prime.dvd_mul (by decide : Nat.Prime 5) |>.mp hdvd5 with h53 | h52
  · have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) h53; omega
  · have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) h52; omega

private theorem norm_add_lt_of_unit_ne {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    {z₁ z₂ : ℂ} (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (hne : z₁ ≠ z₂) :
    ‖(w₁ : ℂ) * z₁ + (w₂ : ℂ) * z₂‖ < w₁ + w₂ := by
  have hns1 : z₁.re * z₁.re + z₁.im * z₁.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z₁
    rw [hz₁, one_pow, Complex.normSq_apply] at h; exact h
  have hns2 : z₂.re * z₂.re + z₂.im * z₂.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z₂
    rw [hz₂, one_pow, Complex.normSq_apply] at h; exact h
  have hdiff_pos : 0 < Complex.normSq (z₁ - z₂) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hdiff_pos
  have hdot_lt : z₁.re * z₂.re + z₁.im * z₂.im < 1 := by
    linarith only [hns1, hns2, hdiff_pos]
  have hsq_lt : ‖(w₁ : ℂ) * z₁ + (w₂ : ℂ) * z₂‖ ^ 2 < (w₁ + w₂) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    have hexp : (w₁ * z₁.re + w₂ * z₂.re) * (w₁ * z₁.re + w₂ * z₂.re) +
        (w₁ * z₁.im + w₂ * z₂.im) * (w₁ * z₁.im + w₂ * z₂.im) =
        w₁ ^ 2 * (z₁.re * z₁.re + z₁.im * z₁.im) +
          w₂ ^ 2 * (z₂.re * z₂.re + z₂.im * z₂.im) +
          2 * w₁ * w₂ * (z₁.re * z₂.re + z₁.im * z₂.im) := by ring
    rw [hexp, hns1, hns2, mul_one, mul_one]
    have hprod_pos : 0 < 2 * w₁ * w₂ := by positivity
    have hm := mul_lt_mul_of_pos_left hdot_lt hprod_pos
    linarith only [hm, show (w₁ + w₂) ^ 2 = w₁ ^ 2 + w₂ ^ 2 + 2 * w₁ * w₂ * 1 by ring]
  nlinarith only [hsq_lt, norm_nonneg ((w₁ : ℂ) * z₁ + (w₂ : ℂ) * z₂), hw₁, hw₂]

/-- **Universal strict finite-cutoff sub-unit modulus for all `N ≥ 3`:**
for **every** `σ ∈ ℝ`, **every** nonzero clock `t ≠ 0`, **every** nonzero Fourier index `k ≠ 0`,
and **every** cutoff `N ≥ 3`, `‖bornCoefficient σ t k N‖ < 1` and
`(phase t (N + 3))^{-k} - bornCoefficient σ t k N ≠ 0`. -/
theorem norm_bornCoefficient_lt_one_of_three_le (σ : ℝ) {t : ℝ} (ht : t ≠ 0)
    {k : ℤ} (hk : k ≠ 0) {N : ℕ} (hN : 3 ≤ N) :
    ‖bornCoefficient σ t k N‖ < 1 ∧
      (phase t (N + 3) : ℂ) ^ (-k) - bornCoefficient σ t k N ≠ 0 := by
  have hlt1 : ‖bornCoefficient σ t k N‖ < 1 := by
    have hnot := not_phase_eq_three_and_five ht hk
    have hq_ex : ∃ q : ℕ, q ∈ primes N ∧ q ≠ 2 ∧
        (phase t 2 : ℂ) ^ (-k) ≠ (phase t q : ℂ) ^ (-k) := by
      by_cases h23 : (phase t 2 : ℂ) ^ (-k) = (phase t 3 : ℂ) ^ (-k)
      · refine ⟨5, Nat.mem_primesBelow.mpr ⟨by omega, by decide⟩, by decide, ?_⟩
        exact fun h25 => hnot ⟨h23, h25⟩
      · exact ⟨3, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_three⟩, by decide, h23⟩
    obtain ⟨q, hq_mem, hq_ne2, hph_ne⟩ := hq_ex
    have h2_mem : 2 ∈ primes N := Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
    set R : Finset ℕ := (primes N).erase 2 |>.erase q
    have hq_er : q ∈ (primes N).erase 2 := Finset.mem_erase.mpr ⟨hq_ne2, hq_mem⟩
    have hsum_num : (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) =
        ((bornWeight σ 2 : ℂ) * (phase t 2 : ℂ) ^ (-k) +
          (bornWeight σ q : ℂ) * (phase t q : ℂ) ^ (-k)) +
          ∑ p ∈ R, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k) := by
      rw [← Finset.add_sum_erase _ _ h2_mem, ← Finset.add_sum_erase _ _ hq_er, add_assoc]
    have hsum_den : bornMass σ N = (bornWeight σ 2 + bornWeight σ q) + ∑ p ∈ R, bornWeight σ p := by
      rw [bornMass, ← Finset.add_sum_erase _ _ h2_mem, ← Finset.add_sum_erase _ _ hq_er, add_assoc]
    have hw2 : 0 < bornWeight σ 2 := Real.rpow_pos_of_pos (by norm_num) _
    have hwq : 0 < bornWeight σ q :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.mem_primesBelow.mp hq_mem).2.pos) _
    have hpair_lt := norm_add_lt_of_unit_ne hw2 hwq
      (by rw [norm_zpow, Circle.norm_coe, one_zpow])
      (by rw [norm_zpow, Circle.norm_coe, one_zpow]) hph_ne
    have hrest_le : ‖∑ p ∈ R, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)‖ ≤
        ∑ p ∈ R, bornWeight σ p := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      have hwp : 0 ≤ bornWeight σ p := Real.rpow_nonneg (Nat.cast_nonneg p) _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hwp, norm_zpow, Circle.norm_coe,
        one_zpow, mul_one]
    have hbm_pos : 0 < bornMass σ N := by
      rw [hsum_den]
      exact add_pos_of_pos_of_nonneg (add_pos hw2 hwq)
        (Finset.sum_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    rw [bornCoefficient_eq_sum, norm_div, Complex.norm_real, Real.norm_of_nonneg hbm_pos.le,
      div_lt_one hbm_pos, hsum_num, hsum_den]
    exact (norm_add_le _ _).trans_lt (add_lt_add_of_lt_of_le hpair_lt hrest_le)
  refine ⟨hlt1, fun hsub0 => ?_⟩
  have heq := sub_eq_zero.mp hsub0
  have hn := congrArg norm heq
  rw [norm_zpow, Circle.norm_coe, one_zpow] at hn
  linarith only [hlt1, hn]

/-- Single-mode step extraction operator built **purely** from consecutive values of one Fourier
mode `bornCoefficient σ t k` and the deterministic phase `(phase t (j + 3))^{-k}`. -/
def bornStepExtraction (σ t : ℝ) (k : ℤ) (j : ℕ) : ℂ :=
  (bornCoefficient σ t k (j + 1) - bornCoefficient σ t k j) /
    ((phase t (j + 3) : ℂ) ^ (-k) - bornCoefficient σ t k j)

/-- Exact single-mode reconstructed Born mass on `[3, N)`, defined **solely** from
`bornCoefficient σ t k` and `phase t` without referencing `primes` or `Nat.Prime`. -/
def reconstructedBornMass (σ t : ℝ) (k : ℤ) (N : ℕ) : ℝ :=
  ((2 : ℝ) ^ (-(2 * σ)) + (3 : ℝ) ^ (-(2 * σ)) + (5 : ℝ) ^ (-(2 * σ))) *
    ∏ j ∈ Finset.Ico 3 N, (1 - (bornStepExtraction σ t k j).re)⁻¹

/-- Exact single-mode extracted prime Chebyshev sum, defined **solely** from
`bornCoefficient σ t k` and `phase t` without referencing `primes`, `Nat.Prime`, or `Chebyshev`. -/
def bornExtractedTheta (σ t : ℝ) (k : ℤ) (N : ℕ) : ℝ :=
  Real.log 2 + Real.log 3 + Real.log 5 +
    ∑ j ∈ Finset.Ico 3 N,
      ((j + 3 : ℕ) : ℝ) ^ (2 * σ) * Real.log ((j + 3 : ℕ) : ℝ) *
        (reconstructedBornMass σ t k (j + 1) - reconstructedBornMass σ t k j)

/-- Exact single-mode dyadic critical-weight window on `(N / 2, N]`, defined **solely** from
`bornCoefficient σ t k` and `phase t`. -/
def bornModeDyadicWindow (σ t : ℝ) (k : ℤ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc (N / 2) N,
    (m : ℝ) ^ (2 * σ - 1 / 2) * Real.log (m : ℝ) *
      (reconstructedBornMass σ t k (m - 2) - reconstructedBornMass σ t k (m - 3))

private theorem primes_succ_of_not_prime {j : ℕ} (hnp : ¬ (j + 3).Prime) :
    primes (j + 1) = primes j := by
  ext p
  simp only [primes, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hlt, hp⟩
    by_cases heq : p = j + 3
    · subst heq; exact absurd hp hnp
    · exact ⟨by omega, hp⟩
  · rintro ⟨hlt, hp⟩
    exact ⟨by omega, hp⟩

private theorem primes_succ_of_prime {j : ℕ} (hp : (j + 3).Prime) :
    primes (j + 1) = insert (j + 3) (primes j) ∧ j + 3 ∉ primes j := by
  refine ⟨?_, fun hm => (Nat.mem_primesBelow.mp hm).1.ne rfl⟩
  ext p
  simp only [primes, Nat.mem_primesBelow, Finset.mem_insert]
  constructor
  · rintro ⟨hlt, hpp⟩
    by_cases heq : p = j + 3
    · exact Or.inl heq
    · exact Or.inr ⟨by omega, hpp⟩
  · rintro (rfl | ⟨hlt, hpp⟩)
    · exact ⟨by omega, hp⟩
    · exact ⟨by omega, hpp⟩

/-- **Exact single-mode step identity (`j ≥ 3`, `t ≠ 0`, `k ≠ 0`):**
1. `bornStepExtraction σ t k j = ((bornWeight σ (j + 3) / bornMass σ (j + 1) : ℝ) : ℂ)` when
   `(j + 3)` is prime, and `0` otherwise;
2. `1 - bornStepExtraction σ t k j = ((bornMass σ j / bornMass σ (j + 1) : ℝ) : ℂ)`;
3. `(j + 3)` is prime **if and only if** `bornCoefficient σ t k (j + 1) ≠ bornCoefficient σ t k j`. -/
theorem bornStepExtraction_eq_and_prime_iff (σ : ℝ) {t : ℝ} (ht : t ≠ 0)
    {k : ℤ} (hk : k ≠ 0) {j : ℕ} (hj : 3 ≤ j) :
    bornStepExtraction σ t k j =
        (if (j + 3).Prime then ((bornWeight σ (j + 3) / bornMass σ (j + 1) : ℝ) : ℂ) else 0) ∧
      1 - (bornStepExtraction σ t k j).re = bornMass σ j / bornMass σ (j + 1) ∧
      ((j + 3).Prime ↔ bornCoefficient σ t k (j + 1) ≠ bornCoefficient σ t k j) := by
  have hden_ne := (norm_bornCoefficient_lt_one_of_three_le σ ht hk hj).2
  have hbm_pos : ∀ n : ℕ, 0 < bornMass σ n := fun n => by
    apply sum_pos' (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    exact ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩, Real.rpow_pos_of_pos (by norm_num) _⟩
  by_cases hp : (j + 3).Prime
  · obtain ⟨hpr_ins, hpr_not⟩ := primes_succ_of_prime hp
    have hbm_succ : bornMass σ (j + 1) = bornWeight σ (j + 3) + bornMass σ j := by
      rw [bornMass, hpr_ins, Finset.sum_insert hpr_not, bornMass]
    have hnum_step : bornCoefficient σ t k (j + 1) - bornCoefficient σ t k j =
        ((bornWeight σ (j + 3) / bornMass σ (j + 1) : ℝ) : ℂ) *
          ((phase t (j + 3) : ℂ) ^ (-k) - bornCoefficient σ t k j) := by
      have hm_j : (bornMass σ j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hbm_pos j).ne'
      have hm_s : (bornMass σ (j + 1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hbm_pos (j + 1)).ne'
      rw [bornCoefficient_eq_sum σ t k (j + 1), hpr_ins, Finset.sum_insert hpr_not, hbm_succ]
      set S_j : ℂ := ∑ p ∈ primes j, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)
      have hbc_j : S_j = bornCoefficient σ t k j * (bornMass σ j : ℂ) := by
        rw [bornCoefficient_eq_sum, div_mul_cancel₀ _ hm_j]
      rw [hbc_j, Complex.ofReal_div, Complex.ofReal_add]
      set wq : ℂ := (bornWeight σ (j + 3) : ℂ)
      set mj : ℂ := (bornMass σ j : ℂ)
      set bc : ℂ := bornCoefficient σ t k j
      set zq : ℂ := (phase t (j + 3) : ℂ) ^ (-k)
      have hms' : wq + mj ≠ 0 := by
        rw [← Complex.ofReal_add, ← hbm_succ]; exact hm_s
      field_simp [hms']
      ring
    have hext : bornStepExtraction σ t k j =
        ((bornWeight σ (j + 3) / bornMass σ (j + 1) : ℝ) : ℂ) := by
      rw [bornStepExtraction, hnum_step, mul_div_cancel_right₀ _ hden_ne]
    have hw_pos : 0 < bornWeight σ (j + 3) := Real.rpow_pos_of_pos (by positivity) _
    have hne_step : bornCoefficient σ t k (j + 1) ≠ bornCoefficient σ t k j := by
      intro heq
      rw [heq, sub_self] at hnum_step
      have hw_ne : ((bornWeight σ (j + 3) / bornMass σ (j + 1) : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (div_pos hw_pos (hbm_pos (j + 1))).ne'
      exact mul_ne_zero hw_ne hden_ne hnum_step.symm
    refine ⟨by rw [if_pos hp, hext], ?_, ⟨fun _ => hne_step, fun _ => hp⟩⟩
    rw [hext, Complex.ofReal_re, hbm_succ]
    have hms_r : bornWeight σ (j + 3) + bornMass σ j ≠ 0 := by
      rw [← hbm_succ]; exact (hbm_pos (j + 1)).ne'
    field_simp [hms_r]; ring
  · have hpr_eq := primes_succ_of_not_prime hp
    have hbc_eq : bornCoefficient σ t k (j + 1) = bornCoefficient σ t k j := by
      rw [bornCoefficient_eq_sum, bornCoefficient_eq_sum, bornMass, bornMass, hpr_eq]
    have hbm_eq : bornMass σ (j + 1) = bornMass σ j := by rw [bornMass, bornMass, hpr_eq]
    have hext0 : bornStepExtraction σ t k j = 0 := by
      rw [bornStepExtraction, hbc_eq, sub_self, zero_div]
    refine ⟨by rw [if_neg hp, hext0], ?_, ⟨fun h => absurd h hp, fun hne => absurd hbc_eq hne⟩⟩
    rw [hext0, Complex.zero_re, sub_zero, hbm_eq, div_self (hbm_pos j).ne']

/-- **Lossless single-mode reconstruction of `bornMass`, `Chebyshev.theta`, and
`dyadicWeightedPrimeOnlyWindow`:** for every `σ ∈ ℝ`, `t ≠ 0`, and `k ≠ 0`:
1. `reconstructedBornMass σ t k N = bornMass σ N` for all `N ≥ 3`;
2. `bornExtractedTheta σ t k N = Chebyshev.theta ((N + 2 : ℕ) : ℝ)` for all `N ≥ 3`;
3. `bornModeDyadicWindow σ t k N = RHTower.dyadicWeightedPrimeOnlyWindow N` for all `N ≥ 12`. -/
theorem reconstructedBornMass_and_theta_eq (σ : ℝ) {t : ℝ} (ht : t ≠ 0)
    {k : ℤ} (hk : k ≠ 0) :
    (∀ N : ℕ, 3 ≤ N → reconstructedBornMass σ t k N = bornMass σ N) ∧
      (∀ N : ℕ, 3 ≤ N → bornExtractedTheta σ t k N = Chebyshev.theta ((N + 2 : ℕ) : ℝ)) ∧
      (∀ N : ℕ, 12 ≤ N →
        bornModeDyadicWindow σ t k N = _root_.RHTower.dyadicWeightedPrimeOnlyWindow N) := by
  have hprimes3 : primes 3 = {2, 3, 5} := by
    ext p
    simp only [primes, Nat.mem_primesBelow, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hlt, hp⟩
      have hge2 := hp.two_le
      interval_cases p
      · left; rfl
      · right; left; rfl
      · exfalso; exact absurd hp (by decide)
      · right; right; rfl
    · rintro (rfl | rfl | rfl)
      · exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨by omega, Nat.prime_three⟩
      · exact ⟨by omega, by decide⟩
  have hbm3 : bornMass σ 3 = (2 : ℝ) ^ (-(2 * σ)) + (3 : ℝ) ^ (-(2 * σ)) + (5 : ℝ) ^ (-(2 * σ)) := by
    rw [bornMass, hprimes3, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [bornWeight]; push_cast; ring
  have hbm_pos : ∀ n : ℕ, 0 < bornMass σ n := fun n => by
    apply sum_pos' (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    exact ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩, Real.rpow_pos_of_pos (by norm_num) _⟩
  have hmass : ∀ N : ℕ, 3 ≤ N → reconstructedBornMass σ t k N = bornMass σ N := by
    intro N hN
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
    induction m with
    | zero =>
      simp only [Nat.add_zero, reconstructedBornMass, Finset.Ico_self, Finset.prod_empty, mul_one, hbm3]
    | succ m ih =>
      have hm3 : 3 ≤ 3 + m := by omega
      rw [reconstructedBornMass, show 3 + (m + 1) = (3 + m) + 1 by omega,
        Finset.prod_Ico_succ_top hm3, ← mul_assoc, ← reconstructedBornMass, ih hm3,
        (bornStepExtraction_eq_and_prime_iff σ ht hk hm3).2.1, inv_div,
        mul_div_cancel₀ _ (hbm_pos (3 + m)).ne']
  have hmass_step : ∀ j : ℕ, 3 ≤ j →
      reconstructedBornMass σ t k (j + 1) - reconstructedBornMass σ t k j =
        if (j + 3).Prime then ((j + 3 : ℕ) : ℝ) ^ (-(2 * σ)) else 0 := by
    intro j hj
    rw [hmass (j + 1) (by omega), hmass j hj]
    by_cases hp : (j + 3).Prime
    · obtain ⟨hins, hnot⟩ := primes_succ_of_prime hp
      rw [if_pos hp, bornMass, hins, Finset.sum_insert hnot, ← bornMass, add_sub_cancel_right]
      rfl
    · rw [if_neg hp, bornMass, primes_succ_of_not_prime hp, ← bornMass, sub_self]
  have htheta3 : Chebyshev.theta ((3 + 2 : ℕ) : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [Chebyshev.theta, Nat.floor_natCast]
    have hfilt : (Finset.Ioc 0 (3 + 2)).filter Nat.Prime = {2, 3, 5} := by decide
    rw [hfilt, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    push_cast; ring
  have htheta : ∀ N : ℕ, 3 ≤ N → bornExtractedTheta σ t k N = Chebyshev.theta ((N + 2 : ℕ) : ℝ) := by
    intro N hN
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
    induction m with
    | zero =>
      simp only [bornExtractedTheta, Finset.Ico_self, Finset.sum_empty, add_zero, htheta3]
    | succ m ih =>
      have hm3 : 3 ≤ 3 + m := by omega
      rw [bornExtractedTheta, show 3 + (m + 1) = (3 + m) + 1 by omega,
        Finset.sum_Ico_succ_top hm3, ← add_assoc, ← bornExtractedTheta, ih hm3,
        hmass_step (3 + m) hm3]
      have hth_step : Chebyshev.theta ((((3 + m) + 1 + 2 : ℕ) : ℝ)) =
          Chebyshev.theta (((3 + m + 2 : ℕ) : ℝ)) +
            if (3 + m + 3).Prime then Real.log (((3 + m + 3 : ℕ) : ℝ)) else 0 := by
        rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast, Nat.floor_natCast,
          show (3 + m) + 1 + 2 = (3 + m + 2) + 1 by omega,
          Finset.sum_filter, Finset.sum_filter,
          Finset.sum_Ioc_succ_top (Nat.zero_le _), show (3 + m + 2) + 1 = 3 + m + 3 by omega]
      rw [hth_step]
      congr 1
      split_ifs with hp
      · have hpos : (0 : ℝ) < ((3 + m + 3 : ℕ) : ℝ) := by positivity
        calc ((3 + m + 3 : ℕ) : ℝ) ^ (2 * σ) * Real.log ((3 + m + 3 : ℕ) : ℝ) *
              ((3 + m + 3 : ℕ) : ℝ) ^ (-(2 * σ))
            = (((3 + m + 3 : ℕ) : ℝ) ^ (2 * σ) * ((3 + m + 3 : ℕ) : ℝ) ^ (-(2 * σ))) *
                Real.log ((3 + m + 3 : ℕ) : ℝ) := by ring
          _ = Real.log ((3 + m + 3 : ℕ) : ℝ) := by
                rw [← Real.rpow_add hpos, add_neg_cancel, Real.rpow_zero, one_mul]
      · ring
  refine ⟨hmass, htheta, fun N hN => ?_⟩
  rw [bornModeDyadicWindow, _root_.RHTower.dyadicWeightedPrimeOnlyWindow, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm_gt : N / 2 < m := (Finset.mem_Ioc.mp hm).1
  have hm_ge7 : 7 ≤ m := by omega
  have hj3 : 3 ≤ m - 3 := by omega
  have hm_sub : m - 2 = (m - 3) + 1 := by omega
  have hm_add : (m - 3) + 3 = m := by omega
  rw [hm_sub, hmass_step (m - 3) hj3, hm_add]
  split_ifs with hp
  · have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    calc (m : ℝ) ^ (2 * σ - 1 / 2) * Real.log (m : ℝ) * (m : ℝ) ^ (-(2 * σ))
        = ((m : ℝ) ^ (2 * σ - 1 / 2) * (m : ℝ) ^ (-(2 * σ))) * Real.log (m : ℝ) := by ring
      _ = (m : ℝ) ^ (-1 / 2 : ℝ) * Real.log (m : ℝ) := by
            rw [← Real.rpow_add hm_pos, show (2 * σ - 1 / 2) + -(2 * σ) = (-1 / 2 : ℝ) by ring]
      _ = Real.log (m : ℝ) / Real.sqrt (m : ℝ) := by
            rw [show (-1 / 2 : ℝ) = -((1 / 2 : ℝ)) by ring, Real.rpow_neg hm_pos.le,
              ← Real.sqrt_eq_rpow, inv_mul_eq_div]
  · ring

/-! ### Section 3: Using `ζ(ρ) = 0` (without setting `Re ρ = 1 / 2`) to force strict positive power-scaled deficit & excess, vs. zero limit under `RiemannHypothesis` -/

private theorem one_sub_re_le_zeroReSup_of_left_zero {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1 / 2) (hζ : riemannZeta ρ = 0) :
    1 - ρ.re ≤ _root_.RHTower.zeroReSup := by
  set w : ℂ := 1 - ρ
  have hw_re : w.re = 1 - ρ.re := by simp [w]
  have hw0 : 0 < w.re := by linarith only [hw_re, hρ1]
  have hw1 : w.re < 1 := by linarith only [hw_re, hρ0]
  have hw_ne1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hw1; exact lt_irrefl 1 hw1
  have hζw : riemannZeta w = 0 :=
    _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ hρ0 (by linarith only [hρ1])
  have hxiw : _root_.RHTower.xi w = 0 := (_root_.RHTower.xi_eq_zero_iff hw0 hw_ne1).mpr hζw
  obtain ⟨q, hq⟩ := _root_.RHTower.exists_xiZeroCopy_of_xi_eq_zero hxiw
  have hle := _root_.RHTower.re_le_zeroReSup q
  rw [hq, hw_re] at hle
  exact hle

/-- **Using `ζ(ρ) = 0` (without setting `Re ρ = 1 / 2`) to force both power-scaled deficit and
excess of the single prime Fourier mode strictly above `c > 0` at arbitrarily large cutoffs:**
let `ρ ∈ ℂ` be any putative left-hand zero with `0 < Re ρ < 1 / 2` and `riemannZeta ρ = 0`.
Then `ρ.im ≠ 0`, and for **every** nonzero Fourier mode `k₀ ≠ 0` (in particular `k₀ = 1`, the
first prime Fourier mode), **every** exponent `α ∈ (Re ρ, 1 / 2)`, and **every** fixed `c > 0`:
1. There exists a strictly increasing cutoff sequence `φ : ℕ → ℕ` (`Tendsto φ atTop atTop`) such
   that `(φ j + 2)^α · (1 - bornExtractedTheta ρ.re ρ.im k₀ (φ j) / (φ j + 2)) ≥ c` for all `j`;
2. There exists a strictly increasing cutoff sequence `ψ : ℕ → ℕ` (`Tendsto ψ atTop atTop`) such
   that `(ψ j + 2)^α · (bornExtractedTheta ρ.re ρ.im k₀ (ψ j) / (ψ j + 2) - 1) ≥ c` for all `j`;
3. There exists a strictly increasing cutoff sequence `χ : ℕ → ℕ` (`Tendsto χ atTop atTop`) such
   that `(χ j)^α · (bornModeDyadicWindow ρ.re ρ.im k₀ (χ j) / √(χ j) - 2(1 - 1 / √2)) ≥ c` for all `j`. -/
theorem zeta_zero_forces_single_mode_power_deficit_and_excess {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1 / 2) (hζ : riemannZeta ρ = 0)
    {k₀ : ℤ} (hk₀ : k₀ ≠ 0) {α : ℝ} (hα_lo : ρ.re < α) (hα_hi : α < 1 / 2)
    {c : ℝ} (hc : 0 < c) :
    ρ.im ≠ 0 ∧
      (∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
        ∀ j : ℕ,
          c ≤ ((φ j + 2 : ℕ) : ℝ) ^ α *
            (1 - bornExtractedTheta ρ.re ρ.im k₀ (φ j) / ((φ j + 2 : ℕ) : ℝ))) ∧
      (∃ ψ : ℕ → ℕ, Tendsto ψ atTop atTop ∧
        ∀ j : ℕ,
          c ≤ ((ψ j + 2 : ℕ) : ℝ) ^ α *
            (bornExtractedTheta ρ.re ρ.im k₀ (ψ j) / ((ψ j + 2 : ℕ) : ℝ) - 1)) ∧
      (∃ χ : ℕ → ℕ, Tendsto χ atTop atTop ∧
        ∀ j : ℕ,
          c ≤ (χ j : ℝ) ^ α *
            (bornModeDyadicWindow ρ.re ρ.im k₀ (χ j) / Real.sqrt (χ j : ℝ) -
              2 * (1 - (Real.sqrt 2)⁻¹))) := by
  have him_ne : ρ.im ≠ 0 :=
    openStrip_zeta_zero_im_ne_zero ⟨ρ, hρ0, by linarith only [hρ1]⟩ hζ
  obtain ⟨_, htheta_eq, hdyad_eq⟩ := reconstructedBornMass_and_theta_eq ρ.re him_ne hk₀
  have hsup_ge : 1 - ρ.re ≤ _root_.RHTower.zeroReSup :=
    one_sub_re_le_zeroReSup_of_left_zero hρ0 hρ1 hζ
  set b : ℝ := 1 - (ρ.re + α) / 2 with hb_def
  have hb_lt_sup : b < _root_.RHTower.zeroReSup := by linarith only [hb_def, hα_lo, hsup_ge]
  have hb_gt_one_sub_α : 1 - α < b := by linarith only [hb_def, hα_lo]
  have hb_gt_half : 1 / 2 < b := by linarith only [hb_gt_one_sub_α, hα_hi]
  have hgap_pos : 0 < b + α - 1 := by linarith only [hb_gt_one_sub_α]
  -- Part 1: Positive power-scaled deficit `1 - bornExtractedTheta / (N + 2) ≥ c / (N + 2)^α`
  have hfreq_def : ∃ᶠ N : ℕ in atTop,
      c ≤ ((N + 2 : ℕ) : ℝ) ^ α *
        (1 - bornExtractedTheta ρ.re ρ.im k₀ N / ((N + 2 : ℕ) : ℝ)) := by
    rw [Filter.frequently_atTop]
    intro N₀
    have hgrow : Tendsto (fun x : ℝ => (x - 1) ^ (b + α - 1) - 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-1 : ℝ)
        ((tendsto_rpow_atTop hgap_pos).comp (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id))
    have hlow := _root_.RHTower.frequently_chebyshevPsi_sub_lt_neg_rpow hb_lt_sup
    have hev_x := (eventually_ge_atTop (((max N₀ 3 + 3 : ℕ) : ℝ))).and
      (hgrow.eventually_ge_atTop c)
    obtain ⟨x, hx_lt, hx_geN, hx_c⟩ := (hlow.and_eventually hev_x).exists
    have hx_ge6 : (6 : ℝ) ≤ x :=
      le_trans (by exact_mod_cast (by omega : 6 ≤ max N₀ 3 + 3)) hx_geN
    set M : ℕ := ⌊x⌋₊
    have hx_pos : 0 < x := by linarith only [hx_ge6]
    have hM_le_x : (M : ℝ) ≤ x := Nat.floor_le hx_pos.le
    have hx_lt_M1 : x < (M : ℝ) + 1 := Nat.lt_floor_add_one x
    have hM_ge : max N₀ 3 + 3 ≤ M := Nat.le_floor hx_geN
    set N : ℕ := M - 2
    have hN_ge0 : N₀ ≤ N := by have := le_max_left N₀ 3; omega
    have hN_ge3 : 3 ≤ N := by have := le_max_right N₀ 3; omega
    have hN2_eq : N + 2 = M := by omega
    have htheta_fl : Chebyshev.theta x = Chebyshev.theta ((N + 2 : ℕ) : ℝ) := by
      rw [hN2_eq, Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast]
    have hth_le_psi : Chebyshev.theta x ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
    have hdiff_gt : x ^ b - 1 < ((N + 2 : ℕ) : ℝ) - Chebyshev.theta ((N + 2 : ℕ) : ℝ) := by
      rw [← htheta_fl, hN2_eq]
      linarith only [hx_lt, hth_le_psi, hx_lt_M1]
    have hN2_ge1 : (1 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 2)
    have hN2_pos : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
    have hxb_ge : ((N + 2 : ℕ) : ℝ) ^ b ≤ x ^ b := by
      rw [hN2_eq]; exact Real.rpow_le_rpow (by positivity) hM_le_x (by linarith only [hb_gt_half])
    have hx1_le : x - 1 ≤ ((N + 2 : ℕ) : ℝ) := by rw [hN2_eq]; linarith only [hx_lt_M1]
    have hpow_ge : (x - 1) ^ (b + α - 1) ≤ ((N + 2 : ℕ) : ℝ) ^ (b + α - 1) :=
      Real.rpow_le_rpow (by linarith only [hx_ge6]) hx1_le hgap_pos.le
    refine ⟨N, hN_ge0, ?_⟩
    rw [htheta_eq N hN_ge3]
    have hid : ((N + 2 : ℕ) : ℝ) ^ α *
        (1 - Chebyshev.theta ((N + 2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ)) =
        ((N + 2 : ℕ) : ℝ) ^ (α - 1) * (((N + 2 : ℕ) : ℝ) - Chebyshev.theta ((N + 2 : ℕ) : ℝ)) := by
      rw [show α - 1 = α + (-1 : ℝ) by ring, Real.rpow_add hN2_pos, Real.rpow_neg_one]
      field_simp [hN2_pos.ne']
    rw [hid]
    have h1_le : ((N + 2 : ℕ) : ℝ) ^ (α - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN2_ge1 (by linarith only [hα_hi])
    have hrpow_mul : ((N + 2 : ℕ) : ℝ) ^ (α - 1) * ((N + 2 : ℕ) : ℝ) ^ b =
        ((N + 2 : ℕ) : ℝ) ^ (b + α - 1) := by
      rw [← Real.rpow_add hN2_pos]; congr 1; ring
    have hstep : ((N + 2 : ℕ) : ℝ) ^ (b + α - 1) - 1 ≤
        ((N + 2 : ℕ) : ℝ) ^ (α - 1) * (((N + 2 : ℕ) : ℝ) - Chebyshev.theta ((N + 2 : ℕ) : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left (le_trans (sub_le_sub_right hxb_ge 1) hdiff_gt.le)
        (Real.rpow_nonneg hN2_pos.le (α - 1))
      rw [mul_sub, hrpow_mul, mul_one] at hm
      linarith only [hm, h1_le]
    linarith only [hx_c, hpow_ge, hstep]
  -- Part 2: Positive power-scaled excess `bornExtractedTheta / (N + 2) - 1 ≥ c / (N + 2)^α`
  have hfreq_exc : ∃ᶠ N : ℕ in atTop,
      c ≤ ((N + 2 : ℕ) : ℝ) ^ α *
        (bornExtractedTheta ρ.re ρ.im k₀ N / ((N + 2 : ℕ) : ℝ) - 1) := by
    obtain ⟨C_pt, hC_pt⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
    rw [Filter.frequently_atTop]
    intro N₀
    have hb_sub_half : 0 < b - 1 / 2 := sub_pos.mpr hb_gt_half
    have hgrow1 : Tendsto (fun x : ℝ => x ^ (b - 1 / 2)) atTop atTop :=
      tendsto_rpow_atTop hb_sub_half
    have hgrow2 : Tendsto (fun x : ℝ => (1 / 2) * (x / 2) ^ (b + α - 1)) atTop atTop :=
      ((tendsto_rpow_atTop hgap_pos).comp
        (Filter.tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).const_mul_atTop (by norm_num)
    have hhigh := _root_.RHTower.frequently_rpow_lt_chebyshevPsi_sub hb_lt_sup
    have hev_x := ((eventually_ge_atTop (((max N₀ 3 + 4 : ℕ) : ℝ))).and
      (hgrow1.eventually_ge_atTop (2 * max C_pt 0))).and (hgrow2.eventually_ge_atTop c)
    obtain ⟨x, hx_gt, ⟨hx_geN, hx_C⟩, hx_c⟩ := (hhigh.and_eventually hev_x).exists
    have hx_ge7 : (7 : ℝ) ≤ x :=
      le_trans (by exact_mod_cast (by omega : 7 ≤ max N₀ 3 + 4)) hx_geN
    set M : ℕ := ⌊x⌋₊
    have hx_pos : 0 < x := by linarith only [hx_ge7]
    have hM_le_x : (M : ℝ) ≤ x := Nat.floor_le hx_pos.le
    have hM_ge : max N₀ 3 + 4 ≤ M := Nat.le_floor hx_geN
    set N : ℕ := M - 2
    have hN_ge0 : N₀ ≤ N := by have := le_max_left N₀ 3; omega
    have hN_ge3 : 3 ≤ N := by have := le_max_right N₀ 3; omega
    have hN2_eq : N + 2 = M := by omega
    have htheta_fl : Chebyshev.theta x = Chebyshev.theta ((N + 2 : ℕ) : ℝ) := by
      rw [hN2_eq, Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast]
    have hsqrt_le : C_pt * Real.sqrt x ≤ (1 / 2) * x ^ b := by
      have h1 : C_pt * Real.sqrt x ≤ max C_pt 0 * x ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx_pos.le _)
      have h2 : x ^ b = x ^ (b - 1 / 2) * x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hx_pos]; congr 1; ring
      rw [h2]
      have h3 := mul_le_mul_of_nonneg_right hx_C (Real.rpow_nonneg hx_pos.le (1 / 2 : ℝ))
      linarith only [h1, h3]
    have hth_diff : (1 / 2) * x ^ b ≤ Chebyshev.theta ((N + 2 : ℕ) : ℝ) - ((N + 2 : ℕ) : ℝ) := by
      have hpt := hC_pt x
      rw [← htheta_fl, hN2_eq]
      linarith only [hx_gt, hpt, hsqrt_le, hM_le_x]
    have hN2_pos : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
    have hx_half_le : x / 2 ≤ ((N + 2 : ℕ) : ℝ) := by
      rw [hN2_eq]
      have hx_lt_M1 : x < (M : ℝ) + 1 := Nat.lt_floor_add_one x
      have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 4 ≤ M)
      linarith only [hx_lt_M1, hM4]
    have hN2_le_x : ((N + 2 : ℕ) : ℝ) ≤ x := by rwa [hN2_eq]
    have hrpow_inv : x ^ (α - 1) ≤ ((N + 2 : ℕ) : ℝ) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos hN2_pos hN2_le_x (by linarith only [hα_hi])
    refine ⟨N, hN_ge0, ?_⟩
    rw [htheta_eq N hN_ge3]
    have hid : ((N + 2 : ℕ) : ℝ) ^ α *
        (Chebyshev.theta ((N + 2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ) - 1) =
        ((N + 2 : ℕ) : ℝ) ^ (α - 1) * (Chebyshev.theta ((N + 2 : ℕ) : ℝ) - ((N + 2 : ℕ) : ℝ)) := by
      rw [show α - 1 = α + (-1 : ℝ) by ring, Real.rpow_add hN2_pos, Real.rpow_neg_one]
      field_simp [hN2_pos.ne']
    rw [hid]
    have hstep1 : ((N + 2 : ℕ) : ℝ) ^ (α - 1) * ((1 / 2) * x ^ b) ≤
        ((N + 2 : ℕ) : ℝ) ^ (α - 1) * (Chebyshev.theta ((N + 2 : ℕ) : ℝ) - ((N + 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hth_diff (Real.rpow_nonneg hN2_pos.le _)
    have hstep2 : (1 / 2) * x ^ (b + α - 1) ≤ ((N + 2 : ℕ) : ℝ) ^ (α - 1) * ((1 / 2) * x ^ b) := by
      have hx_comb : x ^ (α - 1) * ((1 / 2) * x ^ b) = (1 / 2) * x ^ (b + α - 1) := by
        rw [← mul_left_comm, ← Real.rpow_add hx_pos]; congr 2; ring
      rw [← hx_comb]
      exact mul_le_mul_of_nonneg_right hrpow_inv (by positivity)
    have hstep3 : (1 / 2) * (x / 2) ^ (b + α - 1) ≤ (1 / 2) * x ^ (b + α - 1) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith only [hx_pos]) hgap_pos.le) (by norm_num)
    linarith only [hx_c, hstep3, hstep2, hstep1]
  -- Part 3: Dyadic single-mode window excess via `xiRightCenteredZero_re_le_of_eventually_dyadicWeightedPrimeWindow_upper`
  have hfreq_dyad : ∃ᶠ N : ℕ in atTop,
      c ≤ (N : ℝ) ^ α *
        (bornModeDyadicWindow ρ.re ρ.im k₀ N / Real.sqrt (N : ℝ) - 2 * (1 - (Real.sqrt 2)⁻¹)) := by
    by_contra hnot_freq
    rw [Filter.not_frequently, Filter.eventually_atTop] at hnot_freq
    obtain ⟨N₁, hN₁⟩ := hnot_freq
    set α' : ℝ := (ρ.re + α) / 2 with hα'_def
    have hα'_gt : ρ.re < α' := by linarith only [hα'_def, hα_lo]
    have hα'_lt : α' < α := by linarith only [hα'_def, hα_lo]
    have hβ_pos : 0 < 1 / 2 - α' := by linarith only [hα'_lt, hα_hi]
    have hlog_sub : Tendsto (fun n : ℕ => 2 * Real.sqrt 2 * Real.log (n : ℝ) / (n : ℝ) ^ (1 / 2 - α'))
        atTop (𝓝 0) := by
      have h0 := ((isLittleO_log_rpow_atTop hβ_pos).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop).const_mul (2 * Real.sqrt 2)
      rw [mul_zero] at h0
      exact h0.congr fun n => by dsimp only [Function.comp_apply]; ring
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hlog_sub.eventually (gt_mem_nhds zero_lt_one))
    set N_cut : ℕ := max (max N₁ N₂) 12
    have hwin : ∀ n : ℕ, N_cut ≤ n →
        _root_.RHTower.dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt (n : ℝ) + (c + 1) * (n : ℝ) ^ (1 / 2 - α') := by
      intro n hn
      have hn12 : 12 ≤ n := (le_max_right _ 12).trans hn
      have hn1 : N₁ ≤ n := ((le_max_left N₁ N₂).trans (le_max_left _ 12)).trans hn
      have hn2 : N₂ ≤ n := ((le_max_right N₁ N₂).trans (le_max_left _ 12)).trans hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
      have hno := not_le.mp (hN₁ n hn1)
      rw [hdyad_eq n hn12] at hno
      have hpo_le : _root_.RHTower.dyadicWeightedPrimeOnlyWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt (n : ℝ) + c * (n : ℝ) ^ (1 / 2 - α) := by
        have h1 : _root_.RHTower.dyadicWeightedPrimeOnlyWindow n / Real.sqrt (n : ℝ) -
            2 * (1 - (Real.sqrt 2)⁻¹) < c / (n : ℝ) ^ α :=
          (lt_div_iff₀' (Real.rpow_pos_of_pos hn_pos α)).mpr hno
        have h2 := mul_lt_mul_of_pos_right h1 hsq_pos
        rw [sub_mul, div_mul_cancel₀ _ hsq_pos.ne'] at h2
        have hpow_eq : c / (n : ℝ) ^ α * Real.sqrt (n : ℝ) = c * (n : ℝ) ^ (1 / 2 - α) := by
          rw [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_assoc, ← Real.rpow_neg hn_pos.le,
            ← Real.rpow_add hn_pos]
          congr 2; ring
        rw [hpow_eq] at h2
        linarith only [h2]
      have hpo_le' : c * (n : ℝ) ^ (1 / 2 - α) ≤ c * (n : ℝ) ^ (1 / 2 - α') :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hn_ge1 (by linarith only [hα'_lt])) hc.le
      have hpp_le : _root_.RHTower.dyadicWeightedHigherPrimePowerWindow n ≤
          (n : ℝ) ^ (1 / 2 - α') := by
        have hlog := _root_.RHTower.dyadicWeightedHigherPrimePowerWindow_le_log (by omega : 1 ≤ n)
        have hlt1 := hN₂ n hn2
        have hle1 : 2 * Real.sqrt 2 * Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 - α') := by
          have := (div_lt_one (Real.rpow_pos_of_pos hn_pos _)).mp hlt1
          exact this.le
        exact hlog.trans hle1
      rw [_root_.RHTower.dyadicWeightedPrimeWindow_eq_primeOnly_add_higherPrimePower]
      linarith only [hpo_le, hpo_le', hpp_le]
    set w : ℂ := 1 - ρ
    have hw_re : w.re = 1 - ρ.re := by simp [w]
    have hw0 : 0 < w.re := by linarith only [hw_re, hρ1]
    have hw1 : w.re < 1 := by linarith only [hw_re, hρ0]
    have hw_half : 1 / 2 < w.re := by linarith only [hw_re, hρ1]
    have hw_ne1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hw1; exact lt_irrefl 1 hw1
    have hζw : riemannZeta w = 0 :=
      _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ hρ0 (by linarith only [hρ1])
    have hxiw : _root_.RHTower.xi w = 0 := (_root_.RHTower.xi_eq_zero_iff hw0 hw_ne1).mpr hζw
    let sup_w : _root_.RHTower.XiDivisorSupport :=
      ⟨w, _root_.RHTower.mem_xi_divisor_support_of_eq_zero hxiw⟩
    have hdiv_pos := _root_.RHTower.xi_divisor_pos_on_support sup_w
    let q : _root_.RHTower.XiZeroCopy := ⟨sup_w, ⟨0, by omega⟩⟩
    have hq_right : 0 < (Complex.I * _root_.RHTower.xiSpectralPoint q).re := by
      have hc : Complex.I * _root_.RHTower.xiSpectralPoint q = w - 1 / 2 := by
        simpa only [q, sup_w] using _root_.RHTower.I_mul_xiSpectralPoint q
      rw [hc, Complex.sub_re]
      norm_num
      linarith only [hw_half]
    let qr : _root_.RHTower.XiRightZeroCopy := ⟨q, hq_right⟩
    have hqb := _root_.RHTower.xiRightCenteredZero_re_le_of_eventually_dyadicWeightedPrimeWindow_upper
      (N := N_cut) (C := c + 1) (alpha := 1 / 2 - α') hβ_pos.le (by positivity) hwin qr
    have hqr_re : (_root_.RHTower.xiRightCenteredZero qr).re = w.re - 1 / 2 := by
      change (Complex.I * _root_.RHTower.xiSpectralPoint q).re = _
      have hc : Complex.I * _root_.RHTower.xiSpectralPoint q = w - 1 / 2 := by
        simpa only [q, sup_w] using _root_.RHTower.I_mul_xiSpectralPoint q
      rw [hc, Complex.sub_re]; norm_num
    rw [hqr_re, hw_re] at hqb
    linarith only [hqb, hα'_gt]
  obtain ⟨φ, hφ_mono, hφ⟩ := Filter.extraction_of_frequently_atTop hfreq_def
  obtain ⟨ψ, hψ_mono, hψ⟩ := Filter.extraction_of_frequently_atTop hfreq_exc
  obtain ⟨χ, hχ_mono, hχ⟩ := Filter.extraction_of_frequently_atTop hfreq_dyad
  exact ⟨him_ne, ⟨φ, hφ_mono.tendsto_atTop, hφ⟩, ⟨ψ, hψ_mono.tendsto_atTop, hψ⟩,
    ⟨χ, hχ_mono.tendsto_atTop, hχ⟩⟩

/-- **Under `RiemannHypothesis`, the `(N + 2)^α`-scaled single-mode deficit converges to `0`
for every `α < 1 / 2` and every `(σ, t, k₀)` (`t ≠ 0`, `k₀ ≠ 0`):** proving non-vacuity of the
zero-forced positive excess in `zeta_zero_forces_single_mode_power_deficit_and_excess`. -/
theorem rh_single_mode_power_deficit_tendsto_zero (hRH : RiemannHypothesis)
    (σ : ℝ) {t : ℝ} (ht : t ≠ 0) {k₀ : ℤ} (hk₀ : k₀ ≠ 0) {α : ℝ} (hα : α < 1 / 2) :
    Tendsto (fun N : ℕ =>
      ((N + 2 : ℕ) : ℝ) ^ α *
        (1 - bornExtractedTheta σ t k₀ N / ((N + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
  obtain ⟨_, htheta_eq, _⟩ := reconstructedBornMass_and_theta_eq σ ht hk₀
  set ε : ℝ := (1 / 2 - α) / 2 with hε_def
  have hε_pos : 0 < ε := by linarith only [hε_def, hα]
  obtain ⟨C_psi, hC_psi0, hC_psi⟩ :=
    _root_.RHTower.Sieve.exists_chebyshevPsiReal_error_power_bound hRH hε_pos
  obtain ⟨C_pt, hC_pt⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set K : ℝ := C_psi + max C_pt 0
  have hmaj : Tendsto (fun N : ℕ => K * ((N + 2 : ℕ) : ℝ) ^ (-ε)) atTop (𝓝 0) := by
    have hx_top : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    have h0 := (tendsto_rpow_neg_atTop hε_pos).comp hx_top |>.const_mul K
    rwa [mul_zero] at h0
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 3] with N hN3
  rw [htheta_eq N hN3, Real.norm_eq_abs]
  set x : ℝ := ((N + 2 : ℕ) : ℝ)
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast (by omega : 1 ≤ N + 2)
  have hx_pos : 0 < x := zero_lt_one.trans_le hx1
  have hpsi_eq : _root_.RHTower.chebyshevPsiReal x = Chebyshev.psi x :=
    _root_.RHTower.chebyshevPsiReal_eq_psi x
  have hpsi_b := hC_psi x hx1
  rw [hpsi_eq] at hpsi_b
  have hth_b : |x - Chebyshev.theta x| ≤ K * x ^ (1 / 2 + ε) := by
    have hle1 := Chebyshev.theta_le_psi x
    have hle2 := hC_pt x
    have hpt_abs : |Chebyshev.psi x - Chebyshev.theta x| ≤ max C_pt 0 * x ^ (1 / 2 + ε) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hle1)]
      calc Chebyshev.psi x - Chebyshev.theta x
          ≤ C_pt * Real.sqrt x := hle2
        _ ≤ max C_pt 0 * x ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx_pos.le _)
        _ ≤ max C_pt 0 * x ^ (1 / 2 + ε) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hε_pos])) (le_max_right _ _)
    have htri : |x - Chebyshev.theta x| ≤
        |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
      rw [abs_sub_comm x (Chebyshev.theta x),
        show Chebyshev.theta x - x = (Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x) by ring]
      exact abs_sub _ _
    dsimp only [K]
    linarith only [htri, hpsi_b, hpt_abs, show (C_psi + max C_pt 0) * x ^ (1 / 2 + ε) =
      C_psi * x ^ (1 / 2 + ε) + max C_pt 0 * x ^ (1 / 2 + ε) by ring]
  have hid : |x ^ α * (1 - Chebyshev.theta x / x)| = x ^ (α - 1) * |x - Chebyshev.theta x| := by
    have h1 : x ^ α * (1 - Chebyshev.theta x / x) = x ^ (α - 1) * (x - Chebyshev.theta x) := by
      rw [show α - 1 = α + (-1 : ℝ) by ring, Real.rpow_add hx_pos, Real.rpow_neg_one]
      field_simp [hx_pos.ne']
    rw [h1, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx_pos _)]
  rw [hid]
  have hK_nn : 0 ≤ K := add_nonneg hC_psi0.le (le_max_right _ _)
  have hexp_eq : x ^ (α - 1) * (K * x ^ (1 / 2 + ε)) = K * x ^ (-ε) := by
    rw [mul_left_comm, ← Real.rpow_add hx_pos]
    congr 2
    linarith only [hε_def]
  rw [← hexp_eq]
  exact mul_le_mul_of_nonneg_left hth_b (Real.rpow_nonneg hx_pos.le _)

/-- **Non-vacuous fixed-parameter RH equivalence via a single subcritical prime Fourier mode:**
at **any** fixed real exponent `σ ∈ ℝ`, **any** fixed nonzero clock `t ≠ 0`, and **any** fixed
nonzero Fourier index `k₀ ≠ 0` (for example `σ = 1 / 4`, `t = 200`, `k₀ = 1` — with **no**
quantification over putative off-critical zeros), `RiemannHypothesis` is unconditionally
equivalent to convergence of `(N + 2)^α · (1 - bornExtractedTheta σ t k₀ N / (N + 2))` to `0`
for all `α < 1 / 2`. -/
theorem rh_iff_fixed_point_single_mode_power_deficit (σ : ℝ) {t : ℝ} (ht : t ≠ 0)
    {k₀ : ℤ} (hk₀ : k₀ ≠ 0) :
    RiemannHypothesis ↔
      ∀ α : ℝ, α < 1 / 2 →
        Tendsto (fun N : ℕ =>
          ((N + 2 : ℕ) : ℝ) ^ α *
            (1 - bornExtractedTheta σ t k₀ N / ((N + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
  constructor
  · exact fun hRH α hα => rh_single_mode_power_deficit_tendsto_zero hRH σ ht hk₀ hα
  · intro hlim
    rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
    intro w hw_half hw_one hζw
    set ρ : ℂ := 1 - w
    have hρ_re : ρ.re = 1 - w.re := by simp [ρ]
    have hρ0 : 0 < ρ.re := by linarith only [hρ_re, hw_one]
    have hρ1 : ρ.re < 1 / 2 := by linarith only [hρ_re, hw_half]
    have hζρ : riemannZeta ρ = 0 :=
      _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζw
        (by linarith only [hw_half]) hw_one
    set α : ℝ := (ρ.re + 1 / 2) / 2
    have hα_lo : ρ.re < α := by dsimp only [α]; linarith only [hρ1]
    have hα_hi : α < 1 / 2 := by dsimp only [α]; linarith only [hρ1]
    obtain ⟨him_ne, ⟨φ, hφ, hφ_ge⟩, _, _⟩ :=
      zeta_zero_forces_single_mode_power_deficit_and_excess hρ0 hρ1 hζρ hk₀ hα_lo hα_hi zero_lt_one
    obtain ⟨_, hth_σ, _⟩ := reconstructedBornMass_and_theta_eq σ ht hk₀
    obtain ⟨_, hth_ρ, _⟩ := reconstructedBornMass_and_theta_eq ρ.re him_ne hk₀
    have hlim_φ := (hlim α hα_hi).comp hφ
    have hev_lt := hlim_φ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    have hev_3 := hφ.eventually_ge_atTop 3
    obtain ⟨j, hj_lt, hj_3⟩ := (hev_lt.and hev_3).exists
    dsimp only [Function.comp_apply] at hj_lt
    have heq_th : bornExtractedTheta σ t k₀ (φ j) = bornExtractedTheta ρ.re ρ.im k₀ (φ j) := by
      rw [hth_σ (φ j) hj_3, hth_ρ (φ j) hj_3]
    rw [heq_th] at hj_lt
    linarith only [hφ_ge j, hj_lt]

/-- **Under `RiemannHypothesis` on the lower quarter-strip `0 < σ ≤ 1 / 4` (including
`[2401 / 19200, 1 / 4]`), the direct unreconstructed smooth-subtracted Born Fourier mode
`(N + 2)^α · ‖bornCoefficient σ t k N - smoothBornCoefficient σ t k N‖` converges to `0` for
every `α < 1 / 2`:** below `σ = 1 / 4` (`Re(2σ) ≤ 1 / 2`), no lower-endpoint constant offset
enters `smoothBornCoefficient`. -/
theorem rh_quarter_bornCoefficient_sub_smooth_power_tendsto_zero (hRH : RiemannHypothesis)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ_q : σ ≤ 1 / 4) (t : ℝ) (k : ℤ) {α : ℝ} (hα : α < 1 / 2) :
    Tendsto (fun N : ℕ =>
      ((N + 2 : ℕ) : ℝ) ^ α *
        ‖bornCoefficient σ t k N - smoothBornCoefficient σ t k N‖) atTop (𝓝 0) := by
  have hσ1 : σ < 1 / 2 := by linarith only [hσ_q]
  set a : ℝ := 1 - 2 * σ with ha_def
  have ha0 : 0 < a := by linarith only [ha_def, hσ1]
  have ha1 : a < 1 := by linarith only [ha_def, hσ0]
  set ε : ℝ := (1 / 2 - α) / 3 with hε_def
  have hε_pos : 0 < ε := by linarith only [hε_def, hα]
  obtain ⟨C_psi, hC_psi0, hC_psi⟩ :=
    _root_.RHTower.Sieve.exists_chebyshevPsiReal_error_power_bound hRH hε_pos
  obtain ⟨C_pt, hC_pt⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set K_e : ℝ := C_psi + max C_pt 0
  have hK_e_pos : 0 < K_e := add_pos_of_pos_of_nonneg hC_psi0 (le_max_right _ _)
  have htheta_err : ∀ u : ℝ, 2 ≤ u → |_root_.RHTower.thetaError u| ≤ K_e * u ^ (-1 / 2 + ε) := by
    intro u hu2
    have hu1 : 1 ≤ u := by linarith only [hu2]
    have hu_pos : 0 < u := by linarith only [hu2]
    have hpsi_b := hC_psi u hu1
    rw [_root_.RHTower.chebyshevPsiReal_eq_psi] at hpsi_b
    have hle1 := Chebyshev.theta_le_psi u
    have hpt_b : |Chebyshev.psi u - Chebyshev.theta u| ≤ max C_pt 0 * u ^ (1 / 2 + ε) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hle1)]
      calc Chebyshev.psi u - Chebyshev.theta u
          ≤ C_pt * Real.sqrt u := hC_pt u
        _ ≤ max C_pt 0 * u ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hu_pos.le _)
        _ ≤ max C_pt 0 * u ^ (1 / 2 + ε) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith only [hε_pos])) (le_max_right _ _)
    have hth_b : |Chebyshev.theta u - u| ≤ K_e * u ^ (1 / 2 + ε) := by
      have htri : |Chebyshev.theta u - u| ≤
          |Chebyshev.psi u - u| + |Chebyshev.psi u - Chebyshev.theta u| := by
        rw [show Chebyshev.theta u - u =
            (Chebyshev.psi u - u) - (Chebyshev.psi u - Chebyshev.theta u) by ring]
        exact abs_sub _ _
      dsimp only [K_e]
      linarith only [htri, hpsi_b, hpt_b, show (C_psi + max C_pt 0) * u ^ (1 / 2 + ε) =
        C_psi * u ^ (1 / 2 + ε) + max C_pt 0 * u ^ (1 / 2 + ε) by ring]
    have herr_eq : _root_.RHTower.thetaError u = (Chebyshev.theta u - u) / u := by
      have ht := _root_.RHTower.theta_eq_mul_thetaError hu_pos
      field_simp [hu_pos.ne']
      linarith only [ht]
    rw [herr_eq, abs_div, abs_of_pos hu_pos]
    calc |Chebyshev.theta u - u| / u
        ≤ (K_e * u ^ (1 / 2 + ε)) / u := div_le_div_of_nonneg_right hth_b hu_pos.le
      _ = K_e * (u ^ (1 / 2 + ε) * u ^ (-1 : ℝ)) := by
            rw [Real.rpow_neg_one]; ring
      _ = K_e * u ^ (-1 / 2 + ε) := by
            rw [← Real.rpow_add hu_pos]; congr 2; ring
  let x : ℕ → ℝ := fun N => ((N + 2 : ℕ) : ℝ)
  have hx_top : Tendsto x atTop atTop := by
    simpa only [x, Nat.cast_add, Nat.cast_ofNat] using
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  let sc : ℕ → ℝ := fun N => a * Real.log (x N) / (x N) ^ a
  let s : ℂ := ((2 * σ : ℝ) : ℂ) - (((k : ℝ) * t : ℝ) : ℂ) * Complex.I
  let s₀ : ℂ := ((2 * σ : ℝ) : ℂ)
  let U : ℕ → ℂ := fun N =>
    (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) * (sc N : ℂ)
  let U_sm : ℕ → ℂ := fun N => smoothPrimeSum s (x N) * (sc N : ℂ)
  let V : ℕ → ℂ := fun N => (bornMass σ N : ℂ) * (sc N : ℂ)
  let V_sm : ℕ → ℂ := fun N => smoothPrimeSum s₀ (x N) * (sc N : ℂ)
  have hrem_pow : ∀ {α' : ℝ}, α' < 1 / 2 → ∀ z : ℂ, z.re = 2 * σ → z ≠ 0 → z ≠ 1 →
      Tendsto (fun N : ℕ =>
        (x N) ^ α' *
          ‖_root_.RHTower.primeCpowAbelPrimitive z (x N) * (_root_.RHTower.thetaError (x N) : ℂ) -
            ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
              _root_.RHTower.primeCpowAbelKernel z u‖ * sc N) atTop (𝓝 0) := by
    intro α' hα' z hz_re _ _
    set ε' : ℝ := (1 / 2 - α') / 3 with hε'_def
    have hε'_pos : 0 < ε' := by linarith only [hε'_def, hα']
    obtain ⟨C_psi', hC_psi0', hC_psi'⟩ :=
      _root_.RHTower.Sieve.exists_chebyshevPsiReal_error_power_bound hRH hε'_pos
    set K_e' : ℝ := C_psi' + max C_pt 0
    have htheta_err' : ∀ u : ℝ, 2 ≤ u → |_root_.RHTower.thetaError u| ≤ K_e' * u ^ (-1 / 2 + ε') := by
      intro u hu2
      have hu1 : 1 ≤ u := by linarith only [hu2]
      have hu_pos : 0 < u := by linarith only [hu2]
      have hpsi_b := hC_psi' u hu1
      rw [_root_.RHTower.chebyshevPsiReal_eq_psi] at hpsi_b
      have hle1 := Chebyshev.theta_le_psi u
      have hpt_b : |Chebyshev.psi u - Chebyshev.theta u| ≤ max C_pt 0 * u ^ (1 / 2 + ε') := by
        rw [abs_of_nonneg (sub_nonneg.mpr hle1)]
        calc Chebyshev.psi u - Chebyshev.theta u
            ≤ C_pt * Real.sqrt u := hC_pt u
          _ ≤ max C_pt 0 * u ^ (1 / 2 : ℝ) := by
              rw [Real.sqrt_eq_rpow]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hu_pos.le _)
          _ ≤ max C_pt 0 * u ^ (1 / 2 + ε') :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith only [hε'_pos])) (le_max_right _ _)
      have hth_b : |Chebyshev.theta u - u| ≤ K_e' * u ^ (1 / 2 + ε') := by
        have htri : |Chebyshev.theta u - u| ≤
            |Chebyshev.psi u - u| + |Chebyshev.psi u - Chebyshev.theta u| := by
          rw [show Chebyshev.theta u - u =
              (Chebyshev.psi u - u) - (Chebyshev.psi u - Chebyshev.theta u) by ring]
          exact abs_sub _ _
        dsimp only [K_e']
        linarith only [htri, hpsi_b, hpt_b, show (C_psi' + max C_pt 0) * u ^ (1 / 2 + ε') =
          C_psi' * u ^ (1 / 2 + ε') + max C_pt 0 * u ^ (1 / 2 + ε') by ring]
      have herr_eq : _root_.RHTower.thetaError u = (Chebyshev.theta u - u) / u := by
        have ht := _root_.RHTower.theta_eq_mul_thetaError hu_pos
        field_simp [hu_pos.ne']
        linarith only [ht]
      rw [herr_eq, abs_div, abs_of_pos hu_pos]
      calc |Chebyshev.theta u - u| / u
          ≤ (K_e' * u ^ (1 / 2 + ε')) / u := div_le_div_of_nonneg_right hth_b hu_pos.le
        _ = K_e' * (u ^ (1 / 2 + ε') * u ^ (-1 : ℝ)) := by rw [Real.rpow_neg_one]; ring
        _ = K_e' * u ^ (-1 / 2 + ε') := by rw [← Real.rpow_add hu_pos]; congr 2; ring
    set p : ℝ := 1 / 2 + ε' - 2 * σ with hp_def
    have hp_pos : 0 < p := by linarith only [hp_def, hσ_q, hε'_pos]
    set Cz : ℝ := ‖z‖ + 1 / Real.log 2
    have hCz_pos : 0 < Cz := add_pos_of_nonneg_of_pos (norm_nonneg _)
      (div_pos zero_lt_one (Real.log_pos (by norm_num)))
    set K_tot : ℝ := a * K_e' + a * K_e' * Cz / (p * Real.log 2)
    have hmaj_z : Tendsto (fun N : ℕ =>
        K_tot * (Real.log (x N) / (x N) ^ ε') * (x N) ^ (-ε')) atTop (𝓝 0) := by
      have h1 := ((isLittleO_log_rpow_atTop hε'_pos).tendsto_div_nhds_zero.comp hx_top).const_mul K_tot
      have h2 := (tendsto_rpow_neg_atTop hε'_pos).comp hx_top
      have hm := h1.mul h2
      rw [mul_zero] at hm
      exact hm.congr fun N => by dsimp only [Function.comp_apply]
    refine squeeze_zero' (by
      filter_upwards [eventually_ge_atTop 2] with N _
      have hx2 : 2 ≤ x N := by dsimp only [x]; exact_mod_cast (by omega : 2 ≤ N + 2)
      have hsc_nn : 0 ≤ sc N := by
        dsimp only [sc]
        exact div_nonneg (mul_nonneg ha0.le (Real.log_nonneg (by linarith only [hx2])))
          (Real.rpow_nonneg (by linarith only [hx2]) a)
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith only [hx2]) α') (norm_nonneg _)) hsc_nn)
      ?_ hmaj_z
    filter_upwards [eventually_ge_atTop 2] with N _
    have hx4 : 4 ≤ x N := by dsimp only [x]; exact_mod_cast (by omega : 4 ≤ N + 2)
    have hx2 : 2 ≤ x N := by linarith only [hx4]
    have hx1 : 1 < x N := by linarith only [hx4]
    have hx_pos : 0 < x N := zero_lt_one.trans hx1
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogx_pos : 0 < Real.log (x N) := Real.log_pos hx1
    have hlogx_ge1 : 1 ≤ Real.log (x N) := by
      have hexp4 : Real.exp 1 ≤ x N := by have := Real.exp_one_lt_d9; linarith only [this, hx4]
      have h := Real.log_le_log (Real.exp_pos 1) hexp4
      rwa [Real.log_exp] at h
    have hK_e'_pos : 0 < K_e' := add_pos_of_pos_of_nonneg hC_psi0' (le_max_right _ _)
    have hbnd1 : ‖_root_.RHTower.primeCpowAbelPrimitive z (x N) *
        (_root_.RHTower.thetaError (x N) : ℂ)‖ ≤
        K_e' * (x N) ^ (a - 1 / 2 + ε') / Real.log (x N) := by
      rw [norm_mul, _root_.RHTower.norm_primeCpowAbelPrimitive hx1, Complex.norm_real,
        Real.norm_eq_abs, show 1 - z.re = a by linarith only [hz_re, ha_def]]
      calc (x N) ^ a / Real.log (x N) * |_root_.RHTower.thetaError (x N)|
          ≤ (x N) ^ a / Real.log (x N) * (K_e' * (x N) ^ (-1 / 2 + ε')) :=
            mul_le_mul_of_nonneg_left (htheta_err' (x N) hx2) (by positivity)
        _ = K_e' * ((x N) ^ a * (x N) ^ (-1 / 2 + ε')) / Real.log (x N) := by ring
        _ = K_e' * (x N) ^ (a - 1 / 2 + ε') / Real.log (x N) := by
              rw [← Real.rpow_add hx_pos]; congr 3; ring
    have hrpow_int : IntervalIntegrable (fun u : ℝ => u ^ (p - 1)) volume 2 (x N) :=
      (ContinuousOn.rpow_const (fun _ _ => continuousWithinAt_id) fun u hu =>
        Or.inl (by rw [Set.mem_Icc] at hu; change u ≠ 0; linarith only [hu.1])).intervalIntegrable_of_Icc hx2
    have hrpow_val : (∫ u in (2 : ℝ)..(x N), u ^ (p - 1)) ≤ (x N) ^ p / p := by
      have hd : ∀ u ∈ Set.uIcc 2 (x N), HasDerivAt (fun y : ℝ => y ^ p / p) (u ^ (p - 1)) u := by
        intro u hu; rw [Set.uIcc_of_le hx2] at hu
        have hu0 : 0 < u := by linarith only [hu.1]
        have h := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hu0.ne')).div_const p
        rwa [mul_div_cancel_left₀ _ hp_pos.ne'] at h
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hrpow_int]
      have h2_nn : 0 ≤ (2 : ℝ) ^ p / p := by positivity
      linarith only [h2_nn]
    have hbnd2 : ‖∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
        _root_.RHTower.primeCpowAbelKernel z u‖ ≤
        (K_e' * Cz / Real.log 2) * ((x N) ^ p / p) := by
      have hmono := intervalIntegral.integral_mono_on hx2
        (_root_.RHTower.intervalIntegrable_thetaError_mul_primeCpowAbelKernel z hx2).norm
        (hrpow_int.const_mul (K_e' * Cz / Real.log 2)) fun u hu => by
          have hu2 : 2 ≤ u := hu.1
          have hu_pos : 0 < u := by linarith only [hu2]
          have hlog_ge : Real.log 2 ≤ Real.log u := Real.log_le_log zero_lt_two hu2
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have he := htheta_err' u hu2
          have hK := _root_.RHTower.norm_primeCpowAbelKernel_le z hu2
          rw [hz_re] at hK
          have hlog_div : u ^ (-(2 * σ)) / Real.log u ≤ u ^ (-(2 * σ)) / Real.log 2 :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg hu_pos.le _) hlog2_pos hlog_ge
          calc |_root_.RHTower.thetaError u| * ‖_root_.RHTower.primeCpowAbelKernel z u‖
              ≤ (K_e' * u ^ (-1 / 2 + ε')) * (Cz * (u ^ (-(2 * σ)) / Real.log 2)) :=
                mul_le_mul he (hK.trans (mul_le_mul_of_nonneg_left hlog_div hCz_pos.le))
                  (norm_nonneg _) (by positivity)
            _ = (K_e' * Cz / Real.log 2) * (u ^ (-1 / 2 + ε') * u ^ (-(2 * σ))) := by ring
            _ = (K_e' * Cz / Real.log 2) * u ^ (p - 1) := by
                  rw [← Real.rpow_add hu_pos]; congr 2; linarith only [hp_def]
      rw [intervalIntegral.integral_const_mul] at hmono
      exact (intervalIntegral.norm_integral_le_integral_norm hx2).trans
        (hmono.trans (mul_le_mul_of_nonneg_left hrpow_val (by positivity)))
    have hpa_eq : p = a - 1 / 2 + ε' := by linarith only [hp_def, ha_def]
    have htot : ‖_root_.RHTower.primeCpowAbelPrimitive z (x N) *
        (_root_.RHTower.thetaError (x N) : ℂ) -
        ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
          _root_.RHTower.primeCpowAbelKernel z u‖ ≤
        (K_e' + K_e' * Cz / (p * Real.log 2)) * (x N) ^ p := by
      rw [← hpa_eq] at hbnd1
      have hbnd1' : K_e' * (x N) ^ p / Real.log (x N) ≤ K_e' * (x N) ^ p :=
        div_le_self (by positivity) hlogx_ge1
      refine (norm_sub_le _ _).trans ((add_le_add (hbnd1.trans hbnd1') hbnd2).trans_eq ?_)
      ring
    dsimp only [sc]
    have hpow_id : (x N) ^ α' * (x N) ^ p / (x N) ^ a = (1 / (x N) ^ ε') * (x N) ^ (-ε') := by
      rw [← Real.rpow_add hx_pos, div_eq_mul_inv, ← Real.rpow_neg hx_pos.le,
        ← Real.rpow_add hx_pos, one_div, ← Real.rpow_neg hx_pos.le, ← Real.rpow_add hx_pos]
      congr 1
      linarith only [hpa_eq, hε'_def]
    calc (x N) ^ α' *
          ‖_root_.RHTower.primeCpowAbelPrimitive z (x N) *
              (_root_.RHTower.thetaError (x N) : ℂ) -
            ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
              _root_.RHTower.primeCpowAbelKernel z u‖ *
            (a * Real.log (x N) / (x N) ^ a)
        ≤ (x N) ^ α' * ((K_e' + K_e' * Cz / (p * Real.log 2)) * (x N) ^ p) *
            (a * Real.log (x N) / (x N) ^ a) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htot (Real.rpow_nonneg hx_pos.le _)) (by positivity)
      _ = K_tot * Real.log (x N) * ((x N) ^ α' * (x N) ^ p / (x N) ^ a) := by
            dsimp only [K_tot]; ring
      _ = K_tot * (Real.log (x N) / (x N) ^ ε') * (x N) ^ (-ε') := by
            rw [hpow_id]; ring
  have hs_re : s.re = 2 * σ := by
    simp only [s, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]; ring
  have hs0_re : s₀.re = 2 * σ := by simp [s₀]
  have hs_ne0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hs_re] at this; linarith
  have hs_ne1 : s ≠ 1 := fun h => by have := congrArg Complex.re h; simp [hs_re] at this; linarith
  have hs0_ne0 : s₀ ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hs0_re] at this; linarith
  have hs0_ne1 : s₀ ≠ 1 := fun h => by have := congrArg Complex.re h; simp [hs0_re] at this; linarith
  have hU_diff : Tendsto (fun N : ℕ => (x N) ^ α * ‖U N - U_sm N‖) atTop (𝓝 0) := by
    refine (hrem_pow hα s hs_re hs_ne0 hs_ne1).congr fun N => ?_
    dsimp only [U, U_sm, sc, smoothPrimeSum]
    have hx2 : 2 ≤ x N := by dsimp only [x]; exact_mod_cast (by omega : 2 ≤ N + 2)
    have hsc_pos : 0 ≤ a * Real.log (x N) / (x N) ^ a := by
      have : 0 < Real.log (x N) := Real.log_pos (by linarith only [hx2])
      have : 0 < (x N) ^ a := Real.rpow_pos_of_pos (by linarith only [hx2]) a
      positivity
    have hps_eq : (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) =
        (2 : ℂ) ^ (-s) + _root_.RHTower.primeCpowSumIoc s (x N) := by
      have hpr : primes N = insert 2 ((Finset.Ioc 2 (N + 2)).filter Nat.Prime) := by
        ext p; simp only [primes, Nat.mem_primesBelow, Finset.mem_insert, Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨hlt, hp⟩; by_cases h2 : p = 2
          · exact Or.inl h2
          · exact Or.inr ⟨⟨by have := hp.two_le; omega, by omega⟩, hp⟩
        · rintro (rfl | ⟨⟨_, hle⟩, hp⟩)
          · exact ⟨by omega, Nat.prime_two⟩
          · exact ⟨by omega, hp⟩
      rw [hpr, Finset.sum_insert (by simp)]
      have hsum_cpow : ∀ p : ℕ, 0 < p →
          (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k) = (p : ℂ) ^ (-s) := by
        intro p hp
        have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp
        have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
        have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
          rw [← Complex.ofReal_natCast, Complex.ofReal_log hp_pos.le]
        rw [bornWeight, Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, phase, Circle.coe_exp,
          ← Complex.exp_int_mul, ← Complex.exp_add, Complex.cpow_def_of_ne_zero hp_ne, hlog]
        congr 1; dsimp only [s]; push_cast; ring
      congr 1
      · exact hsum_cpow 2 (by norm_num)
      · rw [_root_.RHTower.primeCpowSumIoc, show ⌊x N⌋₊ = N + 2 by dsimp only [x]; exact Nat.floor_natCast _,
          Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hp : p.Prime
        · rw [if_pos hp, if_pos hp]; exact hsum_cpow p hp.pos
        · rw [if_neg hp, if_neg hp]
    have hid : (∑ p ∈ primes N, (bornWeight σ p : ℂ) * (phase t p : ℂ) ^ (-k)) -
        ((2 : ℂ) ^ (-s) + (x N : ℂ) ^ (1 - s) / ((1 - s) * (Real.log (x N) : ℂ)) -
          _root_.RHTower.primeCpowAbelWeight s 2 * (Chebyshev.theta 2 : ℂ) -
          s / (1 - s) * _root_.RHTower.primeCpowAbelPrimitive s 2 +
          1 / (1 - s) * _root_.RHTower.primeCpowLogSqIntegral s (x N)) =
        _root_.RHTower.primeCpowAbelPrimitive s (x N) * (_root_.RHTower.thetaError (x N) : ℂ) -
          ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
            _root_.RHTower.primeCpowAbelKernel s u := by
      rw [hps_eq]
      have hm := _root_.RHTower.primeCpowSumIoc_sub_main hs_ne0 hs_ne1 hx2
      dsimp only [x, s] at hm ⊢
      linear_combination hm
    rw [← sub_mul, hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsc_pos]
    ring
  have hV_diff_any : ∀ {α' : ℝ}, α' < 1 / 2 →
      Tendsto (fun N : ℕ => (x N) ^ α' * ‖V N - V_sm N‖) atTop (𝓝 0) := by
    intro α' hα'
    refine (hrem_pow hα' s₀ hs0_re hs0_ne0 hs0_ne1).congr fun N => ?_
    dsimp only [V, V_sm, sc, smoothPrimeSum]
    have hx2 : 2 ≤ x N := by dsimp only [x]; exact_mod_cast (by omega : 2 ≤ N + 2)
    have hsc_pos : 0 ≤ a * Real.log (x N) / (x N) ^ a := by
      have : 0 < Real.log (x N) := Real.log_pos (by linarith only [hx2])
      have : 0 < (x N) ^ a := Real.rpow_pos_of_pos (by linarith only [hx2]) a
      positivity
    have hps0_eq : (bornMass σ N : ℂ) =
        (2 : ℂ) ^ (-s₀) + _root_.RHTower.primeCpowSumIoc s₀ (x N) := by
      have hpr : primes N = insert 2 ((Finset.Ioc 2 (N + 2)).filter Nat.Prime) := by
        ext p; simp only [primes, Nat.mem_primesBelow, Finset.mem_insert, Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨hlt, hp⟩; by_cases h2 : p = 2
          · exact Or.inl h2
          · exact Or.inr ⟨⟨by have := hp.two_le; omega, by omega⟩, hp⟩
        · rintro (rfl | ⟨⟨_, hle⟩, hp⟩)
          · exact ⟨by omega, Nat.prime_two⟩
          · exact ⟨by omega, hp⟩
      rw [bornMass, Complex.ofReal_sum, hpr, Finset.sum_insert (by simp)]
      have hsum_cpow0 : ∀ p : ℕ, 0 < p → (bornWeight σ p : ℂ) = (p : ℂ) ^ (-s₀) := by
        intro p hp
        have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp
        have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
        have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
          rw [← Complex.ofReal_natCast, Complex.ofReal_log hp_pos.le]
        rw [bornWeight, Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp,
          Complex.cpow_def_of_ne_zero hp_ne, hlog]
        congr 1; dsimp only [s₀]; push_cast; ring
      congr 1
      · exact hsum_cpow0 2 (by norm_num)
      · rw [_root_.RHTower.primeCpowSumIoc, show ⌊x N⌋₊ = N + 2 by dsimp only [x]; exact Nat.floor_natCast _,
          Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hp : p.Prime
        · rw [if_pos hp, if_pos hp]; exact hsum_cpow0 p hp.pos
        · rw [if_neg hp, if_neg hp]
    have hid : (bornMass σ N : ℂ) -
        ((2 : ℂ) ^ (-s₀) + (x N : ℂ) ^ (1 - s₀) / ((1 - s₀) * (Real.log (x N) : ℂ)) -
          _root_.RHTower.primeCpowAbelWeight s₀ 2 * (Chebyshev.theta 2 : ℂ) -
          s₀ / (1 - s₀) * _root_.RHTower.primeCpowAbelPrimitive s₀ 2 +
          1 / (1 - s₀) * _root_.RHTower.primeCpowLogSqIntegral s₀ (x N)) =
        _root_.RHTower.primeCpowAbelPrimitive s₀ (x N) * (_root_.RHTower.thetaError (x N) : ℂ) -
          ∫ u in (2 : ℝ)..(x N), (_root_.RHTower.thetaError u : ℂ) *
            _root_.RHTower.primeCpowAbelKernel s₀ u := by
      rw [hps0_eq]
      have hm := _root_.RHTower.primeCpowSumIoc_sub_main hs0_ne0 hs0_ne1 hx2
      dsimp only [x, s₀] at hm ⊢
      linear_combination hm
    rw [← sub_mul, hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsc_pos]
    ring
  have hV_diff := hV_diff_any hα
  have hV_lim : Tendsto V atTop (𝓝 1) := by
    have hm := (powerMass_asymptotic ha0 ha1).comp hx_top
    have hc := (Complex.continuous_ofReal.tendsto 1).comp hm
    rw [Complex.ofReal_one] at hc
    refine hc.congr fun N => ?_
    dsimp only [Function.comp_apply, V, sc, x]
    have hcut : cutoff ((N + 2 : ℕ) : ℝ) = N := by unfold cutoff; rw [Nat.floor_natCast]; omega
    rw [powerMass, hcut, bornMass, ← Complex.ofReal_mul, mul_div_assoc]
    have hsum_eq : (∑ p ∈ primes N, (p : ℝ) ^ (a - 1)) = ∑ p ∈ primes N, bornWeight σ p :=
      Finset.sum_congr rfl fun p _ => by
        rw [bornWeight, show a - 1 = -(2 * σ) by linarith only [ha_def]]
    rw [hsum_eq]
  have hV_sm_lim : Tendsto V_sm atTop (𝓝 1) := by
    have h0 : Tendsto (fun N => V N - V_sm N) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hd := hV_diff_any (by norm_num : (0 : ℝ) < 1 / 2)
      simpa only [Real.rpow_zero, one_mul] using hd
    have hsub := hV_lim.sub h0
    rw [sub_zero] at hsub
    exact hsub.congr fun N => sub_sub_cancel (V N) (V_sm N)
  have hU_bdd : ∀ N : ℕ, ‖U N‖ ≤ ‖V N‖ := by
    intro N
    dsimp only [U, V]
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [bornMass, Complex.ofReal_sum]
    refine (norm_sum_le _ _).trans ?_
    have hpos_sum : 0 ≤ ∑ p ∈ primes N, bornWeight σ p :=
      Finset.sum_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg hpos_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have hbw_nn : 0 ≤ bornWeight σ p := by
      rw [bornWeight]; exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hph_n : ‖(phase t p : ℂ) ^ (-k)‖ = 1 := by
      rw [norm_zpow, Circle.norm_coe, one_zpow]
    have hbw_n : ‖(bornWeight σ p : ℂ)‖ = bornWeight σ p := by
      rw [Complex.norm_real, Real.norm_of_nonneg hbw_nn]
    rw [norm_mul, hbw_n, hph_n, mul_one]
  have hmaj : Tendsto (fun N : ℕ =>
      ((x N) ^ α * ‖U N - U_sm N‖ * ‖V N‖ +
        ‖V N‖ * ((x N) ^ α * ‖V N - V_sm N‖)) /
        (‖V N‖ * ‖V_sm N‖)) atTop (𝓝 0) := by
    have hnum := (hU_diff.mul hV_lim.norm).add (hV_lim.norm.mul hV_diff)
    have hden := hV_lim.norm.mul hV_sm_lim.norm
    rw [norm_one, mul_one, mul_zero, add_zero] at hnum
    rw [norm_one, mul_one] at hden
    have hq := hnum.div hden one_ne_zero
    rwa [zero_div] at hq
  refine squeeze_zero' (by
    filter_upwards [eventually_ge_atTop 0] with N _
    exact mul_nonneg (Real.rpow_nonneg (by positivity) α) (norm_nonneg _)) ?_ hmaj
  filter_upwards [hV_sm_lim.eventually_ne one_ne_zero] with N hVsm_ne
  have hx1 : 1 < x N := by dsimp only [x]; exact_mod_cast (by omega : 1 < N + 2)
  have hlog_pos : 0 < Real.log (x N) := Real.log_pos hx1
  have hxa_pos : 0 < (x N) ^ a := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) a
  have hsc_ne : (sc N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos (mul_pos ha0 hlog_pos) hxa_pos).ne'
  have hbm_pos : 0 < bornMass σ N := by
    apply sum_pos' (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
    exact ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩, Real.rpow_pos_of_pos (by norm_num) _⟩
  have hV_ne : V N ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hbm_pos.ne') hsc_ne
  have hbc_quot : bornCoefficient σ t k N = U N / V N := by
    rw [bornCoefficient_eq_sum]; dsimp only [U, V]; rw [mul_div_mul_right _ _ hsc_ne]
  have hsm_quot : smoothBornCoefficient σ t k N = U_sm N / V_sm N := by
    rw [smoothBornCoefficient]; dsimp only [U_sm, V_sm, s, s₀, x]
    rw [mul_div_mul_right _ _ hsc_ne]
  have hdiff_quot : U N / V N - U_sm N / V_sm N =
      ((U N - U_sm N) * V N + U N * (V_sm N - V N)) / (V N * V_sm N) := by
    set u1 := U N; set u2 := U_sm N; set v1 := V N; set v2 := V_sm N
    field_simp [hV_ne, hVsm_ne]; ring
  rw [hbc_quot, hsm_quot, hdiff_quot, norm_div, norm_mul, mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hxα_nn : 0 ≤ ((N + 2 : ℕ) : ℝ) ^ α := Real.rpow_nonneg (by positivity) α
  calc ((N + 2 : ℕ) : ℝ) ^ α * ‖(U N - U_sm N) * V N + U N * (V_sm N - V N)‖
      ≤ ((N + 2 : ℕ) : ℝ) ^ α *
          (‖(U N - U_sm N) * V N‖ + ‖U N * (V_sm N - V N)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hxα_nn
    _ ≤ ((N + 2 : ℕ) : ℝ) ^ α *
          (‖U N - U_sm N‖ * ‖V N‖ + ‖V N‖ * ‖V N - V_sm N‖) := by
        rw [norm_mul (U N - U_sm N), norm_mul (U N), norm_sub_rev (V_sm N) (V N)]
        exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hU_bdd N) (norm_nonneg _))) hxα_nn
    _ = _ := by dsimp only [x]; ring

private theorem div_le_div_of_le_of_le {a b c d : ℝ}
    (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b) :
    a / b ≤ c / d :=
  (div_le_div_of_nonneg_right hac (hd.trans_le hdb).le).trans
    (div_le_div_of_nonneg_left hc hd hdb)

private theorem sum_Ico_diff_mul_eq {α : Type*} [CommRing α] (f g : ℕ → α) {m K : ℕ} (hmK : m ≤ K) :
    ∑ n ∈ Finset.Ico m K, (f (n + 1) - f n) * g n =
      f K * g K - f m * g m - ∑ n ∈ Finset.Ico m K, f (n + 1) * (g (n + 1) - g n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmK
  induction d with
  | zero => simp
  | succ d ih =>
    have hmd : m ≤ m + d := by omega
    rw [show m + (d + 1) = (m + d) + 1 by omega,
      Finset.sum_Ico_succ_top hmd, Finset.sum_Ico_succ_top hmd, ih hmd]
    ring

private theorem neg_log_one_sub_sub_le_sq {u : ℝ} (hu0 : 0 ≤ u) (hu_half : u ≤ 1 / 2) :
    |-Real.log (1 - u) - u| ≤ u ^ 2 := by
  have hint1 : IntervalIntegrable (fun y : ℝ => y / (1 - y)) volume 0 u := by
    refine (ContinuousOn.div continuousOn_id (continuousOn_const.sub continuousOn_id) ?_).intervalIntegrable_of_Icc hu0
    intro y hy; dsimp only [Pi.sub_apply, id]; linarith only [hy.2, hu_half]
  have hint2 : IntervalIntegrable (fun y : ℝ => 2 * y) volume 0 u :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 u
  have hderiv1 : ∀ y ∈ Set.uIcc 0 u,
      HasDerivAt (fun x : ℝ => -Real.log (1 - x) - x) (y / (1 - y)) y := by
    intro y hy
    rw [Set.uIcc_of_le hu0] at hy
    have h1y : 0 < 1 - y := by linarith only [hy.2, hu_half]
    have hd_sub : HasDerivAt (fun x : ℝ => 1 - x) (-1) y := by
      have h0 : HasDerivAt (fun x : ℝ => 1 - x) (0 - 1) y :=
        (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id' y)
      exact h0.congr_deriv (by ring)
    have hd := ((hd_sub.log h1y.ne').neg).sub (hasDerivAt_id' y)
    refine hd.congr_deriv ?_
    field_simp [h1y.ne']; ring
  have hval1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv1 hint1
  simp only [sub_zero, Real.log_one, neg_zero] at hval1
  have hderiv2 : ∀ y ∈ Set.uIcc 0 u, HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
    intro y _
    exact ((hasDerivAt_id' y).pow 2).congr_deriv (by norm_num)
  have hval2 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2 hint2
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero] at hval2
  have hnonneg : 0 ≤ -Real.log (1 - u) - u := by
    rw [← hval1]
    exact intervalIntegral.integral_nonneg hu0 fun y hy =>
      div_nonneg hy.1 (by linarith only [hy.2, hu_half])
  have hle : -Real.log (1 - u) - u ≤ u ^ 2 := by
    rw [← hval1, ← hval2]
    refine intervalIntegral.integral_mono_on hu0 hint1 hint2 fun y hy => ?_
    have h1y : 1 / 2 ≤ 1 - y := by linarith only [hy.2, hu_half]
    calc y / (1 - y) ≤ y / (1 / 2) :=
          div_le_div_of_nonneg_left hy.1 (by norm_num) h1y
      _ = 2 * y := by ring
  rw [abs_of_nonneg hnonneg]
  exact hle

private theorem abs_exp_sub_one_le_two_abs {r : ℝ} (hr : |r| ≤ 1 / 2) :
    |Real.exp r - 1| ≤ 2 * |r| := by
  have hexp_half_lt2 : Real.exp (1 / 2) ≤ 2 := by
    have hsq : (Real.exp (1 / 2)) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul, show (2 : ℕ) * (1 / 2 : ℝ) = 1 by norm_num]
      have := Real.exp_one_lt_d9
      linarith only [this]
    nlinarith only [hsq, Real.exp_pos (1 / 2)]
  rcases le_total 0 r with hr0 | hr0
  · have hr_half : r ≤ 1 / 2 := (le_abs_self r).trans hr
    have hint1 : IntervalIntegrable Real.exp volume 0 r := Real.continuous_exp.intervalIntegrable 0 r
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => Real.hasDerivAt_exp y) hint1
    rw [Real.exp_zero] at hval
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hr0)), abs_of_nonneg hr0, ← hval]
    have hmono := intervalIntegral.integral_mono_on hr0 hint1
      (intervalIntegrable_const (c := (2 : ℝ))) fun y hy =>
        (Real.exp_le_exp.mpr (hy.2.trans hr_half)).trans hexp_half_lt2
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hmono
  · set u : ℝ := -r
    have hu0 : 0 ≤ u := by dsimp only [u]; linarith only [hr0]
    have hint1 : IntervalIntegrable (fun y : ℝ => Real.exp (-y)) volume 0 u :=
      (Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 u
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => -Real.exp (-x))
      (f' := fun x : ℝ => Real.exp (-x))
      (fun y _ => by
        have h0 : HasDerivAt (fun x : ℝ => -Real.exp (-x)) (-(Real.exp (-y) * (-1))) y :=
          ((hasDerivAt_id' y).neg.exp).neg
        exact h0.congr_deriv (by ring)) hint1
    simp only [neg_zero, Real.exp_zero] at hval
    have h1_sub : 1 - Real.exp r = ∫ y in (0 : ℝ)..u, Real.exp (-y) := by
      dsimp only [u] at hval; rw [neg_neg] at hval; linarith only [hval]
    have hle1 : Real.exp r ≤ 1 := Real.exp_le_one_iff.mpr hr0
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle1), show |r| = u by
      dsimp only [u]; rw [abs_of_nonpos hr0]]
    rw [h1_sub]
    have hmono := intervalIntegral.integral_mono_on hu0 hint1
      (intervalIntegrable_const (c := (1 : ℝ))) fun y hy =>
        Real.exp_le_one_iff.mpr (by linarith only [hy.1])
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hmono
    linarith only [hmono, hu0]

private theorem norm_exp_I_sub_le (θ₁ θ₂ : ℝ) :
    ‖Complex.exp ((θ₁ : ℂ) * Complex.I) - Complex.exp ((θ₂ : ℂ) * Complex.I)‖ ≤ |θ₁ - θ₂| := by
  wlog hle : θ₂ ≤ θ₁ generalizing θ₁ θ₂
  · rw [norm_sub_rev, abs_sub_comm]
    exact this θ₂ θ₁ (le_of_not_ge hle)
  have hint : IntervalIntegrable (fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I) * Complex.I)
      volume θ₂ θ₁ := (by fun_prop : Continuous _).intervalIntegrable θ₂ θ₁
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => by
      have hid_c : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 y := by
        simpa only [id, Complex.real_smul, mul_one, one_smul] using
          (hasDerivAt_id y).smul_const (1 : ℂ)
      simpa only [one_mul] using (hid_c.mul_const Complex.I).cexp) hint
  rw [← hftc, abs_of_nonneg (sub_nonneg.mpr hle)]
  have hnorm1 : ∀ y ∈ Set.uIoc θ₂ θ₁,
      ‖Complex.exp ((y : ℂ) * Complex.I) * Complex.I‖ ≤ (1 : ℝ) := fun y _ => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hnorm1
  rwa [one_mul, abs_of_nonneg (sub_nonneg.mpr hle)] at hb

private theorem log_sub_log_le_div {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Real.log v - Real.log u ≤ (v - u) / u := by
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹) volume u v :=
    (ContinuousOn.inv₀ (continuousOn_id : ContinuousOn (fun t : ℝ => t) (Icc u v)) fun t ht =>
      (by linarith only [hu, ht.1] : t ≠ 0)).intervalIntegrable_of_Icc huv
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => Real.hasDerivAt_log
      (by rw [Set.uIcc_of_le huv] at ht; exact (by linarith only [hu, ht.1] : t ≠ 0)))
    hint
  rw [← hftc]
  have hmono := intervalIntegral.integral_mono_on huv hint
    (intervalIntegrable_const (c := u⁻¹)) fun t ht =>
      inv_anti₀ hu ht.1
  simpa only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using hmono

private theorem rpow_integral_le_of_pos {a : ℝ} (ha : 0 < a) {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t : ℝ => t ^ (a - 1)) volume u v ∧
      (∫ t in u..v, t ^ (a - 1)) ≤ v ^ a / a := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (a - 1)) volume u v :=
    (ContinuousOn.rpow_const (fun _ _ => continuousWithinAt_id) fun t ht =>
      Or.inl (by rw [Set.mem_Icc] at ht; change t ≠ 0; linarith only [hu, ht.1])).intervalIntegrable_of_Icc huv
  refine ⟨hint, ?_⟩
  have hderiv : ∀ t ∈ Set.uIcc u v, HasDerivAt (fun y : ℝ => y ^ a / a) (t ^ (a - 1)) t := by
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    have ht0 : 0 < t := by linarith only [hu, ht.1]
    have hd := (Real.hasDerivAt_rpow_const (p := a) (Or.inl ht0.ne')).div_const a
    rwa [mul_div_cancel_left₀ _ ha.ne'] at hd
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hu_pos : 0 ≤ u ^ a / a := div_nonneg (Real.rpow_nonneg (by linarith only [hu]) a) ha.le
  linarith only [hu_pos]

private def smoothMassReal (σ x : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(2 * σ)) +
    x ^ (1 - 2 * σ) / ((1 - 2 * σ) * Real.log x) -
    ((2 : ℝ) ^ (-(2 * σ)) / Real.log 2) * Chebyshev.theta 2 -
    (2 * σ) / (1 - 2 * σ) * ((2 : ℝ) ^ (1 - 2 * σ) / Real.log 2) +
    1 / (1 - 2 * σ) * ∫ u in (2 : ℝ)..x, u ^ (-(2 * σ)) / (Real.log u) ^ 2

private theorem ofReal_smoothMassReal {σ : ℝ} (_hσ1 : σ < 1 / 2) {x : ℝ} (hx2 : 2 ≤ x) :
    (smoothMassReal σ x : ℂ) = smoothPrimeSum ((2 * σ : ℝ) : ℂ) x := by
  have hcpow : ∀ (y : ℝ) (r : ℝ), 0 < y → ((y ^ r : ℝ) : ℂ) = (y : ℂ) ^ (r : ℂ) := fun y r hy =>
    Complex.ofReal_cpow hy.le r
  unfold smoothMassReal smoothPrimeSum _root_.RHTower.primeCpowAbelWeight
    _root_.RHTower.primeCpowAbelPrimitive _root_.RHTower.primeCpowLogSqIntegral
  have hx_pos : 0 < x := by linarith only [hx2]
  have hint_eq : ((∫ u in (2 : ℝ)..x, u ^ (-(2 * σ)) / (Real.log u) ^ 2 : ℝ) : ℂ) =
      ∫ u in (2 : ℝ)..x, (u : ℂ) ^ (-((2 * σ : ℝ) : ℂ)) / (Real.log u : ℂ) ^ 2 := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hx2] at hu
    have hu_pos : 0 < u := by linarith only [hu.1]
    rw [Complex.ofReal_div, hcpow u (-(2 * σ)) hu_pos, Complex.ofReal_neg, Complex.ofReal_pow]
  push_cast
  rw [hint_eq, hcpow 2 (-(2 * σ)) zero_lt_two, hcpow 2 (1 - 2 * σ) zero_lt_two,
    hcpow x (1 - 2 * σ) hx_pos]
  simp only [Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat]

private theorem smoothPrimeSum_sub_eq_integral {s : ℂ} (hs1 : s ≠ 1) {x y : ℝ}
    (hx2 : 2 ≤ x) (hxy : x ≤ y) :
    smoothPrimeSum s y - smoothPrimeSum s x =
      ∫ u in x..y, (u : ℂ) ^ (-s) / (Real.log u : ℂ) := by
  have hy2 : 2 ≤ y := hx2.trans hxy
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hI1 : IntervalIntegrable (fun u : ℝ =>
      (1 - s) * ((u : ℂ) ^ (-s) / (Real.log u : ℂ)) -
        (u : ℂ) ^ (-s) / (Real.log u : ℂ) ^ 2) volume x y := by
    have hc : ContinuousOn (fun u : ℝ =>
        (1 - s) * ((u : ℂ) ^ (-s) / (Real.log u : ℂ)) -
          (u : ℂ) ^ (-s) / (Real.log u : ℂ) ^ 2) (Icc 2 y) :=
      (continuousOn_const.mul _root_.RHTower.continuousOn_cpow_div_log).sub
        _root_.RHTower.continuousOn_cpow_div_log_sq
    exact (hc.mono (Set.Icc_subset_Icc hx2 le_rfl)).intervalIntegrable_of_Icc hxy
  have hI_main : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s) / (Real.log u : ℂ)) volume x y :=
    (_root_.RHTower.continuousOn_cpow_div_log.mono
      (Set.Icc_subset_Icc hx2 le_rfl)).intervalIntegrable_of_Icc hxy
  have hI2_all : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s) / (Real.log u : ℂ) ^ 2) volume a b :=
    fun a b ha hab =>
      (_root_.RHTower.continuousOn_cpow_div_log_sq.mono
        (Set.Icc_subset_Icc ha le_rfl)).intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => _root_.RHTower.hasDerivAt_primeCpowAbelPrimitive hs1
      (by rw [Set.uIcc_of_le hxy] at hu; linarith only [hx2, hu.1])) hI1
  have hsplit_int := intervalIntegral.integral_add_adjacent_intervals
    (hI2_all 2 x le_rfl hx2) (hI2_all x y hx2 hxy)
  have hsub_int : (∫ u in x..y,
      ((1 - s) * ((u : ℂ) ^ (-s) / (Real.log u : ℂ)) -
        (u : ℂ) ^ (-s) / (Real.log u : ℂ) ^ 2)) =
      (1 - s) * (∫ u in x..y, (u : ℂ) ^ (-s) / (Real.log u : ℂ)) -
        ∫ u in x..y, (u : ℂ) ^ (-s) / (Real.log u : ℂ) ^ 2 := by
    rw [intervalIntegral.integral_sub (hI_main.const_mul (1 - s)) (hI2_all x y hx2 hxy),
      intervalIntegral.integral_const_mul]
  rw [hsub_int] at hftc
  unfold smoothPrimeSum _root_.RHTower.primeCpowLogSqIntegral
  rw [← hsplit_int]
  set M_int : ℂ := ∫ u in x..y, (u : ℂ) ^ (-s) / (Real.log u : ℂ)
  set J_2x : ℂ := ∫ u in (2 : ℝ)..x, (u : ℂ) ^ (-s) / (Real.log u : ℂ) ^ 2
  set J_xy : ℂ := ∫ u in x..y, (u : ℂ) ^ (-s) / (Real.log u : ℂ) ^ 2
  have hpy : (y : ℂ) ^ (1 - s) / ((1 - s) * (Real.log y : ℂ)) =
      _root_.RHTower.primeCpowAbelPrimitive s y / (1 - s) := by
    rw [_root_.RHTower.primeCpowAbelPrimitive, div_div, mul_comm (Real.log y : ℂ) (1 - s)]
  have hpx : (x : ℂ) ^ (1 - s) / ((1 - s) * (Real.log x : ℂ)) =
      _root_.RHTower.primeCpowAbelPrimitive s x / (1 - s) := by
    rw [_root_.RHTower.primeCpowAbelPrimitive, div_div, mul_comm (Real.log x : ℂ) (1 - s)]
  rw [hpy, hpx]
  set py : ℂ := _root_.RHTower.primeCpowAbelPrimitive s y
  set px : ℂ := _root_.RHTower.primeCpowAbelPrimitive s x
  field_simp [h1s]
  linear_combination -hftc

private theorem smoothMassReal_sub_eq_integral {σ : ℝ} (hσ1 : σ < 1 / 2) {x y : ℝ}
    (hx2 : 2 ≤ x) (hxy : x ≤ y) :
    smoothMassReal σ y - smoothMassReal σ x =
      ∫ u in x..y, u ^ (-(2 * σ)) / Real.log u := by
  have hy2 : 2 ≤ y := hx2.trans hxy
  have hs0_ne1 : ((2 * σ : ℝ) : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith only [this, hσ1]
  have hc := smoothPrimeSum_sub_eq_integral hs0_ne1 hx2 hxy
  rw [← ofReal_smoothMassReal hσ1 hy2, ← ofReal_smoothMassReal hσ1 hx2, ← Complex.ofReal_sub] at hc
  have hint_c : (∫ u in x..y, (u : ℂ) ^ (-((2 * σ : ℝ) : ℂ)) / (Real.log u : ℂ)) =
      ((∫ u in x..y, u ^ (-(2 * σ)) / Real.log u : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hxy] at hu
    have hu_pos : 0 < u := by linarith only [hx2, hu.1]
    rw [Complex.ofReal_div, Complex.ofReal_cpow hu_pos.le, Complex.ofReal_neg]
  rw [hint_c] at hc
  exact Complex.ofReal_inj.mp hc

private theorem smoothMassReal_asymptotic {σ : ℝ} (_hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) :
    Tendsto (fun x : ℝ =>
      smoothMassReal σ x * ((1 - 2 * σ) * Real.log x / x ^ (1 - 2 * σ))) atTop (𝓝 1) := by
  set a : ℝ := 1 - 2 * σ with ha_def
  have ha : 0 < a := by linarith only [ha_def, hσ1]
  set K₀ : ℝ := (2 : ℝ) ^ (-(2 * σ)) -
    ((2 : ℝ) ^ (-(2 * σ)) / Real.log 2) * Chebyshev.theta 2 -
    (2 * σ) / (1 - 2 * σ) * ((2 : ℝ) ^ (1 - 2 * σ) / Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmaj : Tendsto (fun x : ℝ =>
      |K₀| * a * (Real.log x / x ^ a) +
        (1 / (a * (Real.log 2) ^ 2)) * (Real.log x / x ^ (a / 2)) +
        (4 / a) * (1 / Real.log x)) atTop (𝓝 0) := by
    have h1 := (_root_.RHTower.tendsto_log_div_rpow_atTop (ha := ha)).const_mul (|K₀| * a)
    have h2 := (_root_.RHTower.tendsto_log_div_rpow_atTop (ha := half_pos ha)).const_mul
      (1 / (a * (Real.log 2) ^ 2))
    have h3 : Tendsto (fun x : ℝ => (4 / a) * (1 / Real.log x)) atTop (𝓝 0) := by
      have h0 := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (4 / a)
      rw [mul_zero] at h0
      exact h0.congr fun x => by dsimp only [Function.comp_apply]; rw [one_div]
    simpa only [mul_zero, add_zero] using (h1.add h2).add h3
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with x hx16
  have hx_pos : 0 < x := by linarith only [hx16]
  have hx1 : 1 < x := by linarith only [hx16]
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx1
  have hxa_pos : 0 < x ^ a := Real.rpow_pos_of_pos hx_pos a
  have hsqrt_ge2 : 2 ≤ Real.sqrt x := by
    have h4 : (2 : ℝ) = Real.sqrt 4 := by norm_num
    rw [h4]; exact Real.sqrt_le_sqrt (by linarith only [hx16])
  have hsqrt_le_x : Real.sqrt x ≤ x := by
    have h1 : Real.sqrt x ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [hx16])
    rwa [Real.sqrt_sq hx_pos.le] at h1
  have hcont_int : ∀ u v : ℝ, 2 ≤ u → u ≤ v →
      IntervalIntegrable (fun t : ℝ => t ^ (-(2 * σ)) / (Real.log t) ^ 2) volume u v := by
    intro u v hu huv
    refine (ContinuousOn.div
      (ContinuousOn.rpow_const (fun _ _ => continuousWithinAt_id) fun t ht =>
        Or.inl (by linarith only [hu, ht.1] : t ≠ 0))
      ((ContinuousOn.log (continuousOn_id : ContinuousOn (fun t : ℝ => t) (Icc u v)) fun t ht =>
        (by linarith only [hu, ht.1] : t ≠ 0)).pow 2)
      fun t ht => by
        dsimp only [Function.comp_apply, id]
        exact pow_ne_zero 2 (Real.log_pos (by linarith only [hu, ht.1])).ne').intervalIntegrable_of_Icc huv
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont_int 2 (Real.sqrt x) le_rfl hsqrt_ge2)
    (hcont_int (Real.sqrt x) x hsqrt_ge2 hsqrt_le_x)
  obtain ⟨hr1_int, hr1_le⟩ := rpow_integral_le_of_pos ha le_rfl hsqrt_ge2
  obtain ⟨hr2_int, hr2_le⟩ := rpow_integral_le_of_pos ha hsqrt_ge2 hsqrt_le_x
  have hlow_int : (∫ u in (2 : ℝ)..(Real.sqrt x), u ^ (-(2 * σ)) / (Real.log u) ^ 2) ≤
      (1 / (Real.log 2) ^ 2) * (x ^ (a / 2) / a) := by
    have hm := intervalIntegral.integral_mono_on hsqrt_ge2
      (hcont_int 2 (Real.sqrt x) le_rfl hsqrt_ge2)
      (hr1_int.const_mul (1 / (Real.log 2) ^ 2)) fun u hu => by
        have hu0 : 0 ≤ u := by linarith only [hu.1]
        have hlog_ge : (Real.log 2) ^ 2 ≤ (Real.log u) ^ 2 :=
          pow_le_pow_left₀ hlog2_pos.le (Real.log_le_log zero_lt_two hu.1) 2
        have hinv_le : 1 / (Real.log u) ^ 2 ≤ 1 / (Real.log 2) ^ 2 :=
          one_div_le_one_div_of_le (pow_pos hlog2_pos 2) hlog_ge
        rw [show -(2 * σ) = a - 1 by linarith only [ha_def], div_eq_inv_mul, ← one_div]
        exact mul_le_mul_of_nonneg_right hinv_le (Real.rpow_nonneg hu0 _)
    rw [intervalIntegral.integral_const_mul] at hm
    have hsq_a : (Real.sqrt x) ^ a = x ^ (a / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx_pos.le, show (1 / 2 : ℝ) * a = a / 2 by ring]
    rw [hsq_a] at hr1_le
    exact hm.trans (mul_le_mul_of_nonneg_left hr1_le (by positivity))
  have hhigh_int : (∫ u in (Real.sqrt x)..x, u ^ (-(2 * σ)) / (Real.log u) ^ 2) ≤
      (4 / (Real.log x) ^ 2) * (x ^ a / a) := by
    have hm := intervalIntegral.integral_mono_on hsqrt_le_x
      (hcont_int (Real.sqrt x) x hsqrt_ge2 hsqrt_le_x)
      (hr2_int.const_mul (4 / (Real.log x) ^ 2)) fun u hu => by
        have hu0 : 0 ≤ u := by linarith only [hsqrt_ge2, hu.1]
        have hlog_half : Real.log x / 2 ≤ Real.log u := by
          have h := Real.log_le_log (Real.sqrt_pos.mpr hx_pos) hu.1
          rwa [Real.log_sqrt hx_pos.le] at h
        have hsq_le : (Real.log x / 2) ^ 2 ≤ (Real.log u) ^ 2 :=
          pow_le_pow_left₀ (half_pos hlogx_pos).le hlog_half 2
        have hinv_le : 1 / (Real.log u) ^ 2 ≤ 4 / (Real.log x) ^ 2 := by
          have h := one_div_le_one_div_of_le (pow_pos (half_pos hlogx_pos) 2) hsq_le
          rwa [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, one_div_div] at h
        rw [show -(2 * σ) = a - 1 by linarith only [ha_def], div_eq_inv_mul, ← one_div]
        exact mul_le_mul_of_nonneg_right hinv_le (Real.rpow_nonneg hu0 _)
    rw [intervalIntegral.integral_const_mul] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left hr2_le (by positivity))
  set J : ℝ := ∫ u in (2 : ℝ)..x, u ^ (-(2 * σ)) / (Real.log u) ^ 2
  have hJ_nn : 0 ≤ J := intervalIntegral.integral_nonneg (by linarith only [hx16]) fun u hu =>
    div_nonneg (Real.rpow_nonneg (by linarith only [hu.1]) _) (sq_nonneg _)
  have hJ_le : J ≤ (1 / (Real.log 2) ^ 2) * (x ^ (a / 2) / a) + (4 / (Real.log x) ^ 2) * (x ^ a / a) := by
    rw [← hsplit]; linarith only [hlow_int, hhigh_int]
  have hid : smoothMassReal σ x * (a * Real.log x / x ^ a) - 1 =
      K₀ * (a * Real.log x / x ^ a) + J * (Real.log x / x ^ a) := by
    have hsm : smoothMassReal σ x = x ^ a / (a * Real.log x) + K₀ + (1 / a) * J := by
      dsimp only [smoothMassReal, K₀, J, a]; ring
    rw [hsm]
    set P : ℝ := x ^ a
    set L : ℝ := Real.log x
    field_simp [ha.ne', hlogx_pos.ne', hxa_pos.ne']
    ring
  rw [Real.norm_eq_abs, hid]
  have hxa_half : x ^ (a / 2) / x ^ a = 1 / x ^ (a / 2) := by
    rw [div_eq_iff hxa_pos.ne', div_mul_eq_mul_div, one_mul,
      eq_div_iff (Real.rpow_pos_of_pos hx_pos _).ne', ← Real.rpow_add hx_pos, add_halves]
  have hJ_mul : J * (Real.log x / x ^ a) ≤
      (1 / (a * (Real.log 2) ^ 2)) * (Real.log x / x ^ (a / 2)) + (4 / a) * (1 / Real.log x) := by
    have hm := mul_le_mul_of_nonneg_right hJ_le (div_nonneg hlogx_pos.le hxa_pos.le)
    have hrhs : ((1 / (Real.log 2) ^ 2) * (x ^ (a / 2) / a) +
        (4 / (Real.log x) ^ 2) * (x ^ a / a)) * (Real.log x / x ^ a) =
        (1 / (a * (Real.log 2) ^ 2)) * (Real.log x * (x ^ (a / 2) / x ^ a)) +
          (4 / a) * (1 / Real.log x) := by
      set P : ℝ := x ^ a
      set Ph : ℝ := x ^ (a / 2)
      set L : ℝ := Real.log x
      set L2 : ℝ := Real.log 2
      field_simp [ha.ne', hlogx_pos.ne', hxa_pos.ne', hlog2_pos.ne']
    rw [hrhs, hxa_half, mul_one_div] at hm
    exact hm
  have hK_abs : |K₀ * (a * Real.log x / x ^ a)| = |K₀| * a * (Real.log x / x ^ a) := by
    rw [abs_mul, abs_of_pos (div_pos (mul_pos ha hlogx_pos) hxa_pos)]; ring
  have hJ_abs : |J * (Real.log x / x ^ a)| = J * (Real.log x / x ^ a) :=
    abs_of_nonneg (mul_nonneg hJ_nn (div_nonneg hlogx_pos.le hxa_pos.le))
  calc |K₀ * (a * Real.log x / x ^ a) + J * (Real.log x / x ^ a)|
      ≤ |K₀ * (a * Real.log x / x ^ a)| + |J * (Real.log x / x ^ a)| := abs_add_le _ _
    _ = |K₀| * a * (Real.log x / x ^ a) + J * (Real.log x / x ^ a) := by rw [hK_abs, hJ_abs]
    _ ≤ |K₀| * a * (Real.log x / x ^ a) +
          ((1 / (a * (Real.log 2) ^ 2)) * (Real.log x / x ^ (a / 2)) +
            (4 / a) * (1 / Real.log x)) := by linarith only [hJ_mul]
    _ = |K₀| * a * (Real.log x / x ^ a) +
          (1 / (a * (Real.log 2) ^ 2)) * (Real.log x / x ^ (a / 2)) +
          (4 / a) * (1 / Real.log x) := by ring

private theorem smooth_born_step_bounds {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    {t : ℝ} (ht : t ≠ 0) {k₀ : ℤ} (hk₀ : k₀ ≠ 0)
    (hsm_lim : Tendsto (fun n : ℕ => ‖smoothBornCoefficient σ t k₀ n‖) atTop
      (𝓝 (bornLorentzianLimit σ t k₀)))
    (hbc_lim : Tendsto (fun n : ℕ => ‖bornCoefficient σ t k₀ n‖) atTop
      (𝓝 (bornLorentzianLimit σ t k₀))) :
    ∃ (N_s : ℕ) (δ C_s : ℝ), 4 ≤ N_s ∧ 0 < δ ∧ 0 < C_s ∧
      ∀ n : ℕ, N_s ≤ n →
        let xn : ℝ := ((n + 2 : ℕ) : ℝ)
        let xn1 : ℝ := ((n + 3 : ℕ) : ℝ)
        0 < smoothMassReal σ xn ∧
        0 < bornMass σ n ∧
        xn ^ (1 - 2 * σ) / (2 * (1 - 2 * σ) * Real.log xn) ≤ smoothMassReal σ xn ∧
        smoothMassReal σ xn ≤ 2 * xn ^ (1 - 2 * σ) / ((1 - 2 * σ) * Real.log xn) ∧
        xn ^ (1 - 2 * σ) / (2 * (1 - 2 * σ) * Real.log xn) ≤ bornMass σ n ∧
        ‖smoothBornCoefficient σ t k₀ n‖ ≤ 1 - δ ∧
        ‖bornCoefficient σ t k₀ n‖ ≤ 1 - δ ∧
        0 ≤ 1 - smoothMassReal σ xn / smoothMassReal σ xn1 ∧
        1 - smoothMassReal σ xn / smoothMassReal σ xn1 ≤ C_s / xn ∧
        ‖((1 - smoothMassReal σ xn / smoothMassReal σ xn1 : ℝ) : ℂ) -
            (smoothBornCoefficient σ t k₀ (n + 1) - smoothBornCoefficient σ t k₀ n) /
              ((phase t (n + 3) : ℂ) ^ (-k₀) - smoothBornCoefficient σ t k₀ n)‖ ≤
          C_s / xn ^ 2 ∧
        ‖((phase t (n + 4) : ℂ) ^ (-k₀) - smoothBornCoefficient σ t k₀ (n + 1))⁻¹ -
            ((phase t (n + 3) : ℂ) ^ (-k₀) - smoothBornCoefficient σ t k₀ n)⁻¹‖ ≤
          C_s / xn := by
  set a : ℝ := 1 - 2 * σ with ha_def
  have ha0 : 0 < a := by linarith only [ha_def, hσ1]
  have ha1 : a < 1 := by linarith only [ha_def, hσ0]
  set ω : ℝ := (k₀ : ℝ) * t with hω_def
  have hω_ne : ω ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hk₀) ht
  have hlor_lt1 : bornLorentzianLimit σ t k₀ < 1 := by
    rw [bornLorentzianLimit, ← ha_def, ← hω_def]
    have hsq_gt : a ^ 2 < a ^ 2 + ω ^ 2 := lt_add_of_pos_right _ (sq_pos_of_ne_zero hω_ne)
    have hsqrt_gt : a < Real.sqrt (a ^ 2 + ω ^ 2) := by
      have h1 := Real.sqrt_lt_sqrt (sq_nonneg a) hsq_gt
      rwa [Real.sqrt_sq ha0.le] at h1
    exact (div_lt_one (lt_trans ha0 hsqrt_gt)).mpr hsqrt_gt
  set δ : ℝ := (1 - bornLorentzianLimit σ t k₀) / 2 with hδ_def
  have hδ_pos : 0 < δ := by linarith only [hδ_def, hlor_lt1]
  have h1_sub_δ : bornLorentzianLimit σ t k₀ < 1 - δ := by linarith only [hδ_def, hlor_lt1]
  let xseq : ℕ → ℝ := fun n => ((n + 2 : ℕ) : ℝ)
  have hx_top : Tendsto xseq atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hH_asymp := (smoothMassReal_asymptotic hσ0 hσ1).comp hx_top
  have hM_asymp : Tendsto (fun n : ℕ =>
      bornMass σ n * (a * Real.log (xseq n) / (xseq n) ^ a)) atTop (𝓝 1) := by
    have hm := (powerMass_asymptotic ha0 ha1).comp hx_top
    refine hm.congr fun n => ?_
    dsimp only [Function.comp_apply, xseq]
    have hcut : cutoff ((n + 2 : ℕ) : ℝ) = n := by unfold cutoff; rw [Nat.floor_natCast]; omega
    rw [powerMass, hcut, bornMass, mul_div_assoc]
    have hsum_eq : (∑ p ∈ primes n, (p : ℝ) ^ (a - 1)) = ∑ p ∈ primes n, bornWeight σ p :=
      Finset.sum_congr rfl fun p _ => by
        rw [bornWeight, show a - 1 = -(2 * σ) by linarith only [ha_def]]
    rw [hsum_eq]
  have hev_base : ∀ᶠ n : ℕ in atTop,
      1 / 2 ≤ smoothMassReal σ (xseq n) * (a * Real.log (xseq n) / (xseq n) ^ a) ∧
      smoothMassReal σ (xseq n) * (a * Real.log (xseq n) / (xseq n) ^ a) ≤ 2 ∧
      1 / 2 ≤ bornMass σ n * (a * Real.log (xseq n) / (xseq n) ^ a) ∧
      ‖smoothBornCoefficient σ t k₀ n‖ ≤ 1 - δ ∧
      ‖bornCoefficient σ t k₀ n‖ ≤ 1 - δ := by
    have h1 := hH_asymp.eventually (Icc_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
    have h2 := hM_asymp.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    have h3 := hsm_lim.eventually (Iic_mem_nhds h1_sub_δ)
    have h4 := hbc_lim.eventually (Iic_mem_nhds h1_sub_δ)
    filter_upwards [h1, h2, h3, h4] with n hn1 hn2 hn3 hn4
    exact ⟨hn1.1, hn1.2, hn2, hn3, hn4⟩
  have hev_succ : ∀ᶠ n : ℕ in atTop,
      1 / 2 ≤ smoothMassReal σ (xseq (n + 1)) * (a * Real.log (xseq (n + 1)) / (xseq (n + 1)) ^ a) ∧
      ‖smoothBornCoefficient σ t k₀ (n + 1)‖ ≤ 1 - δ := by
    have hs := (tendsto_add_atTop_nat 1).eventually hev_base
    filter_upwards [hs] with n hn
    exact ⟨hn.1, hn.2.2.2.1⟩
  rw [Filter.eventually_atTop] at hev_base hev_succ
  obtain ⟨N₁, hN₁⟩ := hev_base
  obtain ⟨N₂, hN₂⟩ := hev_succ
  set N_s : ℕ := max 4 (max N₁ N₂)
  set C_rot : ℝ := 2 * a * |ω| / δ
  set C_bdiff : ℝ := 2 * (2 * a + C_rot)
  set C_s : ℝ := 1 + 2 * a + C_rot + (|ω| + C_bdiff) / δ ^ 2
  have hC_s_pos : 0 < C_s := by
    dsimp only [C_s, C_bdiff, C_rot]; positivity
  refine ⟨N_s, δ, C_s, le_max_left _ _, hδ_pos, hC_s_pos, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left N₁ N₂) (le_max_right 4 _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_right 4 _)) hn
  have hn4 : 4 ≤ n := le_trans (le_max_left 4 _) hn
  obtain ⟨hH_lo, hH_hi, hM_lo, hBsm_n, hB_n⟩ := hN₁ n hn1
  obtain ⟨_, hBsm_n1⟩ := hN₂ n hn2
  dsimp only
  set xn : ℝ := ((n + 2 : ℕ) : ℝ)
  set xn1 : ℝ := ((n + 3 : ℕ) : ℝ)
  have hxn_eq : xseq n = xn := rfl
  have hxn1_eq : xseq (n + 1) = xn1 := rfl
  rw [hxn_eq] at hH_lo hH_hi hM_lo
  have hxn_ge6 : (6 : ℝ) ≤ xn := by dsimp only [xn]; exact_mod_cast (by omega : 6 ≤ n + 2)
  have hxn_pos : 0 < xn := by linarith only [hxn_ge6]
  have hxn2 : 2 ≤ xn := by linarith only [hxn_ge6]
  have hxn1_eq_add : xn1 = xn + 1 := by dsimp only [xn, xn1]; push_cast; ring
  have hxn_le1 : xn ≤ xn1 := by linarith only [hxn1_eq_add]
  have hxn1_2 : 2 ≤ xn1 := hxn2.trans hxn_le1
  have hlog_pos : 0 < Real.log xn := Real.log_pos (by linarith only [hxn_ge6])
  have hxa_pos : 0 < xn ^ a := Real.rpow_pos_of_pos hxn_pos a
  have hsc_pos : 0 < a * Real.log xn / xn ^ a := div_pos (mul_pos ha0 hlog_pos) hxa_pos
  have hH_low_b : xn ^ a / (2 * a * Real.log xn) ≤ smoothMassReal σ xn := by
    have h1 := (div_le_iff₀ hsc_pos).mpr hH_lo
    refine le_trans ?_ h1
    set P : ℝ := xn ^ a; set L : ℝ := Real.log xn
    apply le_of_eq; field_simp [ha0.ne', hlog_pos.ne', hxa_pos.ne']
  have hH_high_b : smoothMassReal σ xn ≤ 2 * xn ^ a / (a * Real.log xn) := by
    have h1 := (le_div_iff₀ hsc_pos).mpr hH_hi
    refine h1.trans (le_of_eq ?_)
    set P : ℝ := xn ^ a; set L : ℝ := Real.log xn
    field_simp [ha0.ne', hlog_pos.ne', hxa_pos.ne']
  have hM_low_b : xn ^ a / (2 * a * Real.log xn) ≤ bornMass σ n := by
    have h1 := (div_le_iff₀ hsc_pos).mpr hM_lo
    refine le_trans ?_ h1
    set P : ℝ := xn ^ a; set L : ℝ := Real.log xn
    apply le_of_eq; field_simp [ha0.ne', hlog_pos.ne', hxa_pos.ne']
  have hH_pos : 0 < smoothMassReal σ xn :=
    lt_of_lt_of_le (div_pos hxa_pos (by positivity)) hH_low_b
  have hM_pos : 0 < bornMass σ n :=
    lt_of_lt_of_le (div_pos hxa_pos (by positivity)) hM_low_b
  have hΔH_eq := smoothMassReal_sub_eq_integral hσ1 hxn2 hxn_le1
  have hcont_H : IntervalIntegrable (fun u : ℝ => u ^ (-(2 * σ)) / Real.log u) volume xn xn1 := by
    refine (ContinuousOn.div
      (ContinuousOn.rpow_const (fun _ _ => continuousWithinAt_id) fun u hu =>
        Or.inl (by linarith only [hxn2, hu.1] : u ≠ 0))
      (ContinuousOn.log (continuousOn_id : ContinuousOn (fun u : ℝ => u) (Icc xn xn1)) fun u hu =>
        (by linarith only [hxn2, hu.1] : u ≠ 0))
      fun u hu => by
        dsimp only [Function.comp_apply, id]
        exact (Real.log_pos (by linarith only [hxn_ge6, hu.1])).ne').intervalIntegrable_of_Icc hxn_le1
  have hΔH_nn : 0 ≤ smoothMassReal σ xn1 - smoothMassReal σ xn := by
    rw [hΔH_eq]
    exact intervalIntegral.integral_nonneg hxn_le1 fun u hu =>
      div_nonneg (Real.rpow_nonneg (by linarith only [hxn2, hu.1]) _)
        (Real.log_pos (by linarith only [hxn_ge6, hu.1])).le
  have hH1_ge : smoothMassReal σ xn ≤ smoothMassReal σ xn1 := by linarith only [hΔH_nn]
  have hH1_pos : 0 < smoothMassReal σ xn1 := lt_of_lt_of_le hH_pos hH1_ge
  have hΔH_le : smoothMassReal σ xn1 - smoothMassReal σ xn ≤ xn ^ (-(2 * σ)) / Real.log xn := by
    rw [hΔH_eq]
    have hm := intervalIntegral.integral_mono_on hxn_le1 hcont_H
      (intervalIntegrable_const (c := xn ^ (-(2 * σ)) / Real.log xn)) fun u hu => by
        have hrp : u ^ (-(2 * σ)) ≤ xn ^ (-(2 * σ)) :=
          Real.rpow_le_rpow_of_nonpos hxn_pos hu.1 (by linarith only [hσ0])
        exact div_le_div_of_le_of_le (Real.rpow_nonneg hxn_pos.le _) hrp
          hlog_pos (Real.log_le_log hxn_pos hu.1)
    rw [intervalIntegral.integral_const, show xn1 - xn = 1 by linarith only [hxn1_eq_add], one_smul] at hm
    exact hm
  have hu_sm_nn : 0 ≤ 1 - smoothMassReal σ xn / smoothMassReal σ xn1 := by
    rw [sub_nonneg]; exact (div_le_one hH1_pos).mpr hH1_ge
  have hu_sm_eq : 1 - smoothMassReal σ xn / smoothMassReal σ xn1 =
      (smoothMassReal σ xn1 - smoothMassReal σ xn) / smoothMassReal σ xn1 := by
    field_simp [hH1_pos.ne']
  have hu_sm_le_2a : 1 - smoothMassReal σ xn / smoothMassReal σ xn1 ≤ 2 * a / xn := by
    rw [hu_sm_eq]
    have h1 : (smoothMassReal σ xn1 - smoothMassReal σ xn) / smoothMassReal σ xn1 ≤
        (xn ^ (-(2 * σ)) / Real.log xn) / (xn ^ a / (2 * a * Real.log xn)) :=
      div_le_div_of_le_of_le (div_nonneg (Real.rpow_nonneg hxn_pos.le _) hlog_pos.le)
        hΔH_le (div_pos hxa_pos (by positivity)) (hH_low_b.trans hH1_ge)
    refine h1.trans (le_of_eq ?_)
    have hxa_split : xn ^ a = xn ^ (-(2 * σ)) * xn := by
      rw [show a = -(2 * σ) + 1 by linarith only [ha_def], Real.rpow_add hxn_pos, Real.rpow_one]
    rw [hxa_split]
    have hrp_ne : xn ^ (-(2 * σ)) ≠ 0 := (Real.rpow_pos_of_pos hxn_pos _).ne'
    set R : ℝ := xn ^ (-(2 * σ)); set L : ℝ := Real.log xn
    field_simp [hrp_ne, hlog_pos.ne', hxn_pos.ne', ha0.ne']
  have hu_sm_le : 1 - smoothMassReal σ xn / smoothMassReal σ xn1 ≤ C_s / xn :=
    hu_sm_le_2a.trans (div_le_div_of_nonneg_right
      (by dsimp only [C_s]; linarith only [ (by positivity : 0 ≤ C_rot),
        (by positivity : 0 ≤ (|ω| + C_bdiff) / δ ^ 2) ]) hxn_pos.le)
  -- Complex phase and smooth step comparison
  set z₃ : ℂ := (phase t (n + 3) : ℂ) ^ (-k₀)
  set z₄ : ℂ := (phase t (n + 4) : ℂ) ^ (-k₀)
  have hz3_norm : ‖z₃‖ = 1 := by dsimp only [z₃]; rw [norm_zpow, Circle.norm_coe, one_zpow]
  have hz4_norm : ‖z₄‖ = 1 := by dsimp only [z₄]; rw [norm_zpow, Circle.norm_coe, one_zpow]
  have hph_exp : ∀ q : ℕ, (phase t q : ℂ) ^ (-k₀) =
      Complex.exp (((ω * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
    intro q
    rw [phase, ← Circle.coe_zpow, ← Circle.exp_intCast_mul, Circle.coe_exp]
    congr 2; rw [hω_def, Int.cast_neg]; ring
  set B₀ : ℂ := smoothBornCoefficient σ t k₀ n
  set B₁ : ℂ := smoothBornCoefficient σ t k₀ (n + 1)
  have hden0_ge : δ ≤ ‖z₃ - B₀‖ := by
    have h := norm_sub_norm_le z₃ B₀
    rw [hz3_norm] at h
    linarith only [h, hBsm_n]
  have hden1_ge : δ ≤ ‖z₄ - B₁‖ := by
    have h := norm_sub_norm_le z₄ B₁
    rw [hz4_norm] at h
    linarith only [h, hBsm_n1]
  have hden0_ne : z₃ - B₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hden0_ge; linarith only [hδ_pos, hden0_ge]
  have hden1_ne : z₄ - B₁ ≠ 0 := fun h => by
    rw [h, norm_zero] at hden1_ge; linarith only [hδ_pos, hden1_ge]
  set s : ℂ := ((2 * σ : ℝ) : ℂ) - ((ω : ℝ) : ℂ) * Complex.I
  have hs_ne1 : s ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [s, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.one_re] at hr
    linarith only [hr, hσ1]
  set U₀ : ℂ := smoothPrimeSum s xn
  set U₁ : ℂ := smoothPrimeSum s xn1
  have hB0_eq : B₀ = U₀ / (smoothMassReal σ xn : ℂ) := by
    dsimp only [B₀, smoothBornCoefficient, U₀, s, ω, xn]
    rw [← ofReal_smoothMassReal hσ1 hxn2]
  have hB1_eq : B₁ = U₁ / (smoothMassReal σ xn1 : ℂ) := by
    dsimp only [B₁, smoothBornCoefficient, U₁, s, ω]
    have hcast : ((n + 1 + 2 : ℕ) : ℝ) = xn1 := rfl
    rw [hcast, ← ofReal_smoothMassReal hσ1 hxn1_2]
  have halg_sm : ((1 - smoothMassReal σ xn / smoothMassReal σ xn1 : ℝ) : ℂ) -
      (B₁ - B₀) / (z₃ - B₀) =
      (((smoothMassReal σ xn1 - smoothMassReal σ xn : ℝ) : ℂ) * z₃ - (U₁ - U₀)) /
        ((smoothMassReal σ xn1 : ℂ) * (z₃ - B₀)) := by
    have hH0_c : (smoothMassReal σ xn : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hH_pos.ne'
    have hH1_c : (smoothMassReal σ xn1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hH1_pos.ne'
    have h1_c : ((1 - smoothMassReal σ xn / smoothMassReal σ xn1 : ℝ) : ℂ) =
        1 - (smoothMassReal σ xn : ℂ) / (smoothMassReal σ xn1 : ℂ) := by push_cast; ring
    rw [h1_c, hB0_eq, hB1_eq, Complex.ofReal_sub]
    set h0c : ℂ := (smoothMassReal σ xn : ℂ)
    set h1c : ℂ := (smoothMassReal σ xn1 : ℂ)
    have hdz : h0c * z₃ - U₀ ≠ 0 := by
      intro hz
      apply hden0_ne
      rw [hB0_eq]
      field_simp [hH0_c]
      linear_combination hz
    field_simp [hH0_c, hH1_c, hden0_ne, hdz]
    ring
  have hrot_num : ‖((smoothMassReal σ xn1 - smoothMassReal σ xn : ℝ) : ℂ) * z₃ - (U₁ - U₀)‖ ≤
      (|ω| / xn) * (smoothMassReal σ xn1 - smoothMassReal σ xn) := by
    have hU_sub : U₁ - U₀ = ∫ u in xn..xn1, (u : ℂ) ^ (-s) / (Real.log u : ℂ) :=
      smoothPrimeSum_sub_eq_integral hs_ne1 hxn2 hxn_le1
    have hH_sub_c : ((smoothMassReal σ xn1 - smoothMassReal σ xn : ℝ) : ℂ) * z₃ =
        ∫ u in xn..xn1, ((u ^ (-(2 * σ)) / Real.log u : ℝ) : ℂ) * z₃ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, ← hΔH_eq]
    have hI_lhs : IntervalIntegrable
        (fun u : ℝ => ((u ^ (-(2 * σ)) / Real.log u : ℝ) : ℂ) * z₃) volume xn xn1 := by
      have hc_real : ContinuousOn (fun u : ℝ => u ^ (-(2 * σ)) / Real.log u) (Icc xn xn1) :=
        ContinuousOn.div
          (ContinuousOn.rpow_const (fun _ _ => continuousWithinAt_id) fun u hu =>
            Or.inl (by linarith only [hxn2, hu.1] : u ≠ 0))
          (ContinuousOn.log (continuousOn_id : ContinuousOn (fun u : ℝ => u) (Icc xn xn1)) fun u hu =>
            (by linarith only [hxn2, hu.1] : u ≠ 0))
          fun u hu => (Real.log_pos (by linarith only [hxn_ge6, hu.1])).ne'
      exact ((Complex.continuous_ofReal.comp_continuousOn hc_real).mul
        continuousOn_const).intervalIntegrable_of_Icc hxn_le1
    have hI_rhs : IntervalIntegrable
        (fun u : ℝ => (u : ℂ) ^ (-s) / (Real.log u : ℂ)) volume xn xn1 :=
      (_root_.RHTower.continuousOn_cpow_div_log.mono
        (Set.Icc_subset_Icc hxn2 le_rfl)).intervalIntegrable_of_Icc hxn_le1
    rw [hH_sub_c, hU_sub, ← intervalIntegral.integral_sub hI_lhs hI_rhs]
    refine (intervalIntegral.norm_integral_le_integral_norm hxn_le1).trans ?_
    have hm := intervalIntegral.integral_mono_on hxn_le1 (hI_lhs.sub hI_rhs).norm
      (hcont_H.const_mul (|ω| / xn)) fun u hu => by
        have hu_pos : 0 < u := by linarith only [hxn_ge6, hu.1]
        have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
        have hlogu_pos : 0 < Real.log u := Real.log_pos (by linarith only [hxn_ge6, hu.1])
        have hcpow_s : (u : ℂ) ^ (-s) / (Real.log u : ℂ) =
            ((u ^ (-(2 * σ)) / Real.log u : ℝ) : ℂ) *
              Complex.exp (((ω * Real.log u : ℝ) : ℂ) * Complex.I) := by
          rw [Complex.cpow_def_of_ne_zero hu_ne, ← Complex.ofReal_log hu_pos.le,
            show (Real.log u : ℂ) * (-s) =
              ((-(2 * σ) * Real.log u : ℝ) : ℂ) + ((ω * Real.log u : ℝ) : ℂ) * Complex.I by
              dsimp only [s]; push_cast; ring,
            Complex.exp_add, ← Complex.ofReal_exp, mul_comm (-(2 * σ)) (Real.log u),
            ← Real.rpow_def_of_pos hu_pos, Complex.ofReal_div, div_mul_eq_mul_div]
        rw [hcpow_s, ← mul_sub, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (div_nonneg (Real.rpow_nonneg hu_pos.le _) hlogu_pos.le)]
        have hz3_e : z₃ = Complex.exp (((ω * Real.log xn1 : ℝ) : ℂ) * Complex.I) := hph_exp (n + 3)
        rw [hz3_e]
        have hexp_b := norm_exp_I_sub_le (ω * Real.log xn1) (ω * Real.log u)
        rw [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hu_pos hu.2))] at hexp_b
        have hlg_b : Real.log xn1 - Real.log u ≤ 1 / xn := by
          calc Real.log xn1 - Real.log u
              ≤ (xn1 - u) / u := log_sub_log_le_div hu_pos hu.2
            _ ≤ 1 / u := div_le_div_of_nonneg_right (by linarith only [hxn1_eq_add, hu.1]) hu_pos.le
            _ ≤ 1 / xn := one_div_le_one_div_of_le hxn_pos hu.1
        have hprod : |ω| * (Real.log xn1 - Real.log u) ≤ |ω| / xn := by
          have := mul_le_mul_of_nonneg_left hlg_b (abs_nonneg ω)
          rwa [mul_one_div] at this
        have hfin := mul_le_mul_of_nonneg_left (hexp_b.trans hprod)
          (div_nonneg (Real.rpow_nonneg hu_pos.le (-(2 * σ))) hlogu_pos.le)
        linarith only [hfin, (show (u ^ (-(2 * σ)) / Real.log u) * (|ω| / xn) =
          (|ω| / xn) * (u ^ (-(2 * σ)) / Real.log u) by ring)]
    rw [intervalIntegral.integral_const_mul, ← hΔH_eq] at hm
    exact hm
  have hrot_step : ‖((1 - smoothMassReal σ xn / smoothMassReal σ xn1 : ℝ) : ℂ) -
      (B₁ - B₀) / (z₃ - B₀)‖ ≤ C_rot / xn ^ 2 := by
    rw [halg_sm, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hH1_pos.le]
    have hden_ge : smoothMassReal σ xn1 * δ ≤ smoothMassReal σ xn1 * ‖z₃ - B₀‖ :=
      mul_le_mul_of_nonneg_left hden0_ge hH1_pos.le
    have h1 : ‖((smoothMassReal σ xn1 - smoothMassReal σ xn : ℝ) : ℂ) * z₃ - (U₁ - U₀)‖ /
        (smoothMassReal σ xn1 * ‖z₃ - B₀‖) ≤
        ((|ω| / xn) * (smoothMassReal σ xn1 - smoothMassReal σ xn)) /
          (smoothMassReal σ xn1 * δ) :=
      div_le_div_of_le_of_le (mul_nonneg (by positivity) hΔH_nn) hrot_num
        (mul_pos hH1_pos hδ_pos) hden_ge
    have h2 : ((|ω| / xn) * (smoothMassReal σ xn1 - smoothMassReal σ xn)) /
        (smoothMassReal σ xn1 * δ) =
        (|ω| / (δ * xn)) * (1 - smoothMassReal σ xn / smoothMassReal σ xn1) := by
      rw [hu_sm_eq]
      field_simp [hH1_pos.ne', hδ_pos.ne', hxn_pos.ne']
    rw [h2] at h1
    calc ‖((smoothMassReal σ xn1 - smoothMassReal σ xn : ℝ) : ℂ) * z₃ - (U₁ - U₀)‖ /
            (smoothMassReal σ xn1 * ‖z₃ - B₀‖)
        ≤ (|ω| / (δ * xn)) * (2 * a / xn) :=
          h1.trans (mul_le_mul_of_nonneg_left hu_sm_le_2a (by positivity))
      _ = C_rot / xn ^ 2 := by
          dsimp only [C_rot]
          field_simp [hδ_pos.ne', hxn_pos.ne']
  have hrot_step_Cs : ‖((1 - smoothMassReal σ xn / smoothMassReal σ xn1 : ℝ) : ℂ) -
      (B₁ - B₀) / (z₃ - B₀)‖ ≤ C_s / xn ^ 2 :=
    hrot_step.trans (div_le_div_of_nonneg_right
      (by dsimp only [C_s]; linarith only [ha0, (by positivity : 0 ≤ (|ω| + C_bdiff) / δ ^ 2)])
      (sq_nonneg xn))
  -- Bound on `‖(z₄ - B₁)⁻¹ - (z₃ - B₀)⁻¹‖`
  have hB_diff_le : ‖B₁ - B₀‖ ≤ C_bdiff / xn := by
    have hq_norm : ‖(B₁ - B₀) / (z₃ - B₀)‖ ≤ (2 * a + C_rot) / xn := by
      have htri : ‖(B₁ - B₀) / (z₃ - B₀)‖ ≤
          ‖((1 - smoothMassReal σ xn / smoothMassReal σ xn1 : ℝ) : ℂ)‖ +
            ‖((1 - smoothMassReal σ xn / smoothMassReal σ xn1 : ℝ) : ℂ) -
              (B₁ - B₀) / (z₃ - B₀)‖ := by
        have := norm_sub_le ((1 - smoothMassReal σ xn / smoothMassReal σ xn1 : ℝ) : ℂ)
          (((1 - smoothMassReal σ xn / smoothMassReal σ xn1 : ℝ) : ℂ) - (B₁ - B₀) / (z₃ - B₀))
        rwa [sub_sub_cancel] at this
      rw [Complex.norm_real, Real.norm_of_nonneg hu_sm_nn] at htri
      have hsq_le : C_rot / xn ^ 2 ≤ C_rot / xn := by
        have hxn_le_sq : xn ≤ xn ^ 2 := by nlinarith only [hxn_ge6]
        exact div_le_div_of_nonneg_left (by dsimp only [C_rot]; positivity) hxn_pos hxn_le_sq
      calc ‖(B₁ - B₀) / (z₃ - B₀)‖
          ≤ 2 * a / xn + C_rot / xn := by linarith only [htri, hu_sm_le_2a, hrot_step, hsq_le]
        _ = (2 * a + C_rot) / xn := by ring
    have hden0_le2 : ‖z₃ - B₀‖ ≤ 2 := by
      have h := norm_sub_le z₃ B₀
      rw [hz3_norm] at h
      linarith only [h, hBsm_n, hδ_pos]
    have hmul : ‖B₁ - B₀‖ = ‖(B₁ - B₀) / (z₃ - B₀)‖ * ‖z₃ - B₀‖ := by
      rw [← norm_mul, div_mul_cancel₀ _ hden0_ne]
    rw [hmul]
    calc ‖(B₁ - B₀) / (z₃ - B₀)‖ * ‖z₃ - B₀‖
        ≤ ((2 * a + C_rot) / xn) * 2 :=
          mul_le_mul hq_norm hden0_le2 (norm_nonneg _) (by dsimp only [C_rot]; positivity)
      _ = C_bdiff / xn := by dsimp only [C_bdiff]; ring
  have hz_diff_le : ‖z₃ - z₄‖ ≤ |ω| / xn := by
    dsimp only [z₃, z₄]
    rw [hph_exp (n + 3), hph_exp (n + 4)]
    have hb := norm_exp_I_sub_le (ω * Real.log ((n + 3 : ℕ) : ℝ))
      (ω * Real.log ((n + 4 : ℕ) : ℝ))
    have h34_le : ((n + 3 : ℕ) : ℝ) ≤ ((n + 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : n + 3 ≤ n + 4)
    have h3_pos : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by positivity
    rw [← mul_sub, abs_mul, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log h3_pos h34_le))] at hb
    have hlg := log_sub_log_le_div h3_pos h34_le
    have hdiff1 : ((n + 4 : ℕ) : ℝ) - ((n + 3 : ℕ) : ℝ) = 1 := by push_cast; ring
    rw [hdiff1] at hlg
    have h1_le : 1 / ((n + 3 : ℕ) : ℝ) ≤ 1 / xn :=
      one_div_le_one_div_of_le hxn_pos (by dsimp only [xn]; exact_mod_cast (by omega : n + 2 ≤ n + 3))
    have hm := mul_le_mul_of_nonneg_left (hlg.trans h1_le) (abs_nonneg ω)
    rw [mul_one_div] at hm
    exact hb.trans hm
  have hinv_diff : ‖(z₄ - B₁)⁻¹ - (z₃ - B₀)⁻¹‖ ≤ C_s / xn := by
    have halg_inv : (z₄ - B₁)⁻¹ - (z₃ - B₀)⁻¹ =
        ((z₃ - z₄) + (B₁ - B₀)) / ((z₄ - B₁) * (z₃ - B₀)) := by
      field_simp [hden0_ne, hden1_ne]; ring
    rw [halg_inv, norm_div, norm_mul]
    have hden_prod : δ ^ 2 ≤ ‖z₄ - B₁‖ * ‖z₃ - B₀‖ := by
      rw [sq]; exact mul_le_mul hden1_ge hden0_ge hδ_pos.le (norm_nonneg _)
    have hnum_le : ‖(z₃ - z₄) + (B₁ - B₀)‖ ≤ (|ω| + C_bdiff) / xn := by
      calc ‖(z₃ - z₄) + (B₁ - B₀)‖
          ≤ ‖z₃ - z₄‖ + ‖B₁ - B₀‖ := norm_add_le _ _
        _ ≤ |ω| / xn + C_bdiff / xn := add_le_add hz_diff_le hB_diff_le
        _ = (|ω| + C_bdiff) / xn := by ring
    have hq : ‖(z₃ - z₄) + (B₁ - B₀)‖ / (‖z₄ - B₁‖ * ‖z₃ - B₀‖) ≤
        ((|ω| + C_bdiff) / xn) / δ ^ 2 :=
      div_le_div_of_le_of_le (by dsimp only [C_bdiff, C_rot]; positivity) hnum_le
        (pow_pos hδ_pos 2) hden_prod
    have hrew : ((|ω| + C_bdiff) / xn) / δ ^ 2 = ((|ω| + C_bdiff) / δ ^ 2) / xn := by ring
    rw [hrew] at hq
    exact hq.trans (div_le_div_of_nonneg_right
      (by dsimp only [C_s]; linarith only [ha0, (by dsimp only [C_rot]; positivity : 0 ≤ C_rot)])
      hxn_pos.le)
  exact ⟨hH_pos, hM_pos, hH_low_b, hH_high_b, hM_low_b, hBsm_n, hB_n,
    hu_sm_nn, hu_sm_le, hrot_step_Cs, hinv_diff⟩

private theorem dyadic_log_mass_ratio_bound_of_mode_error {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    {t : ℝ} (ht : t ≠ 0) {k₀ : ℤ} (hk₀ : k₀ ≠ 0)
    {α β : ℝ} (hα0 : 0 < α) (_hβ0 : 0 < β) (hβα : β < α) (hβ_half : β < 1 / 2)
    {c : ℝ} (hc : 0 < c) {N₀ : ℕ}
    (hsm_lim : Tendsto (fun n : ℕ => ‖smoothBornCoefficient σ t k₀ n‖) atTop
      (𝓝 (bornLorentzianLimit σ t k₀)))
    (hbc_lim : Tendsto (fun n : ℕ => ‖bornCoefficient σ t k₀ n‖) atTop
      (𝓝 (bornLorentzianLimit σ t k₀)))
    (hdisc_step : ∀ n : ℕ, 3 ≤ n →
      ((1 - bornMass σ n / bornMass σ (n + 1) : ℝ) : ℂ) =
        (bornCoefficient σ t k₀ (n + 1) - bornCoefficient σ t k₀ n) /
          ((phase t (n + 3) : ℂ) ^ (-k₀) - bornCoefficient σ t k₀ n) ∧
      0 ≤ 1 - bornMass σ n / bornMass σ (n + 1) ∧
      1 - bornMass σ n / bornMass σ (n + 1) ≤ ((n + 3 : ℕ) : ℝ) ^ (-(2 * σ)) / bornMass σ (n + 1))
    (herr : ∀ n : ℕ, N₀ ≤ n →
      ‖bornCoefficient σ t k₀ n - smoothBornCoefficient σ t k₀ n‖ ≤
        c * ((n + 2 : ℕ) : ℝ) ^ (-α)) :
    ∃ (M₁ : ℕ) (C_oct : ℝ), 0 < C_oct ∧
      ∀ m : ℕ, M₁ ≤ m →
        |Real.log (bornMass σ (2 * m + 2) / smoothMassReal σ ((2 * m + 4 : ℕ) : ℝ)) -
          Real.log (bornMass σ m / smoothMassReal σ ((m + 2 : ℕ) : ℝ))| ≤
            C_oct * ((m + 2 : ℕ) : ℝ) ^ (-β) := by
  obtain ⟨N_s, δ, C_s, hNs4, hδ_pos, hCs_pos, hstep⟩ :=
    smooth_born_step_bounds hσ0 hσ1 ht hk₀ hsm_lim hbc_lim
  set a : ℝ := 1 - 2 * σ with ha_def
  have ha0 : 0 < a := by linarith only [ha_def, hσ1]
  let xseq : ℕ → ℝ := fun n => ((n + 2 : ℕ) : ℝ)
  have hx_top : Tendsto xseq atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have h1_sub_β : 0 < 1 - β := by linarith only [hβ_half]
  have hα_sub_β : 0 < α - β := by linarith only [hβα]
  have hev_decay : ∀ᶠ n : ℕ in atTop,
      2 * a * (Real.log (xseq n) / xseq n) ≤ 1 / 2 ∧
      C_s / xseq n ≤ 1 / 2 ∧
      (Real.log (xseq n)) ^ 2 / (xseq n) ^ (1 - β) ≤ 1 ∧
      Real.log (xseq n) / (xseq n) ^ (α - β) ≤ 1 := by
    have hlim1 : Tendsto (fun x : ℝ => 2 * a * (Real.log x / x)) atTop (𝓝 0) := by
      have h0 := (_root_.RHTower.tendsto_log_div_rpow_atTop (ha := zero_lt_one)).const_mul (2 * a)
      rw [mul_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
      rw [Real.rpow_one]
    have hlim2 : Tendsto (fun x : ℝ => C_s / x) atTop (𝓝 0) := by
      have h0 := tendsto_inv_atTop_zero.const_mul C_s
      rw [mul_zero] at h0
      exact h0.congr fun x => by rw [div_eq_mul_inv]
    have hlim3 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x ^ (1 - β)) atTop (𝓝 0) := by
      have hbase := _root_.RHTower.tendsto_log_div_rpow_atTop (ha := half_pos h1_sub_β)
      have hsq := hbase.pow 2
      rw [zero_pow (by decide : 2 ≠ 0)] at hsq
      refine hsq.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [div_pow, ← Real.rpow_natCast (x ^ ((1 - β) / 2)) 2, ← Real.rpow_mul hx.le,
        show (1 - β) / 2 * (2 : ℕ) = 1 - β by push_cast; ring]
    have hlim4 := _root_.RHTower.tendsto_log_div_rpow_atTop (ha := hα_sub_β)
    filter_upwards [(hlim1.comp hx_top).eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      (hlim2.comp hx_top).eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      (hlim3.comp hx_top).eventually (Iic_mem_nhds zero_lt_one),
      (hlim4.comp hx_top).eventually (Iic_mem_nhds zero_lt_one)] with n h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  rw [Filter.eventually_atTop] at hev_decay
  obtain ⟨N_d, hN_d⟩ := hev_decay
  set M₁ : ℕ := max (max N₀ N_s) N_d
  set C_oct : ℝ := 16 * a ^ 2 + C_s ^ 2 + C_s + 4 * a * c / δ + 2 * c / δ + c * C_s
  have hC_oct_pos : 0 < C_oct := by dsimp only [C_oct]; positivity
  refine ⟨M₁, C_oct, hC_oct_pos, fun m hm => ?_⟩
  have hm_N0 : N₀ ≤ m := le_trans (le_trans (le_max_left N₀ N_s) (le_max_left _ N_d)) hm
  have hm_Ns : N_s ≤ m := le_trans (le_trans (le_max_right N₀ N_s) (le_max_left _ N_d)) hm
  have hm_Nd : N_d ≤ m := le_trans (le_max_right _ N_d) hm
  have hm4 : 4 ≤ m := le_trans hNs4 hm_Ns
  set K : ℕ := 2 * m + 2
  have hmK : m ≤ K := by omega
  set xm : ℝ := ((m + 2 : ℕ) : ℝ)
  have hxm_ge6 : (6 : ℝ) ≤ xm := by dsimp only [xm]; exact_mod_cast (by omega : 6 ≤ m + 2)
  have hxm_pos : 0 < xm := by linarith only [hxm_ge6]
  have hxm_ge1 : 1 ≤ xm := by linarith only [hxm_ge6]
  have hlog_xm_ge1 : 1 ≤ Real.log xm := by
    have hexp_lt6 : Real.exp 1 ≤ 6 := by have := Real.exp_one_lt_d9; linarith
    have h1 := Real.log_le_log (Real.exp_pos 1) (hexp_lt6.trans hxm_ge6)
    rwa [Real.log_exp] at h1
  obtain ⟨_, _, hlog2_xm, hlog_αβ_xm⟩ := hN_d m hm_Nd
  change (Real.log xm) ^ 2 / xm ^ (1 - β) ≤ 1 at hlog2_xm
  change Real.log xm / xm ^ (α - β) ≤ 1 at hlog_αβ_xm
  let r : ℕ → ℝ := fun k => Real.log (bornMass σ k / smoothMassReal σ ((k + 2 : ℕ) : ℝ))
  let u_d : ℕ → ℝ := fun n => 1 - bornMass σ n / bornMass σ (n + 1)
  let u_s : ℕ → ℝ := fun n =>
    1 - smoothMassReal σ ((n + 2 : ℕ) : ℝ) / smoothMassReal σ ((n + 3 : ℕ) : ℝ)
  let E : ℕ → ℂ := fun n => bornCoefficient σ t k₀ n - smoothBornCoefficient σ t k₀ n
  let g : ℕ → ℂ := fun n => ((phase t (n + 3) : ℂ) ^ (-k₀) - smoothBornCoefficient σ t k₀ n)⁻¹
  have htel_r : r K - r m = ∑ n ∈ Finset.Ico m K, (r (n + 1) - r n) := by
    have htel_gen : ∀ k : ℕ, m ≤ k → r k - r m = ∑ n ∈ Finset.Ico m k, (r (n + 1) - r n) := by
      intro k hk
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
      induction d with
      | zero => simp
      | succ d ih =>
        have hmd : m ≤ m + d := by omega
        rw [show m + (d + 1) = (m + d) + 1 by omega, Finset.sum_Ico_succ_top hmd, ← ih hmd]
        ring
    exact htel_gen K hmK
  have hr_step : ∀ n ∈ Finset.Ico m K,
      r (n + 1) - r n =
        ((-Real.log (1 - u_d n) - u_d n) - (-Real.log (1 - u_s n) - u_s n)) +
          (u_d n - u_s n) := by
    intro n hn
    have hn_Ns : N_s ≤ n := le_trans hm_Ns (Finset.mem_Ico.mp hn).1
    have hn1_Ns : N_s ≤ n + 1 := by omega
    obtain ⟨hH_n, hM_n, _, _, _, _, _, _, _, _, _⟩ := hstep n hn_Ns
    obtain ⟨hH_n1, hM_n1, _, _, _, _, _, _, _, _, _⟩ := hstep (n + 1) hn1_Ns
    have hcast3 : ((n + 1 + 2 : ℕ) : ℝ) = ((n + 3 : ℕ) : ℝ) := by push_cast; ring
    have h1_ud : 1 - u_d n = bornMass σ n / bornMass σ (n + 1) := by dsimp only [u_d]; ring
    have h1_us : 1 - u_s n =
        smoothMassReal σ ((n + 2 : ℕ) : ℝ) / smoothMassReal σ ((n + 3 : ℕ) : ℝ) := by
      dsimp only [u_s]; ring
    dsimp only [r]
    rw [hcast3, h1_ud, h1_us, Real.log_div hM_n1.ne' hH_n1.ne', Real.log_div hM_n.ne' hH_n.ne',
      Real.log_div hM_n.ne' hM_n1.ne', Real.log_div hH_n.ne' hH_n1.ne']
    ring
  -- Per-step bounds on `Ico m K`
  have hud_bound : ∀ n ∈ Finset.Ico m K,
      0 ≤ u_d n ∧ u_d n ≤ 1 / 2 ∧ u_d n ≤ 4 * a * Real.log xm / xm := by
    intro n hn
    have hn_m : m ≤ n := (Finset.mem_Ico.mp hn).1
    have hn_lt : n < K := (Finset.mem_Ico.mp hn).2
    have hn_Ns : N_s ≤ n := le_trans hm_Ns hn_m
    have hn1_Ns : N_s ≤ n + 1 := by omega
    have hn_Nd : N_d ≤ n := le_trans hm_Nd hn_m
    obtain ⟨hud_half_raw, _, _, _⟩ := hN_d n hn_Nd
    obtain ⟨_, hud_nn, hud_le⟩ := hdisc_step n (by omega)
    obtain ⟨_, _, _, _, hM_n1_lo, _, _, _, _, _, _⟩ := hstep (n + 1) hn1_Ns
    set xn : ℝ := ((n + 2 : ℕ) : ℝ)
    set xn1 : ℝ := ((n + 3 : ℕ) : ℝ)
    have hxn_ge_xm : xm ≤ xn := by dsimp only [xm, xn]; exact_mod_cast (by omega : m + 2 ≤ n + 2)
    have hxn_pos : 0 < xn := lt_of_lt_of_le hxm_pos hxn_ge_xm
    have hxn1_ge_xn : xn ≤ xn1 := by dsimp only [xn, xn1]; exact_mod_cast (by omega : n + 2 ≤ n + 3)
    have hxn1_pos : 0 < xn1 := lt_of_lt_of_le hxn_pos hxn1_ge_xn
    have hlog_xn1_pos : 0 < Real.log xn1 := Real.log_pos (by linarith only [hxm_ge6, hxn_ge_xm, hxn1_ge_xn])
    have hlog_xn_pos : 0 < Real.log xn := Real.log_pos (by linarith only [hxm_ge6, hxn_ge_xm])
    have hud_le_xn : u_d n ≤ 2 * a * (Real.log xn / xn) := by
      obtain ⟨_, _, _, _, hM_n_lo, _, _, _, _, _, _⟩ := hstep n hn_Ns
      have hMn_le_Mn1 : bornMass σ n ≤ bornMass σ (n + 1) := by
        have hdiv_le1 : bornMass σ n / bornMass σ (n + 1) ≤ 1 := by linarith only [hud_nn]
        have hMn1_pos : 0 < bornMass σ (n + 1) :=
          lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos hxn1_pos a) (by positivity)) hM_n1_lo
        exact (div_le_one hMn1_pos).mp hdiv_le1
      have h3 : xn1 ^ (-(2 * σ)) / bornMass σ (n + 1) ≤
          xn ^ (-(2 * σ)) / (xn ^ a / (2 * a * Real.log xn)) :=
        div_le_div_of_le_of_le (Real.rpow_nonneg hxn_pos.le _)
          (Real.rpow_le_rpow_of_nonpos hxn_pos hxn1_ge_xn (by linarith only [hσ0]))
          (div_pos (Real.rpow_pos_of_pos hxn_pos a) (by positivity))
          (hM_n_lo.trans hMn_le_Mn1)
      have h4 : xn ^ (-(2 * σ)) / (xn ^ a / (2 * a * Real.log xn)) =
          2 * a * (Real.log xn / xn) := by
        have hsp : xn ^ a = xn ^ (-(2 * σ)) * xn := by
          rw [show a = -(2 * σ) + 1 by linarith only [ha_def], Real.rpow_add hxn_pos, Real.rpow_one]
        rw [hsp]
        have hr_ne : xn ^ (-(2 * σ)) ≠ 0 := (Real.rpow_pos_of_pos hxn_pos _).ne'
        field_simp [hr_ne, hxn_pos.ne', ha0.ne', hlog_xn_pos.ne']
      exact hud_le.trans (h3.trans (le_of_eq h4))
    have hxn_le_sq : xn ≤ xm ^ 2 := by
      have hxn_le_2xm : xn ≤ 2 * xm := by
        dsimp only [xn, xm]; exact_mod_cast (by omega : n + 2 ≤ 2 * (m + 2))
      nlinarith only [hxm_ge6, hxn_le_2xm]
    have hlog_le_2 : Real.log xn ≤ 2 * Real.log xm := by
      have h1 := Real.log_le_log hxn_pos hxn_le_sq
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have hdiv_xm : Real.log xn / xn ≤ 2 * Real.log xm / xm :=
      div_le_div_of_le_of_le (by positivity) hlog_le_2 hxm_pos hxn_ge_xm
    refine ⟨hud_nn, hud_le_xn.trans hud_half_raw, ?_⟩
    calc u_d n ≤ 2 * a * (2 * Real.log xm / xm) :=
          hud_le_xn.trans (mul_le_mul_of_nonneg_left hdiv_xm (by positivity))
      _ = 4 * a * Real.log xm / xm := by ring
  have hquad_sum : |∑ n ∈ Finset.Ico m K,
      ((-Real.log (1 - u_d n) - u_d n) - (-Real.log (1 - u_s n) - u_s n))| ≤
      (16 * a ^ 2 + C_s ^ 2) * xm ^ (-β) := by
    have hterm : ∀ n ∈ Finset.Ico m K,
        |(-Real.log (1 - u_d n) - u_d n) - (-Real.log (1 - u_s n) - u_s n)| ≤
          ((16 * a ^ 2) * (Real.log xm) ^ 2 + C_s ^ 2) / xm ^ 2 := by
      intro n hn
      obtain ⟨hud_nn, hud_half, hud_xm⟩ := hud_bound n hn
      have hn_m : m ≤ n := (Finset.mem_Ico.mp hn).1
      have hn_Ns : N_s ≤ n := le_trans hm_Ns hn_m
      have hn_Nd : N_d ≤ n := le_trans hm_Nd hn_m
      obtain ⟨_, hus_half_raw, _, _⟩ := hN_d n hn_Nd
      obtain ⟨_, _, _, _, _, _, _, hus_nn, hus_le, _, _⟩ := hstep n hn_Ns
      have hus_half : u_s n ≤ 1 / 2 := hus_le.trans hus_half_raw
      have hxm_le_xn : xm ≤ ((n + 2 : ℕ) : ℝ) := by
        dsimp only [xm]; exact_mod_cast (by omega : m + 2 ≤ n + 2)
      have hus_xm : u_s n ≤ C_s / xm :=
        hus_le.trans (div_le_div_of_nonneg_left hCs_pos.le hxm_pos hxm_le_xn)
      have hqd := neg_log_one_sub_sub_le_sq hud_nn hud_half
      have hqs := neg_log_one_sub_sub_le_sq hus_nn hus_half
      have hud_sq : (u_d n) ^ 2 ≤ (4 * a * Real.log xm / xm) ^ 2 :=
        pow_le_pow_left₀ hud_nn hud_xm 2
      have hus_sq : (u_s n) ^ 2 ≤ (C_s / xm) ^ 2 :=
        pow_le_pow_left₀ hus_nn hus_xm 2
      calc |(-Real.log (1 - u_d n) - u_d n) - (-Real.log (1 - u_s n) - u_s n)|
          ≤ |-Real.log (1 - u_d n) - u_d n| + |-Real.log (1 - u_s n) - u_s n| := abs_sub _ _
        _ ≤ (u_d n) ^ 2 + (u_s n) ^ 2 := add_le_add hqd hqs
        _ ≤ (4 * a * Real.log xm / xm) ^ 2 + (C_s / xm) ^ 2 := add_le_add hud_sq hus_sq
        _ = ((16 * a ^ 2) * (Real.log xm) ^ 2 + C_s ^ 2) / xm ^ 2 := by ring
    have hcard : ((Finset.Ico m K).card : ℝ) = xm := by
      rw [Nat.card_Ico]; dsimp only [K, xm]; exact_mod_cast (by omega : 2 * m + 2 - m = m + 2)
    have hsum_le : |∑ n ∈ Finset.Ico m K,
        ((-Real.log (1 - u_d n) - u_d n) - (-Real.log (1 - u_s n) - u_s n))| ≤
        ((16 * a ^ 2) * (Real.log xm) ^ 2 + C_s ^ 2) / xm := by
      calc |∑ n ∈ Finset.Ico m K,
              ((-Real.log (1 - u_d n) - u_d n) - (-Real.log (1 - u_s n) - u_s n))|
          ≤ ∑ n ∈ Finset.Ico m K,
              |(-Real.log (1 - u_d n) - u_d n) - (-Real.log (1 - u_s n) - u_s n)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.Ico m K, (((16 * a ^ 2) * (Real.log xm) ^ 2 + C_s ^ 2) / xm ^ 2) :=
            Finset.sum_le_sum hterm
        _ = xm * (((16 * a ^ 2) * (Real.log xm) ^ 2 + C_s ^ 2) / xm ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard]
        _ = ((16 * a ^ 2) * (Real.log xm) ^ 2 + C_s ^ 2) / xm := by
            field_simp [hxm_pos.ne']
    have hlog2_le_pow : (Real.log xm) ^ 2 / xm ≤ xm ^ (-β) := by
      have h1 : (Real.log xm) ^ 2 / xm = ((Real.log xm) ^ 2 / xm ^ (1 - β)) * xm ^ (-β) := by
        rw [show xm ^ (-β) = (xm ^ β)⁻¹ by exact Real.rpow_neg hxm_pos.le β,
          ← div_eq_mul_inv, div_div, ← Real.rpow_add hxm_pos, sub_add_cancel, Real.rpow_one]
      rw [h1]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hxm_pos.le _) hlog2_xm
    have h1_le_log2 : 1 / xm ≤ xm ^ (-β) := by
      have h1 : 1 ≤ (Real.log xm) ^ 2 := by nlinarith only [hlog_xm_ge1]
      exact (div_le_div_of_nonneg_right h1 hxm_pos.le).trans hlog2_le_pow
    refine hsum_le.trans ?_
    rw [add_div, mul_div_assoc]
    calc 16 * a ^ 2 * ((Real.log xm) ^ 2 / xm) + C_s ^ 2 / xm
        ≤ 16 * a ^ 2 * xm ^ (-β) + C_s ^ 2 * xm ^ (-β) :=
          add_le_add (mul_le_mul_of_nonneg_left hlog2_le_pow (by positivity))
            (by rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h1_le_log2 (sq_nonneg C_s))
      _ = (16 * a ^ 2 + C_s ^ 2) * xm ^ (-β) := by ring
  -- Linear difference `∑ (u_d n - u_s n)` via complex step decomposition + summation by parts
  have hlin_sum : |∑ n ∈ Finset.Ico m K, (u_d n - u_s n)| ≤
      (C_s + 4 * a * c / δ + 2 * c / δ + c * C_s) * xm ^ (-β) := by
    let d_cross : ℕ → ℂ := fun n => (u_d n : ℂ) * E n * g n
    let d_rot : ℕ → ℂ := fun n =>
      (smoothBornCoefficient σ t k₀ (n + 1) - smoothBornCoefficient σ t k₀ n) * g n - (u_s n : ℂ)
    have hdecomp : ∀ n ∈ Finset.Ico m K,
        (u_d n : ℂ) - (u_s n : ℂ) = d_cross n + (E (n + 1) - E n) * g n + d_rot n := by
      intro n hn
      have hn_Ns : N_s ≤ n := le_trans hm_Ns (Finset.mem_Ico.mp hn).1
      obtain ⟨_, _, _, _, _, hBsm_n, hB_n, _, _, _, _⟩ := hstep n hn_Ns
      obtain ⟨hud_eq, _, _⟩ := hdisc_step n (by omega)
      set z₃ : ℂ := (phase t (n + 3) : ℂ) ^ (-k₀)
      have hz3_norm : ‖z₃‖ = 1 := by dsimp only [z₃]; rw [norm_zpow, Circle.norm_coe, one_zpow]
      have hden_sm_ne : z₃ - smoothBornCoefficient σ t k₀ n ≠ 0 := fun h0 => by
        have h := norm_sub_norm_le z₃ (smoothBornCoefficient σ t k₀ n)
        rw [hz3_norm, h0, norm_zero] at h
        linarith only [h, hBsm_n, hδ_pos]
      have hden_b_ne : z₃ - bornCoefficient σ t k₀ n ≠ 0 := fun h0 => by
        have h := norm_sub_norm_le z₃ (bornCoefficient σ t k₀ n)
        rw [hz3_norm, h0, norm_zero] at h
        linarith only [h, hB_n, hδ_pos]
      have hud_c : (u_d n : ℂ) =
          (bornCoefficient σ t k₀ (n + 1) - bornCoefficient σ t k₀ n) / (z₃ - bornCoefficient σ t k₀ n) :=
        hud_eq
      dsimp only [d_cross, d_rot, E, g]
      rw [hud_c]
      change (bornCoefficient σ t k₀ (n + 1) - bornCoefficient σ t k₀ n) /
          (z₃ - bornCoefficient σ t k₀ n) - (u_s n : ℂ) =
        (bornCoefficient σ t k₀ (n + 1) - bornCoefficient σ t k₀ n) /
          (z₃ - bornCoefficient σ t k₀ n) *
          (bornCoefficient σ t k₀ n - smoothBornCoefficient σ t k₀ n) *
          (z₃ - smoothBornCoefficient σ t k₀ n)⁻¹ +
        ((bornCoefficient σ t k₀ (n + 1) - smoothBornCoefficient σ t k₀ (n + 1)) -
          (bornCoefficient σ t k₀ n - smoothBornCoefficient σ t k₀ n)) *
          (z₃ - smoothBornCoefficient σ t k₀ n)⁻¹ +
        ((smoothBornCoefficient σ t k₀ (n + 1) - smoothBornCoefficient σ t k₀ n) *
          (z₃ - smoothBornCoefficient σ t k₀ n)⁻¹ - (u_s n : ℂ))
      field_simp [hden_sm_ne, hden_b_ne]
      ring
    have hcard : ((Finset.Ico m K).card : ℝ) = xm := by
      rw [Nat.card_Ico]; dsimp only [K, xm]; exact_mod_cast (by omega : 2 * m + 2 - m = m + 2)
    have hxm_pow_le : xm ^ (-α) ≤ xm ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le hxm_ge1 (by linarith only [hβα])
    have hg_bound : ∀ n : ℕ, N_s ≤ n → ‖g n‖ ≤ 1 / δ := by
      intro n hn
      obtain ⟨_, _, _, _, _, hBsm_n, _, _, _, _, _⟩ := hstep n hn
      set z₃ : ℂ := (phase t (n + 3) : ℂ) ^ (-k₀)
      have hz3_norm : ‖z₃‖ = 1 := by dsimp only [z₃]; rw [norm_zpow, Circle.norm_coe, one_zpow]
      have hden_ge : δ ≤ ‖z₃ - smoothBornCoefficient σ t k₀ n‖ := by
        have h := norm_sub_norm_le z₃ (smoothBornCoefficient σ t k₀ n)
        rw [hz3_norm] at h; linarith only [h, hBsm_n]
      dsimp only [g, z₃] at hden_ge ⊢
      rw [norm_inv, one_div]
      exact inv_anti₀ hδ_pos hden_ge
    -- Bound `∑ d_cross`
    have hcross_sum : ‖∑ n ∈ Finset.Ico m K, d_cross n‖ ≤ (4 * a * c / δ) * xm ^ (-β) := by
      have hterm : ∀ n ∈ Finset.Ico m K,
          ‖d_cross n‖ ≤ (4 * a * c / δ) * Real.log xm * xm ^ (-α) / xm := by
        intro n hn
        obtain ⟨hud_nn, _, hud_xm⟩ := hud_bound n hn
        have hn_m : m ≤ n := (Finset.mem_Ico.mp hn).1
        have hEn := herr n (le_trans hm_N0 hn_m)
        have hgn := hg_bound n (le_trans hm_Ns hn_m)
        have hxm_le_xn : xm ≤ ((n + 2 : ℕ) : ℝ) := by
          dsimp only [xm]; exact_mod_cast (by omega : m + 2 ≤ n + 2)
        have hEn_xm : ‖E n‖ ≤ c * xm ^ (-α) :=
          hEn.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hxm_pos hxm_le_xn (by linarith only [hα0])) hc.le)
        dsimp only [d_cross]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hud_nn]
        calc u_d n * ‖E n‖ * ‖g n‖
            ≤ (4 * a * Real.log xm / xm) * (c * xm ^ (-α)) * (1 / δ) :=
              mul_le_mul (mul_le_mul hud_xm hEn_xm (norm_nonneg _) (by positivity))
                hgn (norm_nonneg _) (by positivity)
          _ = (4 * a * c / δ) * Real.log xm * xm ^ (-α) / xm := by ring
      have h1 : ‖∑ n ∈ Finset.Ico m K, d_cross n‖ ≤
          (4 * a * c / δ) * (Real.log xm / xm ^ (α - β)) * xm ^ (-β) := by
        calc ‖∑ n ∈ Finset.Ico m K, d_cross n‖
            ≤ ∑ n ∈ Finset.Ico m K, ‖d_cross n‖ := norm_sum_le _ _
          _ ≤ ∑ _n ∈ Finset.Ico m K, ((4 * a * c / δ) * Real.log xm * xm ^ (-α) / xm) :=
              Finset.sum_le_sum hterm
          _ = xm * ((4 * a * c / δ) * Real.log xm * xm ^ (-α) / xm) := by
              rw [Finset.sum_const, nsmul_eq_mul, hcard]
          _ = (4 * a * c / δ) * (Real.log xm * xm ^ (-α)) := by field_simp [hxm_pos.ne']
          _ = (4 * a * c / δ) * (Real.log xm / xm ^ (α - β)) * xm ^ (-β) := by
              have hrp : xm ^ (-α) = xm ^ (-β) / xm ^ (α - β) := by
                rw [eq_div_iff (Real.rpow_pos_of_pos hxm_pos _).ne', ← Real.rpow_add hxm_pos]
                congr 1; ring
              rw [hrp]; ring
      calc ‖∑ n ∈ Finset.Ico m K, d_cross n‖
          ≤ (4 * a * c / δ) * 1 * xm ^ (-β) :=
            h1.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlog_αβ_xm (by positivity))
              (Real.rpow_nonneg hxm_pos.le _))
        _ = (4 * a * c / δ) * xm ^ (-β) := by ring
    -- Bound `∑ d_rot`
    have hrot_sum : ‖∑ n ∈ Finset.Ico m K, d_rot n‖ ≤ C_s * xm ^ (-β) := by
      have hterm : ∀ n ∈ Finset.Ico m K, ‖d_rot n‖ ≤ C_s / xm ^ 2 := by
        intro n hn
        have hn_m : m ≤ n := (Finset.mem_Ico.mp hn).1
        obtain ⟨_, _, _, _, _, _, _, _, _, hrot_n, _⟩ := hstep n (le_trans hm_Ns hn_m)
        have hxm_le_xn : xm ≤ ((n + 2 : ℕ) : ℝ) := by
          dsimp only [xm]; exact_mod_cast (by omega : m + 2 ≤ n + 2)
        have hsq : xm ^ 2 ≤ ((n + 2 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ hxm_pos.le hxm_le_xn 2
        dsimp only [d_rot, g]
        rw [← div_eq_mul_inv, norm_sub_rev]
        exact hrot_n.trans (div_le_div_of_nonneg_left hCs_pos.le (pow_pos hxm_pos 2) hsq)
      have h1_le_pow : 1 / xm ≤ xm ^ (-β) := by
        have h1 : 1 / xm = xm ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
        rw [h1]
        exact Real.rpow_le_rpow_of_exponent_le hxm_ge1 (by linarith only [hβ_half])
      calc ‖∑ n ∈ Finset.Ico m K, d_rot n‖
          ≤ ∑ n ∈ Finset.Ico m K, ‖d_rot n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.Ico m K, (C_s / xm ^ 2) := Finset.sum_le_sum hterm
        _ = xm * (C_s / xm ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
        _ = C_s * (1 / xm) := by field_simp [hxm_pos.ne']
        _ ≤ C_s * xm ^ (-β) := mul_le_mul_of_nonneg_left h1_le_pow hCs_pos.le
    -- Bound `∑ (E (n + 1) - E n) * g n` via summation by parts
    have hmain_sum : ‖∑ n ∈ Finset.Ico m K, (E (n + 1) - E n) * g n‖ ≤
        (2 * c / δ + c * C_s) * xm ^ (-β) := by
      rw [sum_Ico_diff_mul_eq E g hmK]
      have hEK : ‖E K * g K‖ ≤ (c / δ) * xm ^ (-α) := by
        rw [norm_mul]
        have h1 := herr K (le_trans hm_N0 hmK)
        have h2 := hg_bound K (le_trans hm_Ns hmK)
        have hxK_ge : xm ≤ ((K + 2 : ℕ) : ℝ) := by
          dsimp only [xm]; exact_mod_cast (by omega : m + 2 ≤ K + 2)
        have h1' : ‖E K‖ ≤ c * xm ^ (-α) :=
          h1.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hxm_pos hxK_ge (by linarith only [hα0])) hc.le)
        calc ‖E K‖ * ‖g K‖ ≤ (c * xm ^ (-α)) * (1 / δ) :=
              mul_le_mul h1' h2 (norm_nonneg _) (by positivity)
          _ = (c / δ) * xm ^ (-α) := by ring
      have hEm : ‖E m * g m‖ ≤ (c / δ) * xm ^ (-α) := by
        rw [norm_mul]
        calc ‖E m‖ * ‖g m‖ ≤ (c * xm ^ (-α)) * (1 / δ) :=
              mul_le_mul (herr m hm_N0) (hg_bound m hm_Ns) (norm_nonneg _) (by positivity)
          _ = (c / δ) * xm ^ (-α) := by ring
      have hsbp_sum : ‖∑ n ∈ Finset.Ico m K, E (n + 1) * (g (n + 1) - g n)‖ ≤
          (c * C_s) * xm ^ (-α) := by
        have hterm : ∀ n ∈ Finset.Ico m K,
            ‖E (n + 1) * (g (n + 1) - g n)‖ ≤ c * C_s * xm ^ (-α) / xm := by
          intro n hn
          have hn_m : m ≤ n := (Finset.mem_Ico.mp hn).1
          have hEn1 := herr (n + 1) (by omega)
          obtain ⟨_, _, _, _, _, _, _, _, _, _, hgn_diff⟩ := hstep n (le_trans hm_Ns hn_m)
          have hxm_le_xn : xm ≤ ((n + 2 : ℕ) : ℝ) := by
            dsimp only [xm]; exact_mod_cast (by omega : m + 2 ≤ n + 2)
          have hxm_le_xn1 : xm ≤ ((n + 1 + 2 : ℕ) : ℝ) := by
            dsimp only [xm]; exact_mod_cast (by omega : m + 2 ≤ n + 1 + 2)
          have hEn1' : ‖E (n + 1)‖ ≤ c * xm ^ (-α) :=
            hEn1.trans (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hxm_pos hxm_le_xn1 (by linarith only [hα0])) hc.le)
          have hgd' : ‖g (n + 1) - g n‖ ≤ C_s / xm := by
            dsimp only [g]
            have hcast4 : n + 1 + 3 = n + 4 := by omega
            rw [hcast4]
            exact hgn_diff.trans (div_le_div_of_nonneg_left hCs_pos.le hxm_pos hxm_le_xn)
          rw [norm_mul]
          calc ‖E (n + 1)‖ * ‖g (n + 1) - g n‖
              ≤ (c * xm ^ (-α)) * (C_s / xm) :=
                mul_le_mul hEn1' hgd' (norm_nonneg _) (by positivity)
            _ = c * C_s * xm ^ (-α) / xm := by ring
        calc ‖∑ n ∈ Finset.Ico m K, E (n + 1) * (g (n + 1) - g n)‖
            ≤ ∑ n ∈ Finset.Ico m K, ‖E (n + 1) * (g (n + 1) - g n)‖ := norm_sum_le _ _
          _ ≤ ∑ _n ∈ Finset.Ico m K, (c * C_s * xm ^ (-α) / xm) := Finset.sum_le_sum hterm
          _ = xm * (c * C_s * xm ^ (-α) / xm) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
          _ = (c * C_s) * xm ^ (-α) := by field_simp [hxm_pos.ne']
      have htot_α : ‖E K * g K - E m * g m - ∑ n ∈ Finset.Ico m K, E (n + 1) * (g (n + 1) - g n)‖ ≤
          (2 * c / δ + c * C_s) * xm ^ (-α) := by
        have htri1 := norm_sub_le (E K * g K - E m * g m)
          (∑ n ∈ Finset.Ico m K, E (n + 1) * (g (n + 1) - g n))
        have htri2 := norm_sub_le (E K * g K) (E m * g m)
        have halg_α : c / δ * xm ^ (-α) + c / δ * xm ^ (-α) + c * C_s * xm ^ (-α) =
            (2 * c / δ + c * C_s) * xm ^ (-α) := by ring
        linarith only [htri1, htri2, hEK, hEm, hsbp_sum, halg_α]
      exact htot_α.trans (mul_le_mul_of_nonneg_left hxm_pow_le (by positivity))
    -- Combine complex norm with real sum
    have hreal_le_norm : |∑ n ∈ Finset.Ico m K, (u_d n - u_s n)| ≤
        ‖∑ n ∈ Finset.Ico m K, ((u_d n : ℂ) - (u_s n : ℂ))‖ := by
      have hcast : ((∑ n ∈ Finset.Ico m K, (u_d n - u_s n) : ℝ) : ℂ) =
          ∑ n ∈ Finset.Ico m K, ((u_d n : ℂ) - (u_s n : ℂ)) := by push_cast; rfl
      rw [← Real.norm_eq_abs, ← Complex.norm_real, hcast]
    rw [Finset.sum_congr rfl hdecomp, Finset.sum_add_distrib, Finset.sum_add_distrib] at hreal_le_norm
    have htri_a := norm_add_le
      (∑ n ∈ Finset.Ico m K, d_cross n + ∑ n ∈ Finset.Ico m K, (E (n + 1) - E n) * g n)
      (∑ n ∈ Finset.Ico m K, d_rot n)
    have htri_b := norm_add_le
      (∑ n ∈ Finset.Ico m K, d_cross n)
      (∑ n ∈ Finset.Ico m K, (E (n + 1) - E n) * g n)
    have halg_β : 4 * a * c / δ * xm ^ (-β) + (2 * c / δ + c * C_s) * xm ^ (-β) + C_s * xm ^ (-β) =
        (C_s + 4 * a * c / δ + 2 * c / δ + c * C_s) * xm ^ (-β) := by ring
    linarith only [hreal_le_norm, htri_a, htri_b, hcross_sum, hmain_sum, hrot_sum, halg_β]
  change |r K - r m| ≤ _
  rw [htel_r, Finset.sum_congr rfl hr_step, Finset.sum_add_distrib]
  calc |(∑ n ∈ Finset.Ico m K,
            ((-Real.log (1 - u_d n) - u_d n) - (-Real.log (1 - u_s n) - u_s n))) +
          ∑ n ∈ Finset.Ico m K, (u_d n - u_s n)|
      ≤ |∑ n ∈ Finset.Ico m K,
            ((-Real.log (1 - u_d n) - u_d n) - (-Real.log (1 - u_s n) - u_s n))| +
          |∑ n ∈ Finset.Ico m K, (u_d n - u_s n)| := abs_add_le _ _
    _ ≤ (16 * a ^ 2 + C_s ^ 2) * xm ^ (-β) +
          (C_s + 4 * a * c / δ + 2 * c / δ + c * C_s) * xm ^ (-β) :=
        add_le_add hquad_sum hlin_sum
    _ = C_oct * xm ^ (-β) := by dsimp only [C_oct]; ring

private theorem smoothMass_sub_bornMass_bound_of_dyadic_log_ratio {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) {β : ℝ} (hβ0 : 0 < β)
    {M₁ : ℕ} {C_oct : ℝ} (hC_oct : 0 < C_oct)
    (hoct : ∀ m : ℕ, M₁ ≤ m →
      |Real.log (bornMass σ (2 * m + 2) / smoothMassReal σ ((2 * m + 4 : ℕ) : ℝ)) -
        Real.log (bornMass σ m / smoothMassReal σ ((m + 2 : ℕ) : ℝ))| ≤
          C_oct * ((m + 2 : ℕ) : ℝ) ^ (-β)) :
    ∃ (M₂ : ℕ) (C_HM : ℝ), 0 < C_HM ∧
      ∀ m : ℕ, M₂ ≤ m →
        |smoothMassReal σ ((m + 2 : ℕ) : ℝ) - bornMass σ m| ≤
          C_HM * ((m + 2 : ℕ) : ℝ) ^ (1 - 2 * σ - β) / Real.log ((m + 2 : ℕ) : ℝ) := by
  set a : ℝ := 1 - 2 * σ with ha_def
  have ha0 : 0 < a := by linarith only [ha_def, hσ1]
  have ha1 : a < 1 := by linarith only [ha_def, hσ0]
  let xseq : ℕ → ℝ := fun n => ((n + 2 : ℕ) : ℝ)
  have hx_top : Tendsto xseq atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hH_asymp := (smoothMassReal_asymptotic hσ0 hσ1).comp hx_top
  have hM_asymp : Tendsto (fun n : ℕ =>
      bornMass σ n * (a * Real.log (xseq n) / (xseq n) ^ a)) atTop (𝓝 1) := by
    have hm := (powerMass_asymptotic ha0 ha1).comp hx_top
    refine hm.congr fun n => ?_
    dsimp only [Function.comp_apply, xseq]
    have hcut : cutoff ((n + 2 : ℕ) : ℝ) = n := by unfold cutoff; rw [Nat.floor_natCast]; omega
    rw [powerMass, hcut, bornMass, mul_div_assoc]
    have hsum_eq : (∑ p ∈ primes n, (p : ℝ) ^ (a - 1)) = ∑ p ∈ primes n, bornWeight σ p :=
      Finset.sum_congr rfl fun p _ => by
        rw [bornWeight, show a - 1 = -(2 * σ) by linarith only [ha_def]]
    rw [hsum_eq]
  let r : ℕ → ℝ := fun n => Real.log (bornMass σ n / smoothMassReal σ (xseq n))
  have hr_lim : Tendsto r atTop (𝓝 0) := by
    have hquot := hM_asymp.div hH_asymp one_ne_zero
    rw [div_one] at hquot
    have hlog_lim := (Real.continuousAt_log one_ne_zero).tendsto.comp hquot
    rw [Real.log_one] at hlog_lim
    refine hlog_lim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp only [Function.comp_apply, Pi.div_apply, r, xseq]
    rw [← ha_def]
    have hxn_gt1 : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n + 2)
    have hsc_ne : a * Real.log ((n + 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) ^ a ≠ 0 :=
      (div_pos (mul_pos ha0 (Real.log_pos hxn_gt1))
        (Real.rpow_pos_of_pos (zero_lt_one.trans hxn_gt1) a)).ne'
    rw [mul_div_mul_right _ _ hsc_ne]
  let τ : ℕ → ℕ := fun k => 2 * k + 2
  have hτ_ge : ∀ (j k : ℕ), k + j ≤ τ^[j] k := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      have h := ih k
      rw [Function.iterate_succ_apply']
      change k + (j + 1) ≤ 2 * (τ^[j] k) + 2
      omega
  have hτ_x : ∀ (j k : ℕ), xseq (τ^[j] k) = (2 : ℝ) ^ j * xseq k := by
    intro j
    induction j with
    | zero => intro k; simp [xseq]
    | succ j ih =>
      intro k
      rw [Function.iterate_succ_apply', pow_succ']
      have hk := ih k
      dsimp only [xseq, τ] at hk ⊢
      push_cast at hk ⊢
      linarith only [hk]
  set q : ℝ := (2 : ℝ) ^ (-β)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos zero_lt_two _
  have hq_lt1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith only [hβ0])
  have h1q_pos : 0 < 1 - q := by linarith only [hq_lt1]
  have hgeom : ∀ K : ℕ, ∑ j ∈ Finset.range K, q ^ j ≤ 1 / (1 - q) := by
    intro K
    have hid : (1 - q) * ∑ j ∈ Finset.range K, q ^ j = 1 - q ^ K := by
      induction K with
      | zero => simp
      | succ K ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
    have hle1 : (1 - q) * ∑ j ∈ Finset.range K, q ^ j ≤ 1 := by
      rw [hid]; linarith only [pow_nonneg hq_pos.le K]
    exact (le_div_iff₀' h1q_pos).mpr hle1
  set C_r : ℝ := C_oct / (1 - q)
  have hC_r_pos : 0 < C_r := div_pos hC_oct h1q_pos
  have hr_bound : ∀ m : ℕ, M₁ ≤ m → |r m| ≤ C_r * (xseq m) ^ (-β) := by
    intro m hm
    have hK_bound : ∀ K : ℕ, |r m - r (τ^[K] m)| ≤ C_r * (xseq m) ^ (-β) := by
      intro K
      have htel : r m - r (τ^[K] m) = ∑ j ∈ Finset.range K, (r (τ^[j] m) - r (τ (τ^[j] m))) := by
        induction K with
        | zero => simp
        | succ K ih =>
          rw [Finset.sum_range_succ, Function.iterate_succ_apply', ← ih]; ring
      rw [htel]
      have hterm : ∀ j ∈ Finset.range K,
          |r (τ^[j] m) - r (τ (τ^[j] m))| ≤ C_oct * (xseq m) ^ (-β) * q ^ j := by
        intro j _
        have hkj : M₁ ≤ τ^[j] m := le_trans hm (le_trans (Nat.le_add_right m j) (hτ_ge j m))
        have ho := hoct (τ^[j] m) hkj
        have hcast : 2 * τ^[j] m + 2 + 2 = 2 * τ^[j] m + 4 := by omega
        dsimp only [r, xseq, τ]
        rw [hcast, abs_sub_comm]
        have hx_pow : (((τ^[j] m + 2 : ℕ) : ℝ)) ^ (-β) = (xseq m) ^ (-β) * q ^ j := by
          change (xseq (τ^[j] m)) ^ (-β) = _
          rw [hτ_x j m, Real.mul_rpow (pow_nonneg zero_le_two j) (by dsimp only [xseq]; positivity),
            ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul zero_le_two,
            mul_comm (j : ℝ) (-β), Real.rpow_mul zero_le_two, Real.rpow_natCast]
          dsimp only [q]; ring
        rw [hx_pow] at ho
        linarith only [ho]
      calc |∑ j ∈ Finset.range K, (r (τ^[j] m) - r (τ (τ^[j] m)))|
          ≤ ∑ j ∈ Finset.range K, |r (τ^[j] m) - r (τ (τ^[j] m))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range K, (C_oct * (xseq m) ^ (-β) * q ^ j) := Finset.sum_le_sum hterm
        _ = C_oct * (xseq m) ^ (-β) * ∑ j ∈ Finset.range K, q ^ j := by rw [← Finset.mul_sum]
        _ ≤ C_oct * (xseq m) ^ (-β) * (1 / (1 - q)) :=
            mul_le_mul_of_nonneg_left (hgeom K)
              (mul_nonneg hC_oct.le (Real.rpow_nonneg (by dsimp only [xseq]; positivity) _))
        _ = C_r * (xseq m) ^ (-β) := by dsimp only [C_r]; ring
    have hτ_top : Tendsto (fun K : ℕ => τ^[K] m) atTop atTop :=
      tendsto_atTop_mono (fun K => le_trans (Nat.le_add_left K m) (hτ_ge K m))
        tendsto_id
    have hlim_K : Tendsto (fun K : ℕ => |r m - r (τ^[K] m)|) atTop (𝓝 |r m|) := by
      have hs := ((tendsto_const_nhds (x := r m)).sub (hr_lim.comp hτ_top)).abs
      rwa [sub_zero] at hs
    exact le_of_tendsto hlim_K (Eventually.of_forall hK_bound)
  have hev_M2 : ∀ᶠ m : ℕ in atTop,
      1 / 2 ≤ smoothMassReal σ (xseq m) * (a * Real.log (xseq m) / (xseq m) ^ a) ∧
      smoothMassReal σ (xseq m) * (a * Real.log (xseq m) / (xseq m) ^ a) ≤ 2 ∧
      0 < bornMass σ m ∧
      C_r * (xseq m) ^ (-β) ≤ 1 / 2 := by
    have h1 := hH_asymp.eventually (Icc_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
    have h2 : ∀ᶠ m : ℕ in atTop, 0 < bornMass σ m := by
      filter_upwards [eventually_ge_atTop 1] with m hm
      apply sum_pos' (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
      exact ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩,
        Real.rpow_pos_of_pos (by norm_num) _⟩
    have h3_lim : Tendsto (fun m : ℕ => C_r * (xseq m) ^ (-β)) atTop (𝓝 0) := by
      have h0 := ((tendsto_rpow_neg_atTop hβ0).comp hx_top).const_mul C_r
      rwa [mul_zero] at h0
    filter_upwards [h1, h2, h3_lim.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with m hm1 hm2 hm3
    exact ⟨hm1.1, hm1.2, hm2, hm3⟩
  rw [Filter.eventually_atTop] at hev_M2
  obtain ⟨N_m2, hN_m2⟩ := hev_M2
  set M₂ : ℕ := max (max M₁ N_m2) 2
  set C_HM : ℝ := 4 * C_r / a
  refine ⟨M₂, C_HM, by positivity, fun m hm => ?_⟩
  have hm_M1 : M₁ ≤ m := le_trans (le_trans (le_max_left M₁ N_m2) (le_max_left _ 2)) hm
  have hm_Nm2 : N_m2 ≤ m := le_trans (le_trans (le_max_right M₁ N_m2) (le_max_left _ 2)) hm
  have hm2 : 2 ≤ m := le_trans (le_max_right _ 2) hm
  obtain ⟨hH_lo, hH_hi, hM_pos, hCr_half⟩ := hN_m2 m hm_Nm2
  set xm : ℝ := xseq m
  have hxm_pos : 0 < xm := by dsimp only [xm, xseq]; positivity
  have hlog_pos : 0 < Real.log xm := Real.log_pos (by dsimp only [xm, xseq]; exact_mod_cast (by omega : 1 < m + 2))
  have hxa_pos : 0 < xm ^ a := Real.rpow_pos_of_pos hxm_pos a
  have hsc_pos : 0 < a * Real.log xm / xm ^ a := div_pos (mul_pos ha0 hlog_pos) hxa_pos
  have hH_pos : 0 < smoothMassReal σ xm := by
    have h := (div_le_iff₀ hsc_pos).mpr hH_lo
    exact lt_of_lt_of_le (div_pos (by norm_num : (0 : ℝ) < 1 / 2) hsc_pos) h
  have hH_upper : smoothMassReal σ xm ≤ 2 * xm ^ a / (a * Real.log xm) := by
    have h := (le_div_iff₀ hsc_pos).mpr hH_hi
    refine h.trans (le_of_eq ?_)
    field_simp [ha0.ne', hlog_pos.ne', hxa_pos.ne']
  have hrm_le : |r m| ≤ C_r * xm ^ (-β) := hr_bound m hm_M1
  have hrm_half : |r m| ≤ 1 / 2 := hrm_le.trans hCr_half
  have hexp_rm : Real.exp (r m) = bornMass σ m / smoothMassReal σ xm :=
    Real.exp_log (div_pos hM_pos hH_pos)
  have hdiff_eq : |smoothMassReal σ xm - bornMass σ m| =
      smoothMassReal σ xm * |Real.exp (r m) - 1| := by
    rw [hexp_rm, show smoothMassReal σ xm - bornMass σ m =
      -(smoothMassReal σ xm * (bornMass σ m / smoothMassReal σ xm - 1)) by
      field_simp [hH_pos.ne']; ring, abs_neg, abs_mul, abs_of_pos hH_pos]
  rw [hdiff_eq]
  have hexp_b := abs_exp_sub_one_le_two_abs hrm_half
  calc smoothMassReal σ xm * |Real.exp (r m) - 1|
      ≤ (2 * xm ^ a / (a * Real.log xm)) * (2 * (C_r * xm ^ (-β))) :=
        mul_le_mul hH_upper (hexp_b.trans (mul_le_mul_of_nonneg_left hrm_le zero_le_two))
          (abs_nonneg _) (by positivity)
    _ = (4 * C_r / a) * (xm ^ a * xm ^ (-β)) / Real.log xm := by ring
    _ = C_HM * xm ^ (1 - 2 * σ - β) / Real.log xm := by
        rw [← Real.rpow_add hxm_pos, show a + -β = 1 - 2 * σ - β by linarith only [ha_def]]

private theorem theta_deficit_bound_of_mass_diff_bound {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) {β : ℝ} (hβ0 : 0 < β) (hβ_half : β < 1 / 2)
    {M₂ : ℕ} {C_HM : ℝ} (hC_HM : 0 < C_HM)
    (hmass_diff : ∀ m : ℕ, M₂ ≤ m →
      |smoothMassReal σ ((m + 2 : ℕ) : ℝ) - bornMass σ m| ≤
        C_HM * ((m + 2 : ℕ) : ℝ) ^ (1 - 2 * σ - β) / Real.log ((m + 2 : ℕ) : ℝ)) :
    ∃ (m₀ : ℕ) (C_fin : ℝ), 0 < C_fin ∧
      ∀ N : ℕ, m₀ ≤ N →
        ((N + 2 : ℕ) : ℝ) - Chebyshev.theta ((N + 2 : ℕ) : ℝ) ≤
          C_fin * ((N + 2 : ℕ) : ℝ) ^ (1 - β) := by
  set m₀ : ℕ := max M₂ 4
  let G : ℕ → ℝ := fun j => smoothMassReal σ ((j + 2 : ℕ) : ℝ) - bornMass σ j
  let w : ℕ → ℝ := fun j => ((j + 3 : ℕ) : ℝ) ^ (2 * σ) * Real.log ((j + 3 : ℕ) : ℝ)
  have h1_sub_β : 0 < 1 - β := by linarith only [hβ_half]
  -- Exact prime step identity for `w j * (bornMass σ (j + 1) - bornMass σ j)`
  have htheta_step : ∀ j : ℕ, 4 ≤ j →
      w j * (bornMass σ (j + 1) - bornMass σ j) =
        Chebyshev.theta ((j + 3 : ℕ) : ℝ) - Chebyshev.theta ((j + 2 : ℕ) : ℝ) := by
    intro j _
    have hth_eq : Chebyshev.theta ((j + 3 : ℕ) : ℝ) - Chebyshev.theta ((j + 2 : ℕ) : ℝ) =
        if (j + 3).Prime then Real.log ((j + 3 : ℕ) : ℝ) else 0 := by
      rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast, Nat.floor_natCast,
        Finset.sum_filter, Finset.sum_filter,
        show j + 3 = (j + 2) + 1 by omega, Finset.sum_Ioc_succ_top (Nat.zero_le _)]
      ring
    have hbm_eq : bornMass σ (j + 1) - bornMass σ j =
        if (j + 3).Prime then ((j + 3 : ℕ) : ℝ) ^ (-(2 * σ)) else 0 := by
      by_cases hp : (j + 3).Prime
      · have hins : primes (j + 1) = insert (j + 3) (primes j) := by
          ext p; simp only [primes, Nat.mem_primesBelow, Finset.mem_insert]
          exact ⟨fun ⟨hlt, hpp⟩ => by by_cases h : p = j + 3 <;> [exact Or.inl h; exact Or.inr ⟨by omega, hpp⟩],
            fun h => h.elim (fun hr => ⟨by omega, hr ▸ hp⟩) (fun ⟨hlt, hpp⟩ => ⟨by omega, hpp⟩)⟩
        have hnot : j + 3 ∉ primes j := fun hm => (Nat.mem_primesBelow.mp hm).1.ne rfl
        rw [if_pos hp, bornMass, hins, Finset.sum_insert hnot, bornMass, bornWeight]
        ring
      · have heq_pr : primes (j + 1) = primes j := by
          ext p; simp only [primes, Nat.mem_primesBelow]
          constructor
          · rintro ⟨hlt, hpp⟩
            by_cases h : p = j + 3
            · subst h; exact absurd hpp hp
            · exact ⟨by omega, hpp⟩
          · rintro ⟨hlt, hpp⟩; exact ⟨by omega, hpp⟩
        rw [if_neg hp, bornMass, bornMass, heq_pr, sub_self]
    rw [hth_eq, hbm_eq]
    split_ifs with hp
    · dsimp only [w]
      have hpos : (0 : ℝ) < ((j + 3 : ℕ) : ℝ) := by positivity
      calc ((j + 3 : ℕ) : ℝ) ^ (2 * σ) * Real.log ((j + 3 : ℕ) : ℝ) *
            ((j + 3 : ℕ) : ℝ) ^ (-(2 * σ))
          = (((j + 3 : ℕ) : ℝ) ^ (2 * σ) * ((j + 3 : ℕ) : ℝ) ^ (-(2 * σ))) *
              Real.log ((j + 3 : ℕ) : ℝ) := by ring
        _ = Real.log ((j + 3 : ℕ) : ℝ) := by
            rw [← Real.rpow_add hpos, add_neg_cancel, Real.rpow_zero, one_mul]
    · ring
  -- Lower bound `1 ≤ w j * (smoothMassReal σ (j + 3) - smoothMassReal σ (j + 2))`
  have hsmooth_step_ge1 : ∀ j : ℕ, 4 ≤ j →
      1 ≤ w j * (smoothMassReal σ ((j + 3 : ℕ) : ℝ) - smoothMassReal σ ((j + 2 : ℕ) : ℝ)) := by
    intro j hj4
    set x0 : ℝ := ((j + 2 : ℕ) : ℝ)
    set x1 : ℝ := ((j + 3 : ℕ) : ℝ)
    have hx0_2 : 2 ≤ x0 := by dsimp only [x0]; exact_mod_cast (by omega : 2 ≤ j + 2)
    have hx1_eq : x1 = x0 + 1 := by dsimp only [x0, x1]; push_cast; ring
    have hx01 : x0 ≤ x1 := by linarith only [hx1_eq]
    have hx1_pos : 0 < x1 := by linarith only [hx0_2, hx01]
    have hlog1_pos : 0 < Real.log x1 := Real.log_pos (by linarith only [hx0_2, hx1_eq])
    rw [smoothMassReal_sub_eq_integral hσ1 hx0_2 hx01]
    have hcont : IntervalIntegrable (fun u : ℝ => u ^ (-(2 * σ)) / Real.log u) volume x0 x1 := by
      refine (ContinuousOn.div
        (ContinuousOn.rpow_const (fun _ _ => continuousWithinAt_id) fun u hu =>
          Or.inl (by linarith only [hx0_2, hu.1] : u ≠ 0))
        (ContinuousOn.log (continuousOn_id : ContinuousOn (fun u : ℝ => u) (Icc x0 x1)) fun u hu =>
          (by linarith only [hx0_2, hu.1] : u ≠ 0))
        fun u hu => by
          dsimp only [Function.comp_apply, id]
          exact (Real.log_pos (by linarith only [hx0_2, hu.1])).ne').intervalIntegrable_of_Icc hx01
    have hm := intervalIntegral.integral_mono_on hx01
      (intervalIntegrable_const (c := x1 ^ (-(2 * σ)) / Real.log x1)) hcont fun u hu => by
        have hu_pos : 0 < u := by linarith only [hx0_2, hu.1]
        have hlogu_pos : 0 < Real.log u := Real.log_pos (by linarith only [hx0_2, hu.1])
        have hrp : x1 ^ (-(2 * σ)) ≤ u ^ (-(2 * σ)) :=
          Real.rpow_le_rpow_of_nonpos hu_pos hu.2 (by linarith only [hσ0])
        exact div_le_div_of_le_of_le (Real.rpow_nonneg hu_pos.le _) hrp
          hlogu_pos (Real.log_le_log hu_pos hu.2)
    rw [intervalIntegral.integral_const, show x1 - x0 = 1 by linarith only [hx1_eq], one_smul] at hm
    have hw_pos : 0 < w j := by
      dsimp only [w]; exact mul_pos (Real.rpow_pos_of_pos hx1_pos _) hlog1_pos
    have hprod := mul_le_mul_of_nonneg_left hm hw_pos.le
    have hlhs : w j * (x1 ^ (-(2 * σ)) / Real.log x1) = 1 := by
      dsimp only [w]
      change (x1 ^ (2 * σ) * Real.log x1) * (x1 ^ (-(2 * σ)) / Real.log x1) = 1
      have h1 : x1 ^ (2 * σ) * x1 ^ (-(2 * σ)) = 1 := by
        rw [← Real.rpow_add hx1_pos, add_neg_cancel, Real.rpow_zero]
      calc (x1 ^ (2 * σ) * Real.log x1) * (x1 ^ (-(2 * σ)) / Real.log x1)
          = (x1 ^ (2 * σ) * x1 ^ (-(2 * σ))) * (Real.log x1 / Real.log x1) := by ring
        _ = 1 := by rw [h1, div_self hlog1_pos.ne', one_mul]
    rwa [hlhs] at hprod
  -- Derivative bound on `w (j + 1) - w j`
  have hw_diff_bound : ∀ j : ℕ, 4 ≤ j →
      |w (j + 1) - w j| ≤ 3 * ((j + 3 : ℕ) : ℝ) ^ (2 * σ - 1) * Real.log ((j + 3 : ℕ) : ℝ) := by
    intro j hj4
    set u0 : ℝ := ((j + 3 : ℕ) : ℝ)
    set u1 : ℝ := ((j + 4 : ℕ) : ℝ)
    have hu0_ge7 : (7 : ℝ) ≤ u0 := by dsimp only [u0]; exact_mod_cast (by omega : 7 ≤ j + 3)
    have hu0_pos : 0 < u0 := by linarith only [hu0_ge7]
    have hu1_eq : u1 = u0 + 1 := by dsimp only [u0, u1]; push_cast; ring
    have hu01 : u0 ≤ u1 := by linarith only [hu1_eq]
    have hlog_u0_ge1 : 1 ≤ Real.log u0 := by
      have hexp_lt7 : Real.exp 1 ≤ 7 := by have := Real.exp_one_lt_d9; linarith
      have h := Real.log_le_log (Real.exp_pos 1) (hexp_lt7.trans hu0_ge7)
      rwa [Real.log_exp] at h
    have hlog_u1_le : Real.log u1 ≤ 2 * Real.log u0 := by
      have h := log_sub_log_le_div hu0_pos hu01
      have hsub1 : u1 - u0 = 1 := by linarith only [hu1_eq]
      rw [hsub1] at h
      have hinv : 1 / u0 ≤ 1 := div_le_one_of_le₀ (by linarith only [hu0_ge7]) hu0_pos.le
      linarith only [h, hinv, hlog_u0_ge1]
    let d_fn : ℝ → ℝ := fun u => u ^ (2 * σ - 1) * (2 * σ * Real.log u + 1)
    have hint : IntervalIntegrable d_fn volume u0 u1 := by
      refine (ContinuousOn.mul
        (ContinuousOn.rpow_const (fun _ _ => continuousWithinAt_id) fun u hu =>
          Or.inl (by linarith only [hu0_ge7, hu.1] : u ≠ 0))
        ((continuousOn_const.mul (ContinuousOn.log (continuousOn_id : ContinuousOn (fun u : ℝ => u) (Icc u0 u1)) fun u hu =>
          (by linarith only [hu0_ge7, hu.1] : u ≠ 0))).add continuousOn_const)).intervalIntegrable_of_Icc hu01
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => by
        rw [Set.uIcc_of_le hu01] at hu
        have hu_pos : 0 < u := by linarith only [hu0_ge7, hu.1]
        have hd1 := Real.hasDerivAt_rpow_const (x := u) (p := 2 * σ) (Or.inl hu_pos.ne')
        have hd2 := Real.hasDerivAt_log hu_pos.ne'
        refine (hd1.mul hd2).congr_deriv ?_
        have hpow_inv : u ^ (2 * σ) * u⁻¹ = u ^ (2 * σ - 1) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hu_pos, show 2 * σ + -1 = 2 * σ - 1 by ring]
        dsimp only [d_fn]
        rw [hpow_inv]; ring) hint
    change (∫ y in u0..u1, d_fn y) = u1 ^ (2 * σ) * Real.log u1 - u0 ^ (2 * σ) * Real.log u0 at hftc
    have hw_sub : w (j + 1) - w j = ∫ u in u0..u1, d_fn u := by
      have hcast4 : ((j + 1 + 3 : ℕ) : ℝ) = u1 := rfl
      dsimp only [w]
      rw [hcast4]
      exact hftc.symm
    have hd_nn : 0 ≤ w (j + 1) - w j := by
      rw [hw_sub]
      exact intervalIntegral.integral_nonneg hu01 fun u hu => by
        dsimp only [d_fn]
        have hu_pos : 0 < u := by linarith only [hu0_ge7, hu.1]
        have hlg_nn : 0 ≤ Real.log u := (Real.log_pos (by linarith only [hu0_ge7, hu.1])).le
        exact mul_nonneg (Real.rpow_nonneg hu_pos.le _) (by nlinarith only [hσ0, hlg_nn])
    rw [abs_of_nonneg hd_nn, hw_sub]
    have hm := intervalIntegral.integral_mono_on hu01 hint
      (intervalIntegrable_const (c := 3 * u0 ^ (2 * σ - 1) * Real.log u0)) fun u hu => by
        dsimp only [d_fn]
        have hu_pos : 0 < u := by linarith only [hu0_ge7, hu.1]
        have hrp : u ^ (2 * σ - 1) ≤ u0 ^ (2 * σ - 1) :=
          Real.rpow_le_rpow_of_nonpos hu0_pos hu.1 (by linarith only [hσ1])
        have hlg_u : Real.log u ≤ 2 * Real.log u0 :=
          (Real.log_le_log hu_pos hu.2).trans hlog_u1_le
        have hlin_b : 2 * σ * Real.log u + 1 ≤ 3 * Real.log u0 := by
          nlinarith only [hσ0, hσ1, hlg_u, hlog_u0_ge1]
        calc u ^ (2 * σ - 1) * (2 * σ * Real.log u + 1)
            ≤ u0 ^ (2 * σ - 1) * (3 * Real.log u0) :=
              mul_le_mul hrp hlin_b (by nlinarith only [hσ0, hlog_u0_ge1, Real.log_le_log hu0_pos hu.1])
                (Real.rpow_nonneg hu0_pos.le _)
          _ = 3 * u0 ^ (2 * σ - 1) * Real.log u0 := by ring
    rw [intervalIntegral.integral_const, show u1 - u0 = 1 by linarith only [hu1_eq], one_smul] at hm
    exact hm
  set C₀ : ℝ := |(((m₀ + 2 : ℕ) : ℝ) - Chebyshev.theta ((m₀ + 2 : ℕ) : ℝ)) - G m₀ * w m₀|
  set C_fin : ℝ := C₀ + 4 * C_HM + 3 * C_HM / (1 - β) + 1
  have hC_fin_pos : 0 < C_fin := by dsimp only [C_fin, C₀]; positivity
  refine ⟨m₀, C_fin, hC_fin_pos, fun N hN => ?_⟩
  have hm0_M2 : M₂ ≤ m₀ := le_max_left _ _
  have hm0_4 : 4 ≤ m₀ := le_max_right _ _
  -- Sum `1 - Δθ j ≤ (G (j + 1) - G j) * w j` over `j ∈ Ico m₀ N`
  have htel_lhs : ∑ j ∈ Finset.Ico m₀ N,
      (1 - (Chebyshev.theta ((j + 3 : ℕ) : ℝ) - Chebyshev.theta ((j + 2 : ℕ) : ℝ))) =
      (((N + 2 : ℕ) : ℝ) - Chebyshev.theta ((N + 2 : ℕ) : ℝ)) -
        (((m₀ + 2 : ℕ) : ℝ) - Chebyshev.theta ((m₀ + 2 : ℕ) : ℝ)) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
    induction d with
    | zero => simp
    | succ d ih =>
      have hmd : m₀ ≤ m₀ + d := by omega
      rw [show m₀ + (d + 1) = (m₀ + d) + 1 by omega, Finset.sum_Ico_succ_top hmd, ih hmd]
      have hc1 : ((m₀ + d + 1 + 2 : ℕ) : ℝ) = ((m₀ + d + 3 : ℕ) : ℝ) := by push_cast; ring
      have hc2 : ((m₀ + d + 3 : ℕ) : ℝ) = ((m₀ + d + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hc1]; linarith only [hc2]
  have hstep_le : ∑ j ∈ Finset.Ico m₀ N,
      (1 - (Chebyshev.theta ((j + 3 : ℕ) : ℝ) - Chebyshev.theta ((j + 2 : ℕ) : ℝ))) ≤
      ∑ j ∈ Finset.Ico m₀ N, (G (j + 1) - G j) * w j := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj4 : 4 ≤ j := le_trans hm0_4 (Finset.mem_Ico.mp hj).1
    have h1 := hsmooth_step_ge1 j hj4
    have h2 := htheta_step j hj4
    have hc3 : ((j + 1 + 2 : ℕ) : ℝ) = ((j + 3 : ℕ) : ℝ) := by push_cast; ring
    dsimp only [G]
    rw [hc3]
    linarith only [h1, h2]
  rw [htel_lhs, sum_Ico_diff_mul_eq G w hN] at hstep_le
  set xN : ℝ := ((N + 2 : ℕ) : ℝ)
  have hxN_ge6 : (6 : ℝ) ≤ xN := by dsimp only [xN]; exact_mod_cast (by omega : 6 ≤ N + 2)
  have hxN_pos : 0 < xN := by linarith only [hxN_ge6]
  have hxN_ge1 : 1 ≤ xN := by linarith only [hxN_ge6]
  have h1_le_xN_pow : 1 ≤ xN ^ (1 - β) := Real.one_le_rpow hxN_ge1 h1_sub_β.le
  -- Boundary term `|G N * w N|`
  have hGN_wN : |G N * w N| ≤ 4 * C_HM * xN ^ (1 - β) := by
    have hGN := hmass_diff N (le_trans hm0_M2 hN)
    set xN1 : ℝ := ((N + 3 : ℕ) : ℝ)
    have hxN1_le_2 : xN1 ≤ 2 * xN := by
      dsimp only [xN, xN1]; exact_mod_cast (by omega : N + 3 ≤ 2 * (N + 2))
    have hxN1_le_sq : xN1 ≤ xN ^ 2 := by nlinarith only [hxN_ge6, hxN1_le_2]
    have hxN1_pos : 0 < xN1 := by linarith only [hxN_pos, (show xN ≤ xN1 by
      dsimp only [xN, xN1]; exact_mod_cast (by omega : N + 2 ≤ N + 3))]
    have hlog_xN_pos : 0 < Real.log xN := Real.log_pos (by linarith only [hxN_ge6])
    have hlog_xN1_le : Real.log xN1 ≤ 2 * Real.log xN := by
      have h := Real.log_le_log hxN1_pos hxN1_le_sq
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    have hrp_xN1 : xN1 ^ (2 * σ) ≤ 2 * xN ^ (2 * σ) := by
      have h2pow : (2 : ℝ) ^ (2 * σ) ≤ 2 := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith only [hσ1] : 2 * σ ≤ 1)
      calc xN1 ^ (2 * σ)
          ≤ (2 * xN) ^ (2 * σ) := Real.rpow_le_rpow hxN1_pos.le hxN1_le_2 (by linarith only [hσ0])
        _ = (2 : ℝ) ^ (2 * σ) * xN ^ (2 * σ) := Real.mul_rpow zero_le_two hxN_pos.le
        _ ≤ 2 * xN ^ (2 * σ) := mul_le_mul_of_nonneg_right h2pow (Real.rpow_nonneg hxN_pos.le _)
    have hwN_le : |w N| ≤ 4 * xN ^ (2 * σ) * Real.log xN := by
      dsimp only [w]
      change |xN1 ^ (2 * σ) * Real.log xN1| ≤ _
      have hnn : 0 ≤ xN1 ^ (2 * σ) * Real.log xN1 :=
        mul_nonneg (Real.rpow_nonneg hxN1_pos.le _)
          (Real.log_pos (by dsimp only [xN1]; exact_mod_cast (by omega : 1 < N + 3))).le
      rw [abs_of_nonneg hnn]
      calc xN1 ^ (2 * σ) * Real.log xN1
          ≤ (2 * xN ^ (2 * σ)) * (2 * Real.log xN) :=
            mul_le_mul hrp_xN1 hlog_xN1_le
              (Real.log_pos (by dsimp only [xN1]; exact_mod_cast (by omega : 1 < N + 3))).le
              (by positivity)
        _ = 4 * xN ^ (2 * σ) * Real.log xN := by ring
    rw [abs_mul]
    calc |G N| * |w N|
        ≤ (C_HM * xN ^ (1 - 2 * σ - β) / Real.log xN) * (4 * xN ^ (2 * σ) * Real.log xN) :=
          mul_le_mul hGN hwN_le (abs_nonneg _) (by positivity)
      _ = 4 * C_HM * (xN ^ (1 - 2 * σ - β) * xN ^ (2 * σ)) := by
          field_simp [hlog_xN_pos.ne']
      _ = 4 * C_HM * xN ^ (1 - β) := by
          rw [← Real.rpow_add hxN_pos, show 1 - 2 * σ - β + 2 * σ = 1 - β by ring]
  -- Summation-by-parts sum `|∑ j ∈ Ico m₀ N, G (j + 1) * (w (j + 1) - w j)|`
  have hsbp_bound : |∑ j ∈ Finset.Ico m₀ N, G (j + 1) * (w (j + 1) - w j)| ≤
      (3 * C_HM / (1 - β)) * xN ^ (1 - β) := by
    have hsum_rpow : ∑ j ∈ Finset.Ico m₀ N, ((j + 3 : ℕ) : ℝ) ^ (-β) ≤
        xN ^ (1 - β) / (1 - β) := by
      have hstep_int : ∀ j : ℕ, 4 ≤ j →
          ((j + 3 : ℕ) : ℝ) ^ (-β) ≤
            ∫ u in ((j + 2 : ℕ) : ℝ)..((j + 3 : ℕ) : ℝ), u ^ (-β) := by
        intro j _
        set u0 : ℝ := ((j + 2 : ℕ) : ℝ)
        set u1 : ℝ := ((j + 3 : ℕ) : ℝ)
        have hu0_2 : 2 ≤ u0 := by dsimp only [u0]; exact_mod_cast (by omega : 2 ≤ j + 2)
        have hu1_eq : u1 = u0 + 1 := by dsimp only [u0, u1]; push_cast; ring
        have hu01 : u0 ≤ u1 := by linarith only [hu1_eq]
        obtain ⟨hint, _⟩ := rpow_integral_le_of_pos h1_sub_β hu0_2 hu01
        rw [show (1 - β) - 1 = -β by ring] at hint
        have hm := intervalIntegral.integral_mono_on hu01
          (intervalIntegrable_const (c := u1 ^ (-β))) hint fun u hu =>
            Real.rpow_le_rpow_of_nonpos (by linarith only [hu0_2, hu.1]) hu.2 (by linarith only [hβ0])
        rw [intervalIntegral.integral_const, show u1 - u0 = 1 by linarith only [hu1_eq], one_smul] at hm
        exact hm
      have hadj_int : ∀ k : ℕ, m₀ ≤ k →
          (∑ j ∈ Finset.Ico m₀ k, ∫ u in ((j + 2 : ℕ) : ℝ)..((j + 3 : ℕ) : ℝ), u ^ (-β)) =
            ∫ u in ((m₀ + 2 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), u ^ (-β) := by
        intro k hk
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
        induction d with
        | zero => simp
        | succ d ih =>
          have hmd : m₀ ≤ m₀ + d := by omega
          rw [show m₀ + (d + 1) = (m₀ + d) + 1 by omega, Finset.sum_Ico_succ_top hmd, ih hmd]
          obtain ⟨hi1, _⟩ := rpow_integral_le_of_pos h1_sub_β
            (u := ((m₀ + 2 : ℕ) : ℝ)) (v := ((m₀ + d + 2 : ℕ) : ℝ))
            (by exact_mod_cast (by omega : 2 ≤ m₀ + 2))
            (by exact_mod_cast (by omega : m₀ + 2 ≤ m₀ + d + 2))
          obtain ⟨hi2, _⟩ := rpow_integral_le_of_pos h1_sub_β
            (u := ((m₀ + d + 2 : ℕ) : ℝ)) (v := ((m₀ + d + 3 : ℕ) : ℝ))
            (by exact_mod_cast (by omega : 2 ≤ m₀ + d + 2))
            (by exact_mod_cast (by omega : m₀ + d + 2 ≤ m₀ + d + 3))
          rw [show (1 - β) - 1 = -β by ring] at hi1 hi2
          have hc : ((m₀ + d + 1 + 2 : ℕ) : ℝ) = ((m₀ + d + 3 : ℕ) : ℝ) := by push_cast; ring
          rw [hc]
          exact intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      obtain ⟨_, htot_int⟩ := rpow_integral_le_of_pos h1_sub_β
        (u := ((m₀ + 2 : ℕ) : ℝ)) (v := xN)
        (by exact_mod_cast (by omega : 2 ≤ m₀ + 2))
        (by dsimp only [xN]; exact_mod_cast (by omega : m₀ + 2 ≤ N + 2))
      rw [show (1 - β) - 1 = -β by ring] at htot_int
      calc ∑ j ∈ Finset.Ico m₀ N, ((j + 3 : ℕ) : ℝ) ^ (-β)
          ≤ ∑ j ∈ Finset.Ico m₀ N, ∫ u in ((j + 2 : ℕ) : ℝ)..((j + 3 : ℕ) : ℝ), u ^ (-β) :=
            Finset.sum_le_sum fun j hj => hstep_int j (le_trans hm0_4 (Finset.mem_Ico.mp hj).1)
        _ = ∫ u in ((m₀ + 2 : ℕ) : ℝ)..xN, u ^ (-β) := hadj_int N hN
        _ ≤ xN ^ (1 - β) / (1 - β) := htot_int
    have hterm : ∀ j ∈ Finset.Ico m₀ N,
        |G (j + 1) * (w (j + 1) - w j)| ≤ 3 * C_HM * ((j + 3 : ℕ) : ℝ) ^ (-β) := by
      intro j hj
      have hj_m0 : m₀ ≤ j := (Finset.mem_Ico.mp hj).1
      have hj4 : 4 ≤ j := le_trans hm0_4 hj_m0
      have hGj1 := hmass_diff (j + 1) (by omega)
      have hc3 : ((j + 1 + 2 : ℕ) : ℝ) = ((j + 3 : ℕ) : ℝ) := by push_cast; ring
      dsimp only [G]
      rw [hc3] at hGj1 ⊢
      set u0 : ℝ := ((j + 3 : ℕ) : ℝ)
      have hu0_pos : 0 < u0 := by dsimp only [u0]; positivity
      have hlog_u0_pos : 0 < Real.log u0 :=
        Real.log_pos (by dsimp only [u0]; exact_mod_cast (by omega : 1 < j + 3))
      have hwd := hw_diff_bound j hj4
      rw [abs_mul]
      calc |smoothMassReal σ u0 - bornMass σ (j + 1)| * |w (j + 1) - w j|
          ≤ (C_HM * u0 ^ (1 - 2 * σ - β) / Real.log u0) * (3 * u0 ^ (2 * σ - 1) * Real.log u0) :=
            mul_le_mul hGj1 hwd (abs_nonneg _) (by positivity)
        _ = 3 * C_HM * (u0 ^ (1 - 2 * σ - β) * u0 ^ (2 * σ - 1)) := by
            field_simp [hlog_u0_pos.ne']
        _ = 3 * C_HM * u0 ^ (-β) := by
            rw [← Real.rpow_add hu0_pos, show 1 - 2 * σ - β + (2 * σ - 1) = -β by ring]
    calc |∑ j ∈ Finset.Ico m₀ N, G (j + 1) * (w (j + 1) - w j)|
        ≤ ∑ j ∈ Finset.Ico m₀ N, |G (j + 1) * (w (j + 1) - w j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Ico m₀ N, (3 * C_HM * ((j + 3 : ℕ) : ℝ) ^ (-β)) :=
          Finset.sum_le_sum hterm
      _ = 3 * C_HM * ∑ j ∈ Finset.Ico m₀ N, ((j + 3 : ℕ) : ℝ) ^ (-β) := by rw [← Finset.mul_sum]
      _ ≤ 3 * C_HM * (xN ^ (1 - β) / (1 - β)) :=
          mul_le_mul_of_nonneg_left hsum_rpow (by positivity)
      _ = (3 * C_HM / (1 - β)) * xN ^ (1 - β) := by ring
  have hC0_le : (((m₀ + 2 : ℕ) : ℝ) - Chebyshev.theta ((m₀ + 2 : ℕ) : ℝ)) - G m₀ * w m₀ ≤
      C₀ * xN ^ (1 - β) := by
    calc (((m₀ + 2 : ℕ) : ℝ) - Chebyshev.theta ((m₀ + 2 : ℕ) : ℝ)) - G m₀ * w m₀
        ≤ C₀ := le_abs_self _
      _ = C₀ * 1 := (mul_one C₀).symm
      _ ≤ C₀ * xN ^ (1 - β) := mul_le_mul_of_nonneg_left h1_le_xN_pow (by dsimp only [C₀]; positivity)
  have hGN_le : G N * w N ≤ 4 * C_HM * xN ^ (1 - β) := (le_abs_self _).trans hGN_wN
  have hsbp_le : -(∑ j ∈ Finset.Ico m₀ N, G (j + 1) * (w (j + 1) - w j)) ≤
      (3 * C_HM / (1 - β)) * xN ^ (1 - β) := (neg_le_abs _).trans hsbp_bound
  have htot : xN - Chebyshev.theta xN ≤
      (C₀ + 4 * C_HM + 3 * C_HM / (1 - β)) * xN ^ (1 - β) := by
    linarith only [hstep_le, hC0_le, hGN_le, hsbp_le]
  exact htot.trans (mul_le_mul_of_nonneg_right
    (by dsimp only [C_fin]; linarith only) (Real.rpow_nonneg hxN_pos.le _))

/-- **Direct unreconstructed smooth-subtracted single-mode power excess from `ζ(ρ) = 0`:**
for any zero `ρ` of `riemannZeta` in `0 < Re ρ < 1 / 2`, any nonzero Fourier index `k₀ ≠ 0`
(in particular `k₀ = 1`), any scaling exponent `α ∈ (Re ρ, 1 / 2)`, and any `c > 0`, there exists
an unbounded cutoff sequence `φ : ℕ → ℕ` (`Tendsto φ atTop atTop`) such that
`c < (φ j + 2)^α · ‖bornCoefficient ρ.re ρ.im k₀ (φ j) - smoothBornCoefficient ρ.re ρ.im k₀ (φ j)‖`
for every `j : ℕ`. -/
theorem zeta_zero_forces_direct_bornCoefficient_sub_smooth_power_excess {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1 / 2) (hζ : riemannZeta ρ = 0)
    {k₀ : ℤ} (hk₀ : k₀ ≠ 0) {α : ℝ} (hα_lo : ρ.re < α) (hα_hi : α < 1 / 2)
    {c : ℝ} (hc : 0 < c) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      ∀ j : ℕ,
        c < ((φ j + 2 : ℕ) : ℝ) ^ α *
          ‖bornCoefficient ρ.re ρ.im k₀ (φ j) - smoothBornCoefficient ρ.re ρ.im k₀ (φ j)‖ := by
  have him_ne : ρ.im ≠ 0 :=
    openStrip_zeta_zero_im_ne_zero ⟨ρ, hρ0, by linarith only [hρ1]⟩ hζ
  have hfreq : ∃ᶠ n : ℕ in atTop,
      c < ((n + 2 : ℕ) : ℝ) ^ α *
        ‖bornCoefficient ρ.re ρ.im k₀ n - smoothBornCoefficient ρ.re ρ.im k₀ n‖ := by
    by_contra hnot_freq
    rw [Filter.not_frequently, Filter.eventually_atTop] at hnot_freq
    obtain ⟨N₀, hN₀⟩ := hnot_freq
    have herr : ∀ n : ℕ, N₀ ≤ n →
        ‖bornCoefficient ρ.re ρ.im k₀ n - smoothBornCoefficient ρ.re ρ.im k₀ n‖ ≤
          c * ((n + 2 : ℕ) : ℝ) ^ (-α) := by
      intro n hn
      have hle : ((n + 2 : ℕ) : ℝ) ^ α *
          ‖bornCoefficient ρ.re ρ.im k₀ n - smoothBornCoefficient ρ.re ρ.im k₀ n‖ ≤ c :=
        not_lt.mp (hN₀ n hn)
      set xn : ℝ := ((n + 2 : ℕ) : ℝ)
      have hxn_pos : 0 < xn := by dsimp only [xn]; positivity
      have hm := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hxn_pos.le (-α))
      have h1 : xn ^ (-α) *
          (xn ^ α * ‖bornCoefficient ρ.re ρ.im k₀ n - smoothBornCoefficient ρ.re ρ.im k₀ n‖) =
          ‖bornCoefficient ρ.re ρ.im k₀ n - smoothBornCoefficient ρ.re ρ.im k₀ n‖ := by
        rw [← mul_assoc, ← Real.rpow_add hxn_pos, neg_add_cancel, Real.rpow_zero, one_mul]
      rw [h1, mul_comm] at hm
      exact hm
    have hbc_lim : Tendsto (fun n : ℕ => ‖bornCoefficient ρ.re ρ.im k₀ n‖) atTop
        (𝓝 (bornLorentzianLimit ρ.re ρ.im k₀)) :=
      subcritical_norm_bornCoefficient_tendsto hρ0 hρ1 ρ.im k₀
    have hsm_lim : Tendsto (fun n : ℕ => ‖smoothBornCoefficient ρ.re ρ.im k₀ n‖) atTop
        (𝓝 (bornLorentzianLimit ρ.re ρ.im k₀)) := by
      have hd0 : Tendsto (fun n : ℕ =>
          ‖bornCoefficient ρ.re ρ.im k₀ n - smoothBornCoefficient ρ.re ρ.im k₀ n‖) atTop (𝓝 0) := by
        simpa only [pow_zero, one_mul] using
          subcritical_bornCoefficient_sub_smooth_superPolyLog hρ0 hρ1 ρ.im k₀ 0
      have hndiff : Tendsto (fun n : ℕ =>
          ‖bornCoefficient ρ.re ρ.im k₀ n‖ - ‖smoothBornCoefficient ρ.re ρ.im k₀ n‖) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => by
          rw [Real.norm_eq_abs]
          exact abs_norm_sub_norm_le _ _) hd0
      have hsub := hbc_lim.sub hndiff
      rw [sub_zero] at hsub
      exact hsub.congr fun n => sub_sub_cancel _ _
    have hdisc_step : ∀ n : ℕ, 3 ≤ n →
        ((1 - bornMass ρ.re n / bornMass ρ.re (n + 1) : ℝ) : ℂ) =
          (bornCoefficient ρ.re ρ.im k₀ (n + 1) - bornCoefficient ρ.re ρ.im k₀ n) /
            ((phase ρ.im (n + 3) : ℂ) ^ (-k₀) - bornCoefficient ρ.re ρ.im k₀ n) ∧
        0 ≤ 1 - bornMass ρ.re n / bornMass ρ.re (n + 1) ∧
        1 - bornMass ρ.re n / bornMass ρ.re (n + 1) ≤
          ((n + 3 : ℕ) : ℝ) ^ (-(2 * ρ.re)) / bornMass ρ.re (n + 1) := by
      intro n hn3
      obtain ⟨hstep_if, h1_sub_re, _⟩ :=
        bornStepExtraction_eq_and_prime_iff ρ.re him_ne hk₀ (j := n) hn3
      have hre_eq : 1 - bornMass ρ.re n / bornMass ρ.re (n + 1) =
          (bornStepExtraction ρ.re ρ.im k₀ n).re := by linarith only [h1_sub_re]
      have hbm1_pos : 0 < bornMass ρ.re (n + 1) := by
        apply sum_pos' (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
        exact ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩,
          Real.rpow_pos_of_pos (by norm_num) _⟩
      have hc_eq : ((1 - bornMass ρ.re n / bornMass ρ.re (n + 1) : ℝ) : ℂ) =
          bornStepExtraction ρ.re ρ.im k₀ n := by
        rw [hre_eq, hstep_if]
        split_ifs <;> simp
      refine ⟨hc_eq, ?_, ?_⟩
      · rw [hre_eq, hstep_if]
        split_ifs
        · rw [Complex.ofReal_re]
          exact div_nonneg (by rw [bornWeight]; exact Real.rpow_nonneg (by positivity) _) hbm1_pos.le
        · simp
      · rw [hre_eq, hstep_if]
        split_ifs
        · rw [Complex.ofReal_re, bornWeight]
        · rw [Complex.zero_re]
          exact div_nonneg (Real.rpow_nonneg (by positivity) _) hbm1_pos.le
    set β : ℝ := (ρ.re + α) / 2 with hβ_def
    have hα0 : 0 < α := lt_trans hρ0 hα_lo
    have hβ0 : 0 < β := by linarith only [hβ_def, hρ0, hα0]
    have hβα : β < α := by linarith only [hβ_def, hα_lo]
    have hβ_gt_ρ : ρ.re < β := by linarith only [hβ_def, hα_lo]
    have hβ_half : β < 1 / 2 := lt_trans hβα hα_hi
    obtain ⟨M₁, C_oct, hC_oct, hoct⟩ :=
      dyadic_log_mass_ratio_bound_of_mode_error hρ0 hρ1 him_ne hk₀
        hα0 hβ0 hβα hβ_half hc hsm_lim hbc_lim hdisc_step herr
    obtain ⟨M₂, C_HM, hC_HM, hmass_diff⟩ :=
      smoothMass_sub_bornMass_bound_of_dyadic_log_ratio hρ0 hρ1 hβ0 hC_oct hoct
    obtain ⟨m₀, C_fin, hC_fin, hth_upper⟩ :=
      theta_deficit_bound_of_mass_diff_bound hρ0 hρ1 hβ0 hβ_half hC_HM hmass_diff
    have hsup_ge : 1 - ρ.re ≤ _root_.RHTower.zeroReSup :=
      one_sub_re_le_zeroReSup_of_left_zero hρ0 hρ1 hζ
    set b : ℝ := 1 - (ρ.re + β) / 2 with hb_def
    have hb_lt_sup : b < _root_.RHTower.zeroReSup := by linarith only [hb_def, hβ_gt_ρ, hsup_ge]
    have hb_gt_1β : 1 - β < b := by linarith only [hb_def, hβ_gt_ρ]
    have hb_pos : 0 < b := by linarith only [hb_gt_1β, hβ_half]
    set η_gap : ℝ := b - (1 - β) with hη_gap
    have hη_pos : 0 < η_gap := by linarith only [hη_gap, hb_gt_1β]
    have hgrow : Tendsto (fun y : ℝ => (y - 1) ^ η_gap) atTop atTop :=
      (tendsto_rpow_atTop hη_pos).comp (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
    have hlow := _root_.RHTower.frequently_chebyshevPsi_sub_lt_neg_rpow hb_lt_sup
    have hev_y := (eventually_ge_atTop (((m₀ + 6 : ℕ) : ℝ))).and
      (hgrow.eventually_gt_atTop (C_fin + 1))
    obtain ⟨y, hy_lt, hy_ge_m0, hy_gt_C⟩ := (hlow.and_eventually hev_y).exists
    have hy_ge6 : (6 : ℝ) ≤ y :=
      le_trans (by exact_mod_cast (by omega : 6 ≤ m₀ + 6)) hy_ge_m0
    set M : ℕ := ⌊y⌋₊
    have hy_pos : 0 < y := by linarith only [hy_ge6]
    have hM_le_y : (M : ℝ) ≤ y := Nat.floor_le hy_pos.le
    have hy_lt_M1 : y < (M : ℝ) + 1 := Nat.lt_floor_add_one y
    have hM_ge : m₀ + 6 ≤ M := Nat.le_floor hy_ge_m0
    set N : ℕ := M - 2
    have hN_ge_m0 : m₀ ≤ N := by omega
    have hN2_eq : N + 2 = M := by omega
    set xN : ℝ := ((N + 2 : ℕ) : ℝ)
    have hxN_ge4 : (4 : ℝ) ≤ xN := by dsimp only [xN]; exact_mod_cast (by omega : 4 ≤ N + 2)
    have hxN_pos : 0 < xN := by linarith only [hxN_ge4]
    have hxN_ge1 : 1 ≤ xN := by linarith only [hxN_ge4]
    have htheta_fl : Chebyshev.theta y = Chebyshev.theta xN := by
      dsimp only [xN]; rw [hN2_eq, Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast]
    have hth_le_psi : Chebyshev.theta y ≤ Chebyshev.psi y := Chebyshev.theta_le_psi y
    have hdiff_gt : y ^ b - 1 < xN - Chebyshev.theta xN := by
      rw [← htheta_fl]; dsimp only [xN]; rw [hN2_eq]
      linarith only [hy_lt, hth_le_psi, hy_lt_M1]
    have hxb_le_yb : xN ^ b ≤ y ^ b := by
      dsimp only [xN]; rw [hN2_eq]
      exact Real.rpow_le_rpow (Nat.cast_nonneg M) hM_le_y hb_pos.le
    have hxN_up := hth_upper N hN_ge_m0
    change xN - Chebyshev.theta xN ≤ C_fin * xN ^ (1 - β) at hxN_up
    have h1_le_pow : 1 ≤ xN ^ (1 - β) := Real.one_le_rpow hxN_ge1 (by linarith only [hβ_half])
    have hxb_lt : xN ^ b < (C_fin + 1) * xN ^ (1 - β) := by
      linarith only [hxb_le_yb, hdiff_gt, hxN_up, h1_le_pow]
    have hxb_split : xN ^ b = xN ^ η_gap * xN ^ (1 - β) := by
      rw [← Real.rpow_add hxN_pos]; congr 1; linarith only [hη_gap]
    rw [hxb_split] at hxb_lt
    have hpow_1β_pos : 0 < xN ^ (1 - β) := Real.rpow_pos_of_pos hxN_pos _
    have hxN_η_lt : xN ^ η_gap < C_fin + 1 := by nlinarith only [hxb_lt, hpow_1β_pos]
    have hy1_le_xN : y - 1 ≤ xN := by dsimp only [xN]; rw [hN2_eq]; linarith only [hy_lt_M1]
    have hy1_pow_le : (y - 1) ^ η_gap ≤ xN ^ η_gap :=
      Real.rpow_le_rpow (by linarith only [hy_ge6]) hy1_le_xN hη_pos.le
    linarith only [hy_gt_C, hy1_pow_le, hxN_η_lt]
  obtain ⟨φ, hφ_mono, hφ⟩ := Filter.extraction_of_frequently_atTop hfreq
  exact ⟨φ, hφ_mono.tendsto_atTop, hφ⟩

#print axioms zeta_zero_forces_superDispersion_iff_ne_zero
#print axioms unconditional_left_zero_exclusion_sub_farkas_and_low_height
#print axioms subcritical_norm_deficit_sub_smooth_superPolyLog
#print axioms subcritical_no_subseq_polyLog_smooth_deficit
#print axioms beurling_countermodel_zero_above_184_yet_same_log_deficit
#print axioms norm_bornCoefficient_two_eq_one_at_resonance
#print axioms norm_bornCoefficient_lt_one_of_three_le
#print axioms bornStepExtraction_eq_and_prime_iff
#print axioms reconstructedBornMass_and_theta_eq
#print axioms zeta_zero_forces_single_mode_power_deficit_and_excess
#print axioms rh_single_mode_power_deficit_tendsto_zero
#print axioms rh_iff_fixed_point_single_mode_power_deficit
#print axioms rh_quarter_bornCoefficient_sub_smooth_power_tendsto_zero
#print axioms zeta_zero_forces_direct_bornCoefficient_sub_smooth_power_excess

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
