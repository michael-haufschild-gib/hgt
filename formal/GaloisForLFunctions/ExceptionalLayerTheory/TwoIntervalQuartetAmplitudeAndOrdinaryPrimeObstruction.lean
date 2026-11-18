import GaloisForLFunctions.ExceptionalLayerTheory.TheBoundaryTraceOfTheTwoIntervalPrimeRadius
import GaloisForLFunctions.ExceptionalLayerTheory.QuadratureOfTwoConsecutivePrimeIntervals
import GaloisForLFunctions.ExceptionalLayerTheory.RemovingPrimeLogarithmsPreservesBothIntervalOscillations
import GaloisForLFunctions.ExceptionalLayerTheory.MixingTwoPrimeDilationsRemovesQuartetAliasing
import GaloisForLFunctions.ExceptionalLayerTheory.TwoProperPowerWavesCharacterizeASingleQuartet

/-!
# Two-Interval Ordinary-Prime Quartet Amplitude: Arithmetic Obstructions, Stratum Classification, and Corollaries

For the logarithmic ordinary-prime error `E(t) = θ(e^t) − e^t`, quarter-period step
`h = π / (2 |γ|)`, and scale `A = exp(β h)`, the two-interval radial discrepancy against a
candidate single off-line quartet `(β, γ, m)` (`1/2 < β < 1`, `γ ≠ 0`, `m ≥ 1`) is

`thetaRadialDiscrepancy β γ m t = √((Δ_h E(t))² + A⁻² (Δ_h E(t + h))²) − 2 m ‖(e^{ρ h} − 1)/ρ‖ e^{β t}`.

This module establishes both the exact arithmetic obstructions to ruling out a single quartet by
two-interval prime counts alone and the sharp positive zero-configuration theorems on `ζ(s)`:

1. **Universal adjacent-cofactor and common-middle-endpoint collapse**
   (`adjacent_octave_convolution_eq_neg_apply`, `cofinal_adjacentCount_commonMiddle_radius_collapse`):
   At every prime `2u + 1 ≡ 7 (mod 8)` (`4 ∣ u + 1`), the difference of consecutive first-octave
   Vaughan cofactors `firstOctaveCofactor (u + 1) − firstOctaveCofactor u` is `-1_{d = 2u + 1}`
   pointwise, so its Dirichlet-quotient sum at `(2u + 1) N` equals `-g(N)` identically for **any**
   function `g : ℕ → ℝ` (`g 0 = 0`). Substituting `-adjacentCountAt u (e^s)` at `t, t + h, t + 2h`
   and retaining the shared middle endpoint `E_ψ(t + h)` collapses identically to the raw
   `ψ`-increment squared radius (differing from the `θ`-radius by at most `12(log 4 + 4)e^{(t+2h)/2}`).

2. **Log-weight removal, `{0, 1}`-coprime integer realization, and `{0, 1, 2}`-prime `sEdit` firewall**
   (`exists_coprimeZeroOneSet_realizing_log_and_unweighted_quadrature`, `sEdit_primeLog_wave_approx`,
   `rh_sEdit_ordinaryPrime_realizes_twoIntervalRadius`,
   `unconditional_twoIntervalRadius_prime_and_twin_firewall`):
   - Every `(β, γ, m, Q)` (`1/2 < β < 1`, `γ ≠ 0`, `m ≥ 1`, `Q ≥ 1`) is realized by a `{0, 1}`-set
     of integers `≥ 2` coprime to `Q` with `O(1 + t)` log-weighted radial discrepancy and
     `O(e^{β t} / t)` log-frozen unweighted interval quadrature.
   - Under `RiemannHypothesis`, for every `1/2 < β < 1` and `γ ≠ 0`, `sEdit ((β + 1)/2) β γ 0` gives
     a `{0, 1, 2}`-multiplicity rational-prime count `θ_e` with `O(e^{t/2}(1 + t)²)` radial
     discrepancy; on `1/2 < β < 2/3`, one `sEdit α β γ k₀` simultaneously has sub-square-root
     integer norm count `c < 1/2`, analytic continuation below `Re s = 1/2` with unique right pair
     `{β ± iγ}`, and bounded two-interval ordinary-prime radial discrepancy, while positive Euler
     twins realize the `Γ_ℝ` functional-equation side and `beurling_levy_rigidity_forces_zeta`
     isolates `ζ` when both `Λ_B ≥ 0` and the `Γ_ℝ` functional equation hold.

3. **Unconditional abscissa pinning and automatic `HasPositivePowerLimsup` on `ζ(s)`**
   (`radial_bounded_forces_abscissa_and_limsup`, `thetaRadial_unbounded_of_ne_zetaZeroAbscissa`,
   `thetaRadial_unbounded_of_sub_seven_eighths_lt`,
   `twoIntervalRadialExclusionLaw_of_riemannHypothesis`):
   Boundedness of `thetaRadialDiscrepancy β γ m` against `e^{t/2}(1 + t)²` alone (without assuming
   `HasPositivePowerLimsup`) forces `HasPositivePowerLimsup primeError β`, `¬ RiemannHypothesis`,
   `|θ(y) − y| ≤ L y^β`, `|ψ(y) − y| ≤ L' y^β`, and `zetaZeroAbscissa = β = RHTower.zeroReSup`.
   Consequently `thetaRadialDiscrepancy β γ m` is unconditionally unbounded whenever
   `β ≠ zetaZeroAbscissa`, whenever `20999 / 24000 < β < 1`, and everywhere under `RH`.

4. **Multiplicity-pinned `(2, 3, 6)` equivalence and exact `FiniteOffLine` multi-quartet breaking**
   (`radial_and_ordinary_236_iff_singleQuartet_with_mult`, `finiteOffLine_not_radialUnbounded_iff`,
   `finiteOffLine_not_radialUnbounded_irrational_iff`,
   `finiteOffLine_twoIntervalRadialExclusionLaw_iff`,
   `corollaries_of_twoIntervalRadialExclusionLaw`):
   - Adjoining `(2, 3, 6)` ordinary-prime dilation bounds characterizes
     `HasSingleOffLineQuartet (β + iγ) ∧ quartetCopyMult (β + iγ) = m` with **no**
     `HasPositivePowerLimsup` premise.
   - Under `FiniteOffLine`, **every** multi-quartet configuration (`4 ≤ #(rightZeros)`, whether
     co-abscissa or multi-abscissa) breaks the two-interval circle at all `(β, γ, m)`: bounded radial
     discrepancy holds iff `∃ k ∈ ℕ`, `HasSingleOffLineQuartet (β + i(2k + 1)γ)` with
     `IsOddHarmonicPythagoreanAlias`, so `TwoIntervalRadialExclusionLaw ↔ RH ∨ 4 ≤ #(rightZeros)`.
   - Unconditionally, `TwoIntervalRadialExclusionLaw` implies `∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀`,
     `RH ∨ 4 ≤ #(rightZeros)`, `realPacketNegIndex ≠ 2`, three-rung `confinedGram` index growth
     under `¬ RH`, collapse of `(2, 3, 6)` ordinary-prime recurrences to pure `RH`, exclusion of
     two-wave square/cube proper-power bounds, and cofinal adjacent-octave single-wave exclusion.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Finset MeasureTheory
open scoped ComplexConjugate BigOperators
open RHTower Zeta23
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ExclusionOfTheCriticalState
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.WorldsOfTheZeroConfiguration
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.FEDefect
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ### 1. Ordinary-prime two-interval radial observable and `ψ` / `θ` transfer -/

/-- Centered Chebyshev prime-power count `E_ψ(t) = ψ(e^t) − e^t` on the log scale. -/
def psiLogError (t : ℝ) : ℝ :=
  Chebyshev.psi (Real.exp t) - Real.exp t

/-- Global two-interval ordinary-prime radial exclusion law across all admissible `(β, γ, m)`. -/
def TwoIntervalRadialExclusionLaw : Prop :=
  ∀ β γ : ℝ, ∀ m : ℕ, 1 / 2 < β → β < 1 → γ ≠ 0 → 1 ≤ m →
    IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m)

theorem logStepIncrement_thetaLogError_eq (t h : ℝ) :
    logStepIncrement thetaLogError t h = thetaIntervalIncrement t h :=
  rfl

private theorem cpow_exp_eq (s : ℝ) (ρ : ℂ) :
    (Real.exp s : ℂ) ^ ρ = Complex.exp (ρ * (s : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'),
    ← Complex.ofReal_log (Real.exp_pos s).le, Real.log_exp, mul_comm]

theorem thetaRadialDiscrepancy_neg (β γ : ℝ) (m : ℕ) (t : ℝ) :
    thetaRadialDiscrepancy β (-γ) m t = thetaRadialDiscrepancy β γ m t :=
  radialDiscrepancyOf_neg thetaLogError β γ m t

/-- Uniform `O(e^{(t + 2h)/2})` comparison between the `ψ`- and `θ`-two-interval radii. -/
theorem abs_twoIntervalRadius_psi_sub_theta_le {h A : ℝ} (hh : 0 ≤ h) (hA : 1 ≤ A) (t : ℝ) :
    |twoIntervalRadius psiLogError h A t - twoIntervalRadius thetaLogError h A t| ≤
      12 * (Real.log 4 + 4) * Real.exp ((t + 2 * h) / 2) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  set L : ℝ := 3 * (Real.log 4 + 4)
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hpt : ∀ s : ℝ, s ≤ t + 2 * h →
      |psiLogError s - thetaLogError s| ≤ L * Real.exp ((t + 2 * h) / 2) := by
    intro s hs
    have hdiff : psiLogError s - thetaLogError s =
        Chebyshev.psi (Real.exp s) - Chebyshev.theta (Real.exp s) := by
      dsimp [psiLogError, thetaLogError]; ring
    rw [hdiff, abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
    have h1 := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt (Real.exp s)
    rw [← Real.exp_half] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hL0)
  have hb0 := hpt t (by linarith)
  have hb1 := hpt (t + h) (by linarith)
  have hb2 := hpt (t + 2 * h) le_rfl
  set vψ : ℂ := ⟨logStepIncrement psiLogError t h, logStepIncrement psiLogError (t + h) h / A⟩
  set vθ : ℂ := ⟨logStepIncrement thetaLogError t h, logStepIncrement thetaLogError (t + h) h / A⟩
  rw [twoIntervalRadius_eq_complex_norm hA0, twoIntervalRadius_eq_complex_norm hA0]
  have hre : |(vψ - vθ).re| ≤ 2 * (L * Real.exp ((t + 2 * h) / 2)) := by
    change |(psiLogError (t + h) - psiLogError t) - (thetaLogError (t + h) - thetaLogError t)| ≤ _
    rw [show (psiLogError (t + h) - psiLogError t) - (thetaLogError (t + h) - thetaLogError t) =
      (psiLogError (t + h) - thetaLogError (t + h)) - (psiLogError t - thetaLogError t) by ring]
    exact (abs_sub _ _).trans ((add_le_add hb1 hb0).trans_eq (two_mul _).symm)
  have him : |(vψ - vθ).im| ≤ 2 * (L * Real.exp ((t + 2 * h) / 2)) := by
    change |(psiLogError (t + h + h) - psiLogError (t + h)) / A -
      (thetaLogError (t + h + h) - thetaLogError (t + h)) / A| ≤ _
    rw [← sub_div, show t + h + h = t + 2 * h by ring,
      show (psiLogError (t + 2 * h) - psiLogError (t + h)) -
        (thetaLogError (t + 2 * h) - thetaLogError (t + h)) =
        (psiLogError (t + 2 * h) - thetaLogError (t + 2 * h)) -
          (psiLogError (t + h) - thetaLogError (t + h)) by ring,
      abs_div, abs_of_pos hA0]
    exact (div_le_self (abs_nonneg _) hA).trans
      ((abs_sub _ _).trans ((add_le_add hb2 hb1).trans_eq (two_mul _).symm))
  refine (abs_norm_sub_norm_le vψ vθ).trans ?_
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  exact (add_le_add hre him).trans_eq (by dsimp [L]; ring)

theorem psi_radial_bounded_iff_theta_radial_bounded {β γ : ℝ} (hβ : 0 ≤ β) (hγ : γ ≠ 0) (m : ℕ) :
    ¬ IsLogSqrtSqUnbounded (radialDiscrepancyOf psiLogError β γ m) ↔
      ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m) := by
  simp only [thetaRadialDiscrepancy, isLogSqrtSqUnbounded_iff_not_eventually_le, not_not]
  set h := quarterPeriodStep γ
  set A := quarterPeriodScale β γ
  have hh : 0 ≤ h := (quarterPeriodStep_pos hγ).le
  have hA : 1 ≤ A := Real.one_le_exp (mul_nonneg hβ hh)
  set D : ℝ := 12 * (Real.log 4 + 4) * Real.exp h
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hdiff : ∀ t : ℝ, 0 ≤ t →
      |radialDiscrepancyOf psiLogError β γ m t - radialDiscrepancyOf thetaLogError β γ m t| ≤
        D * Real.exp (t / 2) * (1 + t) ^ 2 := by
    intro t ht
    have hsub : radialDiscrepancyOf psiLogError β γ m t -
        radialDiscrepancyOf thetaLogError β γ m t =
        twoIntervalRadius psiLogError h A t - twoIntervalRadius thetaLogError h A t := by
      unfold radialDiscrepancyOf; ring
    rw [hsub]
    have hb := abs_twoIntervalRadius_psi_sub_theta_le hh hA t
    have hexp : Real.exp ((t + 2 * h) / 2) = Real.exp h * Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h1t : (1 : ℝ) ≤ (1 + t) ^ 2 := by nlinarith
    calc |twoIntervalRadius psiLogError h A t - twoIntervalRadius thetaLogError h A t|
        ≤ 12 * (Real.log 4 + 4) * Real.exp ((t + 2 * h) / 2) := hb
      _ = D * Real.exp (t / 2) * 1 := by dsimp [D]; rw [hexp]; ring
      _ ≤ D * Real.exp (t / 2) * (1 + t) ^ 2 :=
          mul_le_mul_of_nonneg_left h1t (mul_nonneg hD0 (Real.exp_pos _).le)
  constructor <;> rintro ⟨K, T₀, hK⟩ <;> refine ⟨|K| + D, max T₀ 0, fun t ht => ?_⟩
  · have htT : T₀ ≤ t := (le_max_left _ _).trans ht
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
    have h1 := (hK t htT).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le) (sq_nonneg _))
    have h2 := hdiff t ht0
    have htri := abs_sub (radialDiscrepancyOf psiLogError β γ m t)
      (radialDiscrepancyOf psiLogError β γ m t - radialDiscrepancyOf thetaLogError β γ m t)
    rw [sub_sub_cancel] at htri
    linarith
  · have htT : T₀ ≤ t := (le_max_left _ _).trans ht
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
    have h1 := (hK t htT).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le) (sq_nonneg _))
    have h2 := hdiff t ht0
    have htri := abs_add_le (radialDiscrepancyOf thetaLogError β γ m t)
      (radialDiscrepancyOf psiLogError β γ m t - radialDiscrepancyOf thetaLogError β γ m t)
    rw [add_sub_cancel] at htri
    linarith

/-- Forward single-quartet radial law: every single off-line quartet `ρ` satisfies bounded
`thetaRadialDiscrepancy` against `e^{t/2}(1 + t)²` at `(ρ.re, ρ.im, quartetCopyMult ρ)`. -/
theorem not_isLogSqrtSqUnbounded_of_singleQuartet {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy ρ.re ρ.im (quartetCopyMult ρ)) := by
  obtain ⟨hh, _, _, K, hK0, hbound⟩ := singleQuartet_two_theta_intervals hq
  rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not]
  set h := quarterPeriodStep ρ.im
  have hh_eq : Real.pi / (2 * |ρ.im|) = h := rfl
  have hA0 : 0 < quarterPeriodScale ρ.re ρ.im := Real.exp_pos _
  set K' : ℝ := K * Real.exp h * (2 + 8 * h ^ 2)
  refine ⟨K', 3, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have ht16 : 16 ≤ Real.exp t := by
    have h3 : (16 : ℝ) ≤ Real.exp 3 := by
      have := Real.exp_one_gt_d9
      calc (16 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
        _ ≤ Real.exp 1 ^ 3 := by gcongr
        _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    exact h3.trans (Real.exp_le_exp.mpr ht)
  have hb := hbound t ht0 ht16
  have hρ_eq : ((ρ.re : ℂ) + I * (ρ.im : ℂ)) = ρ := by
    apply Complex.ext <;> simp
  have hrad_eq : thetaRadialDiscrepancy ρ.re ρ.im (quartetCopyMult ρ) t =
      ‖(⟨thetaIntervalIncrement t h,
          thetaIntervalIncrement (t + h) h / quarterPeriodScale ρ.re ρ.im⟩ : ℂ)‖ -
        2 * (quartetCopyMult ρ : ℝ) * ‖(Complex.exp (ρ * (h : ℂ)) - 1) / ρ‖ *
          Real.exp (ρ.re * t) := by
    unfold thetaRadialDiscrepancy radialDiscrepancyOf quartetRadialCoeff
    dsimp only
    rw [twoIntervalRadius_eq_complex_norm hA0, logStepIncrement_thetaLogError_eq,
      logStepIncrement_thetaLogError_eq, hρ_eq]
  rw [hrad_eq]
  refine hb.trans ?_
  have hexp : Real.exp ((t + 2 * h) / 2) = Real.exp h * Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpoly : 1 + (t + 2 * h) ^ 2 ≤ (2 + 8 * h ^ 2) * (1 + t) ^ 2 := by
    have h1 : (t + 2 * h) ^ 2 ≤ 2 * t ^ 2 + 8 * h ^ 2 := by
      nlinarith [sq_nonneg (t - 2 * h)]
    have h2 : (1 : ℝ) ≤ (1 + t) ^ 2 := by nlinarith
    have h3 : t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
    nlinarith [sq_nonneg h]
  calc K * Real.exp ((t + 2 * h) / 2) * (1 + (t + 2 * h) ^ 2)
      = K * Real.exp h * Real.exp (t / 2) * (1 + (t + 2 * h) ^ 2) := by rw [hexp]; ring
    _ ≤ K * Real.exp h * Real.exp (t / 2) * ((2 + 8 * h ^ 2) * (1 + t) ^ 2) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = K' * Real.exp (t / 2) * (1 + t) ^ 2 := by dsimp [K']; ring

/-! ### 2. Universal adjacent-cofactor and common-middle-endpoint collapse -/

/-- **Universal adjacent-octave Dirichlet-quotient collapse.**
At any prime `2u + 1 ≡ 7 (mod 8)` (`(2u + 1).Prime`, `4 ∣ u + 1`), the difference of consecutive
first-octave Vaughan cofactor sums weighted by `g(((2u + 1) N) / d)` equals `-g(N)` identically
for **every** function `g : ℕ → ℝ` satisfying `g 0 = 0` and every `N : ℕ`. -/
theorem adjacent_octave_convolution_eq_neg_apply {u : ℕ} (hp : (2 * u + 1).Prime)
    (hu : 4 ∣ u + 1) (g : ℕ → ℝ) (hg0 : g 0 = 0) (N : ℕ) :
    (∑ d ∈ Icc 1 ((2 * u + 1) * N), firstOctaveCofactor (u + 1) d * g (((2 * u + 1) * N) / d)) -
      (∑ d ∈ Icc 1 ((2 * u + 1) * N), firstOctaveCofactor u d * g (((2 * u + 1) * N) / d)) =
      -g N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hg0]
  · set M : ℕ := (2 * u + 1) * N
    have hm : 2 * u + 1 ∈ Icc 1 M :=
      mem_Icc.mpr ⟨by omega, Nat.le_mul_of_pos_right _ hN⟩
    have hq : M / (2 * u + 1) = N := Nat.mul_div_cancel_left N (by omega)
    rw [← Finset.sum_sub_distrib]
    have hcongr : ∀ d ∈ Icc 1 M,
        firstOctaveCofactor (u + 1) d * g (M / d) - firstOctaveCofactor u d * g (M / d) =
          if d = 2 * u + 1 then -g N else 0 := by
      intro d _
      rw [← sub_mul, adjacent_octave_difference hp hu d]
      by_cases hd : d = 2 * u + 1
      · subst hd; rw [if_pos rfl, if_pos rfl, hq]; ring
      · rw [if_neg hd, if_neg hd, zero_mul]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq', if_pos hm]

/-- **Cofinal common-middle-endpoint collapse of adjacent cofactor counts.**
Above every cutoff `B : ℕ`, there exists `u > B` with `(2u + 1).Prime` and `4 ∣ u + 1` such that
setting `D_u(s) = −adjacentCountAt u (e^s)` at the three endpoints `t, t + h, t + 2h` and
retaining the shared middle endpoint `D_u(t + h)` reproduces `twoIntervalRadius psiLogError h A t ^ 2`
identically (independent of `u`), with square root within `12(log 4 + 4)e^{(t + 2h)/2}` of the
ordinary-prime `θ`-radius. -/
theorem cofinal_adjacentCount_commonMiddle_radius_collapse (B : ℕ) :
    ∃ u > B, (2 * u + 1).Prime ∧ 4 ∣ u + 1 ∧
      let D_u : ℝ → ℝ := fun s => -adjacentCountAt u (Real.exp s)
      (∀ s : ℝ, D_u s = psiLogError s) ∧
      (∀ h A t : ℝ,
        (1 + A⁻¹ ^ 2) * D_u (t + h) ^ 2 - 2 * D_u t * D_u (t + h) -
          2 * A⁻¹ ^ 2 * D_u (t + h) * D_u (t + 2 * h) + D_u t ^ 2 +
          A⁻¹ ^ 2 * D_u (t + 2 * h) ^ 2 =
          twoIntervalRadius psiLogError h A t ^ 2) ∧
      (∀ {h A : ℝ}, 0 ≤ h → 1 ≤ A → ∀ t : ℝ,
        |Real.sqrt ((1 + A⁻¹ ^ 2) * D_u (t + h) ^ 2 - 2 * D_u t * D_u (t + h) -
            2 * A⁻¹ ^ 2 * D_u (t + h) * D_u (t + 2 * h) + D_u t ^ 2 +
            A⁻¹ ^ 2 * D_u (t + 2 * h) ^ 2) -
          twoIntervalRadius thetaLogError h A t| ≤
          12 * (Real.log 4 + 4) * Real.exp ((t + 2 * h) / 2)) := by
  obtain ⟨p, hlarge, hp, hclass⟩ := Nat.forall_exists_prime_gt_and_modEq (2 * B + 2)
    (q := 8) (a := 7) (by decide) (by decide)
  change p % 8 = 7 % 8 at hclass
  let u := p / 2
  have hpu : 2 * u + 1 = p := by dsimp [u]; omega
  have h4 : 4 ∣ u + 1 := by dsimp [u]; omega
  have huB : B < u := by dsimp [u]; omega
  have hp' : (2 * u + 1).Prime := hpu.symm ▸ hp
  refine ⟨u, huB, hp', h4, ?_⟩
  intro D_u
  have hD_eq : ∀ s : ℝ, D_u s = psiLogError s := by
    intro s
    dsimp [D_u]
    unfold adjacentCountAt psiLogError
    set N : ℕ := ⌊Real.exp s⌋₊
    have hoct : ∀ v M : ℕ, cofactorCountError v (2 * v) M =
        ∑ d ∈ Icc 1 M, firstOctaveCofactor v d * (Chebyshev.psi (M / d : ℕ) - (M / d : ℕ)) := by
      intro v M
      rw [cofactorCountError, cofactorCountCoeff, mul_comm, RHTower.sum_Icc_mul_apply]
      simp only [sum_vonMangoldt_sub_zeta, firstOctaveCofactor]
    rw [hoct (u + 1), hoct u]
    have hconv := adjacent_octave_convolution_eq_neg_apply hp' h4
      (fun k : ℕ => Chebyshev.psi (k : ℝ) - (k : ℝ)) (by simp [Chebyshev.psi]) N
    have hpsi_fl : Chebyshev.psi (N : ℝ) = Chebyshev.psi (Real.exp s) :=
      (Chebyshev.psi_eq_psi_coe_floor (Real.exp s)).symm
    linarith [hconv, hpsi_fl]
  have hD_fun : D_u = psiLogError := funext hD_eq
  have hquad : ∀ h A t : ℝ,
      (1 + A⁻¹ ^ 2) * D_u (t + h) ^ 2 - 2 * D_u t * D_u (t + h) -
        2 * A⁻¹ ^ 2 * D_u (t + h) * D_u (t + 2 * h) + D_u t ^ 2 +
        A⁻¹ ^ 2 * D_u (t + 2 * h) ^ 2 =
        twoIntervalRadius psiLogError h A t ^ 2 := by
    intro h A t
    rw [hD_fun, ← commonMiddleSumSq_eq psiLogError h A t, twoIntervalRadius,
      Real.sq_sqrt (by positivity)]
  refine ⟨hD_eq, hquad, fun {h A} hh hA t => ?_⟩
  rw [hquad h A t, Real.sqrt_sq (by unfold twoIntervalRadius; exact Real.sqrt_nonneg _)]
  exact abs_twoIntervalRadius_psi_sub_theta_le hh hA t

/-! ### 3. Log-weight removal and `{0, 1}`-coprime integer-set realization -/

/-- Centered unweighted counting weight `(w n : ℝ) − (log n)⁻¹` for a `{0, 1}`-sequence `w`. -/
def centeredCoprimeCountWeight (w : ℕ → ℕ) (n : ℕ) : ℝ :=
  (w n : ℝ) - (Real.log n)⁻¹

private theorem centered_weight_interval_freeze_log (w_seq : ℕ → ℕ) {l u : ℕ} (hl : 2 ≤ l)
    (hlu : l < u) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j : ℕ, l ≤ j → j ≤ u →
      |∑ n ∈ Ioc j u, Real.log n * centeredCoprimeCountWeight w_seq n| ≤ B) :
    |(∑ n ∈ Ioc l u, Real.log n * centeredCoprimeCountWeight w_seq n) -
      Real.log l * ∑ n ∈ Ioc l u, centeredCoprimeCountWeight w_seq n| ≤
      ((Real.log u - Real.log l) / Real.log l) * B := by
  let a (n : ℕ) := Real.log n * centeredCoprimeCountWeight w_seq n
  let wt (n : ℕ) := 1 - Real.log l / Real.log n
  have hlog {n : ℕ} (hn : l ≤ n) : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hmono {i j : ℕ} (hi : l ≤ i) (hj : i ≤ j) : Real.log i ≤ Real.log j :=
    Real.log_le_log (by exact_mod_cast (show 0 < i by omega)) (by exact_mod_cast hj)
  have hwt {n : ℕ} (hn : l ≤ n) : 0 ≤ wt n :=
    sub_nonneg.mpr ((div_le_one (hlog hn)).mpr (hmono le_rfl hn))
  have hinc (i : ℕ) (hi : i ∈ Ioc l (u - 1)) : wt i ≤ wt (i + 1) :=
    sub_le_sub_left (div_le_div_of_nonneg_left (hlog le_rfl).le (hlog (mem_Ioc.mp hi).1.le)
      (hmono (mem_Ioc.mp hi).1.le (Nat.le_succ i))) 1
  have hsum : (∑ n ∈ Ioc l u, wt n * a n) =
      (∑ n ∈ Ioc l u, Real.log n * centeredCoprimeCountWeight w_seq n) -
        Real.log l * ∑ n ∈ Ioc l u, centeredCoprimeCountWeight w_seq n := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    dsimp only [wt, a]
    field_simp [(hlog (mem_Ioc.mp hn).1.le).ne']
  rw [← hsum, abs_le]
  have hpos := sum_weighted_le_of_suffix_bounds hlu a wt
    (fun j hj hju => (abs_le.mp (h j hj hju)).2) (hwt (Nat.le_succ _)) hinc
  have hneg := sum_weighted_le_of_suffix_bounds hlu (fun n => -a n) wt
    (fun j hj hju => by rw [Finset.sum_neg_distrib]; exact neg_le.mpr (abs_le.mp (h j hj hju)).1)
    (hwt (Nat.le_succ _)) hinc
  simp only [mul_neg, Finset.sum_neg_distrib] at hneg
  have hu : wt u ≤ (Real.log u - Real.log l) / Real.log l := by
    rw [show wt u = (Real.log u - Real.log l) / Real.log u by
      dsimp only [wt]; rw [sub_div, div_self (hlog hlu.le).ne']]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr (hmono le_rfl hlu.le)) (hlog le_rfl)
      (hmono le_rfl hlu.le)
  exact ⟨neg_le.mp (hneg.trans (mul_le_mul_of_nonneg_right hu hB)),
    hpos.trans (mul_le_mul_of_nonneg_right hu hB)⟩

/-- **Simultaneous log-weighted and unweighted log-frozen two-interval realization on coprime `{0, 1}` sets.**
For every `1/2 < β < 1`, `γ ≠ 0`, `m ≥ 1`, and modulus `Q ≥ 1`, there exists `w : ℕ → ℕ` supported
on `{n ≥ 2 : gcd(n, Q) = 1}` with values in `{0, 1}` whose logarithmic count `θ_w` has `O(1 + t)`
two-interval radial discrepancy **and** whose unweighted log-frozen interval counts
`Δπ_w(s, h) = ∑_{⌊e^s⌋₊ < n ≤ ⌊e^{s+h}⌋₊} (w(n) − 1/log n)` reproduce the two-interval circle to
`O(e^{β t} / t)` for all `t ≥ 2`. -/
theorem exists_coprimeZeroOneSet_realizing_log_and_unweighted_quadrature {β γ : ℝ} {m Q : ℕ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : γ ≠ 0) (hm : 1 ≤ m) (hQ : 1 ≤ Q) :
    ∃ w : ℕ → ℕ,
      (∀ n : ℕ, (w n = 0 ∨ w n = 1) ∧ (w n = 1 → 2 ≤ n ∧ Nat.Coprime n Q)) ∧
      let θ_w : ℝ → ℝ := fun x => ∑ n ∈ Icc 1 ⌊x⌋₊, (w n : ℝ) * Real.log n
      let E_w : ℝ → ℝ := fun t => θ_w (Real.exp t) - Real.exp t
      let h := quarterPeriodStep γ
      let A := quarterPeriodScale β γ
      let Δπ_w : ℝ → ℝ := fun s =>
        ∑ n ∈ Ioc ⌊Real.exp s⌋₊ ⌊Real.exp (s + h)⌋₊, centeredCoprimeCountWeight w n
      ¬ IsLogSqrtSqUnbounded (radialDiscrepancyOf E_w β γ m) ∧
      (∃ C' : ℝ, 0 ≤ C' ∧ ∀ t : ℝ, 0 ≤ t → |radialDiscrepancyOf E_w β γ m t| ≤ C' * (1 + t)) ∧
      (∃ K_unw : ℝ, 0 ≤ K_unw ∧ ∀ t : ℝ, 2 ≤ t →
        |‖(⟨Real.log (⌊Real.exp t⌋₊ : ℝ) * Δπ_w t,
            Real.log (⌊Real.exp (t + h)⌋₊ : ℝ) * Δπ_w (t + h) / A⟩ : ℂ)‖ -
          quartetRadialCoeff β γ m * Real.exp (β * t)| ≤
          K_unw * Real.exp (β * t) / t) := by
  obtain ⟨w, hw, hdata⟩ :=
    exists_coprimeZeroOneSet_realizing_twoIntervalRadius hβ hβ1 hγ hm hQ
  refine ⟨w, hw, ?_⟩
  intro θ_w E_w h A Δπ_w
  obtain ⟨⟨C₀, hC₀, hθ_b⟩, ⟨C', hC', hrad_b⟩, _, hnot_unb, _, _⟩ := hdata
  refine ⟨hnot_unb, ⟨C', hC', hrad_b⟩, ?_⟩
  have hβ0 : 0 < β := by linarith
  have hh_pos : 0 < h := quarterPeriodStep_pos hγ
  have hA1 : 1 ≤ A := (one_lt_quarterPeriodScale hβ0 hγ).le
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr fun he => by
    have := congrArg Complex.re he; simp [ρ] at this; linarith
  -- Coarse `O(x^β)` bound on `|θ_w x - x|` for `x ≥ 2`
  have hlog_le_rpow : ∃ C_lg : ℝ, 0 ≤ C_lg ∧ ∀ x : ℝ, 2 ≤ x → 1 + Real.log x ≤ C_lg * x ^ β := by
    have hlim : Tendsto (fun t : ℝ => (1 + t) * Real.exp (-(β * t))) atTop (𝓝 0) := by
      have h0 := _root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 β hβ0
      have h1 := h0.const_mul 2
      rw [mul_zero] at h1
      refine squeeze_zero_norm' ?_ h1
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_one]
      have : 1 + t ≤ 2 * t := by linarith
      calc (1 + t) * Real.exp (-(β * t)) ≤ (2 * t) * Real.exp (-(β * t)) :=
            mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        _ = 2 * (t * Real.exp (-β * t)) := by rw [neg_mul]; ring
    obtain ⟨T_lg, hT_lg⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds one_pos))
    set M_lg : ℝ := 1 + Real.log (max (Real.exp T_lg) 2)
    refine ⟨max M_lg 1 + 1, by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    by_cases hxT : Real.exp T_lg ≤ x
    · have ht : T_lg ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxT
      have hlt := hT_lg (Real.log x) ht
      have hmul := mul_lt_mul_of_pos_right hlt (Real.exp_pos (β * Real.log x))
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul,
        mul_comm β (Real.log x)] at hmul
      have hpow_pos : 0 < x ^ β := Real.rpow_pos_of_pos hx0 β
      have h1 : 1 + Real.log x ≤ 1 * x ^ β := by
        rw [Real.rpow_def_of_pos hx0]; linarith
      have h2 : (1 : ℝ) ≤ max M_lg 1 + 1 := by linarith [le_max_right M_lg 1]
      exact h1.trans (mul_le_mul_of_nonneg_right h2 hpow_pos.le)
    · push Not at hxT
      have hle_max : x ≤ max (Real.exp T_lg) 2 := le_max_of_le_left hxT.le
      have hlog_le : 1 + Real.log x ≤ M_lg := by
        dsimp [M_lg]; linarith [Real.log_le_log hx0 hle_max]
      have hxβ1 : 1 ≤ x ^ β := Real.one_le_rpow (by linarith) hβ0.le
      calc 1 + Real.log x ≤ M_lg := hlog_le
        _ ≤ max M_lg 1 + 1 := by linarith [le_max_left M_lg 1]
        _ ≤ (max M_lg 1 + 1) * x ^ β := le_mul_of_one_le_right (by positivity) hxβ1
  obtain ⟨C_lg, hC_lg, hlg⟩ := hlog_le_rpow
  set C_p : ℝ := C₀ * C_lg + 2 * (m : ℝ) / ‖ρ‖ + 1
  have hC_p : 0 ≤ C_p := by dsimp [C_p]; positivity
  have hθ_pow : ∀ x : ℝ, 2 ≤ x → |θ_w x - x| ≤ C_p * x ^ β := by
    intro x hx
    have hx1 : 1 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hb := hθ_b x hx1
    have hw_le : |2 * (m : ℝ) * (((x : ℂ) ^ ρ / ρ).re)| ≤ (2 * (m : ℝ) / ‖ρ‖) * x ^ β := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have h1 := (Complex.abs_re_le_norm ((x : ℂ) ^ ρ / ρ)).trans_eq (norm_div _ _)
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, show ρ.re = β by simp [ρ]] at h1
      calc 2 * (m : ℝ) * |(((x : ℂ) ^ ρ / ρ).re)|
          ≤ 2 * (m : ℝ) * (x ^ β / ‖ρ‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (2 * (m : ℝ) / ‖ρ‖) * x ^ β := by ring
    have htri := abs_sub (θ_w x - x + 2 * (m : ℝ) * (((x : ℂ) ^ ρ / ρ).re))
      (2 * (m : ℝ) * (((x : ℂ) ^ ρ / ρ).re))
    rw [add_sub_cancel_right] at htri
    have h1 := hb.trans (mul_le_mul_of_nonneg_left (hlg x hx) hC₀)
    dsimp [C_p]
    have hxβ0 : 0 ≤ x ^ β := Real.rpow_nonneg hx0.le β
    nlinarith [htri, h1, hw_le]
  -- Exact identity for `∑_{l < n ≤ u} log n * centeredCoprimeCountWeight w n`
  have hlog_sum_eq : ∀ {l u : ℕ}, 1 ≤ l → l ≤ u →
      (∑ n ∈ Ioc l u, Real.log n * centeredCoprimeCountWeight w n) =
        (θ_w u - u) - (θ_w l - l) := by
    intro l u hl hlu
    have hfl_u : ⌊(u : ℝ)⌋₊ = u := Nat.floor_natCast u
    have hfl_l : ⌊(l : ℝ)⌋₊ = l := Nat.floor_natCast l
    have hsplit : Icc 1 u = Icc 1 l ∪ Ioc l u := by
      ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 l) (Ioc l u) :=
      Finset.disjoint_left.mpr fun _ h1 h2 => (mem_Ioc.mp h2).1.not_ge (mem_Icc.mp h1).2
    have hθu : θ_w u = θ_w l + ∑ n ∈ Ioc l u, (w n : ℝ) * Real.log n := by
      dsimp [θ_w]; rw [hfl_u, hfl_l, hsplit, Finset.sum_union hdisj]
    have hterm : ∀ n ∈ Ioc l u,
        Real.log n * centeredCoprimeCountWeight w n = (w n : ℝ) * Real.log n - 1 := by
      intro n hn
      have hn1 : 1 < n := by have := (mem_Ioc.mp hn).1; omega
      have hln : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hn1)).ne'
      unfold centeredCoprimeCountWeight
      rw [mul_sub, mul_inv_cancel₀ hln]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc,
      nsmul_eq_mul, mul_one, Nat.cast_sub hlu, hθu]
    ring
  -- Single-interval log-freezing bound at `s ∈ [t, t + h]` (`t ≥ 2`)
  set B_fac : ℝ := 2 * C_p * Real.exp (2 * β * h)
  have hfreeze_step : ∀ {t s : ℝ}, 2 ≤ t → t ≤ s → s ≤ t + h →
      |Real.log (⌊Real.exp s⌋₊ : ℝ) * Δπ_w s - logStepIncrement E_w s h| ≤
        (2 * (h + 1) * B_fac + 2 * (1 + h)) * Real.exp (β * t) / t := by
    intro t s ht hts hst
    have hs2 : 2 ≤ s := ht.trans hts
    have hexp_s : (7 : ℝ) ≤ Real.exp s := by
      have h2 : (7 : ℝ) ≤ Real.exp 2 := by
        have := Real.exp_one_gt_d9
        calc (7 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
          _ ≤ Real.exp 1 ^ 2 := by gcongr
          _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
      exact h2.trans (Real.exp_le_exp.mpr hs2)
    set l : ℕ := ⌊Real.exp s⌋₊
    set u : ℕ := ⌊Real.exp (s + h)⌋₊
    have hl6 : 6 ≤ l := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ Real.exp s))
    have hl2 : 2 ≤ l := by omega
    have hlu : l ≤ u := Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
    have hl_le : (l : ℝ) ≤ Real.exp s := Nat.floor_le (Real.exp_pos s).le
    have hl_gt : Real.exp s - 1 < (l : ℝ) := by
      have := Nat.lt_floor_add_one (Real.exp s); linarith
    have hu_le : (u : ℝ) ≤ Real.exp (s + h) := Nat.floor_le (Real.exp_pos _).le
    have hu_gt : Real.exp (s + h) - 1 < (u : ℝ) := by
      have := Nat.lt_floor_add_one (Real.exp (s + h)); linarith
    have hround : |(∑ n ∈ Ioc l u, Real.log n * centeredCoprimeCountWeight w n) -
        logStepIncrement E_w s h| ≤ 2 := by
      rw [hlog_sum_eq (by omega) hlu]
      have hθ_fl_l : θ_w l = θ_w (Real.exp s) := by dsimp [θ_w, l]; rw [Nat.floor_natCast]
      have hθ_fl_u : θ_w u = θ_w (Real.exp (s + h)) := by dsimp [θ_w, u]; rw [Nat.floor_natCast]
      unfold logStepIncrement
      dsimp [E_w]
      rw [hθ_fl_l, hθ_fl_u, abs_le]
      exact ⟨by linarith, by linarith⟩
    have ht_pos : 0 < t := by linarith
    have hexp_ge_t : t ≤ Real.exp (β * t) := by
      -- `exp (βt) ≥ (1 + βt/2)² ≥ (1 + t/4)² ≥ t`
      have hbt : t / 4 ≤ β * t / 2 := by nlinarith [hβ]
      have hE : 1 + t / 4 ≤ Real.exp (β * t / 2) := by
        linarith [Real.add_one_le_exp (β * t / 2)]
      have hsq : Real.exp (β * t) = Real.exp (β * t / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [hsq]
      nlinarith [mul_le_mul hE hE (by linarith) (Real.exp_pos (β * t / 2)).le, sq_nonneg (1 - t / 4)]
    have h2_le : (2 : ℝ) ≤ 2 * (1 + h) * Real.exp (β * t) / t := by
      rw [le_div_iff₀ ht_pos]
      have : 2 * t ≤ 2 * (1 + h) * Real.exp (β * t) := by
        nlinarith [hexp_ge_t, hh_pos, Real.exp_pos (β * t)]
      linarith
    rcases eq_or_lt_of_le hlu with heq | hlt
    · have hΔ0 : Δπ_w s = 0 := by
        show ∑ n ∈ Ioc l u, centeredCoprimeCountWeight w n = 0
        rw [← heq, Finset.Ioc_self, Finset.sum_empty]
      have hS0 : ∑ n ∈ Ioc l u, Real.log n * centeredCoprimeCountWeight w n = 0 := by
        rw [heq, Finset.Ioc_self, Finset.sum_empty]
      rw [hS0, zero_sub, abs_neg] at hround
      rw [hΔ0, mul_zero, zero_sub, abs_neg]
      exact hround.trans (h2_le.trans (by
        rw [add_mul, add_div]
        exact le_add_of_nonneg_left (by dsimp [B_fac]; positivity)))
    · set B_cur : ℝ := B_fac * Real.exp (β * t)
      have hB_cur : 0 ≤ B_cur := by dsimp [B_cur, B_fac]; positivity
      have hsurf : ∀ j : ℕ, l ≤ j → j ≤ u →
          |∑ n ∈ Ioc j u, Real.log n * centeredCoprimeCountWeight w n| ≤ B_cur := by
        intro j hj hju
        rw [hlog_sum_eq (by omega) hju]
        have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (hl2.trans hj)
        have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast (hl2.trans hlt.le)
        have hju_le : (j : ℝ) ≤ Real.exp (t + 2 * h) := by
          have : (j : ℝ) ≤ u := by exact_mod_cast hju
          exact this.trans (hu_le.trans (Real.exp_le_exp.mpr (by linarith)))
        have hu_exp_le : (u : ℝ) ≤ Real.exp (t + 2 * h) :=
          hu_le.trans (Real.exp_le_exp.mpr (by linarith))
        have hrpow_bound : ∀ y : ℝ, 2 ≤ y → y ≤ Real.exp (t + 2 * h) →
            |θ_w y - y| ≤ C_p * Real.exp (2 * β * h) * Real.exp (β * t) := by
          intro y hy1 hy2
          refine (hθ_pow y hy1).trans ?_
          have hr1 : y ^ β ≤ (Real.exp (t + 2 * h)) ^ β :=
            Real.rpow_le_rpow (by linarith) hy2 hβ0.le
          have hr2 : (Real.exp (t + 2 * h)) ^ β = Real.exp (2 * β * h) * Real.exp (β * t) := by
            rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
            congr 1; ring
          rw [hr2] at hr1
          calc C_p * y ^ β ≤ C_p * (Real.exp (2 * β * h) * Real.exp (β * t)) :=
                mul_le_mul_of_nonneg_left hr1 hC_p
            _ = C_p * Real.exp (2 * β * h) * Real.exp (β * t) := by ring
        refine (abs_sub _ _).trans ?_
        have b1 := hrpow_bound u hu2 hu_exp_le
        have b2 := hrpow_bound j hj2 hju_le
        dsimp [B_cur, B_fac]
        linarith
      have hfr := centered_weight_interval_freeze_log w hl2 hlt hB_cur hsurf
      have hlog_l_ge : t / 2 ≤ Real.log (l : ℝ) := by
        have half_exp : Real.exp (s - 1) ≤ (l : ℝ) := by
          have he1 : Real.exp (s - 1) = Real.exp s / Real.exp 1 := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
          have he_gt2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have hdiv : Real.exp s / Real.exp 1 ≤ Real.exp s / 2 :=
            div_le_div_of_nonneg_left (Real.exp_pos s).le (by norm_num) he_gt2
          linarith
        have hlog_ge := Real.log_le_log (Real.exp_pos _) half_exp
        rw [Real.log_exp] at hlog_ge
        linarith
      have hlog_diff : Real.log (u : ℝ) - Real.log (l : ℝ) ≤ h + 1 := by
        have hlu_pos : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
        have hlogu_le : Real.log (u : ℝ) ≤ s + h := by
          calc Real.log (u : ℝ) ≤ Real.log (Real.exp (s + h)) := Real.log_le_log hlu_pos hu_le
            _ = s + h := Real.log_exp _
        have half_exp : Real.exp (s - 1) ≤ (l : ℝ) := by
          have he1 : Real.exp (s - 1) = Real.exp s / Real.exp 1 := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
          have he_gt2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have hdiv : Real.exp s / Real.exp 1 ≤ Real.exp s / 2 :=
            div_le_div_of_nonneg_left (Real.exp_pos s).le (by norm_num) he_gt2
          linarith
        have hlogl_ge : s - 1 ≤ Real.log (l : ℝ) := by
          calc s - 1 = Real.log (Real.exp (s - 1)) := (Real.log_exp _).symm
            _ ≤ Real.log (l : ℝ) := Real.log_le_log (Real.exp_pos _) half_exp
        linarith
      have hrat_le : (Real.log (u : ℝ) - Real.log (l : ℝ)) / Real.log (l : ℝ) ≤
          2 * (h + 1) / t := by
        have hlogl_pos : 0 < Real.log (l : ℝ) := by linarith
        calc (Real.log (u : ℝ) - Real.log (l : ℝ)) / Real.log (l : ℝ)
            ≤ (h + 1) / Real.log (l : ℝ) := div_le_div_of_nonneg_right hlog_diff hlogl_pos.le
          _ ≤ (h + 1) / (t / 2) :=
              div_le_div_of_nonneg_left (by positivity) (half_pos ht_pos) hlog_l_ge
          _ = 2 * (h + 1) / t := by ring
      have hfr' : |Real.log (l : ℝ) * Δπ_w s -
          ∑ n ∈ Ioc l u, Real.log n * centeredCoprimeCountWeight w n| ≤
          2 * (h + 1) * B_fac * Real.exp (β * t) / t := by
        rw [abs_sub_comm]
        exact hfr.trans ((mul_le_mul_of_nonneg_right hrat_le hB_cur).trans_eq
          (by dsimp [B_cur]; ring))
      have htri := (abs_add_le (Real.log (l : ℝ) * Δπ_w s -
          ∑ n ∈ Ioc l u, Real.log n * centeredCoprimeCountWeight w n)
        ((∑ n ∈ Ioc l u, Real.log n * centeredCoprimeCountWeight w n) -
          logStepIncrement E_w s h)).trans (add_le_add hfr' hround)
      rw [sub_add_sub_cancel] at htri
      exact htri.trans (by rw [add_mul, add_div]; linarith [h2_le])
  -- Combine both intervals with `hrad_b` (`C' * (1 + t) ≤ 2 * C' * e^{β t} / t` for large `t`, or `t^2 ≤ 2 / β^2 * e^{β t}`)
  have hsq_exp : ∀ t : ℝ, 2 ≤ t → t * (1 + t) ≤ (4 / β ^ 2) * Real.exp (β * t) := by
    intro t ht
    have hbt_nn : 0 ≤ β * t := by positivity
    -- `(β t)² / 2 ≤ exp(β t)` from `sum_range_le_exp` / quadratic Taylor bound
    have hquad_exp : (β * t) ^ 2 / 2 ≤ Real.exp (β * t) := by
      have h3 := Real.sum_le_exp_of_nonneg hbt_nn 3
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero] at h3
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
        Nat.factorial_one] at h3
      have hfac2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num
      rw [hfac2] at h3
      linarith
    have h1t : t * (1 + t) ≤ 2 * t ^ 2 := by nlinarith
    have hβ2 : 0 < β ^ 2 := sq_pos_of_pos hβ0
    calc t * (1 + t) ≤ 2 * t ^ 2 := h1t
      _ = (4 / β ^ 2) * ((β * t) ^ 2 / 2) := by field_simp [hβ2.ne']; ring
      _ ≤ (4 / β ^ 2) * Real.exp (β * t) :=
          mul_le_mul_of_nonneg_left hquad_exp (by positivity)
  set K_step : ℝ := 2 * (h + 1) * B_fac + 2 * (1 + h)
  refine ⟨2 * K_step + C' * (4 / β ^ 2), by dsimp [K_step, B_fac]; positivity, fun t ht => ?_⟩
  have ht_pos : 0 < t := by linarith
  set v_unw : ℂ := ⟨Real.log (⌊Real.exp t⌋₊ : ℝ) * Δπ_w t,
    Real.log (⌊Real.exp (t + h)⌋₊ : ℝ) * Δπ_w (t + h) / A⟩
  set v_log : ℂ := ⟨logStepIncrement E_w t h, logStepIncrement E_w (t + h) h / A⟩
  have hr0 := hfreeze_step ht le_rfl (by linarith)
  have hr1 := hfreeze_step ht (by linarith) le_rfl
  have hv_diff : |‖v_unw‖ - ‖v_log‖| ≤ 2 * K_step * Real.exp (β * t) / t := by
    refine (abs_norm_sub_norm_le v_unw v_log).trans ?_
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : |(v_unw - v_log).re| ≤ K_step * Real.exp (β * t) / t := hr0
    have him : |(v_unw - v_log).im| ≤ K_step * Real.exp (β * t) / t := by
      rw [Complex.sub_im]
      change |Real.log (⌊Real.exp (t + h)⌋₊ : ℝ) * Δπ_w (t + h) / A -
        logStepIncrement E_w (t + h) h / A| ≤ _
      rw [← sub_div, abs_div, abs_of_pos hA0]
      exact (div_le_self (abs_nonneg _) hA1).trans hr1
    rw [show 2 * K_step * Real.exp (β * t) / t =
      K_step * Real.exp (β * t) / t + K_step * Real.exp (β * t) / t by ring]
    exact add_le_add hre him
  have hrad_t : |‖v_log‖ - quartetRadialCoeff β γ m * Real.exp (β * t)| ≤
      C' * (4 / β ^ 2) * Real.exp (β * t) / t := by
    have hb := hrad_b t ht_pos.le
    unfold radialDiscrepancyOf at hb
    rw [twoIntervalRadius_eq_complex_norm hA0] at hb
    refine hb.trans ?_
    rw [le_div_iff₀ ht_pos]
    have hsq := hsq_exp t ht
    calc C' * (1 + t) * t = C' * (t * (1 + t)) := by ring
      _ ≤ C' * ((4 / β ^ 2) * Real.exp (β * t)) := mul_le_mul_of_nonneg_left hsq hC'
      _ = C' * (4 / β ^ 2) * Real.exp (β * t) := by ring
  have htri := (abs_add_le (‖v_unw‖ - ‖v_log‖)
    (‖v_log‖ - quartetRadialCoeff β γ m * Real.exp (β * t))).trans (add_le_add hv_diff hrad_t)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans_eq (by ring)

/-! ### 4. `{0, 1, 2}`-rational-prime `sEdit` realization and Euler-twin firewall -/

/-- Logarithmic prime count of a two-sided rational-prime edit `e : ℕ → ℤ`: each prime `p` is
counted with multiplicity `1 + e(p) ∈ {0, 1, 2}`. -/
def editedTheta (e : ℕ → ℤ) (x : ℝ) : ℝ :=
  Chebyshev.theta x + ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (e p : ℝ) * Real.log p

theorem editedTheta_eq_sum_primes {e : ℕ → ℤ} (he : IsEdit e) {x : ℝ} (_hx : 0 ≤ x) :
    editedTheta e x =
      (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, ((1 + e p : ℤ) : ℝ) * Real.log p) ∧
    (∀ p : ℕ, 1 + e p = 0 ∨ 1 + e p = 1 ∨ 1 + e p = 2) := by
  refine ⟨?_, fun p => ?_⟩
  · unfold editedTheta
    rw [Chebyshev.theta_eq_sum_primesLE]
    have hset : Nat.primesLE ⌊x⌋₊ = (Finset.Iic ⌊x⌋₊).filter Nat.Prime := by
      ext p
      rw [Nat.primesLE_eq_filter_Icc_one, mem_filter, mem_filter, mem_Icc, mem_Iic]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.one_lt.le, h.1⟩, h.2⟩⟩
    rw [hset, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    push_cast; ring
  · rcases he.range p with h | h | h <;> rw [h] <;> decide

/-- **Unconditional prime-logarithm wave approximation for `sEdit`.**
For every `0 < β < α < 1`, `γ : ℝ`, and `k₀ : ℕ`, the `{0, 1, 2}`-prime edit `sEdit α β γ k₀`
approximates `-2 ∑_{p ≤ x} p^{β - 1} cos(γ log p) log p` within `O(x^{α / 2} (1 + log x)²)`
unconditionally across all `x ≥ 1`. -/
theorem sEdit_primeLog_wave_approx {α β : ℝ} (hβ0 : 0 < β) (hβα : β < α) (hα1 : α < 1)
    (γ : ℝ) (k₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          ((sEdit α β γ k₀ p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) *
            Real.log p| ≤
        C * x ^ (α / 2) * (1 + Real.log x) ^ 2 := by
  have hα0 : 0 < α := hβ0.trans hβα
  have hβ1 : β < 1 := hβα.trans hα1
  have hgap : 0 < α - β := sub_pos.mpr hβα
  set k₁ : ℕ := max k₀ (⌈1 / (α - β)⌉₊ + 1)
  have hk₁_k₀ : k₀ ≤ k₁ := le_max_left _ _
  have hk₁_prod : 1 ≤ (k₁ : ℝ) * (α - β) := by
    have hceil : 1 / (α - β) ≤ (⌈1 / (α - β)⌉₊ : ℝ) := Nat.le_ceil _
    have hk₁_ge : (⌈1 / (α - β)⌉₊ : ℝ) ≤ k₁ := by
      exact_mod_cast ((Nat.le_succ _).trans (le_max_right k₀ _))
    have hdiv := hceil.trans hk₁_ge
    rwa [div_le_iff₀ hgap] at hdiv
  -- Unweighted partial sum bound on `[1, y]` (`1 ≤ y`)
  set r : ℝ := (2 : ℝ) ^ (α / 2)
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
  set C_unw : ℝ := 52 * (r / (r - 1)) + 4 + 3 * (2 : ℝ) ^ k₁
  have hC_unw : 0 ≤ C_unw := by
    have hq : 0 ≤ r / (r - 1) := div_nonneg (by linarith) (by linarith)
    dsimp [C_unw]; positivity
  let coeff (p : ℕ) : ℝ :=
    (sEdit α β γ k₀ p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)
  have hunw_bound : ∀ y : ℝ, 1 ≤ y →
      |∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, coeff p| ≤
        C_unw * y ^ (α / 2) * (1 + Real.log y) := by
    intro y hy
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    have hyα : 1 ≤ y ^ (α / 2) := Real.one_le_rpow hy (by linarith)
    have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
    set K := Nat.log 2 ⌊y⌋₊
    set T := (Finset.Iio (2 ^ (K + 1))).filter Nat.Prime
    let f0 (p : ℕ) : ℝ := if p ≤ ⌊y⌋₊ then coeff p else 0
    have hpart : ∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, coeff p =
        ∑ k ∈ Finset.range (K + 1), ∑ p ∈ RHTower.BeurlingDeletion.blockPrimes k, f0 p := by
      have hfib : ∑ k ∈ Finset.range (K + 1), ∑ p ∈ RHTower.BeurlingDeletion.blockPrimes k, f0 p =
          ∑ p ∈ T, f0 p := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := Finset.range (K + 1)) (g := Nat.log 2)
          (fun p hp => by
            rw [Finset.mem_range]
            have hp' := Finset.mem_filter.mp hp
            exact Nat.lt_succ_of_le (Nat.le_of_lt_succ
              (Nat.log_lt_of_lt_pow hp'.2.ne_zero (Finset.mem_Iio.mp hp'.1))))]
        refine Finset.sum_congr rfl fun k hk => Finset.sum_congr ?_ fun _ _ => rfl
        ext p
        simp only [Finset.mem_filter, Finset.mem_Iio, RHTower.BeurlingDeletion.mem_blockPrimes, T]
        have hk' : k < K + 1 := Finset.mem_range.mp hk
        constructor
        · rintro ⟨hp, h2k, hlt⟩
          exact ⟨⟨lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hk'), hp⟩,
            Nat.log_eq_of_pow_le_of_lt_pow h2k hlt⟩
        · rintro ⟨⟨_, hp⟩, hlog⟩
          exact ⟨hp, hlog ▸ Nat.pow_log_le_self 2 hp.ne_zero,
            hlog ▸ Nat.lt_pow_succ_log_self (by norm_num) p⟩
      rw [hfib]
      have hsub : (Finset.Iic ⌊y⌋₊).filter Nat.Prime ⊆ T := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr
          (lt_of_le_of_lt (Finset.mem_Iic.mp hp1) (Nat.lt_pow_succ_log_self (by norm_num) _)), hp2⟩
      symm
      rw [← Finset.sum_subset hsub fun p _ hpnot => by
        dsimp [f0]
        rw [if_neg (fun hle => hpnot (Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr hle,
          (Finset.mem_filter.mp ‹_›).2⟩))]]
      refine Finset.sum_congr rfl fun p hp => ?_
      dsimp [f0]
      rw [if_pos (Finset.mem_Iic.mp (Finset.mem_filter.mp hp).1)]
    rw [hpart]
    have h2K : (2 : ℝ) ^ K ≤ y := by
      have h1 : 2 ^ K ≤ ⌊y⌋₊ := Nat.pow_log_le_self 2 (Nat.floor_pos.mpr hy).ne'
      exact (by exact_mod_cast h1 : (2 : ℝ) ^ K ≤ ⌊y⌋₊).trans (Nat.floor_le hy0.le)
    have hK1 : (K : ℝ) + 1 ≤ 2 * (1 + Real.log y) := by
      have h := Real.log_le_log (by positivity) h2K
      rw [Real.log_pow] at h
      nlinarith [Real.log_two_gt_d9]
    have hrK : r ^ K ≤ y ^ (α / 2) := by
      dsimp [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num)]
      exact Real.rpow_le_rpow (by positivity) (by rwa [Real.rpow_natCast]) (by linarith)
    have hgeom : ∑ k ∈ Finset.range (K + 1), r ^ k ≤ r / (r - 1) * y ^ (α / 2) := by
      rw [geom_sum_eq hr1.ne', div_le_iff₀ (by linarith)]
      have hrK' : r ^ (K + 1) = r * r ^ K := by rw [pow_succ]; ring
      have he : r / (r - 1) * y ^ (α / 2) * (r - 1) = r * y ^ (α / 2) := by
        field_simp; exact div_self (sub_pos.mpr hr1).ne'
      rw [he, hrK']
      nlinarith [pow_pos (show (0 : ℝ) < r by linarith) K]
    -- Bound each block `k`
    have hblk : ∀ k ∈ Finset.range (K + 1),
        |∑ p ∈ RHTower.BeurlingDeletion.blockPrimes k, f0 p| ≤
          if k < k₁ then 3 * (2 : ℝ) ^ k
          else 26 * r ^ k * ((K : ℝ) + 1) + 2 := by
      intro k hk
      by_cases hkk₁ : k < k₁
      · rw [if_pos hkk₁]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hcard : ((RHTower.BeurlingDeletion.blockPrimes k).card : ℝ) ≤ (2 : ℝ) ^ k := by
          exact_mod_cast RHTower.BeurlingDeletion.card_blockPrimes_le k
        calc ∑ p ∈ RHTower.BeurlingDeletion.blockPrimes k, |f0 p|
            ≤ ∑ _p ∈ RHTower.BeurlingDeletion.blockPrimes k, (3 : ℝ) := by
              refine Finset.sum_le_sum fun p hp => ?_
              dsimp [f0]
              split_ifs
              · dsimp [coeff]
                have hp1 : (1 : ℝ) ≤ p :=
                  by exact_mod_cast (RHTower.BeurlingDeletion.mem_blockPrimes.mp hp).1.one_lt.le
                have he_le : |(sEdit α β γ k₀ p : ℝ)| ≤ 1 := (isEdit_sEdit α β γ k₀).abs_le_one p
                have hp_pow : (p : ℝ) ^ (β - 1) ≤ 1 :=
                  Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
                have hcos_le : |Real.cos (γ * Real.log p)| ≤ 1 := Real.abs_cos_le_one _
                have h2_le : |2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)| ≤ 2 := by
                  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
                  nlinarith [mul_le_mul hp_pow hcos_le (abs_nonneg _) zero_le_one]
                exact (abs_add_le _ _).trans (by linarith)
              · simp
          _ = ((RHTower.BeurlingDeletion.blockPrimes k).card : ℝ) * 3 := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 3 * (2 : ℝ) ^ k := by linarith
      · rw [if_neg hkk₁]
        push Not at hkk₁
        have hk_prod : 1 ≤ (k : ℝ) * (α - β) := one_le_of_le hβα hk₁_prod hkk₁
        have hk_k₀ : k₀ ≤ k := hk₁_k₀.trans hkk₁
        have hdev := norm_sum_target_testFn_le hα0 hα1 hβ1 γ hk_prod hk_k₀ (⌊y⌋₊ : ℝ) 0
        have hre_eq : (∑ p ∈ RHTower.BeurlingDeletion.blockPrimes k,
            target α β γ k₀ p * RHTower.BeurlingDeletion.testFn (⌊y⌋₊ : ℝ) 0 p).re =
            ∑ p ∈ RHTower.BeurlingDeletion.blockPrimes k, f0 p := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hp_pos : 0 < p := (RHTower.BeurlingDeletion.mem_blockPrimes.mp hp).1.pos
          dsimp [f0, coeff, target, RHTower.BeurlingDeletion.testFn]
          by_cases hpy : p ≤ ⌊y⌋₊
          · rw [if_pos ⟨hp_pos, by exact_mod_cast hpy⟩, if_pos hpy]
            simp
            left
            rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), ← Complex.ofReal_mul,
              Complex.cos_ofReal_re]
          · rw [if_neg (fun h => hpy (by exact_mod_cast h.2)), if_neg hpy]
            simp
        have habs_le := (Complex.abs_re_le_norm _).trans hdev
        rw [hre_eq, abs_zero, zero_add] at habs_le
        have hlog2_le1 : Real.sqrt (Real.log 2) ≤ 1 := by
          rw [Real.sqrt_le_one]
          exact Real.log_two_lt_d9.le.trans (by norm_num)
        have hrk : (2 : ℝ) ^ ((k : ℝ) * α / 2) = r ^ k := by
          dsimp [r]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring
        have hsk : Real.sqrt ((k : ℝ) + 1) ≤ (K : ℝ) + 1 := by
          have hkK : (k : ℝ) + 1 ≤ (K : ℝ) + 1 := by
            have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            exact_mod_cast Nat.add_le_add_right this 1
          refine (Real.sqrt_le_sqrt hkK).trans ?_
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [Nat.cast_nonneg (α := ℝ) K]
        rw [hrk] at habs_le
        calc |∑ p ∈ RHTower.BeurlingDeletion.blockPrimes k, f0 p|
            ≤ 26 * r ^ k * Real.sqrt ((k : ℝ) + 1) * Real.sqrt (Real.log 2) + 2 := habs_le
          _ ≤ 26 * r ^ k * ((K : ℝ) + 1) * 1 + 2 := by gcongr
          _ = 26 * r ^ k * ((K : ℝ) + 1) + 2 := by ring
    -- Sum block bounds over `k ∈ range (K + 1)`
    have hlow_sum : ∑ k ∈ (Finset.range (K + 1)).filter (· < k₁), (3 * (2 : ℝ) ^ k) ≤
        3 * (2 : ℝ) ^ k₁ := by
      have hsub_k1 : (Finset.range (K + 1)).filter (· < k₁) ⊆ Finset.range k₁ := by
        intro k hk; exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
      calc ∑ k ∈ (Finset.range (K + 1)).filter (· < k₁), (3 * (2 : ℝ) ^ k)
          ≤ ∑ k ∈ Finset.range k₁, 3 * (2 : ℝ) ^ k :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_k1 (fun _ _ _ => by positivity)
        _ = 3 * ∑ k ∈ Finset.range k₁, (2 : ℝ) ^ k := by rw [← Finset.mul_sum]
        _ = 3 * (((2 : ℝ) ^ k₁ - 1) / (2 - 1)) := by
            rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
        _ ≤ 3 * (2 : ℝ) ^ k₁ := by linarith
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hblk).trans ?_)
    have hsplit_ite : (∑ k ∈ Finset.range (K + 1),
        if k < k₁ then 3 * (2 : ℝ) ^ k else 26 * r ^ k * ((K : ℝ) + 1) + 2) ≤
        3 * (2 : ℝ) ^ k₁ +
          ∑ k ∈ Finset.range (K + 1), (26 * r ^ k * ((K : ℝ) + 1) + 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (K + 1)) (· < k₁)]
      have h1 : ∑ k ∈ (Finset.range (K + 1)).filter (· < k₁),
          (if k < k₁ then 3 * (2 : ℝ) ^ k else 26 * r ^ k * ((K : ℝ) + 1) + 2) ≤
          3 * (2 : ℝ) ^ k₁ := by
        rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_filter.mp hk).2)]
        exact hlow_sum
      have h2 : ∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < k₁),
          (if k < k₁ then 3 * (2 : ℝ) ^ k else 26 * r ^ k * ((K : ℝ) + 1) + 2) ≤
          ∑ k ∈ Finset.range (K + 1), (26 * r ^ k * ((K : ℝ) + 1) + 2) := by
        rw [Finset.sum_congr rfl (fun k hk => if_neg (Finset.mem_filter.mp hk).2)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      exact add_le_add h1 h2
    refine hsplit_ite.trans ?_
    have hhi_sum : ∑ k ∈ Finset.range (K + 1), (26 * r ^ k * ((K : ℝ) + 1) + 2) ≤
        (52 * (r / (r - 1)) + 4) * y ^ (α / 2) * (1 + Real.log y) := by
      have heq : ∑ k ∈ Finset.range (K + 1), (26 * r ^ k * ((K : ℝ) + 1) + 2) =
          26 * ((K : ℝ) + 1) * (∑ k ∈ Finset.range (K + 1), r ^ k) + 2 * ((K : ℝ) + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.mul_sum]
        push_cast
        congr 1
        · exact Finset.sum_congr rfl fun _ _ => by ring
        · ring
      rw [heq]
      have hq : 0 ≤ r / (r - 1) := div_nonneg (by linarith) (by linarith)
      have h1 : 26 * ((K : ℝ) + 1) * (∑ k ∈ Finset.range (K + 1), r ^ k) ≤
          52 * (r / (r - 1)) * y ^ (α / 2) * (1 + Real.log y) := by
        calc 26 * ((K : ℝ) + 1) * (∑ k ∈ Finset.range (K + 1), r ^ k)
            ≤ 26 * (2 * (1 + Real.log y)) * (r / (r - 1) * y ^ (α / 2)) := by gcongr
          _ = 52 * (r / (r - 1)) * y ^ (α / 2) * (1 + Real.log y) := by ring
      have h2 : 2 * ((K : ℝ) + 1) ≤ 4 * y ^ (α / 2) * (1 + Real.log y) := by
        calc 2 * ((K : ℝ) + 1) ≤ 4 * (1 + Real.log y) := by linarith
          _ ≤ 4 * y ^ (α / 2) * (1 + Real.log y) := by
              nlinarith [mul_le_mul_of_nonneg_right hyα (by linarith : 0 ≤ 1 + Real.log y)]
      linarith
    have hconst_le : 3 * (2 : ℝ) ^ k₁ ≤
        3 * (2 : ℝ) ^ k₁ * y ^ (α / 2) * (1 + Real.log y) := by
      have hprod1 : 1 ≤ y ^ (α / 2) * (1 + Real.log y) :=
        one_le_mul_of_one_le_of_one_le hyα (by linarith)
      have := mul_le_mul_of_nonneg_left hprod1 (by positivity : 0 ≤ 3 * (2 : ℝ) ^ k₁)
      linarith
    dsimp [C_unw]
    linarith
  -- Multiply by `log p` via `sum_weighted_le_of_suffix_bounds` on `(0, ⌊x⌋₊]`
  refine ⟨2 * C_unw, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  let a (n : ℕ) : ℝ := if n.Prime then coeff n else 0
  have hsum_eq : (∑ p ∈ (Finset.Iic N).filter Nat.Prime, coeff p * Real.log p) =
      ∑ n ∈ Ioc 0 N, Real.log n * a n := by
    rw [Finset.sum_filter]
    have hset : Finset.Iic N = insert 0 (Ioc 0 N) := by
      ext n; simp only [mem_Iic, mem_insert, mem_Ioc]; omega
    rw [hset, Finset.sum_insert (by simp), if_neg Nat.not_prime_zero, zero_add]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [a]; split_ifs <;> ring
  rw [hsum_eq]
  set M_x : ℝ := C_unw * x ^ (α / 2) * (1 + Real.log x)
  have hM_x : 0 ≤ M_x := by
    dsimp [M_x]
    exact mul_nonneg (mul_nonneg hC_unw (Real.rpow_nonneg hx0.le _))
      (by linarith [Real.log_nonneg hx])
  have hpref : ∀ m : ℕ, m ≤ N → |∑ i ∈ Finset.Iic m, a i| ≤ M_x := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · have h0 : Finset.Iic (0 : ℕ) = {0} := by ext i; simp
      rw [h0, Finset.sum_singleton]
      simp [a, Nat.not_prime_zero, hM_x]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
      have hmx : (m : ℝ) ≤ x :=
        (by exact_mod_cast hm : (m : ℝ) ≤ N).trans (Nat.floor_le hx0.le)
      have heq_m : ∑ i ∈ Finset.Iic m, a i =
          ∑ p ∈ (Finset.Iic ⌊(m : ℝ)⌋₊).filter Nat.Prime, coeff p := by
        rw [Nat.floor_natCast, Finset.sum_filter]
      rw [heq_m]
      refine (hunw_bound m hm1).trans ?_
      dsimp [M_x]
      have hrp : (m : ℝ) ^ (α / 2) ≤ x ^ (α / 2) :=
        Real.rpow_le_rpow (by positivity) hmx (by linarith)
      have hlg_m : 1 + Real.log m ≤ 1 + Real.log x := by
        linarith [Real.log_le_log (by linarith) hmx]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hrp hC_unw) hlg_m
        (by linarith [Real.log_nonneg hm1]) (mul_nonneg hC_unw (Real.rpow_nonneg hx0.le _))
  have hsuff : ∀ j : ℕ, 0 ≤ j → j ≤ N → |∑ i ∈ Ioc j N, a i| ≤ 2 * M_x := by
    intro j _ hjN
    have hdiff : ∑ i ∈ Ioc j N, a i = (∑ i ∈ Finset.Iic N, a i) - (∑ i ∈ Finset.Iic j, a i) := by
      have hsplit : Finset.Iic N = Finset.Iic j ∪ Ioc j N := by
        ext i; simp only [mem_Iic, mem_union, mem_Ioc]; omega
      have hdisj : Disjoint (Finset.Iic j) (Ioc j N) :=
        Finset.disjoint_left.mpr fun _ h1 h2 => (mem_Ioc.mp h2).1.not_ge (mem_Iic.mp h1)
      rw [hsplit, Finset.sum_union hdisj]; ring
    rw [hdiff]
    exact (abs_sub _ _).trans ((add_le_add (hpref N le_rfl) (hpref j hjN)).trans_eq (two_mul _).symm)
  have hw0 : 0 ≤ Real.log ((0 + 1 : ℕ) : ℝ) := by simp
  have hw_mono : ∀ i ∈ Ioc 0 (N - 1), Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) := by
    intro i hi
    have hi1 : 1 ≤ i := (mem_Ioc.mp hi).1
    exact Real.log_le_log (by exact_mod_cast hi1) (by exact_mod_cast Nat.le_succ i)
  have hpos := sum_weighted_le_of_suffix_bounds (Nat.pos_of_ne_zero (by omega)) a
    (fun n => Real.log n) (fun j hj hjN => (abs_le.mp (hsuff j hj hjN)).2) hw0 hw_mono
  have hneg := sum_weighted_le_of_suffix_bounds (Nat.pos_of_ne_zero (by omega)) (fun n => -a n)
    (fun n => Real.log n)
    (fun j hj hjN => by rw [Finset.sum_neg_distrib]; exact neg_le.mpr (abs_le.mp (hsuff j hj hjN)).1)
    hw0 hw_mono
  simp only [mul_neg, Finset.sum_neg_distrib] at hneg
  have habs_sum : |∑ n ∈ Ioc 0 N, Real.log n * a n| ≤ Real.log (N : ℝ) * (2 * M_x) :=
    abs_le.mpr ⟨neg_le.mp hneg, hpos⟩
  have hlogN : Real.log (N : ℝ) ≤ 1 + Real.log x := by
    have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    linarith [Real.log_le_log hN0 hNx]
  refine habs_sum.trans ?_
  calc Real.log (N : ℝ) * (2 * M_x)
      ≤ (1 + Real.log x) * (2 * M_x) := mul_le_mul_of_nonneg_right hlogN (by positivity)
    _ = 2 * C_unw * x ^ (α / 2) * (1 + Real.log x) ^ 2 := by dsimp [M_x]; ring

/-- Mean-value bound `‖(y : ℂ)^{ρ - 1} − (x : ℂ)^{ρ - 1}‖ ≤ ‖ρ - 1‖ (y − x) x^{β - 2}` for
`0 < x ≤ y` and `ρ = β + iγ` with `β < 1`. -/
private theorem norm_cpow_sub_one_diff_le {β γ x y : ℝ} (hβ1 : β < 1) (hx : 0 < x)
    (hxy : x ≤ y) :
    let ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
    ‖(y : ℂ) ^ (ρ - 1) - (x : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ - 1‖ * (y - x) * x ^ (β - 2) := by
  intro ρ
  have h0 : (0 : ℝ) ∉ Set.uIcc x y := by
    rw [Set.uIcc_of_le hxy]; intro h; linarith [h.1]
  have hne_neg1 : ρ - 2 ≠ -1 := by
    intro he
    have := congrArg Complex.re he
    simp [ρ] at this
    linarith
  have hint := integral_cpow (a := x) (b := y) (r := ρ - 2) (Or.inr ⟨hne_neg1, h0⟩)
  have he1 : ρ - 2 + 1 = ρ - 1 := by ring
  rw [he1] at hint
  have hρ1_ne : ρ - 1 ≠ 0 := fun he => hne_neg1 (by linear_combination he)
  have heq : (y : ℂ) ^ (ρ - 1) - (x : ℂ) ^ (ρ - 1) =
      (ρ - 1) * ∫ s in x..y, (s : ℂ) ^ (ρ - 2) := by
    rw [hint]; field_simp [hρ1_ne]
  rw [heq, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hbound : ∀ s ∈ Set.uIoc x y, ‖(s : ℂ) ^ (ρ - 2)‖ ≤ x ^ (β - 2) := by
    intro s hs
    rw [Set.uIoc_of_le hxy] at hs
    have hs0 : 0 < s := hx.trans hs.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hs0, show (ρ - 2).re = β - 2 by simp [ρ]]
    exact Real.rpow_le_rpow_of_nonpos hx hs.1.le (by linarith)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at h
  linarith

/-- Under `RiemannHypothesis`, `2 ∑_{p ≤ x} p^{β - 1} cos(γ log p) log p` approximates
`2 Re(x^{β + iγ} / (β + iγ))` within `O(√x (1 + log x)²)` across all `x ≥ 1` for every
`1/2 < β < 1` and `γ : ℝ`. -/
private theorem rh_prime_wave_sum_approx (hRH : RiemannHypothesis) {β : ℝ} (hβ : 1 / 2 < β)
    (hβ1 : β < 1) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |2 * (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p) -
        2 * (((x : ℂ) ^ (((β : ℂ) + I * (γ : ℂ))) / (((β : ℂ) + I * (γ : ℂ)))).re)| ≤
        C * Real.sqrt x * (1 + Real.log x) ^ 2 := by
  set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  have hβ0 : 0 < β := by linarith
  have hρ_re0 : 0 < ρ.re := by simp [ρ, hβ0]
  have hρ_re1 : ρ.re ≤ 1 := by simp [ρ, hβ1.le]
  have hρ_ne : ρ ≠ 0 := fun he => by rw [he, Complex.zero_re] at hρ_re0; exact lt_irrefl 0 hρ_re0
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
  -- Uniform `|θ(y) - y| ≤ K_θ √y (1 + log y)²` for all `y ≥ 1` under `RiemannHypothesis`
  set K_rh : ℝ := |200 * (RHTower.xiLineTwoLogDerivConstant + 2)| + 80 + 3 * (Real.log 4 + 4)
  have hK_rh : 0 ≤ K_rh := by dsimp [K_rh]; positivity
  have hθ_rh : ∀ y : ℝ, 1 ≤ y → |Chebyshev.theta y - y| ≤ K_rh * Real.sqrt y * (1 + Real.log y) ^ 2 := by
    intro y hy
    have hlog_nn : 0 ≤ Real.log y := Real.log_nonneg hy
    have h1_sq : 1 ≤ (1 + Real.log y) ^ 2 := by nlinarith
    have hsqrt1 : 1 ≤ Real.sqrt y := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hy
    have hpt : |Chebyshev.psi y - Chebyshev.theta y| ≤
        3 * (Real.log 4 + 4) * Real.sqrt y * (1 + Real.log y) ^ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
      have h1 := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt y
      exact h1.trans (le_mul_of_one_le_right (by positivity) h1_sq)
    have hpsi : |Chebyshev.psi y - y| ≤
        (|200 * (RHTower.xiLineTwoLogDerivConstant + 2)| + 80) *
          Real.sqrt y * (1 + Real.log y) ^ 2 := by
      by_cases hy16 : 16 ≤ y
      · have h1 := RHTower.abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH hy16
        have hsq : Real.log y ^ 2 ≤ (1 + Real.log y) ^ 2 := by nlinarith
        calc |Chebyshev.psi y - y|
            ≤ |200 * (RHTower.xiLineTwoLogDerivConstant + 2)| * Real.sqrt y * Real.log y ^ 2 :=
              h1.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)) (sq_nonneg _))
          _ ≤ (|200 * (RHTower.xiLineTwoLogDerivConstant + 2)| + 80) *
                Real.sqrt y * (1 + Real.log y) ^ 2 := by
              have := mul_le_mul_of_nonneg_left hsq
                (mul_nonneg (abs_nonneg (200 * (RHTower.xiLineTwoLogDerivConstant + 2)))
                  (Real.sqrt_nonneg y))
              nlinarith [Real.sqrt_nonneg y]
      · have h5 := RiemannGaussian.abs_chebyshevPsi_sub_self_le_five_mul_self_of_one_le hy
        have hy_lt : y ≤ 16 := (not_le.mp hy16).le
        calc |Chebyshev.psi y - y| ≤ 5 * 16 := by linarith
          _ = 80 * 1 * 1 := by norm_num
          _ ≤ (|200 * (RHTower.xiLineTwoLogDerivConstant + 2)| + 80) *
                Real.sqrt y * (1 + Real.log y) ^ 2 := by
              have hprod : 1 ≤ Real.sqrt y * (1 + Real.log y) ^ 2 :=
                one_le_mul_of_one_le_of_one_le hsqrt1 h1_sq
              nlinarith [abs_nonneg (200 * (RHTower.xiLineTwoLogDerivConstant + 2))]
    have htri := abs_sub (Chebyshev.psi y - y) (Chebyshev.psi y - Chebyshev.theta y)
    rw [show (Chebyshev.psi y - y) - (Chebyshev.psi y - Chebyshev.theta y) =
      Chebyshev.theta y - y by ring] at htri
    dsimp [K_rh]
    linarith [htri, hpsi, hpt]
  set C_tot : ℝ := 2 * (K_rh + 2 * K_rh * ‖ρ - 1‖ + 2 * ‖ρ - 1‖ + 1 / ‖ρ‖ + 1)
  refine ⟨C_tot, by dsimp [C_tot]; positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1_sq : 1 ≤ (1 + Real.log x) ^ 2 := by nlinarith
  have hsqrt1 : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hx
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  let g (n : ℕ) : ℝ := (((n : ℂ) ^ (ρ - 1)).re)
  let δ (n : ℕ) : ℝ := Chebyshev.theta (n : ℝ) - (n : ℝ)
  have hδ0 : δ 0 = 0 := by simp [δ, Chebyshev.theta]
  -- Rewrite prime sum as `∑_{1 ≤ n ≤ N} (δ n - δ(n - 1) + 1) * g n`
  have hg_prime : ∀ n : ℕ, 1 ≤ n →
      g n = (n : ℝ) ^ (β - 1) * Real.cos (γ * Real.log n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [g]
    have hcp : (n : ℂ) ^ (ρ - 1) =
        (((n : ℝ) ^ (β - 1) : ℝ) : ℂ) * Complex.exp (((γ * Real.log n : ℝ) : ℂ) * I) := by
      have hnC : ((n : ℝ) : ℂ) = (n : ℂ) := Complex.ofReal_natCast n
      rw [← hnC, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn0.ne'),
        ← Complex.ofReal_log hn0.le, Real.rpow_def_of_pos hn0, Complex.ofReal_exp,
        ← Complex.exp_add]
      congr 1; dsimp [ρ]; push_cast; ring
    rw [hcp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hjump : ∀ n : ℕ, 1 ≤ n →
      (if n.Prime then Real.log n else 0) = δ n - δ (n - 1) + 1 := by
    intro n hn
    let fn (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
    have hp_sum : ∀ m : ℕ, Chebyshev.theta (m : ℝ) = ∑ k ∈ Icc 1 m, fn k := by
      intro m
      rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_Icc_one, Finset.sum_filter]
    have hsplit : Icc 1 n = Icc 1 (n - 1) ∪ {n} := by
      ext k; simp only [mem_Icc, mem_union, mem_singleton]; omega
    have hdisj : Disjoint (Icc 1 (n - 1)) {n} := by
      rw [Finset.disjoint_singleton_right, mem_Icc]; omega
    dsimp [δ]
    rw [hp_sum n, hp_sum (n - 1), hsplit, Finset.sum_union hdisj, Finset.sum_singleton,
      Nat.cast_sub hn, Nat.cast_one]
    dsimp [fn]; ring
  have hprime_split : (∑ p ∈ (Finset.Iic N).filter Nat.Prime,
      (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p) =
      (∑ n ∈ Icc 1 N, (δ n - δ (n - 1)) * g n) + ∑ n ∈ Icc 1 N, g n := by
    rw [Finset.sum_filter]
    have hset : Finset.Iic N = insert 0 (Icc 1 N) := by
      ext n; simp only [mem_Iic, mem_insert, mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp), if_neg Nat.not_prime_zero, zero_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hj := hjump n hn1
    rw [← hg_prime n hn1]
    by_cases hnp : n.Prime
    · rw [if_pos hnp] at hj ⊢; linarith [congrArg (· * g n) hj]
    · rw [if_neg hnp] at hj ⊢; linarith [congrArg (· * g n) hj]
  -- Bound 1: Abel summation of `∑_{1 ≤ n ≤ N} (δ n - δ(n - 1)) * g n`
  have habel_id : ∀ M : ℕ, 1 ≤ M →
      ∑ n ∈ Icc 1 M, (δ n - δ (n - 1)) * g n =
        δ M * g M - ∑ n ∈ Icc 1 (M - 1), δ n * (g (n + 1) - g n) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp [hδ0]
    | succ M hM ih =>
      have h1 : Icc 1 (M + 1) = insert (M + 1) (Icc 1 M) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      have h2 : Icc 1 M = insert M (Icc 1 (M - 1)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [h1, Finset.sum_insert (by rw [mem_Icc]; omega), ih, Nat.add_sub_cancel, h2,
        Finset.sum_insert (by rw [mem_Icc]; omega)]
      ring
  have habel_bound : |∑ n ∈ Icc 1 N, (δ n - δ (n - 1)) * g n| ≤
      (K_rh + 2 * K_rh * ‖ρ - 1‖) * Real.sqrt x * (1 + Real.log x) ^ 2 := by
    rw [habel_id N hN1]
    have hδ_le : ∀ n : ℕ, 1 ≤ n → n ≤ N →
        |δ n| ≤ K_rh * Real.sqrt n * (1 + Real.log x) ^ 2 := by
      intro n hn1 hnN
      have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hnx : (n : ℝ) ≤ x := (by exact_mod_cast hnN : (n : ℝ) ≤ N).trans hNx
      refine (hθ_rh n hnR1).trans ?_
      have hlg : (1 + Real.log n) ^ 2 ≤ (1 + Real.log x) ^ 2 :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hnR1])
          (by linarith [Real.log_le_log (by linarith) hnx]) 2
      exact mul_le_mul_of_nonneg_left hlg (mul_nonneg hK_rh (Real.sqrt_nonneg _))
    have hbdry : |δ N * g N| ≤ K_rh * Real.sqrt x * (1 + Real.log x) ^ 2 := by
      rw [abs_mul]
      have hgN : |g N| ≤ 1 := by
        rw [hg_prime N hN1, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
        have hp1 : (N : ℝ) ^ (β - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
        have hc1 := Real.abs_cos_le_one (γ * Real.log N)
        nlinarith [mul_le_mul hp1 hc1 (abs_nonneg _) zero_le_one]
      calc |δ N| * |g N| ≤ (K_rh * Real.sqrt N * (1 + Real.log x) ^ 2) * 1 :=
            mul_le_mul (hδ_le N hN1 le_rfl) hgN (abs_nonneg _) (by positivity)
        _ ≤ K_rh * Real.sqrt x * (1 + Real.log x) ^ 2 := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNx) hK_rh) (sq_nonneg _)
    have hsum_diff : |∑ n ∈ Icc 1 (N - 1), δ n * (g (n + 1) - g n)| ≤
        2 * K_rh * ‖ρ - 1‖ * Real.sqrt x * (1 + Real.log x) ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ n ∈ Icc 1 (N - 1),
          |δ n * (g (n + 1) - g n)| ≤
            K_rh * ‖ρ - 1‖ * (1 + Real.log x) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        intro n hn
        have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
        have hnN : n ≤ N := (mem_Icc.mp hn).2.trans (Nat.sub_le N 1)
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hg_diff : |g (n + 1) - g n| ≤ ‖ρ - 1‖ * (n : ℝ) ^ (β - 2) := by
          dsimp [g]
          rw [← Complex.sub_re]
          refine (Complex.abs_re_le_norm _).trans ?_
          have hmvt := norm_cpow_sub_one_diff_le (γ := γ) hβ1 hn0
            (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ (n + 1 : ℕ))
          simpa [show ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 by push_cast; ring] using hmvt
        have hrpow_comb : Real.sqrt n * (n : ℝ) ^ (β - 2) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
          exact Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)
        rw [abs_mul]
        calc |δ n| * |g (n + 1) - g n|
            ≤ (K_rh * Real.sqrt n * (1 + Real.log x) ^ 2) * (‖ρ - 1‖ * (n : ℝ) ^ (β - 2)) :=
              mul_le_mul (hδ_le n hn1 hnN) hg_diff (abs_nonneg _) (by positivity)
          _ = K_rh * ‖ρ - 1‖ * (1 + Real.log x) ^ 2 * (Real.sqrt n * (n : ℝ) ^ (β - 2)) := by
              ring
          _ ≤ K_rh * ‖ρ - 1‖ * (1 + Real.log x) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hrpow_comb (by positivity)
      calc ∑ n ∈ Icc 1 (N - 1), |δ n * (g (n + 1) - g n)|
          ≤ ∑ n ∈ Icc 1 (N - 1),
              K_rh * ‖ρ - 1‖ * (1 + Real.log x) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ n ∈ Icc 1 N,
              K_rh * ‖ρ - 1‖ * (1 + Real.log x) ^ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right (Nat.sub_le N 1)) (fun _ _ _ => by positivity)
        _ = K_rh * ‖ρ - 1‖ * (1 + Real.log x) ^ 2 * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [← Finset.mul_sum]
        _ ≤ K_rh * ‖ρ - 1‖ * (1 + Real.log x) ^ 2 * (2 * Real.sqrt N) :=
            mul_le_mul_of_nonneg_left (RHTower.sum_rpow_neg_half_le N) (by positivity)
        _ ≤ K_rh * ‖ρ - 1‖ * (1 + Real.log x) ^ 2 * (2 * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNx) (by norm_num)) (by positivity)
        _ = 2 * K_rh * ‖ρ - 1‖ * Real.sqrt x * (1 + Real.log x) ^ 2 := by ring
    exact (abs_sub _ _).trans ((add_le_add hbdry hsum_diff).trans_eq (by ring))
  -- Bound 2: Euler–Maclaurin comparison `|(∑_{1 ≤ n ≤ N} g n) - Re(x^ρ / ρ)|`
  have hmain_bound : |(∑ n ∈ Icc 1 N, g n) - (((x : ℂ) ^ ρ / ρ).re)| ≤
      (2 * ‖ρ - 1‖ + 1 / ‖ρ‖ + 1) * Real.sqrt x * (1 + Real.log x) ^ 2 := by
    have hstep_int : ∀ n ∈ Icc 1 N,
        |g n - ((((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ).re)| ≤
          ‖ρ - 1‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      intro n hn
      have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have h0_mem : (0 : ℝ) ∉ Set.uIcc (n : ℝ) (n + 1 : ℝ) := by
        rw [Set.uIcc_of_le (by linarith)]; intro hm; linarith [hm.1]
      have hint_n := integral_cpow (a := (n : ℝ)) (b := ((n + 1 : ℕ) : ℝ)) (r := ρ - 1)
        (Or.inl (by simp [ρ]; linarith))
      rw [sub_add_cancel] at hint_n
      have hint_const : ∫ _u in (n : ℝ)..((n + 1 : ℕ) : ℝ), (n : ℂ) ^ (ρ - 1) =
          (n : ℂ) ^ (ρ - 1) := by
        rw [intervalIntegral.integral_const, show ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 by push_cast; ring,
          one_smul]
      have hdiff_int : (n : ℂ) ^ (ρ - 1) - (((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ) =
          ∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ), ((n : ℂ) ^ (ρ - 1) - (u : ℂ) ^ (ρ - 1)) := by
        have hi1 : IntervalIntegrable (fun _u : ℝ => (n : ℂ) ^ (ρ - 1)) volume
            (n : ℝ) ((n + 1 : ℕ) : ℝ) := intervalIntegrable_const
        have hi2 : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (ρ - 1)) volume
            (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
          intervalIntegral.intervalIntegrable_cpow (Or.inr (by push_cast; exact h0_mem))
        rw [intervalIntegral.integral_sub hi1 hi2, hint_const, hint_n, sub_div]
        push_cast; rfl
      have hre_le := Complex.abs_re_le_norm ((n : ℂ) ^ (ρ - 1) -
        (((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ))
      rw [Complex.sub_re] at hre_le
      refine hre_le.trans ?_
      rw [hdiff_int]
      have hpt_u : ∀ u ∈ Set.uIoc (n : ℝ) ((n + 1 : ℕ) : ℝ),
          ‖(n : ℂ) ^ (ρ - 1) - (u : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ - 1‖ * (n : ℝ) ^ (β - 2) := by
        intro u hu
        rw [Set.uIoc_of_le (by exact_mod_cast Nat.le_succ n)] at hu
        rw [norm_sub_rev]
        have hmvt := norm_cpow_sub_one_diff_le (γ := γ) hβ1 hn0 hu.1.le
        have hudiff : u - (n : ℝ) ≤ 1 := by
          have : u ≤ (n : ℝ) + 1 := by simpa using hu.2
          linarith
        exact hmvt.trans (mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right (norm_nonneg _) hudiff) (Real.rpow_nonneg hn0.le _))
      have hni := intervalIntegral.norm_integral_le_of_norm_le_const hpt_u
      rw [show |((n + 1 : ℕ) : ℝ) - (n : ℝ)| = 1 by
        rw [show ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 by push_cast; ring, abs_one], mul_one] at hni
      exact hni.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)) (norm_nonneg _))
    -- Telescope `∑_{1 ≤ n ≤ N} (((n + 1)^ρ / ρ - n^ρ / ρ).re) = ((N + 1)^ρ / ρ - 1 / ρ).re`
    have htel : ∑ n ∈ Icc 1 N, ((((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ).re) =
        ((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((1 : ℂ) ^ ρ / ρ).re) := by
      have hIoc : Icc 1 N = Ioc 0 N := by ext k; simp only [mem_Icc, mem_Ioc]; omega
      rw [hIoc]
      have key : ∀ M : ℕ, ∑ n ∈ Ioc 0 M, ((((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ).re) =
          ((((M + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((1 : ℂ) ^ ρ / ρ).re) := by
        intro M
        induction M with
        | zero => simp
        | succ M ih =>
          rw [Finset.sum_Ioc_succ_top (Nat.zero_le M), ih, Complex.sub_re]; ring
      exact key N
    have hsum_err : |(∑ n ∈ Icc 1 N, g n) -
        (((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((1 : ℂ) ^ ρ / ρ).re))| ≤
        2 * ‖ρ - 1‖ * Real.sqrt x := by
      rw [← htel, ← Finset.sum_sub_distrib]
      calc |∑ n ∈ Icc 1 N, (g n - ((((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ).re))|
          ≤ ∑ n ∈ Icc 1 N, ‖ρ - 1‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hstep_int)
        _ = ‖ρ - 1‖ * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [← Finset.mul_sum]
        _ ≤ ‖ρ - 1‖ * (2 * Real.sqrt N) :=
            mul_le_mul_of_nonneg_left (RHTower.sum_rpow_neg_half_le N) (norm_nonneg _)
        _ ≤ ‖ρ - 1‖ * (2 * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNx) (by norm_num)) (norm_nonneg _)
        _ = 2 * ‖ρ - 1‖ * Real.sqrt x := by ring
    have hend1 : |(((1 : ℂ) ^ ρ / ρ).re)| ≤ 1 / ‖ρ‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      simp only [Complex.one_cpow, norm_div, norm_one, le_refl]
    have hendN : |((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((x : ℂ) ^ ρ / ρ).re)| ≤ 1 := by
      rw [← Complex.sub_re]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [← sub_div, norm_div, div_le_iff₀ hρ_pos]
      have hxN1 : x ≤ ((N + 1 : ℕ) : ℝ) := (Nat.lt_floor_add_one x).le.trans_eq (by push_cast; rfl)
      have hmvt := RHTower.norm_ofReal_cpow_sub_cpow_le hx0 hxN1 hρ_re0 hρ_re1
      rw [show ((N + 1 : ℕ) : ℂ) = (((N + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl]
      have hdiff_le1 : ((N + 1 : ℕ) : ℝ) - x ≤ 1 := by
        push_cast; linarith [hNx]
      have hrpow_le1 : x ^ (ρ.re - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx (by simp [ρ]; linarith)
      calc ‖(((N + 1 : ℕ) : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ‖
          ≤ ‖ρ‖ * (((N + 1 : ℕ) : ℝ) - x) * x ^ (ρ.re - 1) := hmvt
        _ ≤ ‖ρ‖ * 1 * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hdiff_le1 hρ_pos.le) hrpow_le1
              (Real.rpow_nonneg hx0.le _) (by positivity)
        _ = 1 * ‖ρ‖ := by ring
    have hcomb : |(∑ n ∈ Icc 1 N, g n) - (((x : ℂ) ^ ρ / ρ).re)| ≤
        2 * ‖ρ - 1‖ * Real.sqrt x + 1 / ‖ρ‖ + 1 := by
      have hsplit : (∑ n ∈ Icc 1 N, g n) - (((x : ℂ) ^ ρ / ρ).re) =
          ((∑ n ∈ Icc 1 N, g n) -
            (((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((1 : ℂ) ^ ρ / ρ).re))) +
            ((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re - (((x : ℂ) ^ ρ / ρ).re)) -
            (((1 : ℂ) ^ ρ / ρ).re) := by ring
      rw [hsplit]
      exact ((abs_sub _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add hsum_err hendN)) hend1)).trans_eq (by ring)
    have hprod1 : 1 ≤ Real.sqrt x * (1 + Real.log x) ^ 2 :=
      one_le_mul_of_one_le_of_one_le hsqrt1 h1_sq
    calc |(∑ n ∈ Icc 1 N, g n) - (((x : ℂ) ^ ρ / ρ).re)|
        ≤ 2 * ‖ρ - 1‖ * Real.sqrt x + 1 / ‖ρ‖ + 1 := hcomb
      _ ≤ 2 * ‖ρ - 1‖ * (Real.sqrt x * (1 + Real.log x) ^ 2) +
            (1 / ‖ρ‖ + 1) * (Real.sqrt x * (1 + Real.log x) ^ 2) := by
          have h1 : 2 * ‖ρ - 1‖ * Real.sqrt x ≤
              2 * ‖ρ - 1‖ * (Real.sqrt x * (1 + Real.log x) ^ 2) := by
            have := mul_le_mul_of_nonneg_left h1_sq
              (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖ρ - 1‖) (Real.sqrt_nonneg x))
            linarith
          have h2 : 1 / ‖ρ‖ + 1 ≤ (1 / ‖ρ‖ + 1) * (Real.sqrt x * (1 + Real.log x) ^ 2) :=
            le_mul_of_one_le_right (by positivity) hprod1
          linarith
      _ = (2 * ‖ρ - 1‖ + 1 / ‖ρ‖ + 1) * Real.sqrt x * (1 + Real.log x) ^ 2 := by ring
  -- Combine `hprime_split`, `habel_bound`, and `hmain_bound`
  rw [hprime_split, show 2 * ((∑ n ∈ Icc 1 N, (δ n - δ (n - 1)) * g n) + ∑ n ∈ Icc 1 N, g n) -
      2 * (((x : ℂ) ^ ρ / ρ).re) =
    2 * (∑ n ∈ Icc 1 N, (δ n - δ (n - 1)) * g n) +
      2 * ((∑ n ∈ Icc 1 N, g n) - (((x : ℂ) ^ ρ / ρ).re)) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  dsimp [C_tot]
  linarith [habel_bound, hmain_bound]

private theorem rh_sEdit_radial_bounded_of_params (hRH : RiemannHypothesis) {α β γ : ℝ}
    (hβ : 1 / 2 < β) (hβα : β < α) (hα1 : α < 1) (hγ : γ ≠ 0) (k₀ : ℕ) :
    ¬ IsLogSqrtSqUnbounded
        (radialDiscrepancyOf
          (fun t => editedTheta (sEdit α β γ k₀) (Real.exp t) - Real.exp t) β γ 1) := by
  have hβ0 : 0 < β := by linarith
  have hβ1 : β < 1 := hβα.trans hα1
  obtain ⟨C₁, hC₁, hedit⟩ := sEdit_primeLog_wave_approx hβ0 hβα hα1 γ k₀
  obtain ⟨C₂, hC₂, hwave⟩ := rh_prime_wave_sum_approx hRH hβ hβ1 γ
  -- Bound `|Chebyshev.theta x - x|` under `hRH`
  set K_θ : ℝ := |200 * (RHTower.xiLineTwoLogDerivConstant + 2)| + 3 * (Real.log 4 + 4)
  have hK_θ : 0 ≤ K_θ := by dsimp [K_θ]; positivity
  have hθ_rh : ∀ x : ℝ, 16 ≤ x →
      |Chebyshev.theta x - x| ≤ K_θ * Real.sqrt x * (1 + Real.log x) ^ 2 := by
    intro x hx
    have hx1 : 1 ≤ x := by linarith
    have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h1_sq : 1 ≤ (1 + Real.log x) ^ 2 := by nlinarith
    have hsq : Real.log x ^ 2 ≤ (1 + Real.log x) ^ 2 := by nlinarith
    have h1 := (RHTower.abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH hx).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)) (sq_nonneg _))
    have h2 : |Chebyshev.psi x - Chebyshev.theta x| ≤
        3 * (Real.log 4 + 4) * Real.sqrt x * (1 + Real.log x) ^ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
      exact (GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt x).trans
        (le_mul_of_one_le_right (by positivity) h1_sq)
    have htri := abs_sub (Chebyshev.psi x - x) (Chebyshev.psi x - Chebyshev.theta x)
    rw [show (Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x) =
      Chebyshev.theta x - x by ring] at htri
    have h1' := h1.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    dsimp [K_θ]; linarith
  set C_all : ℝ := K_θ + C₁ + C₂
  have hC_all : 0 ≤ C_all := by dsimp [C_all]; positivity
  set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  have hmode : ∀ s : ℝ, 3 ≤ s →
      |editedTheta (sEdit α β γ k₀) (Real.exp s) - Real.exp s +
        2 * (1 : ℝ) * (Complex.exp (ρ * (s : ℂ)) / ρ).re| ≤
        C_all * Real.exp (s / 2) * (1 + s) ^ 2 := by
    intro s hs
    have hx16 : 16 ≤ Real.exp s := by
      have h3 : (16 : ℝ) ≤ Real.exp 3 := by
        have := Real.exp_one_gt_d9
        calc (16 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
          _ ≤ Real.exp 1 ^ 3 := by gcongr
          _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
      exact h3.trans (Real.exp_le_exp.mpr hs)
    set x := Real.exp s
    have hx1 : 1 ≤ x := by linarith
    have hb_θ := hθ_rh x hx16
    have hb_ed := (hedit x hx1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : α / 2 ≤ 1 / 2)).trans_eq
          (Real.sqrt_eq_rpow x).symm) hC₁) (sq_nonneg _))
    have hb_wv := hwave x hx1
    have hcp : (x : ℂ) ^ ρ = Complex.exp (ρ * (s : ℂ)) := by
      dsimp [x]; exact cpow_exp_eq s ρ
    rw [hcp] at hb_wv
    have hsum_id : editedTheta (sEdit α β γ k₀) x - x +
        2 * (1 : ℝ) * (Complex.exp (ρ * (s : ℂ)) / ρ).re =
        (Chebyshev.theta x - x) +
          (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
            ((sEdit α β γ k₀ p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) *
              Real.log p) -
          (2 * (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
              (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p) -
            2 * (Complex.exp (ρ * (s : ℂ)) / ρ).re) := by
      unfold editedTheta
      have hlin : (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          ((sEdit α β γ k₀ p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) *
            Real.log p) =
          (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (sEdit α β γ k₀ p : ℝ) * Real.log p) +
            2 * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
              (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hlin]; ring
    rw [hsum_id]
    have htri := (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hb_θ hb_ed)) hb_wv)
    have hsqrt_x : Real.sqrt x = Real.exp (s / 2) := (Real.exp_half s).symm
    have hlog_x : Real.log x = s := Real.log_exp s
    rw [hsqrt_x, hlog_x] at htri
    exact htri.trans_eq (by dsimp [C_all]; ring)
  -- Transfer pointwise mode bound to `¬ IsLogSqrtSqUnbounded`
  set h := quarterPeriodStep γ
  have hh : 0 < h := quarterPeriodStep_pos hγ
  rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not]
  refine ⟨4 * C_all * Real.exp h * (1 + 2 * h) ^ 2, 3, fun t ht => ?_⟩
  set B_t : ℝ := C_all * Real.exp ((t + 2 * h) / 2) * (1 + (t + 2 * h)) ^ 2
  have hm_step : ∀ s : ℝ, t ≤ s → s ≤ t + 2 * h →
      |editedTheta (sEdit α β γ k₀) (Real.exp s) - Real.exp s +
        2 * ((1 : ℕ) : ℝ) * (Complex.exp (ρ * (s : ℂ)) / ρ).re| ≤ B_t := by
    intro s hs1 hs2
    rw [Nat.cast_one]
    refine (hmode s (ht.trans hs1)).trans ?_
    dsimp [B_t]
    have hexp_le : Real.exp (s / 2) ≤ Real.exp ((t + 2 * h) / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hsq_le : (1 + s) ^ 2 ≤ (1 + (t + 2 * h)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact mul_le_mul (mul_le_mul_of_nonneg_left hexp_le hC_all) hsq_le (sq_nonneg _)
      (by positivity)
  have hrad := abs_radialDiscrepancyOf_le_of_mode_error
    (f := fun s => editedTheta (sEdit α β γ k₀) (Real.exp s) - Real.exp s) (t := t) hβ0.le hγ 1
    (hm_step t le_rfl (by linarith))
    (hm_step (t + h) (by linarith) (by linarith))
    (hm_step (t + 2 * h) (by linarith) le_rfl)
  refine hrad.trans ?_
  dsimp [B_t]
  have hexp_sp : Real.exp ((t + 2 * h) / 2) = Real.exp h * Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1t : (1 + (t + 2 * h)) ^ 2 ≤ (1 + 2 * h) ^ 2 * (1 + t) ^ 2 := by
    have : 1 + (t + 2 * h) ≤ (1 + 2 * h) * (1 + t) := by nlinarith [ht, hh]
    exact (pow_le_pow_left₀ (by linarith) this 2).trans_eq (mul_pow _ _ 2)
  rw [hexp_sp]
  calc 4 * (C_all * (Real.exp h * Real.exp (t / 2)) * (1 + (t + 2 * h)) ^ 2)
      ≤ 4 * (C_all * (Real.exp h * Real.exp (t / 2)) * ((1 + 2 * h) ^ 2 * (1 + t) ^ 2)) := by
        gcongr
    _ = 4 * C_all * Real.exp h * (1 + 2 * h) ^ 2 * Real.exp (t / 2) * (1 + t) ^ 2 := by ring

/-- **`{0, 1, 2}`-rational-prime realization of the two-interval quartet circle under `RH`.**
1. For **every** `1/2 < β < 1` and `γ ≠ 0`, `sEdit ((β + 1)/2) β γ 0` assigns `{0, 1, 2}`
   multiplicities to actual rational primes and satisfies `¬ IsLogSqrtSqUnbounded` at `(β, γ, 1)`.
2. For **every** `1/2 < β < 2/3` and `γ ≠ 0`, there exist `α, k₀, c < 1/2, σ₁ < 1/2` such that a
   single `e = sEdit α β γ k₀` simultaneously has sub-square-root integer norm count `c < 1/2`,
   analytic continuation across `Re s = 1/2` with unique right-half-plane zeros `{β ± iγ}`, and
   bounded two-interval ordinary-prime radial discrepancy (`¬ IsLogSqrtSqUnbounded`). -/
theorem rh_sEdit_ordinaryPrime_realizes_twoIntervalRadius (hRH : RiemannHypothesis) :
    (∀ {β γ : ℝ}, 1 / 2 < β → β < 1 → γ ≠ 0 →
      let e := sEdit ((β + 1) / 2) β γ 0
      IsEdit e ∧
        ¬ IsLogSqrtSqUnbounded
            (radialDiscrepancyOf (fun t => editedTheta e (Real.exp t) - Real.exp t) β γ 1)) ∧
    (∀ {β γ : ℝ}, 1 / 2 < β → β < 2 / 3 → γ ≠ 0 →
      ∃ (α : ℝ) (k₀ : ℕ) (c σ₁ : ℝ),
        c < 1 / 2 ∧ σ₁ < 1 / 2 ∧
        IsIntegerNormFakeAt (editSystem (sEdit α β γ k₀)) c ∧
        DifferentiableOn ℂ (editG α β γ k₀) {s : ℂ | σ₁ < s.re} ∧
        (∀ s : ℂ, 1 / 2 < s.re → (editG α β γ k₀ s = 0 ↔
          s = zeroPt β γ ∨ s = conj (zeroPt β γ))) ∧
        ¬ IsLogSqrtSqUnbounded
            (radialDiscrepancyOf
              (fun t => editedTheta (sEdit α β γ k₀) (Real.exp t) - Real.exp t) β γ 1)) := by
  refine ⟨fun {β γ} hβ hβ1 hγ => ⟨isEdit_sEdit _ _ _ _,
    rh_sEdit_radial_bounded_of_params hRH hβ (by linarith) (by linarith) hγ 0⟩,
    fun {β γ} hlo hhi hγ => ?_⟩
  obtain ⟨α, k₀, c, σ₁, hc, hσ₁, _, hfake, _, hdiff, hzeros, _⟩ :=
    rh_subSqrt_singlePair_realization_and_defect_barrier hRH hlo hhi hγ
  -- Extract `β < α ∧ α < 1` from the existence of a deleted prime `sEdit α β γ k₀ p₀ = -1`
  obtain ⟨p₀, _, hep₀, -⟩ := exists_least_deleted_prime (by linarith : c ≤ 1) hfake
  have hsel : p₀ ∈ selected α β γ k₀ := by
    by_contra hnot
    unfold sEdit at hep₀
    rw [if_neg hnot] at hep₀
    norm_num at hep₀
  obtain ⟨k, i, hgood, hp₀_ne⟩ := hsel
  have hcond : α < 1 ∧ β < 1 ∧ 1 ≤ (k : ℝ) * (α - β) ∧ k₀ ≤ k := by
    by_contra hnot
    unfold sGood at hgood
    rw [dif_neg hnot] at hgood
    exact hp₀_ne hgood.symm
  have hβα : β < α := by
    by_contra hle
    push Not at hle
    have hnonpos : (k : ℝ) * (α - β) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) (by linarith)
    linarith [hcond.2.2.1]
  exact ⟨α, k₀, c, σ₁, hc, hσ₁, hfake, hdiff, hzeros,
    rh_sEdit_radial_bounded_of_params hRH hlo hβα hcond.1 hγ k₀⟩

/-- **Unconditional prime-edit / Euler-twin firewall for the two-interval quartet circle.**
1. Unconditionally for every `β ∈ (1/2, 2/3)` and `γ ≠ 0`, either `¬ RiemannHypothesis` holds, or
   there exists a `{0, 1, 2}`-rational-prime edit `sEdit α β γ k₀` simultaneously achieving
   integer norm-count exponent `c < 1/2`, analytic continuation below `Re s = 1/2` with unique
   right zero pair `{β ± iγ}`, and bounded two-interval ordinary-prime radial discrepancy.
2. Unconditionally for every `β ∈ (1/2, 1)`, positive degree-one Euler twins (with exact `Γ_ℝ`
   functional equation and real multiplicative coefficients `≥ 1`) vanish at `Re s = β` and carry
   confined quartet critical states.
3. Conversely, adjoining **both** a countable nonnegative Beurling prime system (`Λ_B ≥ 0`) **and**
   the `Γ_ℝ` functional equation up to an `L²` strip defect uniquely forces `ζ_B = ζ`
   (`beurling_levy_rigidity_forces_zeta`). -/
theorem unconditional_twoIntervalRadius_prime_and_twin_firewall {β γ : ℝ}
    (hlo : 1 / 2 < β) (hhi : β < 2 / 3) (hγ : γ ≠ 0) :
    (¬ RiemannHypothesis ∨
      ∃ (α : ℝ) (k₀ : ℕ) (c σ₁ : ℝ),
        c < 1 / 2 ∧ σ₁ < 1 / 2 ∧
        IsIntegerNormFakeAt (editSystem (sEdit α β γ k₀)) c ∧
        DifferentiableOn ℂ (editG α β γ k₀) {s : ℂ | σ₁ < s.re} ∧
        (∀ s : ℂ, 1 / 2 < s.re → (editG α β γ k₀ s = 0 ↔
          s = zeroPt β γ ∨ s = conj (zeroPt β γ))) ∧
        ¬ IsLogSqrtSqUnbounded
            (radialDiscrepancyOf
              (fun t => editedTheta (sEdit α β γ k₀) (Real.exp t) - Real.exp t) β γ 1)) ∧
    (∃ (F : RHTower.ExtendedSelbergClass) (s : ℂ), F.coeff.IsMultiplicative ∧ F.coeff 1 = 1 ∧
      (∀ n : ℕ, n ≠ 0 → (F.coeff n).im = 0 ∧ 1 ≤ (F.coeff n).re) ∧ s.re = β ∧ F s = 0) := by
  refine ⟨?_, ?_⟩
  · by_cases hRH : RiemannHypothesis
    · exact Or.inr ((rh_sEdit_ordinaryPrime_realizes_twoIntervalRadius hRH).2 hlo hhi hγ)
    · exact Or.inl hRH
  · obtain ⟨F, s, hm, h1, hge, hre, hFs, -⟩ :=
      (singleQuartet_realized_in_models hlo).2.2.2 hlo (by linarith)
    exact ⟨F, s, hm, h1, hge, hre, hFs⟩

/-! ### 5. Unconditional abscissa pinning and automatic `HasPositivePowerLimsup` on `ζ(s)` -/

/-- **Unconditional abscissa pinning from a bounded two-interval radius.**
If `thetaRadialDiscrepancy β γ m` (`1/2 < β < 1`, `γ ≠ 0`, `m ≥ 1`) is bounded against
`e^{t/2}(1 + t)²`, then **without assuming `HasPositivePowerLimsup`**:
1. `HasPositivePowerLimsup primeError β` holds;
2. `¬ RiemannHypothesis` holds;
3. `|θ(y) − y| ≤ L y^β` and `|ψ(y) − y| ≤ L' y^β` hold eventually;
4. `zetaZeroAbscissa = β` and `RHTower.zeroReSup = β`! -/
theorem radial_bounded_forces_abscissa_and_limsup {β γ : ℝ} {m : ℕ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (hbdd : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m)) :
    HasPositivePowerLimsup primeError β ∧
    ¬ RiemannHypothesis ∧
    zetaZeroAbscissa = β ∧
    RHTower.zeroReSup = β ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ y : ℝ in atTop, |Chebyshev.theta y - y| ≤ L * y ^ β) ∧
    (∃ L' : ℝ, 0 ≤ L' ∧ ∀ᶠ y : ℝ in atTop, |Chebyshev.psi y - y| ≤ L' * y ^ β) := by
  have hβ0 : 0 < β := by linarith
  have hpsi_bdd : ¬ IsLogSqrtSqUnbounded (radialDiscrepancyOf psiLogError β γ m) :=
    (psi_radial_bounded_iff_theta_radial_bounded hβ0.le hγ m).mpr hbdd
  rw [show thetaRadialDiscrepancy β γ m = radialDiscrepancyOf thetaLogError β γ m from rfl,
    isLogSqrtSqUnbounded_iff_not_eventually_le, not_not] at hbdd
  rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not] at hpsi_bdd
  obtain ⟨K, T₀, hK⟩ := hbdd
  obtain ⟨K_p, T_p, hK_p⟩ := hpsi_bdd
  set h := quarterPeriodStep γ
  set A := quarterPeriodScale β γ
  set C := quartetRadialCoeff β γ m
  have hh_pos : 0 < h := quarterPeriodStep_pos hγ
  have hA1 : 1 ≤ A := (one_lt_quarterPeriodScale hβ0 hγ).le
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hC_pos : 0 < C := quartetRadialCoeff_pos hγ hm
  -- `(|K| + |K_p| + 1) e^{t/2} (1 + t)² ≤ (C / 2) e^{β t}` eventually
  have hsmall : ∀ᶠ t : ℝ in atTop,
      (|K| + |K_p| + 1) * Real.exp (t / 2) * (1 + t) ^ 2 ≤ C / 2 * Real.exp (β * t) := by
    set M_k : ℝ := 4 * (|K| + |K_p| + 1)
    have hM_k : 0 < M_k := by dsimp [M_k]; positivity
    obtain ⟨L_t, hL_t⟩ := eventually_atTop.mp
      ((_root_.isLittleO_exp_mul_rpow_of_lt 2 hβ).def (div_pos (half_pos hC_pos) hM_k))
    filter_upwards [eventually_ge_atTop (max L_t 1)] with t ht
    have htL : L_t ≤ t := (le_max_left _ _).trans ht
    have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
    have he := hL_t t htL
    change ‖Real.exp ((1 / 2) * t) * t ^ (2 : ℝ)‖ ≤ (C / 2 / M_k) * ‖Real.exp (β * t)‖ at he
    simp only [Real.norm_eq_abs, Real.rpow_two, show 1 / 2 * t = t / 2 by ring, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg t)] at he
    have h1t : (1 + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
    calc (|K| + |K_p| + 1) * Real.exp (t / 2) * (1 + t) ^ 2
        ≤ (|K| + |K_p| + 1) * Real.exp (t / 2) * (4 * t ^ 2) :=
          mul_le_mul_of_nonneg_left h1t (by positivity)
      _ = M_k * (Real.exp (t / 2) * t ^ 2) := by dsimp [M_k]; ring
      _ ≤ M_k * ((C / 2 / M_k) * Real.exp (β * t)) := mul_le_mul_of_nonneg_left he hM_k.le
      _ = C / 2 * Real.exp (β * t) := by field_simp [hM_k.ne']
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hsmall
  set B₀ : ℝ := max (max T₀ T_p) (max T₁ 1)
  have hB₀_T₀ : T₀ ≤ B₀ := (le_max_left T₀ T_p).trans (le_max_left _ _)
  have hB₀_Tp : T_p ≤ B₀ := (le_max_right T₀ T_p).trans (le_max_left _ _)
  have hB₀_T₁ : T₁ ≤ B₀ := (le_max_left T₁ 1).trans (le_max_right _ _)
  have hB₀_1 : 1 ≤ B₀ := (le_max_right T₁ 1).trans (le_max_right _ _)
  -- Part 1: `HasPositivePowerLimsup primeError β` from `psiLogError` radius lower bound
  have hlimsup : HasPositivePowerLimsup primeError β := by
    set c₀ : ℝ := C / (8 * Real.exp (2 * β * h))
    refine ⟨c₀, by dsimp [c₀]; positivity, fun X₀ => ?_⟩
    set t : ℝ := max B₀ (Real.log (max X₀ 1))
    have htB : B₀ ≤ t := le_max_left _ _
    have htX : X₀ ≤ Real.exp t := by
      calc X₀ ≤ max X₀ 1 := le_max_left _ _
        _ = Real.exp (Real.log (max X₀ 1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp t := Real.exp_le_exp.mpr (le_max_right _ _)
    have hb_p := (hK_p t (hB₀_Tp.trans htB)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        ((le_abs_self K_p).trans (by linarith [abs_nonneg K] : |K_p| ≤ |K| + |K_p| + 1))
        (Real.exp_pos _).le) (sq_nonneg _))
    have hb_sm := hT₁ t (hB₀_T₁.trans htB)
    have hrad_ge : C / 2 * Real.exp (β * t) ≤ twoIntervalRadius psiLogError h A t := by
      have hl := (abs_le.mp (hb_p.trans hb_sm)).1
      unfold radialDiscrepancyOf at hl
      linarith
    have hsum3 : twoIntervalRadius psiLogError h A t ≤
        |psiLogError t| + 2 * |psiLogError (t + h)| + |psiLogError (t + 2 * h)| := by
      rw [twoIntervalRadius_eq_complex_norm hA0]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      dsimp only [logStepIncrement]
      have h1 : |psiLogError (t + h) - psiLogError t| ≤ |psiLogError (t + h)| + |psiLogError t| :=
        abs_sub _ _
      have h2 : |(psiLogError (t + h + h) - psiLogError (t + h)) / A| ≤
          |psiLogError (t + 2 * h)| + |psiLogError (t + h)| := by
        rw [abs_div, abs_of_pos hA0]
        refine (div_le_self (abs_nonneg _) hA1).trans ?_
        rw [show t + h + h = t + 2 * h by ring]; exact abs_sub _ _
      linarith
    have hmax3 : C / 8 * Real.exp (β * t) ≤ |psiLogError t| ∨
        C / 8 * Real.exp (β * t) ≤ |psiLogError (t + h)| ∨
        C / 8 * Real.exp (β * t) ≤ |psiLogError (t + 2 * h)| := by
      by_contra! hall; linarith [hrad_ge, hsum3, hall.1, hall.2.1, hall.2.2]
    have hpick : ∀ s : ℝ, t ≤ s → s ≤ t + 2 * h → C / 8 * Real.exp (β * t) ≤ |psiLogError s| →
        ∃ x : ℝ, X₀ ≤ x ∧ c₀ * x ^ β ≤ |primeError x| := by
      intro s hs1 hs2 hEs
      refine ⟨Real.exp s, htX.trans (Real.exp_le_exp.mpr hs1), ?_⟩
      have hrpow : (Real.exp s) ^ β = Real.exp (β * s) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos s), Real.log_exp]; ring
      have hexp_le : Real.exp (β * s) ≤ Real.exp (2 * β * h) * Real.exp (β * t) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [hβ0, hs2])
      rw [hrpow]
      calc c₀ * Real.exp (β * s)
          ≤ c₀ * (Real.exp (2 * β * h) * Real.exp (β * t)) :=
            mul_le_mul_of_nonneg_left hexp_le (by dsimp [c₀]; positivity)
        _ = C / 8 * Real.exp (β * t) := by
            dsimp [c₀]; field_simp [(Real.exp_pos (2 * β * h)).ne']
        _ ≤ |primeError (Real.exp s)| := hEs
    rcases hmax3 with h0 | h1 | h2
    · exact hpick t le_rfl (by linarith) h0
    · exact hpick (t + h) (by linarith) (by linarith) h1
    · exact hpick (t + 2 * h) (by linarith) le_rfl h2
  -- Part 2: `¬ RiemannHypothesis` and `β ≤ zeroReSup`, `β ≤ zetaZeroAbscissa`
  have hβ_le_sup : β ≤ RHTower.zeroReSup := by
    by_contra hlt
    exact not_hasPositivePowerLimsup_of_zeroReSup_lt (not_le.mp hlt) hlimsup
  have hnrh : ¬ RiemannHypothesis := by
    intro hRH
    have hsup_half : RHTower.zeroReSup ≤ 1 / 2 :=
      RHTower.zeroReSup_le_of_forall_re_le fun q =>
        (RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q).le
    linarith
  have hsup_le_Θ : RHTower.zeroReSup ≤ zetaZeroAbscissa := by
    refine RHTower.zeroReSup_le_of_forall_re_le fun q => ?_
    have h0 := xiZeroCopy_re_pos q
    have h1 := xiZeroCopy_re_lt_one q
    have hne1 : (q.1 : ℂ) ≠ 1 := fun he => by rw [he, Complex.one_re] at h1; exact lt_irrefl 1 h1
    have hζ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp
      (xi_eq_zero_of_mem_divisor_support q.1)
    exact re_le_zetaZeroAbscissa hζ
  have hβ_le_Θ : β ≤ zetaZeroAbscissa := hβ_le_sup.trans hsup_le_Θ
  -- Part 3: Step-`h` backward telescoping gives `|θ(y) - y| ≤ L y^β` and `|ψ(y) - y| ≤ L' y^β`
  have hinc_le : ∀ s : ℝ, B₀ ≤ s → |thetaLogError (s + h) - thetaLogError s| ≤
      (2 * C) * Real.exp (β * s) := by
    intro s hs
    have hb_s := (hK s (hB₀_T₀.trans hs)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        ((le_abs_self K).trans (by linarith [abs_nonneg K_p] : |K| ≤ |K| + |K_p| + 1))
        (Real.exp_pos _).le) (sq_nonneg _))
    have hb_sm := hT₁ s (hB₀_T₁.trans hs)
    have hrad_le : twoIntervalRadius thetaLogError h A s ≤ (2 * C) * Real.exp (β * s) := by
      have hu := (abs_le.mp (hb_s.trans hb_sm)).2
      unfold radialDiscrepancyOf at hu
      linarith [mul_pos hC_pos (Real.exp_pos (β * s))]
    have hstep_le : |thetaLogError (s + h) - thetaLogError s| ≤
        twoIntervalRadius thetaLogError h A s := by
      rw [twoIntervalRadius_eq_complex_norm hA0]
      exact Complex.abs_re_le_norm _
    exact hstep_le.trans hrad_le
  set M₀ : ℝ := Chebyshev.theta (Real.exp (B₀ + h)) + Real.exp (B₀ + h)
  have hM₀_nn : 0 ≤ M₀ := add_nonneg (Chebyshev.theta_nonneg _) (Real.exp_pos _).le
  have hbase_le : ∀ u : ℝ, B₀ ≤ u → u ≤ B₀ + h → |thetaLogError u| ≤ M₀ := by
    intro u _ hu_hi
    dsimp [thetaLogError, M₀]
    have hθ_nn : 0 ≤ Chebyshev.theta (Real.exp u) := Chebyshev.theta_nonneg _
    have hθ_hi : Chebyshev.theta (Real.exp u) ≤ Chebyshev.theta (Real.exp (B₀ + h)) :=
      Chebyshev.theta_mono (Real.exp_le_exp.mpr hu_hi)
    have hexp_hi : Real.exp u ≤ Real.exp (B₀ + h) := Real.exp_le_exp.mpr hu_hi
    rw [abs_le]
    exact ⟨by linarith [Real.exp_pos u], by linarith [Real.exp_pos u]⟩
  have hA_gt1 : 1 < A := one_lt_quarterPeriodScale hβ0 hγ
  set L₀ : ℝ := M₀ + (2 * C) / (A - 1)
  have hL₀_nn : 0 ≤ L₀ := by dsimp [L₀]; have : 0 < A - 1 := sub_pos.mpr hA_gt1; positivity
  have hθ_log_le : ∀ t : ℝ, B₀ ≤ t → |thetaLogError t| ≤ L₀ * Real.exp (β * t) := by
    intro t ht
    set n : ℕ := ⌊(t - B₀) / h⌋₊
    set u : ℝ := t - (n : ℝ) * h
    have hn_le : (n : ℝ) * h ≤ t - B₀ :=
      (le_div_iff₀ hh_pos).mp (Nat.floor_le (div_nonneg (by linarith) hh_pos.le))
    have hn_gt : t - B₀ < ((n : ℝ) + 1) * h :=
      (div_lt_iff₀ hh_pos).mp (Nat.lt_floor_add_one _)
    have hu_lo : B₀ ≤ u := by dsimp [u]; linarith
    have hu_hi : u ≤ B₀ + h := by dsimp [u]; linarith
    have ht_eq : t = u + (n : ℝ) * h := by dsimp [u]; ring
    rw [ht_eq]
    have hind : ∀ k : ℕ, |thetaLogError (u + (k : ℝ) * h)| ≤
        L₀ * Real.exp (β * (u + (k : ℝ) * h)) := by
      intro k
      induction k with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, add_zero]
        have hu0 : 0 ≤ u := by linarith
        have hexp1 : 1 ≤ Real.exp (β * u) := Real.one_le_exp (by positivity)
        have h1 : |thetaLogError u| ≤ L₀ :=
          (hbase_le u hu_lo hu_hi).trans
            (le_add_of_nonneg_right (div_nonneg (by positivity) (sub_pos.mpr hA_gt1).le))
        exact h1.trans (le_mul_of_one_le_right hL₀_nn hexp1)
      | succ k ih =>
        set s : ℝ := u + (k : ℝ) * h
        have hs_lo : B₀ ≤ s := by dsimp [s]; linarith [mul_nonneg (Nat.cast_nonneg k) hh_pos.le]
        have hnext : u + ((k + 1 : ℕ) : ℝ) * h = s + h := by dsimp [s]; push_cast; ring
        rw [hnext]
        have hexp_A : Real.exp (β * (s + h)) = A * Real.exp (β * s) := by
          dsimp [A, quarterPeriodScale]; rw [mul_add, Real.exp_add, mul_comm]
        have hstep := hinc_le s hs_lo
        have htri : |thetaLogError (s + h)| ≤
            |thetaLogError s| + |thetaLogError (s + h) - thetaLogError s| := by
          have := abs_add_le (thetaLogError s) (thetaLogError (s + h) - thetaLogError s)
          rwa [add_sub_cancel] at this
        have hcomb : L₀ + 2 * C ≤ L₀ * A := by
          have hA_sub : 0 < A - 1 := sub_pos.mpr hA_gt1
          have hid : L₀ * A - (L₀ + 2 * C) = M₀ * (A - 1) := by
            dsimp [L₀]; field_simp [hA_sub.ne']; ring
          nlinarith [mul_nonneg hM₀_nn hA_sub.le]
        rw [hexp_A]
        calc |thetaLogError (s + h)|
            ≤ L₀ * Real.exp (β * s) + (2 * C) * Real.exp (β * s) :=
              htri.trans (add_le_add ih hstep)
          _ = (L₀ + 2 * C) * Real.exp (β * s) := by ring
          _ ≤ (L₀ * A) * Real.exp (β * s) :=
              mul_le_mul_of_nonneg_right hcomb (Real.exp_pos _).le
          _ = L₀ * (A * Real.exp (β * s)) := by ring
    exact hind n
  have hθ_pow : ∀ y : ℝ, Real.exp B₀ ≤ y → |Chebyshev.theta y - y| ≤ L₀ * y ^ β := by
    intro y hy
    have hy0 : 0 < y := (Real.exp_pos B₀).trans_le hy
    have ht : B₀ ≤ Real.log y := (Real.le_log_iff_exp_le hy0).mpr hy
    have hb := hθ_log_le (Real.log y) ht
    dsimp [thetaLogError] at hb
    rw [Real.exp_log hy0, mul_comm β (Real.log y), ← Real.rpow_def_of_pos hy0] at hb
    exact hb
  set L' : ℝ := L₀ + 3 * (Real.log 4 + 4)
  have hL'_nn : 0 ≤ L' := by dsimp [L']; positivity
  have hψ_pow : ∀ y : ℝ, Real.exp B₀ ≤ y → |Chebyshev.psi y - y| ≤ L' * y ^ β := by
    intro y hy
    have hy1 : 1 ≤ y := (Real.one_le_exp (by linarith : 0 ≤ B₀)).trans hy
    have hb_θ := hθ_pow y hy
    have hb_d : |Chebyshev.psi y - Chebyshev.theta y| ≤ 3 * (Real.log 4 + 4) * y ^ β := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
      refine (GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt y).trans ?_
      rw [Real.sqrt_eq_rpow]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy1 hβ.le) (by positivity)
    have htri := abs_add_le (Chebyshev.psi y - Chebyshev.theta y) (Chebyshev.theta y - y)
    rw [sub_add_sub_cancel] at htri
    dsimp [L']; linarith
  -- Part 4: Deduce `zetaZeroAbscissa ≤ β`, hence `zetaZeroAbscissa = β = zeroReSup`
  have hΘ_le_β : zetaZeroAbscissa ≤ β := by
    by_contra hgt
    obtain ⟨ρ_z, hz, hre1, hβ_lt⟩ := RHTower.exists_zetaZero_mem_openStrip_lt_re (not_le.mp hgt)
    have hhalf_lt : 1 / 2 < ρ_z.re := hβ.trans hβ_lt
    obtain ⟨c_pk, hc_pk, hpeaks⟩ := both_prime_error_peaks_at_every_large_cutoff hhalf_lt hre1 hz
    have hgap : 0 < ρ_z.re - β := sub_pos.mpr hβ_lt
    have htend : Tendsto (fun N : ℕ => (Real.sqrt N) ^ (ρ_z.re - β)) atTop atTop := by
      have h1 := (Real.tendsto_rpow_atTop hgap).comp
        ((Real.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop)
      refine h1.congr fun N => ?_
      simp [Real.sqrt_eq_rpow]
    obtain ⟨N, hpk_N, hsqrt_ge, hrpow_gt⟩ :=
      (hpeaks.and (((Real.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop |>.congr fun k => by simp [Real.sqrt_eq_rpow]).eventually_ge_atTop
          (Real.exp B₀) |>.and (htend.eventually_gt_atTop ((L' + 1) / c_pk)))).exists
    obtain ⟨n, _, hsqrt_lt_n, hpeak_n⟩ := hpk_N 1 abs_one
    rw [one_mul] at hpeak_n
    have hn_ge : Real.exp B₀ ≤ (n : ℝ) := hsqrt_ge.trans hsqrt_lt_n.le
    have hn_pos : (0 : ℝ) < n := (Real.exp_pos B₀).trans_le hn_ge
    have hupper := hψ_pow n hn_ge
    have hlower : c_pk * (n : ℝ) ^ ρ_z.re < |Chebyshev.psi n - n| :=
      hpeak_n.trans_le (le_abs_self _)
    have hrpow_n : (L' + 1) / c_pk < (n : ℝ) ^ (ρ_z.re - β) :=
      hrpow_gt.trans_le (Real.rpow_le_rpow (Real.sqrt_nonneg _) hsqrt_lt_n.le hgap.le)
    have hmul1 := (div_lt_iff₀ hc_pk).mp hrpow_n
    have hmul2 := mul_lt_mul_of_pos_right hmul1 (Real.rpow_pos_of_pos hn_pos β)
    rw [mul_comm _ c_pk, mul_assoc, ← Real.rpow_add hn_pos, sub_add_cancel] at hmul2
    have : L' * (n : ℝ) ^ β ≤ (L' + 1) * (n : ℝ) ^ β :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hn_pos.le β)
    linarith
  have hΘ_eq : zetaZeroAbscissa = β := le_antisymm hΘ_le_β hβ_le_Θ
  have hsup_eq : RHTower.zeroReSup = β := le_antisymm (hsup_le_Θ.trans hΘ_le_β) hβ_le_sup
  exact ⟨hlimsup, hnrh, hΘ_eq, hsup_eq,
    ⟨L₀, hL₀_nn, eventually_atTop.mpr ⟨Real.exp B₀, hθ_pow⟩⟩,
    ⟨L', hL'_nn, eventually_atTop.mpr ⟨Real.exp B₀, hψ_pow⟩⟩⟩

/-- **Unconditional off-abscissa radial divergence.** Whenever `β ≠ zetaZeroAbscissa`
(`1/2 < β < 1`, `γ ≠ 0`, `m ≥ 1`), `thetaRadialDiscrepancy β γ m` is unconditionally unbounded
against `e^{t/2}(1 + t)²`. -/
theorem thetaRadial_unbounded_of_ne_zetaZeroAbscissa {β γ : ℝ} {m : ℕ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : γ ≠ 0) (hm : 1 ≤ m) (hne : β ≠ zetaZeroAbscissa) :
    IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m) := by
  by_contra hbdd
  exact hne (radial_bounded_forces_abscissa_and_limsup hβ hβ1 hγ hm hbdd).2.2.1.symm

/-- **Unconditional zero-free half-plane radial divergence (`20999 / 24000 < β < 1`).** -/
theorem thetaRadial_unbounded_of_sub_seven_eighths_lt {β γ : ℝ} {m : ℕ}
    (hhi : 20999 / 24000 < β) (hβ1 : β < 1) (hγ : γ ≠ 0) (hm : 1 ≤ m) :
    IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m) :=
  thetaRadial_unbounded_of_ne_zetaZeroAbscissa (by linarith) hβ1 hγ hm
    (ne_of_gt (lt_of_le_of_lt ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths hhi))

/-- `RiemannHypothesis` unconditionally implies `TwoIntervalRadialExclusionLaw`. -/
theorem twoIntervalRadialExclusionLaw_of_riemannHypothesis (hRH : RiemannHypothesis) :
    TwoIntervalRadialExclusionLaw := by
  intro β γ m hβ hβ1 hγ hm
  by_contra hbdd
  exact (radial_bounded_forces_abscissa_and_limsup hβ hβ1 hγ hm hbdd).2.1 hRH

/-! ### 6. Multiplicity-pinned `(2, 3, 6)` ordinary-prime stratum equivalence without limsup -/

private theorem singleQuartet_psi_radial_transfer {β ω γ : ℝ} {m : ℕ}
    (hβ : 1 / 2 < β) (hω : 0 < ω) (hγ : γ ≠ 0)
    (hq : HasSingleOffLineQuartet ((β : ℂ) + I * (ω : ℂ))) :
    ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m) ↔
      ¬ IsLogSqrtSqUnbounded
          (radialDiscrepancyOf (singleWaveLog β ω (quartetCopyMult ((β : ℂ) + I * (ω : ℂ))))
            β γ m) := by
  rw [← psi_radial_bounded_iff_theta_radial_bounded (by linarith : 0 ≤ β) hγ m]
  set ρ' : ℂ := (β : ℂ) + I * (ω : ℂ)
  set m' : ℕ := quartetCopyMult ρ'
  obtain ⟨K_w, hK_w⟩ := (hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hq.1 hq.2.1).mp hq
  set h := quarterPeriodStep γ
  have hh : 0 < h := quarterPeriodStep_pos hγ
  have hA1 : 1 ≤ quarterPeriodScale β γ := (one_lt_quarterPeriodScale (by linarith) hγ).le
  have hA0 : 0 < quarterPeriodScale β γ := zero_lt_one.trans_le hA1
  set D_w : ℝ := 4 * |K_w| * Real.exp h * (1 + 2 * h) ^ 2
  have hD_w : 0 ≤ D_w := by dsimp [D_w]; positivity
  have hdiff : ∀ t : ℝ, 3 ≤ t →
      |radialDiscrepancyOf psiLogError β γ m t -
          radialDiscrepancyOf (singleWaveLog β ω m') β γ m t| ≤
        D_w * Real.exp (t / 2) * (1 + t) ^ 2 := by
    intro t ht
    have hsub : radialDiscrepancyOf psiLogError β γ m t -
        radialDiscrepancyOf (singleWaveLog β ω m') β γ m t =
        twoIntervalRadius psiLogError h (quarterPeriodScale β γ) t -
          twoIntervalRadius (singleWaveLog β ω m') h (quarterPeriodScale β γ) t := by
      unfold radialDiscrepancyOf; ring
    rw [hsub, twoIntervalRadius_eq_complex_norm hA0, twoIntervalRadius_eq_complex_norm hA0]
    have hpt : ∀ s : ℝ, t ≤ s → s ≤ t + 2 * h →
        |psiLogError s - singleWaveLog β ω m' s| ≤
          |K_w| * Real.exp ((t + 2 * h) / 2) * (1 + (t + 2 * h)) ^ 2 := by
      intro s hs1 hs2
      have hx16 : 16 ≤ Real.exp s := by
        have h3 : (16 : ℝ) ≤ Real.exp 3 := by
          have := Real.exp_one_gt_d9
          calc (16 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
            _ ≤ Real.exp 1 ^ 3 := by gcongr
            _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
        exact h3.trans (Real.exp_le_exp.mpr (ht.trans hs1))
      have hb := hK_w (Real.exp s) hx16
      have hcp : (Real.exp s : ℂ) ^ ρ' = Complex.exp (ρ' * (s : ℂ)) :=
        cpow_exp_eq s ρ'
      rw [hcp, ← Real.exp_half, Real.log_exp] at hb
      have hid : psiLogError s - singleWaveLog β ω m' s =
          Chebyshev.psi (Real.exp s) - Real.exp s +
            2 * (m' : ℝ) * (Complex.exp (ρ' * (s : ℂ)) / ρ').re := by
        unfold psiLogError singleWaveLog; dsimp [ρ']; ring
      rw [hid]
      refine hb.trans ?_
      have hs0 : 0 ≤ s := by linarith
      have hexp_le : Real.exp (s / 2) ≤ Real.exp ((t + 2 * h) / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have hsq_le : s ^ 2 ≤ (1 + (t + 2 * h)) ^ 2 := by nlinarith
      calc K_w * Real.exp (s / 2) * s ^ 2
          ≤ |K_w| * Real.exp (s / 2) * s ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self K_w) (Real.exp_pos _).le) (sq_nonneg _)
        _ ≤ |K_w| * Real.exp ((t + 2 * h) / 2) * (1 + (t + 2 * h)) ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hexp_le (abs_nonneg _)) hsq_le (sq_nonneg _)
              (by positivity)
    set B_s : ℝ := |K_w| * Real.exp ((t + 2 * h) / 2) * (1 + (t + 2 * h)) ^ 2
    have hb0 := hpt t le_rfl (by linarith)
    have hb1 := hpt (t + h) (by linarith) (by linarith)
    have hb2 := hpt (t + 2 * h) (by linarith) le_rfl
    set v1 : ℂ := ⟨logStepIncrement psiLogError t h,
      logStepIncrement psiLogError (t + h) h / quarterPeriodScale β γ⟩
    set v2 : ℂ := ⟨logStepIncrement (singleWaveLog β ω m') t h,
      logStepIncrement (singleWaveLog β ω m') (t + h) h / quarterPeriodScale β γ⟩
    have hre : |(v1 - v2).re| ≤ 2 * B_s := by
      change |(psiLogError (t + h) - psiLogError t) -
        (singleWaveLog β ω m' (t + h) - singleWaveLog β ω m' t)| ≤ 2 * B_s
      rw [show (psiLogError (t + h) - psiLogError t) -
          (singleWaveLog β ω m' (t + h) - singleWaveLog β ω m' t) =
        (psiLogError (t + h) - singleWaveLog β ω m' (t + h)) -
          (psiLogError t - singleWaveLog β ω m' t) by ring]
      exact (abs_sub _ _).trans ((add_le_add hb1 hb0).trans_eq (two_mul _).symm)
    have him : |(v1 - v2).im| ≤ 2 * B_s := by
      change |(psiLogError (t + h + h) - psiLogError (t + h)) / quarterPeriodScale β γ -
        (singleWaveLog β ω m' (t + h + h) - singleWaveLog β ω m' (t + h)) /
          quarterPeriodScale β γ| ≤ 2 * B_s
      rw [← sub_div, show t + h + h = t + 2 * h by ring,
        show (psiLogError (t + 2 * h) - psiLogError (t + h)) -
            (singleWaveLog β ω m' (t + 2 * h) - singleWaveLog β ω m' (t + h)) =
          (psiLogError (t + 2 * h) - singleWaveLog β ω m' (t + 2 * h)) -
            (psiLogError (t + h) - singleWaveLog β ω m' (t + h)) by ring,
        abs_div, abs_of_pos hA0]
      exact (div_le_self (abs_nonneg _) hA1).trans
        ((abs_sub _ _).trans ((add_le_add hb2 hb1).trans_eq (two_mul _).symm))
    have h4B : |‖v1‖ - ‖v2‖| ≤ 4 * B_s :=
      (abs_norm_sub_norm_le v1 v2).trans
        ((Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add hre him).trans_eq (by ring)))
    refine h4B.trans ?_
    dsimp [B_s, D_w]
    have hexp_sp : Real.exp ((t + 2 * h) / 2) = Real.exp h * Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h1t : (1 + (t + 2 * h)) ^ 2 ≤ (1 + 2 * h) ^ 2 * (1 + t) ^ 2 := by
      have : 1 + (t + 2 * h) ≤ (1 + 2 * h) * (1 + t) := by nlinarith [ht, hh]
      exact (pow_le_pow_left₀ (by linarith) this 2).trans_eq (mul_pow _ _ 2)
    rw [hexp_sp]
    calc 4 * (|K_w| * (Real.exp h * Real.exp (t / 2)) * (1 + (t + 2 * h)) ^ 2)
        ≤ 4 * (|K_w| * (Real.exp h * Real.exp (t / 2)) * ((1 + 2 * h) ^ 2 * (1 + t) ^ 2)) := by
          gcongr
      _ = 4 * |K_w| * Real.exp h * (1 + 2 * h) ^ 2 * Real.exp (t / 2) * (1 + t) ^ 2 := by ring
  simp only [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not]
  constructor <;> rintro ⟨K, T₀, hK⟩ <;> refine ⟨|K| + D_w, max T₀ 3, fun t ht => ?_⟩
  · have htT : T₀ ≤ t := (le_max_left _ _).trans ht
    have ht3 : 3 ≤ t := (le_max_right _ _).trans ht
    have h1 := (hK t htT).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le) (sq_nonneg _))
    have h2 := hdiff t ht3
    have htri := abs_sub (radialDiscrepancyOf psiLogError β γ m t)
      (radialDiscrepancyOf psiLogError β γ m t -
        radialDiscrepancyOf (singleWaveLog β ω m') β γ m t)
    rw [sub_sub_cancel] at htri
    linarith
  · have htT : T₀ ≤ t := (le_max_left _ _).trans ht
    have ht3 : 3 ≤ t := (le_max_right _ _).trans ht
    have h1 := (hK t htT).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le) (sq_nonneg _))
    have h2 := hdiff t ht3
    have htri := abs_add_le (radialDiscrepancyOf (singleWaveLog β ω m') β γ m t)
      (radialDiscrepancyOf psiLogError β γ m t -
        radialDiscrepancyOf (singleWaveLog β ω m') β γ m t)
    rw [add_sub_cancel] at htri
    linarith

/-- **Multiplicity-pinned `(2, 3, 6)` ordinary-prime stratum equivalence without `HasPositivePowerLimsup`.**
For `1/2 < β < 1`, `0 < γ`, and `1 ≤ m`, boundedness of `thetaRadialDiscrepancy β γ m` together
with boundedness of `ordinaryThetaDilationResidual a β γ` at `a ∈ {2, 3, 6}` holds if and only if
`HasSingleOffLineQuartet (β + iγ)` holds with exact divisor multiplicity `quartetCopyMult = m`. -/
theorem radial_and_ordinary_236_iff_singleQuartet_with_mult {β γ : ℝ} {m : ℕ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hm : 1 ≤ m) :
    (¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 2 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 3 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 6 β γ)) ↔
    (HasSingleOffLineQuartet ((β : ℂ) + I * (γ : ℂ)) ∧
      quartetCopyMult ((β : ℂ) + I * (γ : ℂ)) = m) := by
  constructor
  · rintro ⟨hrad, h2, h3, h6⟩
    have hnrh := (radial_bounded_forces_abscissa_and_limsup hβ hβ1 hγ.ne' hm hrad).2.1
    have hrh_or_q :=
      (ordinary_prime_recurrences_iff_rh_or_singleQuartet hβ hβ1 hγ).mp ⟨h2, h3, h6⟩
    have hq : HasSingleOffLineQuartet ((β : ℂ) + I * (γ : ℂ)) := hrh_or_q.resolve_left hnrh
    refine ⟨hq, ?_⟩
    have hsw := (singleQuartet_psi_radial_transfer hβ hγ hγ.ne' hq).mp hrad
    obtain ⟨k, hω_eq, hpyth⟩ :=
      (not_isLogSqrtSqUnbounded_singleWaveLog_iff_alias hβ hγ.ne' hγ hm hq.quartetCopyMult_pos).mp
        hsw
    rw [abs_of_pos hγ] at hω_eq
    have hk0 : (k : ℝ) = 0 := by nlinarith [hω_eq, hγ]
    have hden_pos : 0 < β ^ 2 + γ ^ 2 := by positivity
    have hm_sq : (quartetCopyMult ((β : ℂ) + I * (γ : ℂ)) : ℝ) ^ 2 = (m : ℝ) ^ 2 :=
      mul_right_cancel₀ hden_pos.ne' hpyth
    have hm_eqR : (quartetCopyMult ((β : ℂ) + I * (γ : ℂ)) : ℝ) = (m : ℝ) := by
      nlinarith [hm_sq, show (0 : ℝ) < m by exact_mod_cast hm,
        show (0 : ℝ) < quartetCopyMult ((β : ℂ) + I * (γ : ℂ)) by
          exact_mod_cast hq.quartetCopyMult_pos]
    exact Nat.cast_injective hm_eqR
  · rintro ⟨hq, rfl⟩
    have h236 := (ordinary_prime_recurrences_iff_rh_or_singleQuartet hβ hβ1 hγ).mpr (Or.inr hq)
    have hre : ((β : ℂ) + I * (γ : ℂ)).re = β := by simp
    have him : ((β : ℂ) + I * (γ : ℂ)).im = γ := by simp
    have hrad := not_isLogSqrtSqUnbounded_of_singleQuartet hq
    rw [hre, him] at hrad
    exact ⟨hrad, h236⟩

/-! ### 7. Exact `FiniteOffLine` multi-quartet breaking and odd-harmonic Pythagorean classification -/

/-- Complex two-interval increment vector `⟨Δ_h g(t), Δ_h g(t + h) / A⟩`. -/
private def twoIntervalVec (g : ℝ → ℝ) (h A t : ℝ) : ℂ :=
  ⟨logStepIncrement g t h, logStepIncrement g (t + h) h / A⟩

private theorem twoIntervalVec_add (g₁ g₂ : ℝ → ℝ) (h A t : ℝ) :
    twoIntervalVec (fun s => g₁ s + g₂ s) h A t =
      twoIntervalVec g₁ h A t + twoIntervalVec g₂ h A t := by
  apply Complex.ext
  · simp [twoIntervalVec, logStepIncrement]; ring
  · simp [twoIntervalVec, logStepIncrement]; ring

private theorem layer_twoIntervalVec_eq (U : Finset XiZeroCopy) {σ β : ℝ} (hσ : 1 / 2 < σ)
    (hU_re : ∀ q ∈ U, (q.1 : ℂ).re = σ) {h : ℝ} (hh : 0 < h) :
    let A := Real.exp (β * h)
    let r := Real.exp ((σ - β) * h)
    let Ω : Finset ℝ := U.image (fun q => |(q.1 : ℂ).im|)
    let c : ℝ → ℂ := fun ω =>
      -(((U.filter (fun q => |(q.1 : ℂ).im| = ω)).card : ℝ) : ℂ) *
        (Complex.exp ((((σ : ℂ) + I * (ω : ℂ)) * (h : ℂ))) - 1) /
        ((σ : ℂ) + I * (ω : ℂ))
    let f : ℝ → ℝ := fun s => ∑ ω ∈ Ω, (c ω * expChar ω s).re
    let W_U : ℝ → ℝ := fun s => -(∑ q ∈ U, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re)
    (∀ ω ∈ Ω, 0 < ω) ∧
    (∀ ω ∈ Ω, c ω ≠ 0) ∧
    (∀ t : ℝ, twoIntervalVec W_U h A t =
      (Real.exp (σ * t) : ℂ) * ((f t : ℂ) + I * ((r * f (t + h) : ℝ) : ℂ))) := by
  classical
  intro A r Ω c f W_U
  have hω_pos : ∀ ω ∈ Ω, 0 < ω := by
    intro ω hω
    obtain ⟨q, hqU, rfl⟩ := Finset.mem_image.mp hω
    have hre_q := hU_re q hqU
    have h0 := xiZeroCopy_re_pos q
    have h1 := xiZeroCopy_re_lt_one q
    have hne1 : (q.1 : ℂ) ≠ 1 := fun he => by rw [he, Complex.one_re] at h1; exact lt_irrefl 1 h1
    have hζ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp
      (xi_eq_zero_of_mem_divisor_support q.1)
    have h67 := sixtySeven_lt_abs_im_of_offLine_zeta_zero hζ h0 h1 (by linarith)
    linarith
  have hc_ne : ∀ ω ∈ Ω, c ω ≠ 0 := by
    intro ω hω
    obtain ⟨q, hqU, rfl⟩ := Finset.mem_image.mp hω
    have hcard_pos : 0 < (U.filter (fun q' => |(q'.1 : ℂ).im| = |(q.1 : ℂ).im|)).card :=
      Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqU, rfl⟩⟩
    have hm_ne : -((((U.filter (fun q' => |(q'.1 : ℂ).im| = |(q.1 : ℂ).im|)).card : ℝ) : ℂ)) ≠ 0 :=
      neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (by exact_mod_cast hcard_pos.ne'))
    have hexp_ne : Complex.exp ((((σ : ℂ) + I * ((|(q.1 : ℂ).im| : ℝ) : ℂ)) * (h : ℂ))) - 1 ≠ 0 := by
      intro he
      have hn1 : ‖Complex.exp ((((σ : ℂ) + I * ((|(q.1 : ℂ).im| : ℝ) : ℂ)) * (h : ℂ)))‖ = 1 := by
        rw [sub_eq_zero.mp he, norm_one]
      have hn2 : ‖Complex.exp ((((σ : ℂ) + I * ((|(q.1 : ℂ).im| : ℝ) : ℂ)) * (h : ℂ)))‖ =
          Real.exp (σ * h) := by
        rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
      have hgt1 : 1 < Real.exp (σ * h) := Real.one_lt_exp_iff.mpr (by nlinarith)
      linarith
    have hden_ne : ((σ : ℂ) + I * ((|(q.1 : ℂ).im| : ℝ) : ℂ)) ≠ 0 := fun he => by
      have := congrArg Complex.re he; simp at this; linarith
    exact div_ne_zero (mul_ne_zero hm_ne hexp_ne) hden_ne
  -- Group `W_U s` by `ω = |(q.1 : ℂ).im|`
  have hW_fib : ∀ s : ℝ, W_U s =
      ∑ ω ∈ Ω, -(((U.filter (fun q => |(q.1 : ℂ).im| = ω)).card : ℝ) *
        (Complex.exp ((((σ : ℂ) + I * (ω : ℂ)) * (s : ℂ))) /
          ((σ : ℂ) + I * (ω : ℂ))).re) := by
    intro s
    dsimp [W_U, Ω]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_fiberwise_of_maps_to (s := U)
      (t := U.image (fun q => |(q.1 : ℂ).im|)) (g := fun q => |(q.1 : ℂ).im|)
      (fun q hq => Finset.mem_image_of_mem _ hq)]
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hq_same : ∀ q ∈ U.filter (fun q => |(q.1 : ℂ).im| = ω),
        -(Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re =
          -(Complex.exp ((((σ : ℂ) + I * (ω : ℂ)) * (s : ℂ))) /
            ((σ : ℂ) + I * (ω : ℂ))).re := by
      intro q hq
      obtain ⟨hqU, him_eq⟩ := Finset.mem_filter.mp hq
      have hre_eq := hU_re q hqU
      congr 1
      rcases eq_or_eq_neg_of_abs_eq him_eq with hp | hn
      · have hq_eq : (q.1 : ℂ) = (σ : ℂ) + I * (ω : ℂ) := by
          apply Complex.ext <;> simp [hre_eq, hp]
        rw [hq_eq]
      · have hq_eq : (q.1 : ℂ) = conj ((σ : ℂ) + I * (ω : ℂ)) := by
          apply Complex.ext <;> simp [hre_eq, hn]
        rw [hq_eq]
        have hconj : Complex.exp (conj ((σ : ℂ) + I * (ω : ℂ)) * (s : ℂ)) /
            conj ((σ : ℂ) + I * (ω : ℂ)) =
            conj (Complex.exp ((((σ : ℂ) + I * (ω : ℂ)) * (s : ℂ))) /
              ((σ : ℂ) + I * (ω : ℂ))) := by
          rw [map_div₀, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
        rw [hconj, Complex.conj_re]
    rw [Finset.sum_congr rfl hq_same, Finset.sum_const, nsmul_eq_mul, mul_neg]
  have hinc : ∀ s : ℝ, logStepIncrement W_U s h = Real.exp (σ * s) * f s := by
    intro s
    unfold logStepIncrement
    rw [hW_fib (s + h), hW_fib s, ← Finset.sum_sub_distrib]
    dsimp [f]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    set ρ_ω : ℂ := (σ : ℂ) + I * (ω : ℂ)
    set m_ω : ℝ := ((U.filter (fun q => |(q.1 : ℂ).im| = ω)).card : ℝ)
    have h1 : Complex.exp (ρ_ω * ((s + h : ℝ) : ℂ)) =
        Complex.exp (ρ_ω * (s : ℂ)) * Complex.exp (ρ_ω * (h : ℂ)) := by
      rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    have h2 : (-((m_ω : ℂ) * (Complex.exp (ρ_ω * ((s + h : ℝ) : ℂ)) / ρ_ω)) -
        -((m_ω : ℂ) * (Complex.exp (ρ_ω * (s : ℂ)) / ρ_ω))) =
        c ω * Complex.exp (ρ_ω * (s : ℂ)) := by
      dsimp [c, ρ_ω, m_ω]; rw [h1]; ring
    have hsp : Complex.exp (ρ_ω * (s : ℂ)) = (Real.exp (σ * s) : ℂ) * expChar ω s := by
      dsimp [ρ_ω, expChar]
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
    have hre := congrArg Complex.re h2
    simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofReal_mul] at hre
    rw [hre, hsp, show c ω * ((Real.exp (σ * s) : ℂ) * expChar ω s) =
      (Real.exp (σ * s) : ℂ) * (c ω * expChar ω s) by ring, Complex.re_ofReal_mul]
  refine ⟨hω_pos, hc_ne, fun t => ?_⟩
  apply Complex.ext
  · simp [twoIntervalVec, hinc t]
    rw [← Complex.ofReal_mul, Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    ring
  · simp only [twoIntervalVec, hinc (t + h), Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, one_mul, zero_add]
    dsimp [A, r]
    have hexp_eq : Real.exp (σ * (t + h)) * f (t + h) / Real.exp (β * h) =
        Real.exp (σ * t) * (Real.exp ((σ - β) * h) * f (t + h)) := by
      rw [div_eq_iff (Real.exp_pos _).ne']
      have : Real.exp (σ * t) * Real.exp ((σ - β) * h) * Real.exp (β * h) =
          Real.exp (σ * (t + h)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      linear_combination f (t + h) * this.symm
    rw [hexp_eq]
    ring

private theorem bound_layer_twoIntervalVec (V : Finset XiZeroCopy) {h A σ₀ : ℝ}
    (hh : 0 ≤ h) (hA1 : 1 ≤ A) (hσ₀ : 0 ≤ σ₀) (hV_le : ∀ q ∈ V, (q.1 : ℂ).re ≤ σ₀) :
    ∃ M_V : ℝ, 0 ≤ M_V ∧ ∀ t : ℝ, 0 ≤ t →
      ‖twoIntervalVec (fun s => -(∑ q ∈ V, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re))
        h A t‖ ≤ M_V * Real.exp (σ₀ * t) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  set K_V : ℝ := ∑ q ∈ V, ‖(q.1 : ℂ)‖⁻¹
  have hK_V : 0 ≤ K_V := Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (norm_nonneg _)
  refine ⟨4 * K_V * Real.exp (2 * σ₀ * h),
    mul_nonneg (mul_nonneg (by norm_num) hK_V) (Real.exp_pos _).le, fun t ht => ?_⟩
  let W_V (s : ℝ) := -(∑ q ∈ V, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re)
  have hpt_V : ∀ s : ℝ, 0 ≤ s → s ≤ t + 2 * h →
      |W_V s| ≤ K_V * Real.exp (2 * σ₀ * h) * Real.exp (σ₀ * t) := by
    intro s hs1 hs2
    dsimp [W_V]; rw [abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ q ∈ V, |(Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re|
        ≤ ∑ q ∈ V, ‖(q.1 : ℂ)‖⁻¹ * (Real.exp (2 * σ₀ * h) * Real.exp (σ₀ * t)) := by
          refine Finset.sum_le_sum fun q hq => ?_
          refine ((Complex.abs_re_le_norm _).trans_eq (norm_div _ _)).trans ?_
          rw [Complex.norm_exp, div_eq_inv_mul,
            show ((q.1 : ℂ) * (s : ℂ)).re = (q.1 : ℂ).re * s by simp [Complex.mul_re]]
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg _))
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by nlinarith [hV_le q hq, hs1, hs2])
      _ = K_V * Real.exp (2 * σ₀ * h) * Real.exp (σ₀ * t) := by
          simp only [K_V, Finset.sum_mul, mul_assoc]
  have hb0 := hpt_V t ht (by linarith)
  have hb1 := hpt_V (t + h) (by linarith) (by linarith)
  have hb2 := hpt_V (t + 2 * h) (by linarith) le_rfl
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : |(twoIntervalVec W_V h A t).re| ≤
      2 * (K_V * Real.exp (2 * σ₀ * h) * Real.exp (σ₀ * t)) := by
    dsimp [twoIntervalVec, logStepIncrement]
    exact (abs_sub _ _).trans ((add_le_add hb1 hb0).trans_eq (two_mul _).symm)
  have him : |(twoIntervalVec W_V h A t).im| ≤
      2 * (K_V * Real.exp (2 * σ₀ * h) * Real.exp (σ₀ * t)) := by
    dsimp [twoIntervalVec, logStepIncrement]
    rw [abs_div, abs_of_pos hA0, show t + h + h = t + 2 * h by ring]
    exact (div_le_self (abs_nonneg _) hA1).trans
      ((abs_sub _ _).trans ((add_le_add hb2 hb1).trans_eq (two_mul _).symm))
  linarith

private theorem finite_right_layer_collapse (S_right : Finset XiZeroCopy)
    {β γ C K_v T_rad : ℝ} (hβ : 1 / 2 < β) (hγ : 0 < γ) (hC_pos : 0 < C) (hK_v : 0 ≤ K_v)
    (hSr_half : ∀ q ∈ S_right, 1 / 2 < (q.1 : ℂ).re)
    (hre_le_β : ∀ q ∈ S_right, (q.1 : ℂ).re ≤ β)
    (hStop_ne : (letI := Classical.decPred (fun q : XiZeroCopy => (q.1 : ℂ).re = β);
      (S_right.filter (fun q => (q.1 : ℂ).re = β)).Nonempty))
    (hv_rad : ∀ t : ℝ, max T_rad 3 ≤ t →
      |‖twoIntervalVec
          (fun s => -(∑ q ∈ S_right, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re))
          (quarterPeriodStep γ) (quarterPeriodScale β γ) t‖ -
        C * Real.exp (β * t)| ≤ K_v * Real.exp (t / 2) * (1 + t) ^ 2) :
    ∃ k : ℕ, ∀ q ∈ S_right, (q.1 : ℂ).re = β ∧ |(q.1 : ℂ).im| = (2 * (k : ℝ) + 1) * γ := by
  classical
  set h := quarterPeriodStep γ
  set A := quarterPeriodScale β γ
  have hh_pos : 0 < h := quarterPeriodStep_pos hγ.ne'
  have hA1 : 1 ≤ A := (one_lt_quarterPeriodScale (by linarith) hγ.ne').le
  let W_all : ℝ → ℝ := fun s => -(∑ q ∈ S_right, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re)
  set S_top : Finset XiZeroCopy := S_right.filter (fun q => (q.1 : ℂ).re = β)
  set S_sub : Finset XiZeroCopy := S_right.filter (fun q => (q.1 : ℂ).re ≠ β)
  have hStop_ne' : S_top.Nonempty := by convert hStop_ne
  let W_top (s : ℝ) := -(∑ q ∈ S_top, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re)
  let W_sub (s : ℝ) := -(∑ q ∈ S_sub, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re)
  have hW_split : W_all = fun s => W_top s + W_sub s := by
    funext s
    dsimp [W_all, W_top, W_sub, S_top, S_sub]
    rw [← Finset.sum_filter_add_sum_filter_not S_right (fun q => (q.1 : ℂ).re = β)]
    ring
  have htop_info := layer_twoIntervalVec_eq S_top (β := β) hβ
    (fun q hq => (Finset.mem_filter.mp hq).2) hh_pos
  set Ω_top : Finset ℝ := S_top.image (fun q => |(q.1 : ℂ).im|)
  let c_top : ℝ → ℂ := fun ω =>
    -(((S_top.filter (fun q => |(q.1 : ℂ).im| = ω)).card : ℝ) : ℂ) *
      (Complex.exp ((((β : ℂ) + I * (ω : ℂ)) * (h : ℂ))) - 1) /
      ((β : ℂ) + I * (ω : ℂ))
  let f_top : ℝ → ℝ := fun s => ∑ ω ∈ Ω_top, (c_top ω * expChar ω s).re
  obtain ⟨hΩ_top_pos, hc_top_ne, hv_top_eq⟩ := htop_info
  have hr_top_eq : ∀ s : ℝ,
      twoIntervalVec W_top h A s =
        (Real.exp (β * s) : ℂ) * ((f_top s : ℂ) + I * (f_top (s + h) : ℂ)) := by
    intro s
    have he := hv_top_eq s
    simpa [A, quarterPeriodScale, sub_self, zero_mul, Real.exp_zero, one_mul] using he
  have hsub_exp : ∃ σ_sub : ℝ, 1 / 2 ≤ σ_sub ∧ σ_sub < β ∧
      ∀ q ∈ S_sub, (q.1 : ℂ).re ≤ σ_sub := by
    rcases S_sub.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1 / 2, le_rfl, hβ, fun q hq => by rw [hemp] at hq; exact (Finset.notMem_empty q hq).elim⟩
    · set β₂ := (S_sub.image (fun q => (q.1 : ℂ).re)).max' (hne.image _)
      obtain ⟨q₂, hq₂, hq₂_re⟩ := Finset.mem_image.mp (Finset.max'_mem _ (hne.image _))
      obtain ⟨hq₂_Sr, hq₂_ne⟩ := Finset.mem_filter.mp hq₂
      have hgt_half : 1 / 2 < β₂ := hq₂_re ▸ hSr_half q₂ hq₂_Sr
      have hlt_β : β₂ < β := lt_of_le_of_ne (hq₂_re ▸ hre_le_β q₂ hq₂_Sr) (hq₂_re ▸ hq₂_ne)
      exact ⟨β₂, hgt_half.le, hlt_β,
        fun q hq => Finset.le_max' _ _ (Finset.mem_image_of_mem _ hq)⟩
  obtain ⟨σ_sub, hσ_sub_lo, hσ_sub_lt, hS_sub_le⟩ := hsub_exp
  obtain ⟨M_sub, _, hv_sub_le⟩ := bound_layer_twoIntervalVec S_sub hh_pos.le hA1
    (by linarith) hS_sub_le
  have htop_norm_tendsto : Tendsto
      (fun t : ℝ => f_top t ^ 2 + f_top (t + h) ^ 2 - C ^ 2) atTop (𝓝 0) := by
    have hdiff_c : Tendsto
        (fun t : ℝ => ‖(f_top t : ℂ) + I * (f_top (t + h) : ℂ)‖ - C) atTop (𝓝 0) := by
      have ht1 : Tendsto (fun t : ℝ => 4 * K_v * (t ^ (2 : ℝ) * Real.exp (-(β - 1 / 2) * t)))
          atTop (𝓝 0) := by
        simpa using (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (β - 1 / 2)
          (by linarith)).const_mul (4 * K_v)
      have ht2 : Tendsto (fun t : ℝ => M_sub * (t ^ (0 : ℝ) * Real.exp (-(β - σ_sub) * t)))
          atTop (𝓝 0) := by
        simpa using (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (β - σ_sub)
          (sub_pos.mpr hσ_sub_lt)).const_mul M_sub
      have ht_sum := ht1.add ht2
      rw [add_zero] at ht_sum
      refine squeeze_zero_norm' ?_ ht_sum
      filter_upwards [eventually_ge_atTop (max T_rad 3)] with t ht
      have ht0 : 0 ≤ t := by linarith [le_max_right T_rad 3]
      have ht1_le : 1 ≤ t := by linarith [le_max_right T_rad 3]
      rw [Real.norm_eq_abs, Real.rpow_two, Real.rpow_zero, one_mul]
      have hv_split : twoIntervalVec W_all h A t =
          twoIntervalVec W_top h A t + twoIntervalVec W_sub h A t := by
        rw [hW_split, twoIntervalVec_add]
      have htop_n : ‖twoIntervalVec W_top h A t‖ =
          Real.exp (β * t) * ‖(f_top t : ℂ) + I * (f_top (t + h) : ℂ)‖ := by
        rw [hr_top_eq t, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      have htri1 : |‖twoIntervalVec W_top h A t‖ - C * Real.exp (β * t)| ≤
          ‖twoIntervalVec W_sub h A t‖ +
            |‖twoIntervalVec W_all h A t‖ - C * Real.exp (β * t)| := by
        have hns : |‖twoIntervalVec W_top h A t‖ - ‖twoIntervalVec W_all h A t‖| ≤
            ‖twoIntervalVec W_sub h A t‖ := by
          rw [hv_split, abs_sub_comm]
          exact (abs_norm_sub_norm_le _ _).trans_eq (by rw [add_sub_cancel_left])
        have ht_add := abs_add_le (‖twoIntervalVec W_top h A t‖ - ‖twoIntervalVec W_all h A t‖)
          (‖twoIntervalVec W_all h A t‖ - C * Real.exp (β * t))
        rw [sub_add_sub_cancel] at ht_add
        exact ht_add.trans (add_le_add hns le_rfl)
      rw [htop_n, show Real.exp (β * t) * ‖(f_top t : ℂ) + I * (f_top (t + h) : ℂ)‖ -
          C * Real.exp (β * t) =
        Real.exp (β * t) * (‖(f_top t : ℂ) + I * (f_top (t + h) : ℂ)‖ - C) by ring,
        abs_mul, abs_of_pos (Real.exp_pos _)] at htri1
      have hmul := mul_le_mul_of_nonneg_right htri1 (Real.exp_pos (-(β * t))).le
      rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul, add_mul] at hmul
      refine hmul.trans (add_le_add_comm ?_ ?_)
      · have hb_v := hv_rad t ht
        have h1t : (1 + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
        calc |‖twoIntervalVec W_all h A t‖ - C * Real.exp (β * t)| * Real.exp (-(β * t))
            ≤ (K_v * Real.exp (t / 2) * (4 * t ^ 2)) * Real.exp (-(β * t)) :=
              mul_le_mul_of_nonneg_right
                ((hb_v).trans (mul_le_mul_of_nonneg_left h1t
                  (mul_nonneg hK_v (Real.exp_pos _).le)))
                (Real.exp_pos _).le
          _ = 4 * K_v * (t ^ 2 * (Real.exp (t / 2) * Real.exp (-(β * t)))) := by ring
          _ = 4 * K_v * (t ^ 2 * Real.exp (-(β - 1 / 2) * t)) := by
              rw [← Real.exp_add]; congr 3; ring
      · calc ‖twoIntervalVec W_sub h A t‖ * Real.exp (-(β * t))
            ≤ (M_sub * Real.exp (σ_sub * t)) * Real.exp (-(β * t)) :=
              mul_le_mul_of_nonneg_right (hv_sub_le t ht0) (Real.exp_pos _).le
          _ = M_sub * Real.exp (-(β - σ_sub) * t) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have hsq_lim := ((hdiff_c.add_const C).pow 2).sub_const (C ^ 2)
    rw [zero_add, sub_self] at hsq_lim
    refine hsq_lim.congr fun t => ?_
    have hnorm_sq : ‖(f_top t : ℂ) + I * (f_top (t + h) : ℂ)‖ ^ 2 =
        f_top t ^ 2 + f_top (t + h) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [sq]
    rw [sub_add_cancel, hnorm_sq]
  have hΩ_ne : Ω_top.Nonempty := hStop_ne'.image _
  have hΩ_card1 : Ω_top.card = 1 := by
    by_contra hne1
    have hpos_card : 0 < Ω_top.card := Finset.card_pos.mpr hΩ_ne
    have hge2 : 2 ≤ Ω_top.card := by omega
    exact multiFrequency_trigPoly_not_const_twoInterval Ω_top hΩ_top_pos hge2 c_top hc_top_ne
      h (C ^ 2) htop_norm_tendsto
  obtain ⟨ω₀, hΩ_eq⟩ := Finset.card_eq_one.mp hΩ_card1
  have hω₀_mem : ω₀ ∈ Ω_top := hΩ_eq ▸ Finset.mem_singleton_self ω₀
  have hω₀_pos : 0 < ω₀ := hΩ_top_pos ω₀ hω₀_mem
  have hf_top_single : ∀ s : ℝ, f_top s = (c_top ω₀ * expChar ω₀ s).re := by
    intro s; dsimp [f_top]; rw [hΩ_eq, Finset.sum_singleton]
  have hshift_ω₀ : ∀ t : ℝ,
      f_top (t + h) = (Complex.exp (((ω₀ * h : ℝ) : ℂ) * I) * (c_top ω₀ * expChar ω₀ t)).re := by
    intro t
    rw [hf_top_single, show expChar ω₀ (t + h) =
      Complex.exp (((ω₀ * h : ℝ) : ℂ) * I) * expChar ω₀ t by
        simp only [expChar, ← Complex.exp_add]; congr 1; push_cast; ring]
    congr 1; ring
  have htop_alias : ∃ k : ℕ, ω₀ = (2 * (k : ℝ) + 1) * γ ∧ ‖c_top ω₀‖ = C := by
    set w₂ : ℂ := ((Real.cos (ω₀ * h) : ℂ) / 2) *
      Complex.exp (((ω₀ * h : ℝ) : ℂ) * I) * (c_top ω₀) ^ 2
    let cf3 : Fin 3 → ℂ
      | 0 => ((‖c_top ω₀‖ ^ 2 - C ^ 2 : ℝ) : ℂ)
      | 1 => w₂
      | 2 => conj w₂
    let mu3 : Fin 3 → ℝ
      | 0 => 0
      | 1 => 2 * ω₀
      | 2 => -(2 * ω₀)
    set P3 : ℝ → ℂ := fun t => ∑ i : Fin 3, cf3 i * expChar (mu3 i) t
    have hP3_eq : ∀ t : ℝ, P3 t = (((f_top t ^ 2 + f_top (t + h) ^ 2 - C ^ 2 : ℝ) : ℂ)) := by
      intro t
      have hrot := re_sq_add_rot_re_sq (c_top ω₀ * expChar ω₀ t) (ω₀ * h)
      rw [← hf_top_single t, ← hshift_ω₀ t, norm_mul, norm_expChar, mul_one, mul_pow,
        sq (expChar ω₀ t), expChar_add, ← two_mul] at hrot
      rw [hrot]
      dsimp [P3, cf3, mu3, w₂]
      rw [Fin.sum_univ_three]
      have hc0 : expChar 0 t = 1 := by simp [expChar]
      have hcn : expChar (-(2 * ω₀)) t = conj (expChar (2 * ω₀) t) := by
        simp only [expChar, ← Complex.exp_conj]
        congr 1; rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
      have hre_split : ∀ u : ℂ, (u.re : ℂ) = (u + conj u) / 2 := fun u => by
        apply Complex.ext
        · simp
        · simp
      rw [hc0, hcn]
      simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
      rw [hre_split]
      simp only [map_mul, map_div₀, Complex.conj_ofReal, map_ofNat, map_pow]
      ring
    have hP3_ap : HTGeometry.IsBohrAlmostPeriodic P3 :=
      isBohrAlmostPeriodic_sum Finset.univ
        (fun i _ => continuous_const.mul (continuous_expChar (mu3 i)))
        (fun i _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar (mu3 i)))
    have hP3_lim : Tendsto P3 atTop (𝓝 0) := by
      have hc := (Complex.continuous_ofReal.tendsto 0).comp htop_norm_tendsto
      simpa only [Function.comp_def, Complex.ofReal_zero, ← hP3_eq] using hc
    have hP3_zero : P3 = fun _ => 0 :=
      funext (HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hP3_ap hP3_lim)
    have hb1 : bohrCoefficient P3 (2 * ω₀) = w₂ := by
      dsimp [P3]
      rw [bohrCoefficient_sum_expChar, Fin.sum_univ_three]
      rw [if_neg (by dsimp [mu3]; linarith), if_pos rfl, if_neg (by dsimp [mu3]; linarith)]
      simp [cf3]
    have hw₂0 : w₂ = 0 := by
      rw [← hb1, hP3_zero]; unfold bohrCoefficient; simp [bohrMean_zero]
    have hcos0 : Real.cos (ω₀ * h) = 0 := by
      dsimp [w₂] at hw₂0
      have hc_sq_ne : c_top ω₀ ^ 2 ≠ 0 := pow_ne_zero 2 (hc_top_ne ω₀ hω₀_mem)
      rcases mul_eq_zero.mp hw₂0 with hleft | hsq0
      · rcases mul_eq_zero.mp hleft with hdiv | hexp0
        · exact Complex.ofReal_eq_zero.mp (by simpa using div_eq_zero_iff.mp hdiv)
        · exact absurd hexp0 (Complex.exp_ne_zero _)
      · exact absurd hsq0 hc_sq_ne
    have hb0 : bohrCoefficient P3 0 = ((‖c_top ω₀‖ ^ 2 - C ^ 2 : ℝ) : ℂ) := by
      dsimp [P3]
      rw [bohrCoefficient_sum_expChar, Fin.sum_univ_three]
      rw [if_pos rfl, if_neg (by dsimp [mu3]; linarith), if_neg (by dsimp [mu3]; linarith)]
      simp [cf3]
    have hnorm_sq_eq : ‖c_top ω₀‖ ^ 2 = C ^ 2 := by
      have hb0_z : bohrCoefficient P3 0 = 0 := by
        rw [hP3_zero]; unfold bohrCoefficient; simp [bohrMean_zero]
      exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp (hb0.symm.trans hb0_z))
    have hnorm_eq : ‖c_top ω₀‖ = C := by
      nlinarith [hnorm_sq_eq, norm_nonneg (c_top ω₀), hC_pos]
    obtain ⟨kZ, hkZ⟩ := Real.cos_eq_zero_iff.mp hcos0
    have hω_Z : ω₀ = (2 * (kZ : ℝ) + 1) * γ := by
      have hstep : ω₀ * (Real.pi / (2 * |γ|)) = (2 * (kZ : ℝ) + 1) * Real.pi / 2 := hkZ
      rw [abs_of_pos hγ] at hstep
      apply mul_right_cancel₀ Real.pi_ne_zero
      have hmul := congrArg (fun x => x * (2 * γ)) hstep
      field_simp [hγ.ne'] at hmul ⊢
      linarith
    have hkZ_nn : 0 ≤ kZ := by
      have hpos : 0 < (2 * (kZ : ℝ) + 1) * γ := hω_Z ▸ hω₀_pos
      have h2k1 : 0 < 2 * (kZ : ℝ) + 1 := (mul_pos_iff_of_pos_right hγ).mp hpos
      have hkZ_int : (-1 : ℤ) < 2 * kZ := by exact_mod_cast (by linarith : (-1 : ℝ) < 2 * kZ)
      omega
    refine ⟨kZ.toNat, ?_, hnorm_eq⟩
    rw [hω_Z, ← Int.toNat_of_nonneg hkZ_nn]; push_cast; rfl
  obtain ⟨k, hω₀_eq, hc_norm_eq⟩ := htop_alias
  have hS_sub_emp : S_sub = ∅ := by
    by_contra hne_sub
    have hS_sub_ne : S_sub.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne_sub
    set β₂ : ℝ := (S_sub.image (fun q => (q.1 : ℂ).re)).max' (hS_sub_ne.image _)
    obtain ⟨q₂, hq₂, hq₂_re⟩ := Finset.mem_image.mp (Finset.max'_mem _ (hS_sub_ne.image _))
    obtain ⟨hq₂_Sr, hq₂_ne⟩ := Finset.mem_filter.mp hq₂
    have hβ₂_gt : 1 / 2 < β₂ := hq₂_re ▸ hSr_half q₂ hq₂_Sr
    have hβ₂_lt : β₂ < β := lt_of_le_of_ne (hq₂_re ▸ hre_le_β q₂ hq₂_Sr) (hq₂_re ▸ hq₂_ne)
    set S_2 : Finset XiZeroCopy := S_sub.filter (fun q => (q.1 : ℂ).re = β₂)
    set S_3 : Finset XiZeroCopy := S_sub.filter (fun q => (q.1 : ℂ).re ≠ β₂)
    have hS2_ne : S_2.Nonempty := ⟨q₂, Finset.mem_filter.mpr ⟨hq₂, hq₂_re⟩⟩
    obtain ⟨σ₃, hσ₃_lo, hσ₃_lt, hS3_le⟩ : ∃ σ₃ : ℝ, 1 / 2 ≤ σ₃ ∧ σ₃ < β₂ ∧
        ∀ q ∈ S_3, (q.1 : ℂ).re ≤ σ₃ := by
      rcases S_3.eq_empty_or_nonempty with hemp3 | hne3
      · exact ⟨1 / 2, le_rfl, hβ₂_gt,
          fun q hq => by rw [hemp3] at hq; exact (Finset.notMem_empty q hq).elim⟩
      · set b3 := (S_3.image (fun q => (q.1 : ℂ).re)).max' (hne3.image _)
        obtain ⟨q₃, hq₃, hq₃_re⟩ := Finset.mem_image.mp (Finset.max'_mem _ (hne3.image _))
        obtain ⟨hq₃_sub, hq₃_ne⟩ := Finset.mem_filter.mp hq₃
        have hgt3 : 1 / 2 < b3 := hq₃_re ▸ hSr_half q₃ (Finset.mem_filter.mp hq₃_sub).1
        have hle_β₂ : b3 ≤ β₂ :=
          hq₃_re ▸ Finset.le_max' _ _ (Finset.mem_image_of_mem _ hq₃_sub)
        exact ⟨b3, hgt3.le, lt_of_le_of_ne hle_β₂ (hq₃_re ▸ hq₃_ne),
          fun q hq => Finset.le_max' _ _ (Finset.mem_image_of_mem _ hq)⟩
    obtain ⟨M_3, _, hv3_le⟩ := bound_layer_twoIntervalVec S_3 hh_pos.le hA1 (by linarith) hS3_le
    have hS_sub_β₂ : ∀ q ∈ S_sub, (q.1 : ℂ).re ≤ β₂ :=
      fun q hq => Finset.le_max' _ _ (Finset.mem_image_of_mem _ hq)
    obtain ⟨M_sub2, _, hv_sub2_le⟩ := bound_layer_twoIntervalVec S_sub hh_pos.le hA1
      (by linarith) hS_sub_β₂
    have h2_info := layer_twoIntervalVec_eq S_2 hβ₂_gt
      (fun q hq => (Finset.mem_filter.mp hq).2) hh_pos (β := β)
    set r₂ : ℝ := Real.exp ((β₂ - β) * h)
    have hr₂_pos : 0 < r₂ := Real.exp_pos _
    have hr₂_lt1 : r₂ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [hβ₂_lt, hh_pos])
    set Ω_2 : Finset ℝ := S_2.image (fun q => |(q.1 : ℂ).im|)
    let c_2 : ℝ → ℂ := fun ν =>
      -(((S_2.filter (fun q => |(q.1 : ℂ).im| = ν)).card : ℝ) : ℂ) *
        (Complex.exp ((((β₂ : ℂ) + I * (ν : ℂ)) * (h : ℂ))) - 1) /
        ((β₂ : ℂ) + I * (ν : ℂ))
    let f_2 : ℝ → ℝ := fun s => ∑ ν ∈ Ω_2, (c_2 ν * expChar ν s).re
    obtain ⟨hΩ2_pos, hc2_ne, hv2_eq⟩ := h2_info
    have hω₀h : ω₀ * h = (2 * (k : ℝ) + 1) * (Real.pi / 2) := by
      rw [hω₀_eq]; dsimp [h]; unfold quarterPeriodStep
      rw [abs_of_pos hγ]; field_simp [hγ.ne']
    have hexp_ω₀h : Complex.exp (((ω₀ * h : ℝ) : ℂ) * I) = if Even k then I else -I := by
      rw [hω₀h]
      induction k with
      | zero =>
        rw [if_pos Even.zero]
        simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, Complex.exp_mul_I,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
        simp
      | succ m' ih =>
        have hst : (((2 * ((m' + 1 : ℕ) : ℝ) + 1) * (Real.pi / 2) : ℝ) : ℂ) * I =
            (((2 * (m' : ℝ) + 1) * (Real.pi / 2) : ℝ) : ℂ) * I + (Real.pi : ℂ) * I := by
          push_cast; ring
        rw [hst, Complex.exp_add, Complex.exp_pi_mul_I, ih]
        by_cases hm' : Even m'
        · have hm1 : ¬ Even (m' + 1) := by simpa [Nat.even_add_one] using hm'
          rw [if_pos hm', if_neg hm1]; ring
        · have hm1 : Even (m' + 1) := by simpa [Nat.even_add_one] using hm'
          rw [if_neg hm', if_pos hm1]; ring
    set μ₀ : ℝ := if Even k then -ω₀ else ω₀
    set b₀ : ℂ := if Even k then conj (c_top ω₀) else c_top ω₀
    have hμ₀_ne : μ₀ ≠ 0 := by dsimp [μ₀]; split_ifs <;> linarith
    have hb₀_ne : b₀ ≠ 0 := by
      dsimp [b₀]; split_ifs
      · exact map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _) |>.mpr (hc_top_ne ω₀ hω₀_mem)
      · exact hc_top_ne ω₀ hω₀_mem
    have hb₀_norm : ‖b₀‖ = C := by
      dsimp [b₀]; split_ifs
      · rw [Complex.norm_conj]; exact hc_norm_eq
      · exact hc_norm_eq
    have hZ_top_pure : ∀ t : ℝ,
        ((f_top t : ℂ) + I * (f_top (t + h) : ℂ)) = b₀ * expChar μ₀ t := by
      intro t
      rw [hf_top_single t, hshift_ω₀ t, hexp_ω₀h]
      dsimp [b₀, μ₀]
      have hconj_e : conj (expChar ω₀ t) = expChar (-ω₀) t := by
        simp only [expChar, ← Complex.exp_conj]
        congr 1; rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
      by_cases hk_ev : Even k
      · rw [if_pos hk_ev, if_pos hk_ev, if_pos hk_ev, ← hconj_e, ← map_mul]
        set z := c_top ω₀ * expChar ω₀ t
        apply Complex.ext <;> simp
      · rw [if_neg hk_ev, if_neg hk_ev, if_neg hk_ev]
        set z := c_top ω₀ * expChar ω₀ t
        apply Complex.ext <;> simp
    let W_2 (s : ℝ) := -(∑ q ∈ S_2, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re)
    let W_3 (s : ℝ) := -(∑ q ∈ S_3, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re)
    have hsub_split : W_sub = fun s => W_2 s + W_3 s := by
      funext s
      dsimp [W_sub, W_2, W_3, S_2, S_3]
      rw [← Finset.sum_filter_add_sum_filter_not S_sub (fun q => (q.1 : ℂ).re = β₂)]
      ring
    have hcross_tendsto : Tendsto (fun t : ℝ =>
        (conj b₀ * expChar (-μ₀) t * ((f_2 t : ℂ) + I * ((r₂ * f_2 (t + h) : ℝ) : ℂ))).re)
        atTop (𝓝 0) := by
      obtain ⟨M_all, hM_all, hv_all_le⟩ := bound_layer_twoIntervalVec S_right hh_pos.le hA1
        (by linarith) hre_le_β
      set K_rad_sq : ℝ := 4 * K_v * (M_all + C)
      have ht_err1 : Tendsto
          (fun t : ℝ => (K_rad_sq / 2) * (t ^ (2 : ℝ) * Real.exp (-(β₂ - 1 / 2) * t)))
          atTop (𝓝 0) := by
        simpa using (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (β₂ - 1 / 2)
          (by linarith)).const_mul (K_rad_sq / 2)
      have ht_err2 : Tendsto
          (fun t : ℝ => (M_sub2 ^ 2 / 2) * (t ^ (0 : ℝ) * Real.exp (-(β - β₂) * t)))
          atTop (𝓝 0) := by
        simpa using (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (β - β₂)
          (sub_pos.mpr hβ₂_lt)).const_mul (M_sub2 ^ 2 / 2)
      have ht_err3 : Tendsto
          (fun t : ℝ => (C * M_3) * (t ^ (0 : ℝ) * Real.exp (-(β₂ - σ₃) * t)))
          atTop (𝓝 0) := by
        simpa using (_root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (β₂ - σ₃)
          (sub_pos.mpr hσ₃_lt)).const_mul (C * M_3)
      have ht_tot := (ht_err1.add ht_err2).add ht_err3
      rw [add_zero, add_zero] at ht_tot
      refine squeeze_zero_norm' ?_ ht_tot
      filter_upwards [eventually_ge_atTop (max T_rad 3)] with t ht
      have ht0 : 0 ≤ t := by linarith [le_max_right T_rad 3]
      have ht1_le : 1 ≤ t := by linarith [le_max_right T_rad 3]
      rw [Real.norm_eq_abs, Real.rpow_two, Real.rpow_zero, one_mul]
      set v_top := twoIntervalVec W_top h A t
      set v_sub := twoIntervalVec W_sub h A t
      set v_2 := twoIntervalVec W_2 h A t
      set v_3 := twoIntervalVec W_3 h A t
      have hv_all_eq : twoIntervalVec W_all h A t = v_top + v_sub := by
        rw [hW_split, twoIntervalVec_add]
      have hv_sub_eq : v_sub = v_2 + v_3 := by
        dsimp [v_sub, v_2, v_3]; rw [hsub_split, twoIntervalVec_add]
      have hv_top_form : v_top = (Real.exp (β * t) : ℂ) * (b₀ * expChar μ₀ t) := by
        dsimp [v_top]; rw [hr_top_eq t, hZ_top_pure t]
      have hv_top_norm : ‖v_top‖ = C * Real.exp (β * t) := by
        rw [hv_top_form, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), hb₀_norm, norm_expChar, mul_one, mul_comm]
      have hv_top_norm_sq : ‖v_top‖ ^ 2 = C ^ 2 * Real.exp (2 * β * t) := by
        rw [hv_top_norm, mul_pow, sq (Real.exp (β * t)), ← Real.exp_add]
        congr 2; ring
      have hnorm_expand : ∀ z w : ℂ, ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + 2 * (conj z * w).re + ‖w‖ ^ 2 := by
        intro z w
        rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
          Complex.normSq_apply, Complex.normSq_apply]
        simp [Complex.mul_re]; ring
      have hexp_id : ‖twoIntervalVec W_all h A t‖ ^ 2 - C ^ 2 * Real.exp (2 * β * t) =
          2 * Real.exp ((β + β₂) * t) *
            (conj b₀ * expChar (-μ₀) t *
              ((f_2 t : ℂ) + I * ((r₂ * f_2 (t + h) : ℝ) : ℂ))).re +
            2 * (conj v_top * v_3).re + ‖v_sub‖ ^ 2 := by
        rw [hv_all_eq, hnorm_expand v_top v_sub, hv_top_norm_sq, hv_sub_eq]
        have hv2_form : v_2 =
            (Real.exp (β₂ * t) : ℂ) * ((f_2 t : ℂ) + I * ((r₂ * f_2 (t + h) : ℝ) : ℂ)) :=
          hv2_eq t
        have hconj_vtop : conj v_top = (Real.exp (β * t) : ℂ) * (conj b₀ * expChar (-μ₀) t) := by
          rw [hv_top_form, map_mul, map_mul, Complex.conj_ofReal]
          congr 2
          simp only [expChar, ← Complex.exp_conj]
          congr 1; rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
        have hpair : (conj v_top * (v_2 + v_3)).re =
            Real.exp ((β + β₂) * t) *
              (conj b₀ * expChar (-μ₀) t *
                ((f_2 t : ℂ) + I * ((r₂ * f_2 (t + h) : ℝ) : ℂ))).re +
              (conj v_top * v_3).re := by
          rw [mul_add, Complex.add_re]
          congr 1
          rw [hconj_vtop, hv2_form,
            show (Real.exp (β * t) : ℂ) * (conj b₀ * expChar (-μ₀) t) *
              ((Real.exp (β₂ * t) : ℂ) * ((f_2 t : ℂ) + I * ((r₂ * f_2 (t + h) : ℝ) : ℂ))) =
              ((Real.exp (β * t) * Real.exp (β₂ * t) : ℝ) : ℂ) *
                (conj b₀ * expChar (-μ₀) t *
                  ((f_2 t : ℂ) + I * ((r₂ * f_2 (t + h) : ℝ) : ℂ))) by push_cast; ring,
            Complex.re_ofReal_mul, ← Real.exp_add, show β * t + β₂ * t = (β + β₂) * t by ring]
        rw [hpair]; ring
      set target_re := (conj b₀ * expChar (-μ₀) t *
        ((f_2 t : ℂ) + I * ((r₂ * f_2 (t + h) : ℝ) : ℂ))).re
      have h2exp_pos : 0 < 2 * Real.exp ((β + β₂) * t) :=
        mul_pos two_pos (Real.exp_pos _)
      have hmul_bound : 2 * Real.exp ((β + β₂) * t) * |target_re| ≤
          |‖twoIntervalVec W_all h A t‖ ^ 2 - C ^ 2 * Real.exp (2 * β * t)| +
            ‖v_sub‖ ^ 2 + 2 * |(conj v_top * v_3).re| := by
        have h1 : 2 * Real.exp ((β + β₂) * t) * target_re =
            (‖twoIntervalVec W_all h A t‖ ^ 2 - C ^ 2 * Real.exp (2 * β * t)) -
              ‖v_sub‖ ^ 2 - 2 * (conj v_top * v_3).re := by linarith [hexp_id]
        have habs := congrArg abs h1
        rw [abs_mul, abs_of_pos h2exp_pos] at habs
        have ht_tri := (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_of_pos two_pos] at ht_tri
        linarith [habs, ht_tri]
      have hp1 : |‖twoIntervalVec W_all h A t‖ ^ 2 - C ^ 2 * Real.exp (2 * β * t)| ≤
          K_rad_sq * t ^ 2 * Real.exp ((β + 1 / 2) * t) := by
        have hsq_diff : ‖twoIntervalVec W_all h A t‖ ^ 2 - C ^ 2 * Real.exp (2 * β * t) =
            (‖twoIntervalVec W_all h A t‖ - C * Real.exp (β * t)) *
              (‖twoIntervalVec W_all h A t‖ + C * Real.exp (β * t)) := by
          have : Real.exp (2 * β * t) = Real.exp (β * t) ^ 2 := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          rw [this]; ring
        rw [hsq_diff, abs_mul]
        have hd1 := hv_rad t ht
        have h1t : (1 + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
        have hd1' : |‖twoIntervalVec W_all h A t‖ - C * Real.exp (β * t)| ≤
            4 * K_v * t ^ 2 * Real.exp (t / 2) :=
          hd1.trans ((mul_le_mul_of_nonneg_left h1t
            (mul_nonneg hK_v (Real.exp_pos _).le)).trans_eq (by ring))
        have hsum_le : |‖twoIntervalVec W_all h A t‖ + C * Real.exp (β * t)| ≤
            (M_all + C) * Real.exp (β * t) := by
          rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hC_pos.le (Real.exp_pos _).le))]
          linarith [hv_all_le t ht0]
        calc |‖twoIntervalVec W_all h A t‖ - C * Real.exp (β * t)| *
              |‖twoIntervalVec W_all h A t‖ + C * Real.exp (β * t)|
            ≤ (4 * K_v * t ^ 2 * Real.exp (t / 2)) * ((M_all + C) * Real.exp (β * t)) :=
              mul_le_mul hd1' hsum_le (abs_nonneg _)
                (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK_v) (sq_nonneg _))
                  (Real.exp_pos _).le)
          _ = K_rad_sq * t ^ 2 * (Real.exp (t / 2) * Real.exp (β * t)) := by
              dsimp [K_rad_sq]; ring
          _ = K_rad_sq * t ^ 2 * Real.exp ((β + 1 / 2) * t) := by
              rw [← Real.exp_add]; congr 2; ring
      have hp2 : ‖v_sub‖ ^ 2 ≤ M_sub2 ^ 2 * Real.exp (2 * β₂ * t) := by
        calc ‖v_sub‖ ^ 2 ≤ (M_sub2 * Real.exp (β₂ * t)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hv_sub2_le t ht0) 2
          _ = M_sub2 ^ 2 * Real.exp (2 * β₂ * t) := by
              rw [mul_pow, sq (Real.exp (β₂ * t)), ← Real.exp_add]
              congr 2; ring
      have hp3 : 2 * |(conj v_top * v_3).re| ≤ 2 * C * M_3 * Real.exp ((β + σ₃) * t) := by
        have hc1 : |(conj v_top * v_3).re| ≤ ‖v_top‖ * ‖v_3‖ :=
          (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, Complex.norm_conj])
        have hc2 : ‖v_top‖ * ‖v_3‖ ≤ (C * Real.exp (β * t)) * (M_3 * Real.exp (σ₃ * t)) := by
          rw [hv_top_norm]
          exact mul_le_mul_of_nonneg_left (hv3_le t ht0)
            (mul_nonneg hC_pos.le (Real.exp_pos _).le)
        calc 2 * |(conj v_top * v_3).re|
            ≤ 2 * ((C * Real.exp (β * t)) * (M_3 * Real.exp (σ₃ * t))) :=
              mul_le_mul_of_nonneg_left (hc1.trans hc2) zero_le_two
          _ = 2 * C * M_3 * (Real.exp (β * t) * Real.exp (σ₃ * t)) := by ring
          _ = 2 * C * M_3 * Real.exp ((β + σ₃) * t) := by
              rw [← Real.exp_add]; congr 2; ring
      set inv2e : ℝ := (1 / 2) * Real.exp (-((β + β₂) * t))
      have hinv2e_nn : 0 ≤ inv2e := mul_nonneg (by norm_num) (Real.exp_pos _).le
      have hsum_all := (hmul_bound.trans (add_le_add (add_le_add hp1 hp2) hp3))
      have hscaled := mul_le_mul_of_nonneg_right hsum_all hinv2e_nn
      have hlhs : 2 * Real.exp ((β + β₂) * t) * |target_re| * inv2e = |target_re| := by
        dsimp [inv2e]
        calc 2 * Real.exp ((β + β₂) * t) * |target_re| * (1 / 2 * Real.exp (-((β + β₂) * t)))
            = |target_re| * (Real.exp ((β + β₂) * t) * Real.exp (-((β + β₂) * t))) := by ring
          _ = |target_re| := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      have hrhs : (K_rad_sq * t ^ 2 * Real.exp ((β + 1 / 2) * t) +
          M_sub2 ^ 2 * Real.exp (2 * β₂ * t) +
          2 * C * M_3 * Real.exp ((β + σ₃) * t)) * inv2e =
          K_rad_sq / 2 * (t ^ 2 * Real.exp (-(β₂ - 1 / 2) * t)) +
            M_sub2 ^ 2 / 2 * Real.exp (-(β - β₂) * t) +
            C * M_3 * Real.exp (-(β₂ - σ₃) * t) := by
        dsimp [inv2e]
        have he1 : Real.exp ((β + 1 / 2) * t) * Real.exp (-((β + β₂) * t)) =
            Real.exp (-(β₂ - 1 / 2) * t) := by rw [← Real.exp_add]; congr 1; ring
        have he2 : Real.exp (2 * β₂ * t) * Real.exp (-((β + β₂) * t)) =
            Real.exp (-(β - β₂) * t) := by rw [← Real.exp_add]; congr 1; ring
        have he3 : Real.exp ((β + σ₃) * t) * Real.exp (-((β + β₂) * t)) =
            Real.exp (-(β₂ - σ₃) * t) := by rw [← Real.exp_add]; congr 1; ring
        calc (K_rad_sq * t ^ 2 * Real.exp ((β + 1 / 2) * t) +
                M_sub2 ^ 2 * Real.exp (2 * β₂ * t) +
                2 * C * M_3 * Real.exp ((β + σ₃) * t)) *
              (1 / 2 * Real.exp (-((β + β₂) * t)))
            = K_rad_sq / 2 * (t ^ 2 * (Real.exp ((β + 1 / 2) * t) * Real.exp (-((β + β₂) * t)))) +
                M_sub2 ^ 2 / 2 * (Real.exp (2 * β₂ * t) * Real.exp (-((β + β₂) * t))) +
                C * M_3 * (Real.exp ((β + σ₃) * t) * Real.exp (-((β + β₂) * t))) := by ring
          _ = K_rad_sq / 2 * (t ^ 2 * Real.exp (-(β₂ - 1 / 2) * t)) +
                M_sub2 ^ 2 / 2 * Real.exp (-(β - β₂) * t) +
                C * M_3 * Real.exp (-(β₂ - σ₃) * t) := by rw [he1, he2, he3]
      rwa [hlhs, hrhs] at hscaled
    exact sublayer_perturbation_not_tendsto_zero hμ₀_ne hr₂_pos hr₂_lt1 hb₀_ne
      Ω_2 (hS2_ne.image _) hΩ2_pos c_2 hc2_ne h hcross_tendsto
  refine ⟨k, fun q hq_Sr => ?_⟩
  have hq_top : q ∈ S_top := by
    by_contra hnot_top
    have hre_ne : (q.1 : ℂ).re ≠ β := fun he => hnot_top (Finset.mem_filter.mpr ⟨hq_Sr, he⟩)
    have hq_sub : q ∈ S_sub := Finset.mem_filter.mpr ⟨hq_Sr, hre_ne⟩
    rw [hS_sub_emp] at hq_sub
    exact Finset.notMem_empty q hq_sub
  have hre_q : (q.1 : ℂ).re = β := (Finset.mem_filter.mp hq_top).2
  have him_mem : |(q.1 : ℂ).im| ∈ Ω_top := Finset.mem_image_of_mem _ hq_top
  rw [hΩ_eq, Finset.mem_singleton] at him_mem
  exact ⟨hre_q, hω₀_eq ▸ him_mem⟩

/-- **Exact `FiniteOffLine` classification of the two-interval ordinary-prime radius.**
Under `FiniteOffLine`, for any `1/2 < β < 1`, `0 < γ`, and `1 ≤ m`, `thetaRadialDiscrepancy β γ m`
is bounded against `e^{t/2}(1 + t)²` if and only if there exists `k ∈ ℕ` such that `ζ` has a
**single** off-line quartet at `β + i(2k + 1)γ` satisfying `IsOddHarmonicPythagoreanAlias` at
`(β, γ, m)`. Every configuration with `≥ 2` off-line quartets breaks the two-interval circle at
all `(β, γ, m)`. -/
theorem finiteOffLine_not_radialUnbounded_iff
    (hfin_off : RHTower.BacklundConverse.FiniteOffLine) {β γ : ℝ} {m : ℕ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hm : 1 ≤ m) :
    ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m) ↔
      ∃ k : ℕ,
        HasSingleOffLineQuartet ((β : ℂ) + I * (((2 * (k : ℝ) + 1) * γ : ℝ) : ℂ)) ∧
        IsOddHarmonicPythagoreanAlias β γ m ((2 * (k : ℝ) + 1) * γ)
          (quartetCopyMult ((β : ℂ) + I * (((2 * (k : ℝ) + 1) * γ : ℝ) : ℂ))) k := by
  constructor
  · intro hbdd
    obtain ⟨_, hnrh, hΘ_eq, _, _, _⟩ :=
      radial_bounded_forces_abscissa_and_limsup hβ hβ1 hγ.ne' hm hbdd
    have hfin : {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite := by
      refine hfin_off.subset fun q hre => ?_
      have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
        simp [xiSpectralPoint, Complex.mul_im]
      intro him0; apply hre; linarith
    classical
    set S : Finset XiZeroCopy := hfin.toFinset
    set S_right : Finset XiZeroCopy := S.filter (fun q => 1 / 2 < (q.1 : ℂ).re)
    set S_left : Finset XiZeroCopy := S.filter (fun q => ¬ 1 / 2 < (q.1 : ℂ).re)
    obtain ⟨K₀, hK₀, hvk⟩ := RHTower.exists_abs_chebyshevPsi_sub_add_offLineWave_le_of_finite hfin
    let W_all : ℝ → ℝ := fun s => -(∑ q ∈ S_right, (Complex.exp ((q.1 : ℂ) * (s : ℂ)) / (q.1 : ℂ)).re)
    set h := quarterPeriodStep γ
    set A := quarterPeriodScale β γ
    set C := quartetRadialCoeff β γ m
    have hh_pos : 0 < h := quarterPeriodStep_pos hγ.ne'
    have hA1 : 1 ≤ A := (one_lt_quarterPeriodScale (by linarith) hγ.ne').le
    have hA0 : 0 < A := zero_lt_one.trans_le hA1
    have hC_pos : 0 < C := quartetRadialCoeff_pos hγ.ne' hm
    set K_left : ℝ := ∑ q ∈ S_left, ‖(q.1 : ℂ)‖⁻¹
    have hK_left : 0 ≤ K_left := Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (norm_nonneg _)
    have hW_mode : ∀ s : ℝ, 3 ≤ s →
        |psiLogError s - W_all s| ≤ (K₀ + K_left) * Real.exp (s / 2) * (1 + s) ^ 2 := by
      intro s hs
      have hx16 : 16 ≤ Real.exp s := by
        have h3 : (16 : ℝ) ≤ Real.exp 3 := by
          have := Real.exp_one_gt_d9
          calc (16 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
            _ ≤ Real.exp 1 ^ 3 := by gcongr
            _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
        exact h3.trans (Real.exp_le_exp.mpr hs)
      have hx1 : 1 ≤ Real.exp s := by linarith
      have hoff_eq : (RHTower.offLineWave S (Real.exp s)).re =
          -W_all s + ∑ q ∈ S_left, ((Real.exp s : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re := by
        unfold RHTower.offLineWave
        rw [Complex.re_sum, ← Finset.sum_filter_add_sum_filter_not S (fun q => 1 / 2 < (q.1 : ℂ).re)]
        dsimp [W_all, S_right, S_left]
        rw [neg_neg]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [cpow_exp_eq s (q.1 : ℂ)]
      have hid : psiLogError s - W_all s =
          (Chebyshev.psi (Real.exp s) - Real.exp s + (RHTower.offLineWave S (Real.exp s)).re) -
            ∑ q ∈ S_left, ((Real.exp s : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re := by
        dsimp [psiLogError]; rw [hoff_eq]; ring
      rw [hid]
      have hb1 := hvk (Real.exp s) hx16
      rw [← Real.exp_half, Real.log_exp] at hb1
      have hsq : s ^ 2 ≤ (1 + s) ^ 2 := by nlinarith
      have hb1' : |Chebyshev.psi (Real.exp s) - Real.exp s +
          (RHTower.offLineWave S (Real.exp s)).re| ≤ K₀ * Real.exp (s / 2) * (1 + s) ^ 2 :=
        hb1.trans (mul_le_mul_of_nonneg_left hsq (mul_nonneg hK₀ (Real.exp_pos _).le))
      have hb2 : |∑ q ∈ S_left, ((Real.exp s : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re| ≤
          K_left * Real.exp (s / 2) * (1 + s) ^ 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ q ∈ S_left, |((Real.exp s : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re|
            ≤ ∑ q ∈ S_left, ‖(q.1 : ℂ)‖⁻¹ * Real.exp (s / 2) * (1 + s) ^ 2 := by
              refine Finset.sum_le_sum fun q hq => ?_
              have hle_half : (q.1 : ℂ).re ≤ 1 / 2 := not_lt.mp (Finset.mem_filter.mp hq).2
              have hcp : |((Real.exp s : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re| ≤
                  ‖(q.1 : ℂ)‖⁻¹ * Real.exp (s / 2) := by
                refine (Complex.abs_re_le_norm _).trans ?_
                rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos s), div_eq_inv_mul]
                refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg _))
                exact (Real.rpow_le_rpow_of_exponent_le hx1 hle_half).trans_eq
                  ((Real.sqrt_eq_rpow _).symm.trans (Real.exp_half s).symm)
              have h1s : 1 ≤ (1 + s) ^ 2 := by nlinarith
              exact (hcp.trans (le_mul_of_one_le_right
                (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (Real.exp_pos _).le) h1s)).trans_eq
                (by ring)
          _ = K_left * Real.exp (s / 2) * (1 + s) ^ 2 := by
              dsimp [K_left]; rw [Finset.sum_mul, Finset.sum_mul]
      exact (abs_sub _ _).trans ((add_le_add hb1' hb2).trans_eq (by ring))
    have hpsi_bdd : ¬ IsLogSqrtSqUnbounded (radialDiscrepancyOf psiLogError β γ m) :=
      (psi_radial_bounded_iff_theta_radial_bounded (by linarith) hγ.ne' m).mpr hbdd
    rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not] at hpsi_bdd
    obtain ⟨K_p, T_p, hK_p⟩ := hpsi_bdd
    set K_v : ℝ := |K_p| + 4 * (K₀ + K_left) * Real.exp h * (1 + 2 * h) ^ 2
    have hK_v : 0 ≤ K_v := add_nonneg (abs_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hK₀ hK_left))
        (Real.exp_pos _).le) (sq_nonneg _))
    have hv_rad : ∀ t : ℝ, max T_p 3 ≤ t →
        |‖twoIntervalVec W_all h A t‖ - C * Real.exp (β * t)| ≤
          K_v * Real.exp (t / 2) * (1 + t) ^ 2 := by
      intro t ht
      have htTp : T_p ≤ t := (le_max_left _ _).trans ht
      have ht3 : 3 ≤ t := (le_max_right _ _).trans ht
      have hb_p := (hK_p t htTp).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self K_p) (Real.exp_pos _).le) (sq_nonneg _))
      unfold radialDiscrepancyOf at hb_p
      rw [twoIntervalRadius_eq_complex_norm hA0] at hb_p
      set B_t : ℝ := (K₀ + K_left) * Real.exp ((t + 2 * h) / 2) * (1 + (t + 2 * h)) ^ 2
      have hpt : ∀ s : ℝ, t ≤ s → s ≤ t + 2 * h → |psiLogError s - W_all s| ≤ B_t := by
        intro s hs1 hs2
        refine (hW_mode s (ht3.trans hs1)).trans ?_
        dsimp [B_t]
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith)) (add_nonneg hK₀ hK_left))
          (pow_le_pow_left₀ (by linarith) (by linarith) 2) (sq_nonneg _)
          (mul_nonneg (add_nonneg hK₀ hK_left) (Real.exp_pos _).le)
      have hb0 := hpt t le_rfl (by linarith)
      have hb1 := hpt (t + h) (by linarith) (by linarith)
      have hb2 := hpt (t + 2 * h) (by linarith) le_rfl
      have hre : |(twoIntervalVec psiLogError h A t - twoIntervalVec W_all h A t).re| ≤
          2 * B_t := by
        change |(psiLogError (t + h) - psiLogError t) - (W_all (t + h) - W_all t)| ≤ 2 * B_t
        rw [show (psiLogError (t + h) - psiLogError t) - (W_all (t + h) - W_all t) =
          (psiLogError (t + h) - W_all (t + h)) - (psiLogError t - W_all t) by ring]
        exact (abs_sub _ _).trans ((add_le_add hb1 hb0).trans_eq (two_mul _).symm)
      have him : |(twoIntervalVec psiLogError h A t - twoIntervalVec W_all h A t).im| ≤
          2 * B_t := by
        change |(psiLogError (t + h + h) - psiLogError (t + h)) / A -
          (W_all (t + h + h) - W_all (t + h)) / A| ≤ 2 * B_t
        rw [← sub_div, show t + h + h = t + 2 * h by ring,
          show (psiLogError (t + 2 * h) - psiLogError (t + h)) -
              (W_all (t + 2 * h) - W_all (t + h)) =
            (psiLogError (t + 2 * h) - W_all (t + 2 * h)) -
              (psiLogError (t + h) - W_all (t + h)) by ring,
          abs_div, abs_of_pos hA0]
        exact (div_le_self (abs_nonneg _) hA1).trans
          ((abs_sub _ _).trans ((add_le_add hb2 hb1).trans_eq (two_mul _).symm))
      have h4B : |‖twoIntervalVec W_all h A t‖ - ‖twoIntervalVec psiLogError h A t‖| ≤
          4 * B_t := by
        rw [abs_sub_comm]
        exact (abs_norm_sub_norm_le _ _).trans
          ((Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add hre him).trans_eq (by ring)))
      have h4B' : 4 * B_t ≤
          4 * (K₀ + K_left) * Real.exp h * (1 + 2 * h) ^ 2 * Real.exp (t / 2) * (1 + t) ^ 2 := by
        dsimp [B_t]
        have hexp_sp : Real.exp ((t + 2 * h) / 2) = Real.exp h * Real.exp (t / 2) := by
          rw [← Real.exp_add]; congr 1; ring
        have h1t : (1 + (t + 2 * h)) ^ 2 ≤ (1 + 2 * h) ^ 2 * (1 + t) ^ 2 := by
          have : 1 + (t + 2 * h) ≤ (1 + 2 * h) * (1 + t) := by nlinarith [ht3, hh_pos]
          exact (pow_le_pow_left₀ (by linarith) this 2).trans_eq (mul_pow _ _ 2)
        rw [hexp_sp]
        have hfac_nn : 0 ≤ 4 * ((K₀ + K_left) * (Real.exp h * Real.exp (t / 2))) :=
          mul_nonneg (by norm_num) (mul_nonneg (add_nonneg hK₀ hK_left)
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
        calc 4 * ((K₀ + K_left) * (Real.exp h * Real.exp (t / 2)) * (1 + (t + 2 * h)) ^ 2)
            = 4 * ((K₀ + K_left) * (Real.exp h * Real.exp (t / 2))) * (1 + (t + 2 * h)) ^ 2 := by ring
          _ ≤ 4 * ((K₀ + K_left) * (Real.exp h * Real.exp (t / 2))) *
                ((1 + 2 * h) ^ 2 * (1 + t) ^ 2) := mul_le_mul_of_nonneg_left h1t hfac_nn
          _ = 4 * (K₀ + K_left) * Real.exp h * (1 + 2 * h) ^ 2 *
                Real.exp (t / 2) * (1 + t) ^ 2 := by ring
      have htri := (abs_add_le (‖twoIntervalVec W_all h A t‖ - ‖twoIntervalVec psiLogError h A t‖)
        (‖twoIntervalVec psiLogError h A t‖ - C * Real.exp (β * t))).trans
        (add_le_add (h4B.trans h4B') hb_p)
      rw [sub_add_sub_cancel] at htri
      exact htri.trans_eq (by dsimp [K_v]; ring)
    have hre_le_β : ∀ q ∈ S_right, (q.1 : ℂ).re ≤ β := by
      intro q hq
      have h0 := xiZeroCopy_re_pos q
      have h1 := xiZeroCopy_re_lt_one q
      have hne1 : (q.1 : ℂ) ≠ 1 := fun he => by rw [he, Complex.one_re] at h1; exact lt_irrefl 1 h1
      have hζ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp
        (xi_eq_zero_of_mem_divisor_support q.1)
      exact hΘ_eq ▸ re_le_zetaZeroAbscissa hζ
    set S_top : Finset XiZeroCopy := S_right.filter (fun q => (q.1 : ℂ).re = β)
    have hStop_ne : S_top.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rcases S_right.eq_empty_or_nonempty with hSr_emp | hSr_ne
      · apply hnrh
        rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
        intro z hz_lo hz_hi hz0
        have hne1 : z ≠ 1 := fun he => by rw [he, Complex.one_re] at hz_hi; exact lt_irrefl 1 hz_hi
        have hxi := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (by linarith) hne1).mpr hz0
        obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
        have hqS : q ∈ S_right := Finset.mem_filter.mpr
          ⟨hfin.mem_toFinset.mpr (by rw [Set.mem_setOf_eq, hq_eq]; linarith),
            by rw [hq_eq]; exact hz_lo⟩
        rw [hSr_emp] at hqS; exact Finset.notMem_empty q hqS
      · set bmax : ℝ := (S_right.image (fun q => (q.1 : ℂ).re)).max' (hSr_ne.image _)
        have hbmax_mem : bmax ∈ S_right.image (fun q => (q.1 : ℂ).re) :=
          Finset.max'_mem _ (hSr_ne.image _)
        obtain ⟨q_m, hqm_S, hqm_re⟩ := Finset.mem_image.mp hbmax_mem
        have hbmax_lt : bmax < β := by
          refine lt_of_le_of_ne (hqm_re ▸ hre_le_β q_m hqm_S) fun heq => ?_
          have hmem_top : q_m ∈ S_top := Finset.mem_filter.mpr ⟨hqm_S, hqm_re.trans heq⟩
          rw [hemp] at hmem_top; exact Finset.notMem_empty q_m hmem_top
        obtain ⟨z, hz0, hz_gt⟩ := RHTower.exists_zetaZero_mem_openStrip_lt_re
          (hΘ_eq.symm ▸ (max_lt hβ hbmax_lt))
        have hmax_lo := max_lt_iff.mp hz_gt.2
        have hne1 : z ≠ 1 := fun he => by rw [he, Complex.one_re] at hz_gt; exact lt_irrefl 1 hz_gt.1
        have hxi := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (by linarith) hne1).mpr hz0
        obtain ⟨q_z, hqz_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
        have hqz_S : q_z ∈ S_right := Finset.mem_filter.mpr
          ⟨hfin.mem_toFinset.mpr (by rw [Set.mem_setOf_eq, hqz_eq]; linarith),
            by rw [hqz_eq]; exact hmax_lo.1⟩
        have hle_bmax : z.re ≤ bmax := by
          rw [← hqz_eq]
          exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hqz_S)
        linarith [hmax_lo.2]
    obtain ⟨k, hk_pin⟩ := finite_right_layer_collapse S_right hβ hγ hC_pos hK_v
      (fun q hq => (Finset.mem_filter.mp hq).2) hre_le_β (by convert hStop_ne) hv_rad
    set ω₀ : ℝ := (2 * (k : ℝ) + 1) * γ
    have hω₀_pos : 0 < ω₀ := mul_pos (by positivity) hγ
    have hall_right_pin : ∀ z ∈ zetaZeroConfig.carrier, 1 / 2 < z.re →
        z.re = β ∧ |z.im| = ω₀ := by
      intro z hz hgt
      have hne1 : z ≠ 1 := fun he => by
        have h2 := hz.2.2; rw [he, Complex.one_re] at h2; exact lt_irrefl 1 h2
      have hxi := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hz.2.1 hne1).mpr hz.1
      obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
      have hq_Sr : q ∈ S_right := Finset.mem_filter.mpr
        ⟨hfin.mem_toFinset.mpr (by rw [Set.mem_setOf_eq, hq_eq]; linarith),
          by rw [hq_eq]; exact hgt⟩
      obtain ⟨hre_q, him_q⟩ := hk_pin q hq_Sr
      rw [hq_eq] at hre_q him_q
      exact ⟨hre_q, him_q⟩
    obtain ⟨q₀, hq₀_top⟩ := hStop_ne
    obtain ⟨hq₀_re, hq₀_im⟩ := hk_pin q₀ (Finset.mem_filter.mp hq₀_top).1
    have hmem_carrier_of_xi : ∀ {w : ℂ}, xi w = 0 → w ∈ zetaZeroConfig.carrier := by
      intro w hw
      obtain ⟨qw, hqw⟩ := exists_xiZeroCopy_of_xi_eq_zero hw
      rw [← hqw]
      have h0 := xiZeroCopy_re_pos qw
      have h1 := xiZeroCopy_re_lt_one qw
      have hne1 : (qw.1 : ℂ) ≠ 1 := fun he => by rw [he, Complex.one_re] at h1; exact lt_irrefl 1 h1
      exact ⟨(RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp
        (xi_eq_zero_of_mem_divisor_support qw.1), h0, h1⟩
    set ρ₀ : ℂ := (β : ℂ) + I * (ω₀ : ℂ)
    have hρ₀_mem : ρ₀ ∈ zetaZeroConfig.carrier := by
      have hxi0 := xi_eq_zero_of_mem_divisor_support q₀.1
      rcases eq_or_eq_neg_of_abs_eq hq₀_im with hp | hn
      · have hzeq : (q₀.1 : ℂ) = ρ₀ := by apply Complex.ext <;> simp [ρ₀, hq₀_re, hp]
        exact hzeq ▸ hmem_carrier_of_xi hxi0
      · have hzeq : conj (q₀.1 : ℂ) = ρ₀ := by apply Complex.ext <;> simp [ρ₀, hq₀_re, hn]
        exact hzeq ▸ hmem_carrier_of_xi (by rw [xi_conj, hxi0, map_zero])
    have hq_single : HasSingleOffLineQuartet ρ₀ := by
      refine ⟨by simp [ρ₀]; linarith, hρ₀_mem, Set.Subset.antisymm ?_ ?_⟩
      · rintro z ⟨hz_mem, hz_ne⟩
        have hquart_mem : ∀ {w : ℂ}, w.re = β → |w.im| = ω₀ → w ∈ zeroQuartetSet ρ₀ := by
          intro w hw_re hw_im
          simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff]
          rcases eq_or_eq_neg_of_abs_eq hw_im with hp | hn
          · left; apply Complex.ext <;> simp [ρ₀, hw_re, hp]
          · right; left; apply Complex.ext <;> simp [ρ₀, hw_re, hn]
        rcases lt_or_gt_of_ne hz_ne with hlt | hgt
        · have hne1 : z ≠ 1 := fun he => by
            have h2 := hz_mem.2.2; rw [he, Complex.one_re] at h2; exact lt_irrefl 1 h2
          have hxi_z := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hz_mem.2.1 hne1).mpr hz_mem.1
          have hrefl_mem : 1 - z ∈ zetaZeroConfig.carrier :=
            hmem_carrier_of_xi (by rw [xi_one_sub]; exact hxi_z)
          obtain ⟨hre_r, him_r⟩ := hall_right_pin (1 - z) hrefl_mem (by simp; linarith)
          have hm := hquart_mem hre_r him_r
          simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
          rcases hm with hm | hm | hm | hm
          · right; right; left; linear_combination -hm
          · right; right; right; linear_combination -hm
          · left; linear_combination -hm
          · right; left; linear_combination -hm
        · obtain ⟨hre_z, him_z⟩ := hall_right_pin z hz_mem hgt
          exact hquart_mem hre_z him_z
      · intro z hz_q
        have hne1 : ρ₀ ≠ 1 := fun he => by
          have := congrArg Complex.re he; simp [ρ₀] at this; linarith
        have hxi_ρ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hρ₀_mem.2.1 hne1).mpr hρ₀_mem.1
        have hc := hmem_carrier_of_xi (by rw [xi_conj, hxi_ρ, map_zero])
        have hr := hmem_carrier_of_xi (by rw [xi_one_sub]; exact hxi_ρ)
        have hrc := hmem_carrier_of_xi (by rw [xi_one_sub, xi_conj, hxi_ρ, map_zero])
        simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hz_q
        rcases hz_q with rfl | rfl | rfl | rfl
        · exact ⟨hρ₀_mem, by simp [ρ₀]; linarith⟩
        · exact ⟨hc, by simp [ρ₀]; linarith⟩
        · exact ⟨hr, by simp [ρ₀]; linarith⟩
        · exact ⟨hrc, by simp [ρ₀]; linarith⟩
    -- Extract `IsOddHarmonicPythagoreanAlias` via `singleQuartet_psi_radial_transfer`
    have hsw := (singleQuartet_psi_radial_transfer hβ hω₀_pos hγ.ne' hq_single).mp hbdd
    obtain ⟨k', hω_k', hpyth'⟩ :=
      (not_isLogSqrtSqUnbounded_singleWaveLog_iff_alias hβ hγ.ne' hω₀_pos hm
        hq_single.quartetCopyMult_pos).mp hsw
    rw [abs_of_pos hγ] at hω_k'
    have hk_eq : k' = k := by
      dsimp [ω₀] at hω_k'
      have hR : (k' : ℝ) = (k : ℝ) := by nlinarith [hω_k', hγ]
      exact Nat.cast_injective hR
    subst hk_eq
    refine ⟨k', hq_single, ?_⟩
    unfold IsOddHarmonicPythagoreanAlias
    rw [abs_of_pos hγ]
    exact ⟨rfl, hpyth'⟩
  · rintro ⟨k, hq, halias⟩
    set ω₀ : ℝ := (2 * (k : ℝ) + 1) * γ
    have hω₀_pos : 0 < ω₀ := by dsimp [ω₀]; positivity
    rw [singleQuartet_psi_radial_transfer hβ hω₀_pos hγ.ne' hq]
    exact (not_isLogSqrtSqUnbounded_singleWaveLog_iff_alias hβ hγ.ne' hω₀_pos hm
      hq.quartetCopyMult_pos).mpr ⟨k, halias⟩

/-- **Irrational-slope `FiniteOffLine` radial characterization.**
Under `FiniteOffLine`, whenever `(γ / β)²` is irrational (`1/2 < β < 1`, `0 < γ`, `1 ≤ m`),
all odd-harmonic Pythagorean aliases vanish and boundedness of `thetaRadialDiscrepancy β γ m` is
equivalent to `HasSingleOffLineQuartet (β + iγ) ∧ quartetCopyMult (β + iγ) = m`. -/
theorem finiteOffLine_not_radialUnbounded_irrational_iff
    (hfin_off : RHTower.BacklundConverse.FiniteOffLine) {β γ : ℝ} {m : ℕ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hm : 1 ≤ m)
    (hirr : Irrational ((γ / β) ^ 2)) :
    ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m) ↔
      HasSingleOffLineQuartet ((β : ℂ) + I * (γ : ℂ)) ∧
        quartetCopyMult ((β : ℂ) + I * (γ : ℂ)) = m := by
  rw [finiteOffLine_not_radialUnbounded_iff hfin_off hβ hβ1 hγ hm]
  constructor
  · rintro ⟨k, hq, halias⟩
    obtain ⟨rfl, _, hm_eq⟩ := alias_forces_eq_of_irrational_or_same_mult
      (by linarith) hγ.ne' hm hq.quartetCopyMult_pos halias (Or.inl hirr)
    refine ⟨?_, ?_⟩
    · simpa using hq
    · simpa using hm_eq
  · rintro ⟨hq, rfl⟩
    refine ⟨0, by simpa using hq, ?_⟩
    refine ⟨by simp [abs_of_pos hγ], ?_⟩
    simp

/-- **Global `FiniteOffLine` equivalence of `TwoIntervalRadialExclusionLaw`.**
Under `FiniteOffLine`, `TwoIntervalRadialExclusionLaw` holds across all `(β, γ, m)` if and only if
either `RiemannHypothesis` holds or `ζ` has at least **four** distinct zeros right of `Re s = 1/2`
(`≥ 2` off-line quartets). -/
theorem finiteOffLine_twoIntervalRadialExclusionLaw_iff
    (hfin_off : RHTower.BacklundConverse.FiniteOffLine) :
    TwoIntervalRadialExclusionLaw ↔
      (RiemannHypothesis ∨
        (4 : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard) := by
  rw [← no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros]
  constructor
  · intro hlaw ρ₀ hq
    have hunb := hlaw ρ₀.re ρ₀.im (quartetCopyMult ρ₀) hq.1 hq.re_lt_one hq.im_ne_zero
      hq.quartetCopyMult_pos
    exact not_isLogSqrtSqUnbounded_of_singleQuartet hq hunb
  · intro hno_one β γ m hβ hβ1 hγ hm
    have habs_pos : 0 < |γ| := abs_pos.mpr hγ
    have heq_abs : thetaRadialDiscrepancy β |γ| m = thetaRadialDiscrepancy β γ m := by
      funext t
      rcases abs_choice γ with hc | hc
      · rw [hc]
      · rw [hc, thetaRadialDiscrepancy_neg]
    rw [← heq_abs]
    by_contra hbdd
    obtain ⟨k, hq, _⟩ :=
      (finiteOffLine_not_radialUnbounded_iff hfin_off hβ hβ1 habs_pos hm).mp hbdd
    exact hno_one _ hq

/-! ### 8. Unconditional cross-route corollaries of `TwoIntervalRadialExclusionLaw` -/

/-- **Unconditional cross-route corollaries of `TwoIntervalRadialExclusionLaw`.**
Unconditionally (without `FiniteOffLine`), `TwoIntervalRadialExclusionLaw` implies:
1. `ζ` has no single off-line quartet `Q(ρ₀)` of **any** divisor multiplicity `m ≥ 1`;
2. `RiemannHypothesis ∨ 4 ≤ (rightZeros zetaZeroConfig).encard`;
3. `realPacketNegIndex ≠ 2`;
4. Under `¬ RiemannHypothesis`, there exist `R > 0`, `S`, and half-line test states `H` with
   `3 ≤ hermNegIndex (confinedGram R H)` (eliminating the two-rung confined critical-state ladder);
5. `ThreeClockPrimeRecurrenceLaw`, and for every `1/2 < β < 1` and `γ > 0`, the `(2, 3, 6)`
   ordinary-prime dilation recurrences hold if and only if `RiemannHypothesis` holds;
6. Exclusion of two-wave square/cube proper-power bounds (`properPowerDiscrepancy (y²)`) at every
   right-of-line strip zero `ρ ∈ zetaZeroConfig.carrier` (`1/2 < ρ.re`);
7. Cofinal adjacent-octave single-wave exclusion (`adjacentCountAt t`). -/
theorem corollaries_of_twoIntervalRadialExclusionLaw (hlaw : TwoIntervalRadialExclusionLaw) :
    (∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀) ∧
    (RiemannHypothesis ∨
      (4 : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard) ∧
    realPacketNegIndex ≠ 2 ∧
    (¬ RiemannHypothesis →
      ∃ (R : ℝ), 0 < R ∧ ∃ (S : Finset ℝ) (H : S → ℝ → ℝ),
        (∀ s, IsHalfLineTest (H s)) ∧ 3 ≤ hermNegIndex (confinedGram R H)) ∧
    ThreeClockPrimeRecurrenceLaw ∧
    (∀ {β γ : ℝ}, 1 / 2 < β → β < 1 → 0 < γ →
      ((¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 2 β γ) ∧
        ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 3 β γ) ∧
        ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 6 β γ)) ↔
        RiemannHypothesis)) ∧
    (∀ {ρ : ℂ}, 1 / 2 < ρ.re → ρ ∈ zetaZeroConfig.carrier →
      ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
        |properPowerDiscrepancy (y ^ (2 : ℝ)) -
          (quartetPrimeWaveTerm ρ y + quartetPrimeWaveTerm ρ (y ^ (2 / 3 : ℝ)))| ≤
          K * (Real.sqrt y * (1 + Real.log y) ^ 2)) ∧
    (∀ B : ℕ, ∃ t > B, (2 * t + 1).Prime ∧ ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 →
      riemannZeta ρ = 0 → ¬ ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
        |adjacentCountAt t x - 2 * (quartetCopyMult ρ : ℝ) * ((x : ℂ) ^ ρ / ρ).re| ≤
          K * Real.sqrt x * Real.log x ^ 2) := by
  have hno_one : ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := fun ρ₀ hq =>
    not_isLogSqrtSqUnbounded_of_singleQuartet hq
      (hlaw ρ₀.re ρ₀.im (quartetCopyMult ρ₀) hq.1 hq.re_lt_one hq.im_ne_zero hq.quartetCopyMult_pos)
  have h3clock : ThreeClockPrimeRecurrenceLaw := threeClockPrimeRecurrenceLaw_iff.mpr hno_one
  obtain ⟨_, hrh_or_4, hidx_ne2, hgram3, hadj⟩ :=
    corollaries_of_threeClockPrimeRecurrenceLaw h3clock
  have hpdr : ∀ {β γ : ℝ}, 1 / 2 < β → β < 1 → 0 < γ →
      ((¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 2 β γ) ∧
        ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 3 β γ) ∧
        ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 6 β γ)) ↔
        RiemannHypothesis) := by
    intro β γ hβ hβ1 hγ
    rw [ordinary_prime_recurrences_iff_rh_or_singleQuartet hβ hβ1 hγ]
    exact ⟨fun h => h.resolve_right (hno_one _), Or.inl⟩
  have hppc : ∀ {ρ : ℂ}, 1 / 2 < ρ.re → ρ ∈ zetaZeroConfig.carrier →
      ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
        |properPowerDiscrepancy (y ^ (2 : ℝ)) -
          (quartetPrimeWaveTerm ρ y + quartetPrimeWaveTerm ρ (y ^ (2 / 3 : ℝ)))| ≤
          K * (Real.sqrt y * (1 + Real.log y) ^ 2) := by
    intro ρ hhalf hmem hbound
    exact hno_one ρ ((hasSingleOffLineQuartet_iff_two_properPower_waves hhalf hmem).mpr hbound)
  exact ⟨hno_one, hrh_or_4, hidx_ne2, hgram3, h3clock, hpdr, hppc, hadj⟩

#print axioms not_isLogSqrtSqUnbounded_of_singleQuartet
#print axioms finiteOffLine_not_radialUnbounded_iff
#print axioms corollaries_of_twoIntervalRadialExclusionLaw

end GaloisForLFunctions.ExceptionalLayerTheory
