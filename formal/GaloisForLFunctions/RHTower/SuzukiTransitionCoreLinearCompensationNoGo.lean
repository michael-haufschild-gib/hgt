import GaloisForLFunctions.RHTower.SuzukiFixedScaleDressedTransitionCoreNoGo
import GaloisForLFunctions.RHTower.SuzukiTransitionCoreGrowingRankCartanFission

/-!
# Linear compensation rigidity for the Suzuki transition core

The exact positive Suzuki transition core has linear mass along apertures `8n`, whereas every
fixed-width rectangular Xi screw curvature has an unconditional square-root envelope.  This
scaling gap determines the size of every possible correction: if subtracting the corrected core
from Xi curvature leaves an eventually lower-semibounded Ward defect, then the correction is at
least `n / 576` eventually along `8n`.

Consequently no asymptotically sublinear correction can close the rectangular Ward premise.  The
literal growing-rank positive Cartan fission is even farther from the required sign: its completed
observable is the transition core plus a nonnegative cubic mass.  Its rectangular Ward defect
therefore tends to negative infinity.  Growing rank without coefficient-faithful signed linear
atomic--continuous renormalization is not a survivor of
`SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`.

The proof is unconditional.  It uses no RH premise, Xi-zero location, numerical computation,
asymptotic interchange, or added axiom.
-/

open Complex Filter
open scoped Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- A correction to the exact positive transition core is sublinear on the cofinal `8n`
subsequence. -/
def SuzukiTransitionCoreCorrectionSublinear (correction : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => correction (8 * n) / (n : ℝ)) atTop (𝓝 0)

/-- **Linear compensation rigidity.**  Any correction leaving the transition-core rectangular
Ward defect lower-semibounded must carry positive linear mass on the cofinal `8n` subsequence.

This is the strongest positive survivor of the no-go: a viable source completion cannot merely
have growing rank; its signed correction must be of the same linear scale as the positive
transition core. -/
theorem eventually_linear_le_correction_of_transitionCoreWardDefect_bddBelow
    (L : ℝ) (correction : ℕ → ℝ) (lower : ℝ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N - correction N)
        (8 * n)) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 576 ≤ correction (8 * n) := by
  obtain ⟨C, hC, htarget⟩ := exists_abs_xiScrewWindowCurvature_logSample_le_sqrt L
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hscale : Tendsto (fun n : ℕ => 8 * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log (8 * n : ℕ)) atTop atTop := by
    have hlog' := Real.tendsto_log_atTop.comp hscale
    exact hlog'.congr' (Filter.Eventually.of_forall fun n => by norm_num)
  filter_upwards [hlower,
    eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ge_linear,
    hsqrtTop.eventually_ge_atTop (3456 * C),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (-1152 * lower),
    eventually_ge_atTop (1 : ℕ), hlog.eventually_ge_atTop (2 * L)] with
      n hward hcore hnroot hnlower hn hLn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hroot0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hrootSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have hsqrtEight : Real.sqrt (8 : ℝ) ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_nonneg (8 : ℝ)]
  have hsqrtMul : Real.sqrt (8 * n : ℕ) ≤ 3 * Real.sqrt (n : ℝ) := by
    rw [show ((8 * n : ℕ) : ℝ) = 8 * (n : ℝ) by norm_num]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    exact mul_le_mul_of_nonneg_right hsqrtEight hroot0
  have hCle : C ≤ Real.sqrt (n : ℝ) / 3456 := by linarith
  have hCroot : C * Real.sqrt (n : ℝ) ≤ (n : ℝ) / 3456 := by
    have := mul_le_mul_of_nonneg_right hCle hroot0
    nlinarith
  have hsource : C * Real.sqrt (8 * n : ℕ) ≤ (n : ℝ) / 1152 := by
    calc
      C * Real.sqrt (8 * n : ℕ) ≤ C * (3 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtMul hC
      _ ≤ (n : ℝ) / 1152 := by nlinarith
  have hsampleOne : 1 ≤ 8 * n := by omega
  have hsampleL : L ≤ Real.log (8 * n : ℕ) / 2 := by linarith
  have htargetAbs := htarget (8 * n) hsampleOne hsampleL
  have htargetUpper :
      (xiScrewWindowCurvature L (Real.log (8 * n : ℕ))).re ≤
        C * Real.sqrt (8 * n : ℕ) :=
    (le_abs_self _).trans htargetAbs
  have hlowerScale : -(n : ℝ) / 1152 ≤ lower := by nlinarith
  rw [suzukiRectangularWardDefect] at hward
  nlinarith

/-- **Sublinear-renormalization no-go.**  No asymptotically sublinear correction can supply the
semibounded rectangular Ward premise.  The statement is closed and quantifies over every width,
correction, and proposed lower bound. -/
theorem no_sublinear_transitionCore_rectangularWardProducer :
    ¬ ∃ (L : ℝ) (correction : ℕ → ℝ) (lower : ℝ),
      SuzukiTransitionCoreCorrectionSublinear correction ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N - correction N)
          (8 * n) := by
  rintro ⟨L, correction, lower, hsublinear, hlower⟩
  have hlinear :=
    eventually_linear_le_correction_of_transitionCoreWardDefect_bddBelow
      L correction lower hlower
  have hsmall : ∀ᶠ n : ℕ in atTop,
      correction (8 * n) / (n : ℝ) < 1 / 1152 :=
    (tendsto_order.1 hsublinear).2 (1 / 1152) (by norm_num)
  rcases (hlinear.and (hsmall.and (eventually_ge_atTop (1 : ℕ)))).exists with
    ⟨n, hlin, hsmall, hn⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : (1 : ℝ) / 576 ≤ correction (8 * n) / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    simpa [div_eq_mul_inv, mul_comm] using hlin
  norm_num at hratio hsmall
  linarith

/-- The actual growing-rank positive Cartan fission source has rectangular Ward defect tending to
negative infinity.  Rank growth without signed linear compensation is therefore not a survivor. -/
theorem tendsto_suzukiRectangularWardDefect_completedGrowingRankCartanFission_eight_mul_atBot
    (L : ℝ) :
    Tendsto (fun n : ℕ => suzukiRectangularWardDefect L
      suzukiTransitionCoreCompletedStokesFissionObservable (8 * n)) atTop atBot := by
  have hcorrection : ∀ N : ℕ,
      suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiTransitionCoreCompletedStokesFissionObservable N ≤ 0 := by
    intro N
    linarith [suzukiNaturalApertureTransitionCoreCauchyEnergy_le_completedStokesFissionObservable N]
  simpa only [sub_sub_cancel] using
    (tendsto_suzukiRectangularWardDefect_transitionCore_sub_bounded_atBot
      L (B := 0) hcorrection)

/-- **Closed producer-class kill.**  No width makes the literal growing-rank positive Cartan
fission source satisfy even eventual lower semiboundedness on the cofinal `8n` mesh. -/
theorem no_growingRankPositiveCartanFission_rectangularWardProducer :
    ¬ ∃ L lower : ℝ, ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        suzukiTransitionCoreCompletedStokesFissionObservable (8 * n) := by
  rintro ⟨L, lower, hlower⟩
  have hfall :=
    tendsto_suzukiRectangularWardDefect_completedGrowingRankCartanFission_eight_mul_atBot L
  have hbelow : ∀ᶠ n : ℕ in atTop,
      suzukiRectangularWardDefect L
        suzukiTransitionCoreCompletedStokesFissionObservable (8 * n) ≤ lower - 1 :=
    (tendsto_atBot.1 hfall) (lower - 1)
  rcases (hlower.and hbelow).exists with ⟨n, hlow, hhigh⟩
  linarith

end

end RHTower
