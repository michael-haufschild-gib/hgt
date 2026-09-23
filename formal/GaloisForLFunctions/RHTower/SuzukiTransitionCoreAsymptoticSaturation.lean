import GaloisForLFunctions.RHTower.SuzukiTransitionCoreLinearCompensationNoGo

/-!
# Asymptotic saturation forced by the Suzuki transition-core Ward wall

The positive transition core has linear mass along the literal `8n` apertures, whereas the
available Xi curvature is only square-root scale.  Earlier rigidity therefore forced every
semibounding correction to have some positive linear size.  The sharper fact proved here is that
every such correction must cancel *asymptotically all* of the literal transition core: any fixed
fractional under-compensation is impossible.

This is source-faithful and unconditional.  It identifies the genuine remaining datum as the
signed residual after near-total atomic--continuous cancellation, rather than merely the presence
of a growing-rank or linear-scale correction.
-/

open Filter
open scoped Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- A correction asymptotically cancels every prescribed fraction of the literal positive
transition core along the canonical `8n` apertures. -/
def SuzukiTransitionCoreAsymptoticallySaturates (correction : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (1 - ε) * suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) ≤
      correction (8 * n)

/-- **Asymptotic saturation law.** Any correction whose literal transition-core Ward defect is
eventually lower-semibounded cancels an arbitrarily large prescribed fraction of that core. -/
theorem suzukiTransitionCoreAsymptoticallySaturates_of_rectangularWardDefect_bddBelow
    (L : ℝ) (correction : ℕ → ℝ) (lower : ℝ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N - correction N)
        (8 * n)) :
    SuzukiTransitionCoreAsymptoticallySaturates correction := by
  intro ε hε
  obtain ⟨C, hC, htarget⟩ :=
    exists_abs_xiScrewWindowCurvature_logSample_le_sqrt L
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog : Tendsto (fun n : ℕ => Real.log (8 * n : ℕ)) atTop atTop := by
    have hscale : Tendsto (fun n : ℕ => 8 * (n : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
    exact (Real.tendsto_log_atTop.comp hscale).congr'
      (Filter.Eventually.of_forall fun n => by norm_num)
  filter_upwards [hlower,
    eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ge_linear,
    hsqrtTop.eventually_ge_atTop (1728 * C / ε),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (-576 * lower / ε),
    eventually_ge_atTop (1 : ℕ),
    hlog.eventually_ge_atTop (2 * L)] with
      n hward hcore hroot hlow hn hlogn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (n : ℝ) ^ (2 : ℕ) = (n : ℝ) := Real.sq_sqrt hn0
  have hroot' : 1728 * C ≤ ε * Real.sqrt (n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hroot
  have hrootMul := mul_le_mul_of_nonneg_right hroot' hsqrt0
  have hCroot : 3 * C * Real.sqrt (n : ℝ) ≤ ε * (n : ℝ) / 576 := by
    nlinarith [hrootMul]
  have hsqrtEight : Real.sqrt (8 : ℝ) ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_nonneg (8 : ℝ)]
  have hsqrtMul : Real.sqrt (8 * n : ℕ) ≤ 3 * Real.sqrt (n : ℝ) := by
    rw [show ((8 * n : ℕ) : ℝ) = 8 * (n : ℝ) by norm_num]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    exact mul_le_mul_of_nonneg_right hsqrtEight hsqrt0
  have hcurvature : C * Real.sqrt (8 * n : ℕ) ≤ ε * (n : ℝ) / 576 := by
    calc
      C * Real.sqrt (8 * n : ℕ) ≤ C * (3 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtMul hC
      _ ≤ ε * (n : ℝ) / 576 := by nlinarith [hCroot]
  have hlow' : -576 * lower ≤ ε * (n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hlow
  have hbudget : C * Real.sqrt (8 * n : ℕ) - lower ≤ ε * (n : ℝ) / 288 := by
    nlinarith [hcurvature, hlow']
  have hsampleOne : 1 ≤ 8 * n := by omega
  have hsampleL : L ≤ Real.log (8 * n : ℕ) / 2 := by linarith
  have htargetAbs := htarget (8 * n) hsampleOne hsampleL
  have htargetUpper :
      (xiScrewWindowCurvature L (Real.log (8 * n : ℕ))).re ≤
        C * Real.sqrt (8 * n : ℕ) :=
    (le_abs_self _).trans htargetAbs
  rw [suzukiRectangularWardDefect] at hward
  have hresidual :
      suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) - correction (8 * n) ≤
        ε * suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) := by
    have hcoreScaled : ε * (n : ℝ) / 288 ≤
        ε * suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) := by
      calc
        ε * (n : ℝ) / 288 = ε * ((n : ℝ) / 288) := by ring
        _ ≤ ε * suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) :=
          mul_le_mul_of_nonneg_left hcore hε.le
    nlinarith [hward, htargetUpper, hbudget]
  nlinarith [hresidual]

/-- **Fractional-undercompensation no-go.** No correction which leaves a fixed positive fraction
of the literal transition core can make the rectangular Ward defect eventually lower-semibounded. -/
theorem no_fixedFraction_undercompensated_transitionCore_rectangularWardProducer :
    ¬ ∃ (L : ℝ) (correction : ℕ → ℝ) (lower ε : ℝ),
      0 < ε ∧
      (∀ᶠ n : ℕ in atTop,
        correction (8 * n) ≤
          (1 - ε) * suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n)) ∧
      (∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N - correction N)
          (8 * n)) := by
  rintro ⟨L, correction, lower, ε, hε, hunder, hward⟩
  have hsat :=
    suzukiTransitionCoreAsymptoticallySaturates_of_rectangularWardDefect_bddBelow
      L correction lower hward (ε / 2) (by linarith)
  have hcore := eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ge_linear
  rcases (hsat.and (hunder.and (hcore.and (eventually_ge_atTop (1 : ℕ))))).exists with
    ⟨n, hsatn, hundern, hcoren, hn⟩
  have hcorePos : 0 < suzukiNaturalApertureTransitionCoreCauchyEnergy (8 * n) := by
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (n : ℝ) / 288) hcoren
  nlinarith

end

end RHTower
