import GaloisForLFunctions.RHTower.Sieve.LadderMajorantMono
import GaloisForLFunctions.RHTower.Sieve.ScaledBudgetSubstitution
import GaloisForLFunctions.RHTower.Sieve.BudgetLimit

/-!
# The normalised spectral budget at a shrunk window

Shrinking the window by a fixed factor `c ≤ 1` shortens the fibre index range and lowers the
Gallagher cut, but leaves the ladder — and hence the annulus constant, the Möbius majorant and the
smoothing threshold — untouched.  Every majorant is therefore inherited from the full window by the
monotonicity of `Sieve/LadderMajorantMono`, and each of the four normalised quotients is at most a
fixed multiple of its unshrunk counterpart.  So the short-interval mean square for the Möbius
function holds at every window `c · exp((log x)^β)` at once.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The scaled index range dominates the outer scale. -/
theorem sqrt_le_budgetBS {c β : ℝ} (hc0 : 0 < c) (hβ0 : 0 < β) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x ≤ ((budgetBS c β x : ℕ) : ℝ) := by
  filter_upwards [(tendsto_scaledLength hc0 hβ0).eventually_ge_atTop (1 : ℝ)] with x hh1
  rw [budgetBS]
  have := Nat.lt_floor_add_one (Real.sqrt x + scaledLength c β x)
  linarith

/-- **The three spectral groups at an expiry height above the index range.** -/
theorem spectral_terms_le' {sx h W G T0 δ αL βL Ec B0 : ℝ}
    (hsx : 0 < sx) (hW : 1 ≤ W) (hh : 1 ≤ h) (hB0 : 0 < B0)
    (hδ : 0 ≤ δ) (hδle : δ ≤ h / sx) (hGh : G * h = B0) (hG0 : 0 < G) (hT0 : B0 ≤ T0)
    (hxB : B0 ^ 2 ≤ 4 * sx ^ 2) (hαL : 0 ≤ αL) (hβL : 0 ≤ βL) (hEc : 0 ≤ Ec) :
    32 * δ ^ 2 * (αL * G + βL) / (W ^ 2 * h ^ 2)
        + 64 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * B0 * Ec / T0)
            / (Real.pi ^ 2 * G * (W ^ 2 * h ^ 2))
        + 64 * βL / (3 * Real.pi ^ 2 * G ^ 2 * (W ^ 2 * h ^ 2))
      ≤ 136 * αL / (B0 * h * W ^ 2) + 140 * Ec / (B0 * h * W ^ 2)
        + 131 * βL / (B0 ^ 2 * W ^ 2) := by
  have hbase := spectral_terms_le (T0 := B0) hsx hW hh hB0 hδ hδle hGh hG0 rfl hxB hαL hβL hEc
  have hW0 : (0 : ℝ) < W := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hT00 : (0 : ℝ) < T0 := lt_of_lt_of_le hB0 hT0
  have hmid : 5 * Real.exp 1 / 2 * B0 * Ec / T0 ≤ 5 * Real.exp 1 / 2 * B0 * Ec / B0 := by
    have hnum : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * B0 * Ec := by positivity
    exact div_le_div_of_nonneg_left hnum hB0 hT0
  have hstep : 64 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * B0 * Ec / T0)
      / (Real.pi ^ 2 * G * (W ^ 2 * h ^ 2))
      ≤ 64 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * B0 * Ec / B0)
      / (Real.pi ^ 2 * G * (W ^ 2 * h ^ 2)) := by
    have hden : (0 : ℝ) < Real.pi ^ 2 * G * (W ^ 2 * h ^ 2) := by positivity
    gcongr
  linarith [hbase, hstep]

/-! ## The four normalised quotients at a shrunk window -/

set_option maxHeartbeats 400000 in
/-- **The slope quotient vanishes at a shrunk window.** -/
theorem tendsto_slope_quotientS {A delta Ctot c β γ : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 9 / 10 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β)
    (hγβ1 : γ * β < 1) (hCtot : 0 ≤ Ctot) (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ =>
        ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ)
            (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
          / (((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2))
      atTop (𝓝 0) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  have hab : (0 : ℝ) < γ * β := by linarith
  have hmaj := (tendsto_slope_quotient (A := A) (delta := delta) (Ctot := Ctot)
    hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot hdelta).const_mul (2 / c)
  rw [mul_zero] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_le_siftStart hab 2,
      sqrt_le_budgetBS hc0 hβ0',
      (tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_ge_atTop (1 : ℝ)] with x hx1 hQ2 hBS hW
    have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
    have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hnum : (0 : ℝ) ≤ ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x)
        ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x) :=
      ladderAffineSlope_nonneg (by linarith) hη.le
    have hsl : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    have hden : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
        * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      have hB : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) := by linarith
      have : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
        nlinarith [hW]
      positivity
    exact div_nonneg hnum hden.le
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_le_siftStart hab 2,
      sqrt_le_budgetBS hc0 hβ0', eventually_budgetB_le hβ0' hβ1,
      (tendsto_cardLength hβ0').eventually_ge_atTop (1 : ℝ),
      (tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_ge_atTop (1 : ℝ),
      (tendsto_scaledLength hc0 hβ0').eventually_ge_atTop (1 : ℝ)]
      with x hx1 hQ2 hBS hB2 hh1 hW hsl1
    have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
    have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hBSge : (1 : ℕ) ≤ budgetBS c β x := by
      rcases Nat.eq_zero_or_pos (budgetBS c β x) with h0 | hpos
      · rw [h0] at hBS
        norm_num at hBS
        linarith
      · exact hpos
    have hmono := ladderAffineSlope_mono_index (L := ladderSteps β γ x)
      (Q := ((siftStart (γ * β) x : ℕ) : ℝ)) (η := ladderEta β γ x)
      (ρ := budgetRho A delta Ctot β γ x) (by linarith) hη.le hBSge
      (budgetBS_le_budgetB hc1 x)
    have hnumS : (0 : ℝ) ≤ ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x)
        ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x) :=
      ladderAffineSlope_nonneg (by linarith) hη.le
    have hW2 : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      nlinarith [hW]
    have hBSR : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) := by linarith
    have hBR : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by
      have := sqrt_le_budgetB (β := β) x hh1
      linarith
    have hslS : scaledLength c β x = c * cardLength β x := rfl
    -- the scaled denominator dominates `c/2` times the unscaled one
    have hdenS : ((budgetB β x : ℕ) : ℝ) * cardLength β x
          * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 * c / 2
        ≤ ((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
          * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      rw [hslS]
      have hstep : ((budgetB β x : ℕ) : ℝ) * c / 2 ≤ ((budgetBS c β x : ℕ) : ℝ) * c := by
        nlinarith [mul_le_mul_of_nonneg_right hBS hc0.le,
          mul_le_mul_of_nonneg_right hB2 hc0.le]
      have hcl : (0 : ℝ) < cardLength β x := by linarith
      linarith [mul_le_mul_of_nonneg_right hstep (mul_nonneg hcl.le hW2.le)]
    have hdenS0 : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
        * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      have : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
      positivity
    have hd2 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) * cardLength β x
        * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 * c / 2 := by
      have hcl : (0 : ℝ) < cardLength β x := by linarith
      positivity
    calc ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x)
            ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
          / (((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
        ≤ ladderAffineSlope (ladderSteps β γ x) (budgetB β x)
            ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 * c / 2) := by
          gcongr
          exact hnumS.trans hmono
      _ = 2 / c * (ladderAffineSlope (ladderSteps β γ x) (budgetB β x)
            ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)) := by
          field_simp

/-- The shrunk window is below the full one. -/
theorem scaledLength_le_cardLength {c : ℝ} (hc1 : c ≤ 1) (β x : ℝ) :
    scaledLength c β x ≤ cardLength β x := by
  have h0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  rw [scaledLength]
  nlinarith [h0, hc1]

set_option maxHeartbeats 400000 in
/-- **The energy quotient vanishes at a shrunk window.** -/
theorem tendsto_energy_quotientS {c β γ : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ : γ * β < 1) :
    Tendsto (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 (budgetBS c β x),
            ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
          / (((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2))
      atTop (𝓝 0) := by
  have hmaj := (tendsto_energy_quotient (β := β) (γ := γ) hβ0 hβ1 hγ0 hγ1 hγβ).const_mul (2 / c)
  rw [mul_zero] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), sqrt_le_budgetBS hc0 hβ0,
      (tendsto_ladderMass hβ0 hγ0 hγ1 hγβ).eventually_ge_atTop (1 : ℝ)] with x hx1 hBS hW
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hsl : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    have hB : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) := by linarith
    have hW2 : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      nlinarith [hW]
    exact div_nonneg (Finset.sum_nonneg fun n _ => sq_nonneg _) (by positivity)
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), sqrt_le_budgetBS hc0 hβ0,
      eventually_budgetB_le hβ0 hβ1,
      (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
      (tendsto_ladderMass hβ0 hγ0 hγ1 hγβ).eventually_ge_atTop (1 : ℝ)]
      with x hx1 hBS hB2 hh1 hW
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hBSR : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) := by linarith
    have hBR : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by
      have := sqrt_le_budgetB (β := β) x hh1
      linarith
    have hW2 : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      nlinarith [hW]
    have hcl : (0 : ℝ) < cardLength β x := by linarith
    have hnumS : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 (budgetBS c β x),
        ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => sq_nonneg _
    have hmono : (∑ n ∈ Finset.Icc 1 (budgetBS c β x),
          ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
        ≤ ∑ n ∈ Finset.Icc 1 (budgetB β x),
          ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (budgetBS_le_budgetB hc1 x)) fun n _ _ => sq_nonneg _
    have hslS : scaledLength c β x = c * cardLength β x := rfl
    have hstep : ((budgetB β x : ℕ) : ℝ) * c / 2 ≤ ((budgetBS c β x : ℕ) : ℝ) * c := by
      nlinarith [mul_le_mul_of_nonneg_right hBS hc0.le,
        mul_le_mul_of_nonneg_right hB2 hc0.le]
    have hdenS : ((budgetB β x : ℕ) : ℝ) * cardLength β x
          * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 * c / 2
        ≤ ((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
          * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      rw [hslS]
      linarith [mul_le_mul_of_nonneg_right hstep (mul_nonneg hcl.le hW2.le)]
    have hd2 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) * cardLength β x
        * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 * c / 2 := by
      positivity
    calc (∑ n ∈ Finset.Icc 1 (budgetBS c β x),
            ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
          / (((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
        ≤ (∑ n ∈ Finset.Icc 1 (budgetB β x),
            ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 * c / 2) := by
          gcongr
      _ = 2 / c * ((∑ n ∈ Finset.Icc 1 (budgetB β x),
            ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)) := by
          field_simp

set_option maxHeartbeats 400000 in
/-- **The constant quotient vanishes at a shrunk window.** -/
theorem tendsto_const_quotientS {A delta Ctot c β γ : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 9 / 10 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β)
    (hγβ1 : γ * β < 1) (hCtot : 0 ≤ Ctot) (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ =>
        ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
            (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
            (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
          / (((budgetBS c β x : ℕ) : ℝ) ^ 2
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2))
      atTop (𝓝 0) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  have hab : (0 : ℝ) < γ * β := by linarith
  have hmaj := (tendsto_const_quotient (A := A) (delta := delta) (Ctot := Ctot)
    hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot hdelta).const_mul (4 : ℝ)
  rw [mul_zero] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_le_siftStart hab 2,
      sqrt_le_budgetBS hc0 hβ0',
      (tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_ge_atTop (1 : ℝ)] with x hx1 hQ2 hBS hW
    have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
    have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hB : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) := by linarith
    have hW2 : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      nlinarith [hW]
    exact div_nonneg (ladderAffineConst_nonneg (by linarith) hη.le) (by positivity)
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_le_siftStart hab 2,
      sqrt_le_budgetBS hc0 hβ0', eventually_budgetB_le hβ0' hβ1,
      (tendsto_cardLength hβ0').eventually_ge_atTop (1 : ℝ),
      (tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_ge_atTop (1 : ℝ),
      one_le_gallagherCut hβ0' hβ1] with x hx1 hQ2 hBS hB2 hh1 hW hG1
    have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
    have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hBSge : (1 : ℕ) ≤ budgetBS c β x := by
      rcases Nat.eq_zero_or_pos (budgetBS c β x) with h0 | hpos
      · rw [h0] at hBS
        norm_num at hBS
        linarith
      · exact hpos
    have hs0 : (0 : ℝ) ≤ budgetS β x := by
      rw [budgetS, budgetNmin]
      refine relMoebiusSharp_nonneg ?_
      have h1 : (1 : ℕ) ≤ ⌊gallagherCut β x⌋₊ := Nat.le_floor (by exact_mod_cast hG1)
      have : (1 : ℝ) ≤ ((⌊gallagherCut β x⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hmono := ladderAffineConst_mono_index (z₀ := siftStart (γ * β) x)
      (z := ladderTop β γ x) (L := ladderSteps β γ x)
      (Q := ((siftStart (γ * β) x : ℕ) : ℝ)) (η := ladderEta β γ x)
      (ρ := budgetRho A delta Ctot β γ x) (s := budgetS β x) (w₀ := annulusStart β x)
      (by linarith) hη.le hBSge (budgetBS_le_budgetB hc1 x) hs0
    have hnumS : (0 : ℝ) ≤ ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
        (ladderSteps β γ x) (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
        (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x) :=
      ladderAffineConst_nonneg (by linarith) hη.le
    have hW2 : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      nlinarith [hW]
    have hBSR : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) := by linarith
    have hBR : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by
      have := sqrt_le_budgetB (β := β) x hh1
      linarith
    have hsq : ((budgetB β x : ℕ) : ℝ) ^ 2 / 4 ≤ ((budgetBS c β x : ℕ) : ℝ) ^ 2 := by
      nlinarith [hBS, hB2, hsx, hBSR]
    have hdenS : ((budgetB β x : ℕ) : ℝ) ^ 2
          * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 / 4
        ≤ ((budgetBS c β x : ℕ) : ℝ) ^ 2
          * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      nlinarith [hsq, hW2]
    have hd2 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) ^ 2
        * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 / 4 := by
      positivity
    calc ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
            (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
            (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
          / (((budgetBS c β x : ℕ) : ℝ) ^ 2
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
        ≤ ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
            (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
            (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
          / (((budgetB β x : ℕ) : ℝ) ^ 2
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 / 4) := by
          gcongr
          exact hnumS.trans hmono
      _ = 4 * (ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
            (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
            (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
          / (((budgetB β x : ℕ) : ℝ) ^ 2
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)) := by
          field_simp

set_option maxHeartbeats 400000 in
/-- **The non-spectral budget vanishes at a shrunk window.** -/
theorem tendsto_nonSpectralBudgetS {c β γ : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ : γ * β < 1) :
    Tendsto (fun x : ℝ =>
        (204 * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
              * (Real.sqrt x + 1)
            + 2 * (scaledLength c β x + 1) * (2 * scaledLength c β x + 1)
              * (4 * (Real.sqrt x / 2 + scaledLength c β x + 1) * mertensS (ladderTop β γ x)
                + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
                + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2))
          / ((mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2
            * (scaledLength c β x) ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
  have hmaj := (tendsto_nonSpectralBudget (β := β) (γ := γ) hβ0 hβ1 hγ0 hγ1
    hγβ).const_mul (1 / c ^ 2)
  rw [mul_zero] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      (tendsto_ladderMass hβ0 hγ0 hγ1 hγβ).eventually_ge_atTop (1 : ℝ)] with x hx1 hW
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hsl : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    have hW2 : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      nlinarith [hW]
    have hm : (0 : ℝ) ≤ mertensS (ladderTop β γ x) := mertensS_nonneg' _
    refine div_nonneg ?_ (by positivity)
    have t1 : (0 : ℝ) ≤ 204
        * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
        * (Real.sqrt x + 1) := by positivity
    have t2 : (0 : ℝ) ≤ 2 * (scaledLength c β x + 1) * (2 * scaledLength c β x + 1)
        * (4 * (Real.sqrt x / 2 + scaledLength c β x + 1) * mertensS (ladderTop β γ x)
          + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
          + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2) := by
      have a1 : (0 : ℝ) ≤ 4 * (Real.sqrt x / 2 + scaledLength c β x + 1)
          * mertensS (ladderTop β γ x) := mul_nonneg (by linarith) hm
      have a2 : (0 : ℝ) ≤ ((Nat.primesLE (ladderTop β γ x)).card : ℝ) := Nat.cast_nonneg _
      have a3 : (0 : ℝ) ≤ 2 * (scaledLength c β x + 1) * (2 * scaledLength c β x + 1) := by
        positivity
      nlinarith [a1, a2, a3, sq_nonneg ((Nat.primesLE (ladderTop β γ x)).card : ℝ)]
    linarith
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      (tendsto_ladderMass hβ0 hγ0 hγ1 hγβ).eventually_ge_atTop (1 : ℝ)] with x hx1 hW
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hsl : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    have hcl : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hW2 : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      nlinarith [hW]
    have hm : (0 : ℝ) ≤ mertensS (ladderTop β γ x) := mertensS_nonneg' _
    have hsle : scaledLength c β x ≤ cardLength β x := scaledLength_le_cardLength hc1 β x
    have hnum : 204 * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
            * (Real.sqrt x + 1)
          + 2 * (scaledLength c β x + 1) * (2 * scaledLength c β x + 1)
            * (4 * (Real.sqrt x / 2 + scaledLength c β x + 1) * mertensS (ladderTop β γ x)
              + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
              + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2)
        ≤ 204 * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
            * (Real.sqrt x + 1)
          + 2 * (cardLength β x + 1) * (2 * cardLength β x + 1)
            * (4 * (Real.sqrt x / 2 + cardLength β x + 1) * mertensS (ladderTop β γ x)
              + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
              + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2) := by
      gcongr
    have hden : (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2
          * (scaledLength c β x) ^ 2 * Real.sqrt x
        = c ^ 2 * ((mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2
          * (cardLength β x) ^ 2 * Real.sqrt x) := by
      rw [show scaledLength c β x = c * cardLength β x from rfl]
      ring
    rw [hden]
    rw [show (1 : ℝ) / c ^ 2 * ((204 * (((primesRange (siftStart (γ * β) x)
            (ladderTop β γ x)).card : ℝ) + 1) ^ 2 * (Real.sqrt x + 1)
          + 2 * (cardLength β x + 1) * (2 * cardLength β x + 1)
            * (4 * (Real.sqrt x / 2 + cardLength β x + 1) * mertensS (ladderTop β γ x)
              + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
              + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2))
        / ((mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2
          * (cardLength β x) ^ 2 * Real.sqrt x))
      = (204 * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
            * (Real.sqrt x + 1)
          + 2 * (cardLength β x + 1) * (2 * cardLength β x + 1)
            * (4 * (Real.sqrt x / 2 + cardLength β x + 1) * mertensS (ladderTop β γ x)
              + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
              + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2))
        / (c ^ 2 * ((mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2
          * (cardLength β x) ^ 2 * Real.sqrt x)) by field_simp]
    gcongr

set_option maxHeartbeats 400000 in
/-- **The normalised spectral budget vanishes at every shrunk window.** -/
theorem tendsto_normalised_omegaBudgetS {c β γ : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 9 / 10 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β)
    (hγβ1 : γ * β < 1) :
    Tendsto (fun x : ℝ =>
        omegaBudget x (scaledLength c β x) (siftStart (γ * β) x) (ladderTop β γ x)
          / ((mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2
            * (scaledLength c β x) ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  obtain ⟨A, delta, Ctot, hdelta, hCtot, hbound⟩ :=
    exists_eventually_omegaBudgetS_le (c := c) (β := β) (γ := γ) hc0 hc1 hβ0' hβ1 hγ0 hγ1 hγβ1
  have hslope := tendsto_slope_quotientS (A := A) (delta := delta) (Ctot := Ctot)
    hc0 hc1 hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot.le hdelta
  have henergy := tendsto_energy_quotientS (c := c) (β := β) (γ := γ) hc0 hc1 hβ0' hβ1 hγ0 hγ1 hγβ1
  have hconst := tendsto_const_quotientS (A := A) (delta := delta) (Ctot := Ctot)
    hc0 hc1 hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot.le hdelta
  have hns := tendsto_nonSpectralBudgetS (c := c) (β := β) (γ := γ) hc0 hc1 hβ0' hβ1 hγ0 hγ1 hγβ1
  have hmaj := (((hslope.const_mul (136 : ℝ)).add (henergy.const_mul (140 : ℝ))).add
    (hconst.const_mul (131 : ℝ))).add hns
  rw [show (136 : ℝ) * 0 + 140 * 0 + 131 * 0 + 0 = 0 by ring] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [(tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_ge_atTop (1 : ℝ),
      Filter.eventually_gt_atTop (1 : ℝ)] with x hW hx1
    have hh0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hnum : (0 : ℝ) ≤ omegaBudget x (scaledLength c β x) (siftStart (γ * β) x)
        (ladderTop β γ x) := by
      rw [omegaBudget]
      have hint : (0 : ℝ) ≤ ∫ w : ℝ,
          ‖logWindowKernel (fibreWidth x (scaledLength c β x)) w‖ ^ 2
            * ‖omegaWeightedMoebiusPoly (primesRange (siftStart (γ * β) x) (ladderTop β γ x))
                (fibreIndex x (scaledLength c β x)) w‖ ^ 2 :=
        MeasureTheory.integral_nonneg fun w => by positivity
      have hm : (0 : ℝ) ≤ mertensS (ladderTop β γ x) := mertensS_nonneg' _
      have hpc : (0 : ℝ) ≤ ((Nat.primesLE (ladderTop β γ x)).card : ℝ) := Nat.cast_nonneg _
      have t1 : (0 : ℝ) ≤ 16 * Real.sqrt x * (∫ w : ℝ,
          ‖logWindowKernel (fibreWidth x (scaledLength c β x)) w‖ ^ 2
            * ‖omegaWeightedMoebiusPoly (primesRange (siftStart (γ * β) x) (ladderTop β γ x))
                (fibreIndex x (scaledLength c β x)) w‖ ^ 2) :=
        mul_nonneg (by linarith) hint
      have t2 : (0 : ℝ) ≤ 204
          * (((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) + 1) ^ 2
          * (Real.sqrt x + 1) :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith)
      have t3 : (0 : ℝ) ≤ 2 * (scaledLength c β x + 1) * (2 * scaledLength c β x + 1)
          * (4 * (Real.sqrt x / 2 + scaledLength c β x + 1) * mertensS (ladderTop β γ x)
            + 4 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ)
            + 8 * ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2) := by
        refine mul_nonneg (mul_nonneg (by linarith) (by linarith)) ?_
        have a1 : (0 : ℝ) ≤ 4 * (Real.sqrt x / 2 + scaledLength c β x + 1)
            * mertensS (ladderTop β γ x) := mul_nonneg (by linarith) hm
        nlinarith [a1, hpc, sq_nonneg ((Nat.primesLE (ladderTop β γ x)).card : ℝ)]
      linarith [t1, t2, t3]
    have hden : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2
        * (scaledLength c β x) ^ 2 * Real.sqrt x := by
      have : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
        nlinarith [hW]
      exact mul_pos (mul_pos this (pow_pos hh0 2)) hsx
    exact div_nonneg hnum hden.le
  · filter_upwards [hbound, Filter.eventually_gt_atTop (1 : ℝ),
      (tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_ge_atTop (1 : ℝ),
      (tendsto_scaledLength hc0 hβ0').eventually_ge_atTop (1 : ℝ),
      (tendsto_cardLength hβ0').eventually_ge_atTop (1 : ℝ),
      eventually_budgetB_le hβ0' hβ1, eventually_le_siftStart (mul_pos hγ0 hβ0') 2,
      sqrt_le_budgetBS hc0 hβ0',
      Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1)
        (tendsto_ladderEta (β := β) (γ := γ) hβ0' hγβ1)]
      with x hb hx1 hW hsl1 hh1 hB2 hQ2 hBS hη1
    have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
    have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
    have hh0 : (0 : ℝ) < scaledLength c β x := by linarith
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hB0 : (0 : ℝ) < ((budgetBS c β x : ℕ) : ℝ) := by linarith
    have hBB : ((budgetBS c β x : ℕ) : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) :=
      Nat.cast_le.2 (budgetBS_le_budgetB hc1 x)
    have hden : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2
        * (scaledLength c β x) ^ 2 * Real.sqrt x := by
      have : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
        nlinarith [hW]
      exact mul_pos (mul_pos this (pow_pos hh0 2)) hsx
    refine (div_le_div_of_nonneg_right hb hden.le).trans ?_
    have hGdef : gallagherCutS c β x = ((budgetBS c β x : ℕ) : ℝ) / scaledLength c β x := rfl
    have hG0 : (0 : ℝ) < gallagherCutS c β x := by
      rw [hGdef]
      exact div_pos hB0 hh0
    rw [budget_div_eq (sx := Real.sqrt x) (h := scaledLength c β x)
      (W := mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x))
      (G := gallagherCutS c β x) (T0 := budgetT β x) (δ := fibreWidth x (scaledLength c β x))
      (αL := ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x)
        ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x))
      (βL := ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
        (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
        (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x))
      (Ec := ∑ n ∈ Finset.Icc 1 (budgetBS c β x),
        ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
      (B0 := ((budgetBS c β x : ℕ) : ℝ)) hsx (by nlinarith [hW]) hh0 hG0]
    have hGh : gallagherCutS c β x * scaledLength c β x = ((budgetBS c β x : ℕ) : ℝ) := by
      rw [hGdef]
      field_simp
    have hδ0 : (0 : ℝ) ≤ fibreWidth x (scaledLength c β x) := by
      rw [fibreWidth]
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ scaledLength c β x / Real.sqrt x := div_nonneg hh0.le hsx.le
      linarith
    have hδle : fibreWidth x (scaledLength c β x) ≤ scaledLength c β x / Real.sqrt x := by
      rw [fibreWidth]
      have hu : (0 : ℝ) ≤ scaledLength c β x / Real.sqrt x := div_nonneg hh0.le hsx.le
      have := Real.log_le_sub_one_of_pos (by linarith :
        (0:ℝ) < 1 + scaledLength c β x / Real.sqrt x)
      linarith
    have hspec := spectral_terms_le' (sx := Real.sqrt x) (h := scaledLength c β x)
      (W := mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x))
      (G := gallagherCutS c β x) (T0 := budgetT β x) (δ := fibreWidth x (scaledLength c β x))
      (αL := ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x)
        ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x))
      (βL := ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
        (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
        (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x))
      (Ec := ∑ n ∈ Finset.Icc 1 (budgetBS c β x),
        ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
      (B0 := ((budgetBS c β x : ℕ) : ℝ)) hsx hW hsl1 hB0
      hδ0 hδle hGh hG0 (by rw [budgetT]; exact hBB)
      (by nlinarith [hB2, hB0, hBB, Real.sq_sqrt (by linarith : (0:ℝ) ≤ x)])
      (ladderAffineSlope_nonneg (by linarith) hη.le)
      (ladderAffineConst_nonneg (by linarith) hη.le)
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
    have e1 : (136 : ℝ) * ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x)
          ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
          / (((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
        = 136 * (ladderAffineSlope (ladderSteps β γ x) (budgetBS c β x)
            ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
          / (((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)) := by
      ring
    have e2 : (140 : ℝ) * (∑ n ∈ Finset.Icc 1 (budgetBS c β x),
            ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
          / (((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
        = 140 * ((∑ n ∈ Finset.Icc 1 (budgetBS c β x),
            ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
          / (((budgetBS c β x : ℕ) : ℝ) * scaledLength c β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)) := by
      ring
    have e3 : (131 : ℝ) * ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
          (ladderSteps β γ x) (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ)
          (ladderEta β γ x) (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
          / (((budgetBS c β x : ℕ) : ℝ) ^ 2
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
        = 131 * (ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
            (ladderSteps β γ x) (budgetBS c β x) ((siftStart (γ * β) x : ℕ) : ℝ)
            (ladderEta β γ x) (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
          / (((budgetBS c β x : ℕ) : ℝ) ^ 2
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)) := by
      ring
    linarith [hspec, e1, e2, e3]

/-- **The Möbius short-interval mean square at every window `c · exp((log x)^β)`.** -/
theorem averagedMeanSquare_moebius_scaledLength {c β γ : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 9 / 10 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β)
    (hγβ1 : γ * β < 1) :
    AveragedMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) (scaledLength c β) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  refine averagedMeanSquare_moebius_of_omegaBudget (zlo := fun x => siftStart (γ * β) x)
    (zhi := fun x => ladderTop β γ x) (scaledLength_le_sqrt hc1 hβ0' hβ1) ?_ ?_ ?_
    (tendsto_normalised_omegaBudgetS hc0 hc1 hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1)
  · exact Filter.Eventually.of_forall fun x => scaledLength_pos hc0 β x
  · filter_upwards [eventually_ladderTop_facts hβ0' hγ0 hγ1 hγβ1] with x hx
    exact hx.2.2
  · filter_upwards [(tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1).eventually_gt_atTop (0 : ℝ)] with x hx
    exact hx

end

end RHTower.Sieve
