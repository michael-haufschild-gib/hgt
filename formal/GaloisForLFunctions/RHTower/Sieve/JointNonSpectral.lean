import GaloisForLFunctions.RHTower.Sieve.JointSchedule
import GaloisForLFunctions.RHTower.Sieve.NonSpectralBudget
import GaloisForLFunctions.RHTower.Sieve.ScaledBudgetGeometry

/-!
# The non-spectral rows of the joint budget

Two of the four rows of the joint budget quotient are elementary: the joint Turán–Kubilius variance
and the fibre bridge's rounding error.  This module discharges the first.

The variance row divides out to `≍ 4(1/W_P + 1/W_Q) + 8·#P·#Q/(W_P W_Q √x)`, and both halves vanish
— the first because both harmonic masses grow, the second because the two designated ranges are
`x^{o(1)}` while the index range is `√x`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The variance row, majorised.** -/
theorem jointVariance_quotient_le {h B₀ WP WQ NP NQ sx : ℝ}
    (hh : 1 ≤ h) (hsx : 0 < sx) (hB0 : B₀ ≤ 2 * sx) (hB0' : 0 ≤ B₀)
    (hWP : 0 < WP) (hWQ : 0 < WQ) (hNP : 0 ≤ NP) (hNQ : 0 ≤ NQ) :
    2 * (h + 1) * (2 * h + 1) * (B₀ * (WP * WQ) * (WP + WQ + 1) + 2 * (WP * WQ) * NP * NQ)
        / ((WP * WQ) ^ 2 * h ^ 2 * sx)
      ≤ 24 * (1 / WQ + 1 / WP + 1 / (WP * WQ)) + 24 * (NP * NQ) / (WP * WQ * sx) := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hW : (0 : ℝ) < WP * WQ := mul_pos hWP hWQ
  have hden : (0 : ℝ) < (WP * WQ) ^ 2 * h ^ 2 * sx := by positivity
  have hNN : (0 : ℝ) ≤ NP * NQ := mul_nonneg hNP hNQ
  have hnum0 : (0 : ℝ) ≤ B₀ * (WP * WQ) * (WP + WQ + 1) + 2 * (WP * WQ) * NP * NQ := by
    have h1 : (0 : ℝ) ≤ B₀ * (WP * WQ) * (WP + WQ + 1) := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (WP * WQ) * NP * NQ := by positivity
    linarith
  -- step one: the prefactor
  have hpre : 2 * (h + 1) * (2 * h + 1) ≤ 12 * h ^ 2 := by nlinarith [hh]
  have hstep1 : 2 * (h + 1) * (2 * h + 1)
        * (B₀ * (WP * WQ) * (WP + WQ + 1) + 2 * (WP * WQ) * NP * NQ)
      ≤ 12 * h ^ 2 * (B₀ * (WP * WQ) * (WP + WQ + 1) + 2 * (WP * WQ) * NP * NQ) :=
    mul_le_mul_of_nonneg_right hpre hnum0
  have hdiv1 : 2 * (h + 1) * (2 * h + 1)
        * (B₀ * (WP * WQ) * (WP + WQ + 1) + 2 * (WP * WQ) * NP * NQ)
        / ((WP * WQ) ^ 2 * h ^ 2 * sx)
      ≤ 12 * h ^ 2 * (B₀ * (WP * WQ) * (WP + WQ + 1) + 2 * (WP * WQ) * NP * NQ)
        / ((WP * WQ) ^ 2 * h ^ 2 * sx) := by
    gcongr
  refine hdiv1.trans ?_
  -- step two: cancel h² and one factor of WP*WQ
  have hval : 12 * h ^ 2 * (B₀ * (WP * WQ) * (WP + WQ + 1) + 2 * (WP * WQ) * NP * NQ)
        / ((WP * WQ) ^ 2 * h ^ 2 * sx)
      = 12 * (B₀ * (WP + WQ + 1) + 2 * (NP * NQ)) / (WP * WQ * sx) := by
    field_simp
    try ring
  rw [hval]
  -- step three
  have hstep3 : 12 * (B₀ * (WP + WQ + 1) + 2 * (NP * NQ))
      ≤ 12 * (2 * sx * (WP + WQ + 1) + 2 * (NP * NQ)) := by
    have hWs : (0 : ℝ) ≤ WP + WQ + 1 := by linarith
    nlinarith [hB0, hWs, hNN]
  have hdiv3 : 12 * (B₀ * (WP + WQ + 1) + 2 * (NP * NQ)) / (WP * WQ * sx)
      ≤ 12 * (2 * sx * (WP + WQ + 1) + 2 * (NP * NQ)) / (WP * WQ * sx) := by
    gcongr
  refine hdiv3.trans (le_of_eq ?_)
  field_simp
  try ring

/-! ## The variance row vanishes -/

/-- The window length is monotone in the exponent. -/
theorem cardLength_mono_exp {β b x : ℝ} (hβb : β ≤ b) (hx : 1 ≤ Real.log x) :
    cardLength β x ≤ cardLength b x := by
  rw [cardLength, cardLength]
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hx hβb)

/-- **Both designated ranges are negligible against the index range.** -/
theorem tendsto_jointCards_div_sqrt {β a b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβb : β ≤ b)
    (hb0 : 0 < b) (hb1 : b < 1) (ha0 : 0 < a) (hab : a < b) :
    Tendsto (fun x : ℝ =>
      ((jointShortSet β x).card : ℝ) * ((jointLongSet a b x).card : ℝ) / Real.sqrt x)
      atTop (𝓝 0) := by
  have hγ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hγ1 : (1 : ℝ) / 2 < 1 := by norm_num
  have hγβ : (1 : ℝ) / 2 * β < 1 := by nlinarith
  have hδ0 : (0 : ℝ) < a / b := div_pos ha0 hb0
  have hδ1 : a / b < 1 := (div_lt_one hb0).2 hab
  have habb : a / b * b = a := div_mul_cancel₀ a (ne_of_gt hb0)
  have hδβ : a / b * b < 1 := by rw [habb]; linarith
  have hmaj := (tendsto_cardLength_sq_div_sqrt hb0 hb1).const_mul (4 : ℝ)
  rw [mul_zero] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_gt_atTop (1 : ℝ),
      eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ,
      eventually_ladderTop_facts hb0 hδ0 hδ1 hδβ] with x hlog1 hx1 hshort hlong
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hcb : (1 : ℝ) ≤ cardLength b x := by
      rw [cardLength]
      refine Real.one_le_exp ?_
      positivity
    have hP : ((jointShortSet β x).card : ℝ) ≤ 2 * cardLength b x := by
      refine (card_primesRange_le _ _).trans ?_
      have h2 : cardLength β x ≤ cardLength b x := cardLength_mono_exp hβb hlog1
      linarith [hshort.2.1]
    have hQ : ((jointLongSet a b x).card : ℝ) ≤ 2 * cardLength b x := by
      refine (card_primesRange_le _ _).trans ?_
      linarith [hlong.2.1]
    have hP0 : (0 : ℝ) ≤ ((jointShortSet β x).card : ℝ) := Nat.cast_nonneg _
    have hQ0 : (0 : ℝ) ≤ ((jointLongSet a b x).card : ℝ) := Nat.cast_nonneg _
    have hprod : ((jointShortSet β x).card : ℝ) * ((jointLongSet a b x).card : ℝ)
        ≤ 4 * cardLength b x ^ 2 := by nlinarith [hP, hQ, hP0, hQ0, hcb]
    rw [div_le_iff₀ hsx]
    have hfin : 4 * (cardLength b x ^ 2 / Real.sqrt x) * Real.sqrt x
        = 4 * cardLength b x ^ 2 := by
      field_simp
    rw [hfin]
    exact hprod
end

end RHTower.Sieve
