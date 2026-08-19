import GaloisForLFunctions.RHTower.Sieve.JointSchedule
import GaloisForLFunctions.RHTower.Sieve.NonSpectralBudget
import GaloisForLFunctions.RHTower.Sieve.ScaledBudgetGeometry
import GaloisForLFunctions.RHTower.Sieve.RoughRemainderLimit

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
  have hmaj := (tendsto_cardLength_sq_div_sqrt hb0 hb1).const_mul (4 : ℝ)
  rw [mul_zero] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_gt_atTop (1 : ℝ),
      eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ,
      jointLongTopF_le ha0 hab] with x hlog1 hx1 hshort hlong
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
      linarith [hlong]
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
/-- **The variance row of the joint budget vanishes.** -/
theorem tendsto_jointVarianceRow {c β a b : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβb : β ≤ b) (hb0 : 0 < b) (hb1 : b < 1) (ha0 : 0 < a) (hab : a < b) :
    Tendsto (fun x : ℝ =>
      2 * (scaledLength c β x + 1) * (2 * scaledLength c β x + 1)
        * (((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
              * (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x))
              * (Joint.mass (jointShortSet β x) + Joint.mass (jointLongSet a b x) + 1)
            + 2 * (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x))
                * ((jointShortSet β x).card : ℝ) * ((jointLongSet a b x).card : ℝ))
      / ((Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)) ^ 2
          * scaledLength c β x ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
  have hWP := tendsto_jointShortMass hβ0 hβ1
  have hWQ := tendsto_jointLongMass ha0 hab
  have hinvP : Tendsto (fun x : ℝ => 1 / Joint.mass (jointShortSet β x)) atTop (𝓝 0) := by
    refine (hWP.inv_tendsto_atTop).congr fun x => ?_
    rw [Pi.inv_apply, ← one_div]
  have hinvQ : Tendsto (fun x : ℝ => 1 / Joint.mass (jointLongSet a b x)) atTop (𝓝 0) := by
    refine (hWQ.inv_tendsto_atTop).congr fun x => ?_
    rw [Pi.inv_apply, ← one_div]
  have hinvPQ : Tendsto (fun x : ℝ =>
      1 / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)))
      atTop (𝓝 0) := by
    refine ((hWP.atTop_mul_atTop₀ hWQ).inv_tendsto_atTop).congr fun x => ?_
    rw [Pi.inv_apply, ← one_div]
  have hcards := tendsto_jointCards_div_sqrt hβ0 hβ1 hβb hb0 hb1 ha0 hab
  have hcross : Tendsto (fun x : ℝ =>
      ((jointShortSet β x).card : ℝ) * ((jointLongSet a b x).card : ℝ)
        / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x) * Real.sqrt x))
      atTop (𝓝 0) := by
    have hmul := hcards.mul hinvPQ
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [hWP.eventually_gt_atTop 0, hWQ.eventually_gt_atTop 0,
      Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 hx1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    field_simp
  have hmaj : Tendsto (fun x : ℝ =>
      24 * (1 / Joint.mass (jointLongSet a b x) + 1 / Joint.mass (jointShortSet β x)
          + 1 / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)))
        + 24 * (((jointShortSet β x).card : ℝ) * ((jointLongSet a b x).card : ℝ))
            / (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)
              * Real.sqrt x)) atTop (𝓝 0) := by
    have h1 := ((hinvQ.add hinvP).add hinvPQ).const_mul (24 : ℝ)
    have h2 := hcross.const_mul (24 : ℝ)
    have hsum := h1.add h2
    rw [show (24 : ℝ) * (0 + 0 + 0) + 24 * 0 = 0 by ring] at hsum
    refine hsum.congr fun x => ?_
    ring
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hWP.eventually_gt_atTop 0, hWQ.eventually_gt_atTop 0,
      Filter.eventually_gt_atTop (1 : ℝ),
      (tendsto_scaledLength hc0 hβ0).eventually_ge_atTop (1 : ℝ)] with x h1 h2 hx1 hh1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hB0 : (0 : ℝ) ≤ ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hNP : (0 : ℝ) ≤ ((jointShortSet β x).card : ℝ) := Nat.cast_nonneg _
    have hNQ : (0 : ℝ) ≤ ((jointLongSet a b x).card : ℝ) := Nat.cast_nonneg _
    have hsl : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    positivity
  · filter_upwards [hWP.eventually_gt_atTop 0, hWQ.eventually_gt_atTop 0,
      Filter.eventually_gt_atTop (1 : ℝ),
      (tendsto_scaledLength hc0 hβ0).eventually_ge_atTop (1 : ℝ),
      scaledLength_le_sqrt hc1 hβ0 hβ1] with x h1 h2 hx1 hh1 hslsx
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hsl : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    have hB0le : ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
      have := Nat.floor_le (by positivity : (0:ℝ) ≤ Real.sqrt x + scaledLength c β x)
      linarith
    exact jointVariance_quotient_le hh1 hsx hB0le (Nat.cast_nonneg _) h1 h2
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ## The rounding row vanishes -/

/-- **The divisor bound for the joint weight is at most `(log x)²`.** -/
theorem jointDivisorBound_le {c β a b : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hab0 : 0 < a / b * b) (hβ20 : 0 < 1 / 2 * β) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
          / Real.log ((siftStart (1 / 2 * β) x : ℕ) : ℝ))
        * (Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
          / Real.log ((siftStart (a / b * b) x : ℕ) : ℝ))
      ≤ (Real.log x) ^ (2 : ℕ) := by
  have hP : Tendsto (fun x : ℝ => (Real.log x) ^ (1 / 2 * β)) atTop atTop :=
    (tendsto_rpow_atTop hβ20).comp Real.tendsto_log_atTop
  have hQ : Tendsto (fun x : ℝ => (Real.log x) ^ (a / b * b)) atTop atTop :=
    (tendsto_rpow_atTop hab0).comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ), hP.eventually_ge_atTop (1 : ℝ),
    hQ.eventually_ge_atTop (1 : ℝ), scaledLength_le_sqrt hc1 hβ0 hβ1,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log 2)] with x hx4 hP1 hQ1 hsl hlog2
  have hx1 : (1 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hlogP : (1 : ℝ) ≤ Real.log ((siftStart (1 / 2 * β) x : ℕ) : ℝ) :=
    le_trans hP1 (log_siftStart_ge _ x)
  have hlogQ : (1 : ℝ) ≤ Real.log ((siftStart (a / b * b) x : ℕ) : ℝ) :=
    le_trans hQ1 (log_siftStart_ge _ x)
  have hB0 : ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
    have hsl0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    have := Nat.floor_le (by linarith : (0 : ℝ) ≤ Real.sqrt x + scaledLength c β x)
    linarith
  have hsx2 : (2 : ℝ) ≤ Real.sqrt x := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x by linarith), Real.sqrt_nonneg x, hx4]
  have hsl0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
  have hfl : (1 : ℝ) ≤ ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) := by
    have h1 : 1 ≤ ⌊Real.sqrt x + scaledLength c β x⌋₊ := by
      refine Nat.le_floor ?_
      push_cast
      linarith
    exact_mod_cast h1
  have hlogB0 : (0 : ℝ) ≤ Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) :=
    Real.log_nonneg hfl
  have hlogB : Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) ≤ Real.log x := by
    refine (Real.log_le_log (by linarith) hB0).trans ?_
    rw [Real.log_mul (by norm_num) (ne_of_gt hsx), Real.log_sqrt (by linarith)]
    linarith
  have hdivP : Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
      / Real.log ((siftStart (1 / 2 * β) x : ℕ) : ℝ) ≤ Real.log x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hlogB, hlogP, hlogB0, Real.log_nonneg (le_of_lt hx1)]
  have hdivQ : Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
      / Real.log ((siftStart (a / b * b) x : ℕ) : ℝ) ≤ Real.log x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hlogB, hlogQ, hlogB0, Real.log_nonneg (le_of_lt hx1)]
  have hdivP0 : (0 : ℝ) ≤ Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
      / Real.log ((siftStart (1 / 2 * β) x : ℕ) : ℝ) := div_nonneg hlogB0 (by linarith)
  have hdivQ0 : (0 : ℝ) ≤ Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
      / Real.log ((siftStart (a / b * b) x : ℕ) : ℝ) := div_nonneg hlogB0 (by linarith)
  have hlx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (le_of_lt hx1)
  nlinarith [hdivP, hdivQ, hdivP0, hdivQ0, hlx]

/-- **A polylogarithm is negligible against the window squared.** -/
theorem tendsto_rpow_log_div_scaledLength_sq {c β : ℝ} (hc0 : 0 < c) (hβ0 : 0 < β) (d : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ d / scaledLength c β x ^ 2) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_log_div_scaledLength hc0 hβ0 d
  have h2 : Tendsto (fun x : ℝ => 1 / scaledLength c β x) atTop (𝓝 0) := by
    refine ((tendsto_scaledLength hc0 hβ0).inv_tendsto_atTop).congr fun x => ?_
    rw [Pi.inv_apply, ← one_div]
  have hmul := h1.mul h2
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
  have h0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
  field_simp

/-- **The rounding row of the joint budget vanishes.** -/
theorem tendsto_jointRoundingRow {c β a b : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hb0 : 0 < b) (hb1 : b < 1) (ha0 : 0 < a) (hab : a < b) :
    Tendsto (fun x : ℝ =>
      204 * ((Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
              / Real.log ((siftStart (1 / 2 * β) x : ℕ) : ℝ))
            * (Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
              / Real.log ((siftStart (a / b * b) x : ℕ) : ℝ))) ^ 2 * (Real.sqrt x + 1)
      / ((Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)) ^ 2
          * scaledLength c β x ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
  have hab0 : (0 : ℝ) < a / b * b := by
    rw [div_mul_cancel₀ a (ne_of_gt hb0)]; exact ha0
  have hβ20 : (0 : ℝ) < 1 / 2 * β := by linarith
  have hWP := tendsto_jointShortMass hβ0 hβ1
  have hWQ := tendsto_jointLongMass ha0 hab
  have hmaj := (tendsto_rpow_log_div_scaledLength_sq hc0 hβ0 (4 : ℝ)).const_mul (408 : ℝ)
  rw [mul_zero] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have h0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    positivity
  · filter_upwards [jointDivisorBound_le hc0 hc1 hβ0 hβ1 hab0 hβ20,
      hWP.eventually_ge_atTop (1 : ℝ), hWQ.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_ge_atTop (4 : ℝ)] with x hBd hP1 hQ1 hx4
    have hx1 : (1 : ℝ) < x := by linarith
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hsx1 : (1 : ℝ) ≤ Real.sqrt x := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x by linarith), Real.sqrt_nonneg x, hx4]
    have h0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    set Bd : ℝ := (Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
          / Real.log ((siftStart (1 / 2 * β) x : ℕ) : ℝ))
        * (Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ)
          / Real.log ((siftStart (a / b * b) x : ℕ) : ℝ)) with hBdef
    have hlx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (le_of_lt hx1)
    have hBd0 : (0 : ℝ) ≤ Bd := by
      rw [hBdef]
      have hlP : (0 : ℝ) ≤ Real.log ((siftStart (1 / 2 * β) x : ℕ) : ℝ) :=
        le_trans (Real.rpow_nonneg hlx _) (log_siftStart_ge _ x)
      have hlQ : (0 : ℝ) ≤ Real.log ((siftStart (a / b * b) x : ℕ) : ℝ) :=
        le_trans (Real.rpow_nonneg hlx _) (log_siftStart_ge _ x)
      have hfl : (1 : ℝ) ≤ ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) := by
        have h1 : 1 ≤ ⌊Real.sqrt x + scaledLength c β x⌋₊ := by
          refine Nat.le_floor ?_
          push_cast
          linarith
        exact_mod_cast h1
      have hlB : (0 : ℝ) ≤ Real.log ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) :=
        Real.log_nonneg hfl
      positivity
    have hBsq : Bd ^ 2 ≤ (Real.log x) ^ (4 : ℝ) := by
      have hstep : Bd ^ 2 ≤ ((Real.log x) ^ (2 : ℕ)) ^ 2 := by nlinarith [hBd, hBd0]
      have hval : ((Real.log x) ^ (2 : ℕ)) ^ 2 = (Real.log x) ^ (4 : ℝ) := by
        rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      rw [← hval]
      exact hstep
    have hW1 : (1 : ℝ) ≤ (Joint.mass (jointShortSet β x)
        * Joint.mass (jointLongSet a b x)) ^ 2 := by
      have := mul_le_mul hP1 hQ1 (by linarith) (by linarith)
      nlinarith [this]
    rw [div_le_iff₀ (by positivity)]
    have hfin : 408 * ((Real.log x) ^ (4 : ℝ) / scaledLength c β x ^ 2)
        * ((Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)) ^ 2
            * scaledLength c β x ^ 2 * Real.sqrt x)
        = 408 * (Real.log x) ^ (4 : ℝ)
            * ((Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)) ^ 2
              * Real.sqrt x) := by
      field_simp
    rw [hfin]
    have hleft : 204 * Bd ^ 2 * (Real.sqrt x + 1) ≤ 408 * (Real.log x) ^ (4 : ℝ) * Real.sqrt x := by
      have h1 : Real.sqrt x + 1 ≤ 2 * Real.sqrt x := by linarith
      nlinarith [hBsq, hBd0, hsx, h1, Real.rpow_nonneg hlx (4 : ℝ)]
    have hright : 408 * (Real.log x) ^ (4 : ℝ) * Real.sqrt x
        ≤ 408 * (Real.log x) ^ (4 : ℝ)
            * ((Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)) ^ 2
              * Real.sqrt x) := by
      have hp : (0 : ℝ) ≤ 408 * (Real.log x) ^ (4 : ℝ) := by
        have := Real.rpow_nonneg hlx (4 : ℝ)
        linarith
      have hstep : Real.sqrt x
          ≤ (Joint.mass (jointShortSet β x) * Joint.mass (jointLongSet a b x)) ^ 2
            * Real.sqrt x := by nlinarith [hW1, hsx]
      exact mul_le_mul_of_nonneg_left hstep hp
    linarith [hleft, hright]

end

end RHTower.Sieve
