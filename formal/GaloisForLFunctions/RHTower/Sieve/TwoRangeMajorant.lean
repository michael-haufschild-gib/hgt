import GaloisForLFunctions.RHTower.Sieve.TwoRangeSchedule
import GaloisForLFunctions.RHTower.Sieve.AnnulusRelBound

/-!
# The Route-T relative majorant at the two-range schedule

`Sieve/AnnulusRelBound.relScaledMajorant` has five summands.  At the schedule
`D = (log x)^{b+A₃+1}`, `Lx = log 2 + (log x)^b`, `t₀ = (log x)^{4b+3A₃+3}` three of them are
negative powers of the logarithm outright; the other two carry the only arithmetic in the whole
estimate — the zero-free-region factor `e^{−μq}` and the bottom `√xmin` of the high range — and are
handed in as limit hypotheses.

The two schedule parameters are forced in order: `D` by the term `(log 2 + Lx)/D`, then `t₀` by
`Ctot·D²·Lx²/(2π t₀)`.  Nothing else constrains them, which is why both stay polylogarithmic.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

private theorem div_le_div_rgt {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  have hnn : (0 : ℝ) ≤ (b - a) / c := div_nonneg (by linarith) hc.le
  have hdiff : (b - a) / c = b / c - a / c := by ring
  rw [hdiff] at hnn
  linarith

/-- The height of the Route-T contour at the schedule. -/
def twoRangeT₀ (b A₃ x : ℝ) : ℝ := (Real.log x) ^ (4 * b + 3 * A₃ + 3)

theorem twoRangeT₀_pos {b A₃ x : ℝ} (hx : 1 < x) : 0 < twoRangeT₀ b A₃ x :=
  Real.rpow_pos_of_pos (Real.log_pos hx) _

/-- The elementary majorant of the five summands. -/
def twoRangeMajTerms (b A₃ Ctot : ℝ) (μ q xmin : ℝ → ℝ) (x : ℝ) : ℝ :=
  Ctot / (2 * Real.pi)
      * (4 * (Real.log x) ^ (-A₃ - 1)
        + (Real.log x) ^ (2 * b + 2 * A₃ + 4) * Real.exp (-(μ x * q x))
        + (Real.log x) ^ (-(6 * b + 4 * A₃ + 2)))
    + 3 * (Real.log x) ^ (-A₃ - 1)
    + 4 * ((Real.log x) ^ b / Real.sqrt (xmin x))

/-- **The relative majorant, term by term.** -/
theorem relScaledMajorant_le_twoRangeMajTerms {b A₃ Ctot : ℝ} (hb : 0 < b) (_hA₃ : 0 < A₃)
    (hC : 0 ≤ Ctot) {Hmaj μ q xmin : ℝ → ℝ}
    (hH : ∀ᶠ x : ℝ in atTop, 0 ≤ Hmaj x ∧ Hmaj x ≤ (Real.log x) ^ (2 : ℝ))
    (hxpos : ∀ᶠ x : ℝ in atTop, 0 < xmin x) :
    ∀ᶠ x : ℝ in atTop,
      relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x) (Hmaj x) (μ x) (q x)
          (twoRangeT₀ b A₃ x) (xmin x)
        ≤ twoRangeMajTerms b A₃ Ctot μ q xmin x := by
  have hpowb : Tendsto (fun x : ℝ => (Real.log x) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb).comp Real.tendsto_log_atTop
  filter_upwards [hH, hxpos, Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
    hpowb.eventually_ge_atTop (Real.log 2)] with x hHx hxp hx1 hlogbig hlog2
  obtain ⟨hH0, hHle⟩ := hHx
  set L : ℝ := Real.log x with hLdef
  have hL0 : (0 : ℝ) < L := Real.log_pos hx1
  have hL1 : (1 : ℝ) ≤ L := by
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpb : (0 : ℝ) < L ^ b := Real.rpow_pos_of_pos hL0 b
  have hLxle : twoRangeLx b x ≤ 2 * L ^ b := by
    rw [twoRangeLx]; linarith
  have hLx0 : (0 : ℝ) ≤ twoRangeLx b x := by
    rw [twoRangeLx]; linarith
  have hD : twoRangeWidth b A₃ x = L ^ (b + A₃ + 1) := rfl
  have hD0 : (0 : ℝ) < L ^ (b + A₃ + 1) := Real.rpow_pos_of_pos hL0 _
  have hT : twoRangeT₀ b A₃ x = L ^ (4 * b + 3 * A₃ + 3) := rfl
  have hT0 : (0 : ℝ) < L ^ (4 * b + 3 * A₃ + 3) := Real.rpow_pos_of_pos hL0 _
  have hsq : (0 : ℝ) < Real.sqrt (xmin x) := Real.sqrt_pos.2 hxp
  -- the five summands
  have e1 : twoRangeLx b x ^ 2 / twoRangeT₀ b A₃ x ≤ 4 * L ^ (-(2 * b) - 3 * A₃ - 3) := by
    rw [hT]
    have hnum : twoRangeLx b x ^ 2 ≤ 4 * L ^ (2 * b) := by
      have : L ^ (2 * b) = L ^ b * L ^ b := by
        rw [← Real.rpow_add hL0]; congr 1; ring
      nlinarith [hLxle, hLx0, hpb]
    have hid : 4 * L ^ (2 * b) / L ^ (4 * b + 3 * A₃ + 3) = 4 * L ^ (-(2 * b) - 3 * A₃ - 3) := by
      rw [mul_div_assoc, ← Real.rpow_sub hL0]
      congr 2
      ring
    calc twoRangeLx b x ^ 2 / L ^ (4 * b + 3 * A₃ + 3)
        ≤ 4 * L ^ (2 * b) / L ^ (4 * b + 3 * A₃ + 3) := by
          exact div_le_div_rgt hnum hT0
      _ = 4 * L ^ (-(2 * b) - 3 * A₃ - 3) := hid
  have hDsq : twoRangeWidth b A₃ x ^ 2 = L ^ (2 * b + 2 * A₃ + 2) := by
    rw [hD, ← Real.rpow_natCast (L ^ (b + A₃ + 1)) 2, ← Real.rpow_mul hL0.le]
    congr 1
    push_cast
    ring
  have hDsq0 : (0 : ℝ) ≤ twoRangeWidth b A₃ x ^ 2 := by positivity
  have e3 : Hmaj x / twoRangeT₀ b A₃ x ^ 2 ≤ L ^ (2 - (8 * b + 6 * A₃ + 6)) := by
    have hT2 : twoRangeT₀ b A₃ x ^ 2 = L ^ (8 * b + 6 * A₃ + 6) := by
      rw [hT, ← Real.rpow_natCast (L ^ (4 * b + 3 * A₃ + 3)) 2, ← Real.rpow_mul hL0.le]
      congr 1
      push_cast
      ring
    rw [hT2]
    have hT20 : (0 : ℝ) < L ^ (8 * b + 6 * A₃ + 6) := Real.rpow_pos_of_pos hL0 _
    calc Hmaj x / L ^ (8 * b + 6 * A₃ + 6)
        ≤ L ^ (2 : ℝ) / L ^ (8 * b + 6 * A₃ + 6) := div_le_div_rgt hHle hT20
      _ = L ^ (2 - (8 * b + 6 * A₃ + 6)) := by rw [← Real.rpow_sub hL0]
  have e4 : (Real.log 2 + twoRangeLx b x) / twoRangeWidth b A₃ x ≤ 3 * L ^ (-A₃ - 1) := by
    rw [hD]
    have hnum : Real.log 2 + twoRangeLx b x ≤ 3 * L ^ b := by
      rw [twoRangeLx]; linarith
    have hid : 3 * L ^ b / L ^ (b + A₃ + 1) = 3 * L ^ (-A₃ - 1) := by
      rw [mul_div_assoc, ← Real.rpow_sub hL0]
      congr 2
      ring
    calc (Real.log 2 + twoRangeLx b x) / L ^ (b + A₃ + 1)
        ≤ 3 * L ^ b / L ^ (b + A₃ + 1) := div_le_div_rgt hnum hD0
      _ = 3 * L ^ (-A₃ - 1) := hid
  have e5 : 2 * twoRangeLx b x / Real.sqrt (xmin x) ≤ 4 * (L ^ b / Real.sqrt (xmin x)) := by
    have hnum : 2 * twoRangeLx b x ≤ 4 * L ^ b := by linarith
    calc 2 * twoRangeLx b x / Real.sqrt (xmin x)
        ≤ 4 * L ^ b / Real.sqrt (xmin x) := div_le_div_rgt hnum hsq
      _ = 4 * (L ^ b / Real.sqrt (xmin x)) := by ring
  -- assemble
  rw [relScaledMajorant, twoRangeMajTerms]
  have hexp0 : (0 : ℝ) < Real.exp (-(μ x * q x)) := Real.exp_pos _
  have hkey : twoRangeWidth b A₃ x ^ 2
        * (twoRangeLx b x ^ 2 / twoRangeT₀ b A₃ x
          + Hmaj x * (Real.exp (-(μ x * q x)) + 1 / twoRangeT₀ b A₃ x ^ 2))
      ≤ 4 * L ^ (-A₃ - 1)
        + L ^ (2 * b + 2 * A₃ + 4) * Real.exp (-(μ x * q x))
        + L ^ (-(6 * b + 4 * A₃ + 2)) := by
    have hA : twoRangeWidth b A₃ x ^ 2 * (twoRangeLx b x ^ 2 / twoRangeT₀ b A₃ x)
        ≤ 4 * L ^ (-A₃ - 1) := by
      have hstep := mul_le_mul_of_nonneg_left e1 hDsq0
      refine hstep.trans (le_of_eq ?_)
      rw [hDsq, ← mul_assoc, mul_comm (L ^ (2 * b + 2 * A₃ + 2)) (4 : ℝ), mul_assoc,
        ← Real.rpow_add hL0]
      congr 2
      ring
    have hB : twoRangeWidth b A₃ x ^ 2 * (Hmaj x * Real.exp (-(μ x * q x)))
        ≤ L ^ (2 * b + 2 * A₃ + 4) * Real.exp (-(μ x * q x)) := by
      have hstep : Hmaj x * Real.exp (-(μ x * q x))
          ≤ L ^ (2 : ℝ) * Real.exp (-(μ x * q x)) :=
        mul_le_mul_of_nonneg_right hHle hexp0.le
      have := mul_le_mul_of_nonneg_left hstep hDsq0
      refine this.trans (le_of_eq ?_)
      rw [hDsq, ← mul_assoc, ← Real.rpow_add hL0]
      congr 2
      ring
    have hCc : twoRangeWidth b A₃ x ^ 2 * (Hmaj x * (1 / twoRangeT₀ b A₃ x ^ 2))
        ≤ L ^ (-(6 * b + 4 * A₃ + 2)) := by
      have hid : Hmaj x * (1 / twoRangeT₀ b A₃ x ^ 2) = Hmaj x / twoRangeT₀ b A₃ x ^ 2 := by
        ring
      rw [hid]
      have := mul_le_mul_of_nonneg_left e3 hDsq0
      refine this.trans (le_of_eq ?_)
      rw [hDsq, ← Real.rpow_add hL0]
      congr 1
      ring
    have hexpand : twoRangeWidth b A₃ x ^ 2
          * (twoRangeLx b x ^ 2 / twoRangeT₀ b A₃ x
            + Hmaj x * (Real.exp (-(μ x * q x)) + 1 / twoRangeT₀ b A₃ x ^ 2))
        = twoRangeWidth b A₃ x ^ 2 * (twoRangeLx b x ^ 2 / twoRangeT₀ b A₃ x)
          + twoRangeWidth b A₃ x ^ 2 * (Hmaj x * Real.exp (-(μ x * q x)))
          + twoRangeWidth b A₃ x ^ 2 * (Hmaj x * (1 / twoRangeT₀ b A₃ x ^ 2)) := by ring
    rw [hexpand]
    linarith [hA, hB, hCc]
  have hCnn : (0 : ℝ) ≤ Ctot / (2 * Real.pi) := by
    have := Real.pi_pos
    positivity
  have hmain := mul_le_mul_of_nonneg_left hkey hCnn
  have hrw : Ctot * twoRangeWidth b A₃ x ^ 2
        * (twoRangeLx b x ^ 2 / twoRangeT₀ b A₃ x
          + Hmaj x * (Real.exp (-(μ x * q x)) + 1 / twoRangeT₀ b A₃ x ^ 2)) / (2 * Real.pi)
      = Ctot / (2 * Real.pi) * (twoRangeWidth b A₃ x ^ 2
          * (twoRangeLx b x ^ 2 / twoRangeT₀ b A₃ x
            + Hmaj x * (Real.exp (-(μ x * q x)) + 1 / twoRangeT₀ b A₃ x ^ 2))) := by ring
  rw [hrw]
  have h2b : (2 : ℝ) - (8 * b + 6 * A₃ + 6) = -(6 * b + 4 * A₃ + 2) - 2 * b - 2 * A₃ - 2 := by
    ring
  linarith [hmain, e4, e5]

end

end RHTower.Sieve
