import GaloisForLFunctions.RHTower.XiLogDerivRePositiveRightOfStrip
import GaloisForLFunctions.RHTower.XiLogDerivZeroFreePositive

/-!
# The sharp unconditional region of Hadamard positivity

`Re (ξ'/ξ)(s) ≥ 0` for `Re s > ½` is an exact receiver for the Riemann Hypothesis.  In the
line-conjugate pairing the negative set of a single pair is exactly the open disk of radius
`|Re ρ - ½| < ½` centred at `½ + i Im ρ`, so **only copies whose ordinate lies within `½` of
`Im s` can obstruct positivity** — a bounded window, independent of the height.

Two unconditional consequences follow at once.

* Every copy has `|Im ρ| > 4.5`, so for `|Im s| ≤ 4` the window is empty: positivity holds on the
  **whole rectangle** `Re s > ½`, `|Im s| ≤ 4`.
* Inside the window `|γ| < |Im s| + ½`, so the zero-free region gives
  `|Re ρ - ½| ≤ ½ - 1/(58 log(|Im s| + ½)) ≤ Re s - ½`: positivity holds on
  `Re s ≥ 1 - 1/(58 log(|Im s| + ½))`.

The second is strictly wider than the region obtained from the reflection pairing `ρ ↦ 1 - ρ`,
whose far regime only reaches ordinate `4(|Im s| + 1)`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Every divisor copy has ordinate above `4.5`. -/
theorem four_half_lt_abs_im_of_xiZeroCopy (q : XiZeroCopy) : 4.5 < |(q.1 : ℂ).im| := by
  have h := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have habs : |(q.1 : ℂ).im| ^ 2 = ((q.1 : ℂ).im) ^ 2 := sq_abs _
  nlinarith [abs_nonneg ((q.1 : ℂ).im), habs, h]

/-- **The disk engine.**  If every line-conjugate pair lies outside its off-line disk then the
completed logarithmic derivative has nonnegative real part. -/
theorem re_logDeriv_xi_nonneg_of_disk {s : ℂ} (hx : 1 / 2 < s.re) (hs : xi s ≠ 0)
    (hdisk : ∀ q : XiZeroCopy,
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 + (s.im - (q.1 : ℂ).im) ^ 2) :
    0 ≤ (logDeriv xi s).re := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [logDeriv_xi_eq_partialFraction hs]
  refine centralPaired_tsum_re_nonneg_of_lineConj_pairs _ ?_ ?_
  · have h := XiAtlasFinitePart.summable_logDerivTerm hs
    refine h.congr (fun q => ?_)
    show (XiAtlasFinitePart.xiZero q - 1 / 2)⁻¹ - (XiAtlasFinitePart.xiZero q - s)⁻¹ =
      ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹
    rw [XiAtlasFinitePart.xiZero, show ((q.1 : ℂ) - s) = -(s - (q.1 : ℂ)) by ring, inv_neg]
    ring
  · intro q
    obtain ⟨hb0, hb1⟩ := xi_divisor_support_re_mem_open_unit q.1
    have hxiq : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
    have hρ' := xiZero_lineConj_eq q
    have hcenter : (((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2) =
        -((starRingEnd ℂ) ((q.1 : ℂ) - 1 / 2)) := by
      rw [hρ', map_sub, hhalf]; ring
    have hconst : ((((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹).re =
        -((((q.1 : ℂ)) - 1 / 2)⁻¹).re := by
      rw [hcenter, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
    have h1 : s - (q.1 : ℂ) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hcon
      rw [hcon] at hs
      exact hs hxiq
    have h2 : s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hcon
      have hxic : xi (1 - (starRingEnd ℂ) ((q.1 : ℂ))) = 0 := by
        rw [← hρ']
        exact xi_eq_zero_of_mem_divisor_support (xiZeroCopyLineConjEquiv q).1
      rw [hcon] at hs
      exact hs hxic
    have hpos := re_inv_add_re_inv_lineConj_pos (s := s) (ρ := (q.1 : ℂ)) h1 h2 hx (hdisk q)
    have hrw : s - (((xiZeroCopyLineConjEquiv q).1 : ℂ)) =
        s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) := by rw [hρ']
    simp only [Complex.add_re]
    rw [hconst, hrw]
    linarith [hpos]

/-- **The window engine.**  Only copies whose ordinate is within `½` of `Im s` can obstruct. -/
theorem re_logDeriv_xi_nonneg_of_window {s : ℂ} (hx : 1 / 2 < s.re) (hs : xi s ≠ 0)
    (hnear : ∀ q : XiZeroCopy, |s.im - (q.1 : ℂ).im| < 1 / 2 →
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 + (s.im - (q.1 : ℂ).im) ^ 2) :
    0 ≤ (logDeriv xi s).re := by
  refine re_logDeriv_xi_nonneg_of_disk hx hs (fun q => ?_)
  rcases lt_or_ge |s.im - (q.1 : ℂ).im| (1 / 2) with hnearq | hfar
  · exact hnear q hnearq
  · have hstrip := xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hsq : (1 : ℝ) / 4 ≤ (s.im - (q.1 : ℂ).im) ^ 2 := by
      nlinarith [hfar, abs_nonneg (s.im - (q.1 : ℂ).im), sq_abs (s.im - (q.1 : ℂ).im)]
    nlinarith [hstrip, hsq, sq_nonneg (s.re - 1 / 2)]

/-- **Unconditional positivity on the whole low-height rectangle.**  Every copy has ordinate above
`4.5`, so for `|Im s| ≤ 4` the obstruction window is empty. -/
theorem re_logDeriv_xi_nonneg_of_abs_im_le_four {s : ℂ} (hx : 1 / 2 < s.re) (ht : |s.im| ≤ 4) :
    0 ≤ (logDeriv xi s).re := by
  have hs : xi s ≠ 0 := by
    intro hzero
    have hq : (41 : ℝ) / 2 < (s.im) ^ 2 := fortyOne_div_two_lt_im_sq_of_xi_eq_zero hzero
    nlinarith [ht, abs_nonneg s.im, sq_abs s.im, hq]
  refine re_logDeriv_xi_nonneg_of_window hx hs (fun q hnear => ?_)
  exfalso
  have hg := four_half_lt_abs_im_of_xiZeroCopy q
  have h1 : |(q.1 : ℂ).im| - |s.im| ≤ |s.im - (q.1 : ℂ).im| := by
    have := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) s.im
    rwa [abs_sub_comm ((q.1 : ℂ).im) s.im] at this
  linarith

/-- **Unconditional positivity on the zero-free region, sharp form.**  Inside the obstruction
window `|γ| < |Im s| + ½`, so the region's displacement bound applies with that height. -/
theorem re_logDeriv_xi_nonneg_of_zeroFree_sharp {s : ℂ} (hx : 1 / 2 < s.re) (ht : 4 < |s.im|)
    (hreg : 1 - 1 / 58 / Real.log (|s.im| + 1 / 2) ≤ s.re) :
    0 ≤ (logDeriv xi s).re := by
  have hlog4 : 1 < Real.log 4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_gt_d9
    rw [h2]; linarith
  have hL : 1 < Real.log (|s.im| + 1 / 2) :=
    lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hL0 : 0 < Real.log (|s.im| + 1 / 2) := by linarith
  have hs : xi s ≠ 0 := by
    intro hzero
    have h0 : 0 < s.re := by linarith
    have hlt1 : s.re < 1 := by
      by_contra hcon
      exact xi_ne_zero_of_one_le_re (not_lt.mp hcon) hzero
    have hne1 : s ≠ 1 := by
      intro h
      rw [h] at hlt1
      simp at hlt1
    have hz : riemannZeta s = 0 := (xi_eq_zero_iff h0 hne1).mp hzero
    have hup := re_le_one_sub_of_zeta_zero h0 hlt1 hz
    have hlogs : Real.log |s.im| < Real.log (|s.im| + 1 / 2) :=
      Real.log_lt_log (by linarith) (by linarith)
    have hlogs0 : 0 < Real.log |s.im| :=
      lt_trans zero_lt_one (lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (le_of_lt ht)))
    have hcmp : 1 / 58 / Real.log (|s.im| + 1 / 2) < 1 / 58 / Real.log |s.im| := by
      rw [div_div, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlogs, hlogs0]
    linarith
  refine re_logDeriv_xi_nonneg_of_window hx hs (fun q hnear => ?_)
  have hg := four_half_lt_abs_im_of_xiZeroCopy q
  have hglog : 1 < Real.log |(q.1 : ℂ).im| :=
    lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hglog0 : 0 < Real.log |(q.1 : ℂ).im| := by linarith
  have hin : |(q.1 : ℂ).im| < |s.im| + 1 / 2 := by
    have h1 : |(q.1 : ℂ).im| - |s.im| ≤ |s.im - (q.1 : ℂ).im| := by
      have := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) s.im
      rwa [abs_sub_comm ((q.1 : ℂ).im) s.im] at this
    linarith
  have hlogle : Real.log |(q.1 : ℂ).im| < Real.log (|s.im| + 1 / 2) :=
    Real.log_lt_log (by linarith) hin
  have hcmp : 1 / 58 / Real.log (|s.im| + 1 / 2) < 1 / 58 / Real.log |(q.1 : ℂ).im| := by
    rw [div_div, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hlogle, hglog0, hL0]
  have hzf := abs_re_sub_half_le_of_xiZeroCopy q
  have hbound : |(q.1 : ℂ).re - 1 / 2| < s.re - 1 / 2 := by linarith
  nlinarith [hbound, abs_nonneg ((q.1 : ℂ).re - 1 / 2), sq_abs ((q.1 : ℂ).re - 1 / 2),
    sq_nonneg (s.im - (q.1 : ℂ).im)]

end

end RHTower
