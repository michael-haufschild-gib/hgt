import GaloisForLFunctions.RHTower.XiLogDerivReFalsification

/-!
# The criterion throughout a zero-free region

Ordinate locality says only the divisor copies within `1/2` of `Im s` can obstruct.  If those
copies all have off-line displacement at most `w`, and `s` lies strictly further than `w` from the
critical line, the criterion holds at `s`.

Instantiating `w` with the half-width of a zero-free region turns this into: the criterion holds
**throughout any zero-free region**, at every height.  Unlike the low-height box, the region so
obtained is unbounded in the ordinate — it is narrow rather than short.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Window-width form of the criterion.**  If every divisor copy in the unit ordinate window
around `Im s` has off-line displacement at most `w`, and `s` lies strictly further than `w` from
the critical line, then the criterion holds at `s`.

Instantiating `w` with the half-width of a zero-free region at height `Im s` gives the criterion
throughout that region, at every height: taking `w = 1/2 - Z` for a zero-free region
`Re ρ ≤ 1 - Z` valid in the window, the conclusion holds for `Re s > 1 - Z`. -/
theorem re_logDeriv_xi_nonneg_of_window_width {s : ℂ} (hs : 1 / 2 < s.re) {w : ℝ}
    (hw : ∀ q : XiZeroCopy, |s.im - ((q.1 : ℂ)).im| < 1 / 2 →
      |((q.1 : ℂ)).re - 1 / 2| ≤ w)
    (hsw : w < s.re - 1 / 2) :
    0 ≤ (logDeriv xi s).re := by
  by_cases hxi : xi s = 0
  · rw [logDeriv_xi_eq_zero_of_xi_eq_zero hxi]; simp
  refine re_logDeriv_xi_nonneg_of_near_zeros hs hxi (fun q hy => ?_)
  have hyabs : |s.im - ((q.1 : ℂ)).im| < 1 / 2 := by
    nlinarith [sq_abs (s.im - ((q.1 : ℂ)).im), abs_nonneg (s.im - ((q.1 : ℂ)).im)]
  have hq := hw q hyabs
  have hw0 : 0 ≤ w := le_trans (abs_nonneg _) hq
  have habs : |((q.1 : ℂ)).re - 1 / 2| < s.re - 1 / 2 := lt_of_le_of_lt hq hsw
  have hsq : (((q.1 : ℂ)).re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 := by
    rw [← sq_abs (((q.1 : ℂ)).re - 1 / 2), ← sq_abs (s.re - 1 / 2)]
    have h1 : (0 : ℝ) ≤ |((q.1 : ℂ)).re - 1 / 2| := abs_nonneg _
    have h2 : |s.re - 1 / 2| = s.re - 1 / 2 := abs_of_pos (by linarith)
    rw [h2]
    nlinarith
  nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)]

/-- **Zero-free width form.**  A zero-free region of half-width `Z` valid throughout the unit
ordinate window around `Im s` gives the criterion for every abscissa inside it. -/
theorem re_logDeriv_xi_nonneg_of_local_zero_free {s : ℂ} {Z : ℝ} (_hZ0 : 0 < Z) (hZ1 : Z ≤ 1 / 2)
    (hfree : ∀ q : XiZeroCopy, |s.im - ((q.1 : ℂ)).im| < 1 / 2 →
      ((q.1 : ℂ)).re ≤ 1 - Z ∧ Z ≤ ((q.1 : ℂ)).re)
    (hs : 1 - Z < s.re) :
    0 ≤ (logDeriv xi s).re := by
  refine re_logDeriv_xi_nonneg_of_window_width (w := 1 / 2 - Z) (by linarith) (fun q hy => ?_)
    (by linarith)
  obtain ⟨hup, hlow⟩ := hfree q hy
  rw [abs_le]
  constructor <;> linarith

end

end RHTower
