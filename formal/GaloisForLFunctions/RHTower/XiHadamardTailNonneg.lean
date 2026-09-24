import GaloisForLFunctions.RHTower.XiLogDerivZeroFreePositive

/-!
# The Hadamard receiver has no tail obstruction

`Re (ξ'/ξ)(s) ≥ 0` for `Re s > ½` is an exact receiver for the Riemann Hypothesis.  Its
reflection-paired series is **unconditionally nonnegative on every copy of large ordinate**: with
`x = Re s - ½`, a copy of ordinate `γ` contributes a nonnegative paired term as soon as

```text
|γ| ≥ (|Im s| + 1)/x + 1,
```

with no zero-free region and no hypothesis on the copy's real part.  Consequently the sign of
`Re (ξ'/ξ)(s)` is decided by the finitely many copies below that height:

```text
∑_{|γ| < (|Im s|+1)/x + 1} (paired term) ≤ 2 Re (ξ'/ξ)(s).
```

The receiver therefore carries no tail difficulty at all; every obstruction to RH visible through
it is local in the height.
-/

open Complex

namespace RHTower

noncomputable section

/-- The height above which a copy contributes nonnegatively at `s`. -/
def hadamardTailHeight (s : ℂ) : ℝ := (|s.im| + 1) / (s.re - 1 / 2) + 1

/-- **Tail regime.**  Beyond the scaled height the numerator is nonnegative whatever the
displacement of the zero. -/
theorem pairedNumerator_nonneg_tail {x t a g : ℝ} (hx : 0 < x) (ha : |a| ≤ 1 / 2)
    (hg : (|t| + 1) / x + 1 ≤ |g|) :
    0 ≤ x * (x ^ 2 - a ^ 2) + x * (t ^ 2 + g ^ 2) - 2 * a * t * g := by
  have hT : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hGnn : (0 : ℝ) ≤ |g| := abs_nonneg g
  have hxG : |t| + 1 + x ≤ x * |g| := by
    have h := mul_le_mul_of_nonneg_left hg hx.le
    rw [mul_add, mul_one, mul_div_cancel₀ _ hx.ne'] at h
    linarith
  have hG1 : (1 : ℝ) ≤ |g| := by
    have h1 : (|t| + 1) / x ≥ 0 := by positivity
    linarith
  have hcross : 2 * a * t * g ≤ |t| * |g| := by
    have h1 : 2 * a * t * g ≤ |2 * a * t * g| := le_abs_self _
    have habs : |2 * a * t * g| = 2 * |a| * (|t| * |g|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      ring
    rw [habs] at h1
    nlinarith [h1, ha, mul_nonneg hT hGnn, abs_nonneg a]
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs a, abs_nonneg a, ha]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hg2 : g ^ 2 = |g| ^ 2 := (sq_abs g).symm
  have hmain : |t| * |g| + x / 4 ≤ x * (|t| ^ 2 + |g| ^ 2) := by
    have hkey : |t| * |g| + x / 4 ≤ x * |g| ^ 2 := by
      nlinarith [hxG, hG1, hGnn, hT, hx]
    nlinarith [hkey, sq_nonneg (|t|), hx]
  have hxx : -(x / 4) ≤ x * (x ^ 2 - a ^ 2) := by nlinarith [ha2, sq_nonneg x, hx]
  have hrw : x * (t ^ 2 + g ^ 2) = x * (|t| ^ 2 + |g| ^ 2) := by rw [ht2, hg2]
  linarith [hcross, hmain, hxx, hrw]

/-- **The paired resolvent term of a high copy is nonnegative, unconditionally.** -/
theorem xiPairedResolventTerm_nonneg_tail {s : ℂ} {q : XiZeroCopy}
    (hx : 0 < s.re - 1 / 2) (hs : xi s ≠ 0)
    (hg : hadamardTailHeight s ≤ |(q.1 : ℂ).im|) :
    0 ≤ xiPairedResolventTerm s q := by
  obtain ⟨hb0, hb1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hxiq : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
  have hA : (0 : ℝ) < normSq (s - (q.1 : ℂ)) := by
    refine Complex.normSq_pos.mpr (sub_ne_zero.mpr ?_)
    intro h
    rw [h] at hs
    exact hs hxiq
  have hB : (0 : ℝ) < normSq (s - (1 - (q.1 : ℂ))) := by
    refine Complex.normSq_pos.mpr (sub_ne_zero.mpr ?_)
    intro h
    rw [h] at hs
    exact hs (by rw [xi_one_sub]; exact hxiq)
  refine xiPairedResolventTerm_nonneg_of_numerator hA hB ?_
  have habs : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  exact pairedNumerator_nonneg_tail hx habs hg

/-- **The Hadamard receiver is decided below the tail height.**  The copies of ordinate at least
`hadamardTailHeight s` contribute nonnegatively, so the low part alone bounds `2 Re (ξ'/ξ)`. -/
theorem tsum_low_le_two_mul_re_logDeriv_xi {s : ℂ} (hx : 0 < s.re - 1 / 2) (hs : xi s ≠ 0) :
    (∑' q : ({q : XiZeroCopy | |(q.1 : ℂ).im| < hadamardTailHeight s} : Set XiZeroCopy),
        xiPairedResolventTerm s (q : XiZeroCopy))
      ≤ 2 * (logDeriv xi s).re := by
  classical
  set S : Set XiZeroCopy := {q : XiZeroCopy | |(q.1 : ℂ).im| < hadamardTailHeight s} with hS
  have hsum := summable_xiPairedResolventTerm hs
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl S
  have hcompl : 0 ≤ ∑' q : (Sᶜ : Set XiZeroCopy), xiPairedResolventTerm s (q : XiZeroCopy) := by
    refine tsum_nonneg (fun q => ?_)
    exact xiPairedResolventTerm_nonneg_tail hx hs (not_lt.mp q.2)
  rw [two_mul_re_logDeriv_xi_eq_tsum_paired hs, ← hsplit]
  linarith

/-- **Localization of the receiver.**  If the low part is nonnegative then so is `Re (ξ'/ξ)(s)`;
the tail can never obstruct. -/
theorem re_logDeriv_xi_nonneg_of_low_nonneg {s : ℂ} (hx : 0 < s.re - 1 / 2) (hs : xi s ≠ 0)
    (hlow : 0 ≤ ∑' q : ({q : XiZeroCopy | |(q.1 : ℂ).im| < hadamardTailHeight s} : Set XiZeroCopy),
        xiPairedResolventTerm s (q : XiZeroCopy)) :
    0 ≤ (logDeriv xi s).re := by
  have h := tsum_low_le_two_mul_re_logDeriv_xi hx hs
  linarith

end

end RHTower
