import GaloisForLFunctions.RHTower.XiLaguerreZeroSumIdentity
import GaloisForLFunctions.RHTower.XiLaguerrePolya
import GaloisForLFunctions.RHTower.XiHadamardSharpRegion
import GaloisForLFunctions.RHTower.XiResolventMassBudget
import GaloisForLFunctions.RHTower.XiFourthTraceExtendedCriticalLineBand

/-!
# The first Laguerre margin is a disk detector

The inverse-square divisor sum for the Laguerre expression of the centred completed zeta is an
identity between complex quantities.  On the real axis it becomes an identity for the Hardy
function: with `Ξ(t) ≠ 0`,

`(Ξ'(t))² − Ξ(t)Ξ''(t) = Ξ(t)² · Re Σ_q ((t − a_q)²)⁻¹`.

Writing the centred spectral point of a zero copy as `a_q = γ_q − i δ_q`, where `γ_q = Im ρ_q` and
`δ_q = Re ρ_q − 1/2`, the `q`-th real part is exactly

`((t − γ_q)² − δ_q²) / ((t − γ_q)² + δ_q²)²`,

so the atom is strictly positive precisely when the test height lies outside the open disk of
radius `|δ_q|` around `γ_q` on the real axis.  These are the same disks that obstruct the Hadamard
receiver `Re (ξ'/ξ) ≥ 0`; the Laguerre margin is its first-order trace on the critical line.

Two unconditional consequences follow.  The margin is strictly positive at any height whose unit
window contains only on-line copies — a local form of `RH ⟹ L₁ ≥ 0`, needing the hypothesis only
inside one window.  And since every copy has `|Im ρ| > 4.5` while `δ² < 1/4`, no disk reaches a
height with `|t| ≤ 4`, so the margin is strictly positive there with no hypothesis at all.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## The real-axis form of the divisor sum -/

/-- **Hardy-function form of the Laguerre identity.**  The complex identity
`laguerre_XiC_eq_tsum_inv_sq`, restricted to the real axis where `ΞC` is `Ξ`. -/
theorem laguerre_Xi_eq_tsum_inv_sq {t : ℝ} (ht : Xi t ≠ 0) :
    (deriv Xi t) ^ (2 : ℕ) - Xi t * deriv (deriv Xi) t
      = Xi t ^ (2 : ℕ)
        * (∑' q : XiZeroCopy, (((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re := by
  have hz : XiC (t : ℂ) ≠ 0 := by
    rw [XiC_ofReal]
    simpa using ht
  have h := laguerre_XiC_eq_tsum_inv_sq hz
  rw [XiC_ofReal, XiC_deriv_ofReal, XiC_secondDeriv_ofReal] at h
  have hre := congrArg Complex.re h
  have hleft : ((((deriv Xi t : ℝ) : ℂ)) ^ (2 : ℕ)
      - ((Xi t : ℝ) : ℂ) * (((deriv (deriv Xi) t : ℝ) : ℂ))).re
      = (deriv Xi t) ^ (2 : ℕ) - Xi t * deriv (deriv Xi) t := by
    rw [Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hright : ((((Xi t : ℝ) : ℂ)) ^ (2 : ℕ)
      * ∑' q : XiZeroCopy, (((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re
      = Xi t ^ (2 : ℕ)
        * (∑' q : XiZeroCopy, (((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re := by
    have h1 : ((((Xi t : ℝ) : ℂ)) ^ (2 : ℕ)).re = Xi t ^ (2 : ℕ) := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have h2 : ((((Xi t : ℝ) : ℂ)) ^ (2 : ℕ)).im = 0 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
    rw [Complex.mul_re, h1, h2]
    ring
  rw [hleft, hright] at hre
  exact hre

/-! ## The atomwise disk criterion -/

private theorem spectral_re (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint, Complex.mul_re]

private theorem spectral_im (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
  simp [xiSpectralPoint, Complex.mul_im]

private theorem re_inv_sq_pos {w : ℂ} (h : w.im ^ (2 : ℕ) < w.re ^ (2 : ℕ)) :
    0 < ((w ^ (2 : ℕ))⁻¹).re := by
  have hw : w ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have hsq : w ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hw
  rw [Complex.inv_re]
  refine div_pos ?_ (Complex.normSq_pos.mpr hsq)
  have hre : (w ^ (2 : ℕ)).re = w.re ^ (2 : ℕ) - w.im ^ (2 : ℕ) := by
    rw [pow_two, Complex.mul_re]
    ring
  rw [hre]
  linarith

/-- **The exact atom.**  With `a_q = γ_q − i δ_q` the `q`-th contribution to the Laguerre margin at
height `t` is `((t − γ_q)² − δ_q²)/((t − γ_q)² + δ_q²)²`. -/
theorem re_inv_sq_sub_xiSpectralPoint_eq (t : ℝ) (q : XiZeroCopy) :
    ((((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re
      = ((t - (xiSpectralPoint q).re) ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ))
        / (((t - (xiSpectralPoint q).re) ^ (2 : ℕ)
            + (xiSpectralPoint q).im ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  rw [Complex.inv_re]
  have hre : ((t : ℂ) - xiSpectralPoint q).re = t - (xiSpectralPoint q).re := by simp
  have him : ((t : ℂ) - xiSpectralPoint q).im = -(xiSpectralPoint q).im := by simp
  have h1 : (((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ)).re
      = (t - (xiSpectralPoint q).re) ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ) := by
    rw [pow_two, Complex.mul_re, hre, him]
    ring
  have h2 : Complex.normSq (((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))
      = ((t - (xiSpectralPoint q).re) ^ (2 : ℕ)
          + (xiSpectralPoint q).im ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [pow_two, map_mul]
    simp only [Complex.normSq_apply, hre, him]
    ring
  rw [h1, h2]

/-- An atom is strictly positive exactly when the test height lies outside the copy's disk. -/
theorem re_inv_sq_sub_xiSpectralPoint_pos {t : ℝ} {q : XiZeroCopy}
    (h : (xiSpectralPoint q).im ^ (2 : ℕ) < (t - (xiSpectralPoint q).re) ^ (2 : ℕ)) :
    0 < ((((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re := by
  refine re_inv_sq_pos ?_
  have hre : ((t : ℂ) - xiSpectralPoint q).re = t - (xiSpectralPoint q).re := by simp
  have him : ((t : ℂ) - xiSpectralPoint q).im = -(xiSpectralPoint q).im := by simp
  rw [hre, him]
  have hneg : (-(xiSpectralPoint q).im) ^ (2 : ℕ) = (xiSpectralPoint q).im ^ (2 : ℕ) := by ring
  rw [hneg]
  exact h

/-! ## Unconditional positivity regions -/

/-- **Local converse.**  If every copy whose ordinate lies within `1/2` of `t` is on the critical
line, the first Laguerre margin at `t` is strictly positive.  Only one window of the hypothesis
`RH` is used. -/
theorem laguerre_Xi_pos_of_window_onLine {t : ℝ} (ht : Xi t ≠ 0)
    (hwin : ∀ q : XiZeroCopy, |t - (xiSpectralPoint q).re| < 1 / 2 →
      (xiSpectralPoint q).im = 0) :
    0 < (deriv Xi t) ^ (2 : ℕ) - Xi t * deriv (deriv Xi) t := by
  have hz : XiC (t : ℂ) ≠ 0 := by
    rw [XiC_ofReal]
    simpa using ht
  have hpos : ∀ q : XiZeroCopy,
      0 < ((((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re := by
    intro q
    refine re_inv_sq_sub_xiSpectralPoint_pos ?_
    by_cases hw : |t - (xiSpectralPoint q).re| < 1 / 2
    · have him := hwin q hw
      rw [him]
      have hne : t - (xiSpectralPoint q).re ≠ 0 := by
        intro h0
        apply hz
        rw [show (t : ℂ) = xiSpectralPoint q by
          refine Complex.ext ?_ ?_
          · rw [Complex.ofReal_re]; linarith
          · rw [Complex.ofReal_im, him]]
        exact XiC_xiSpectralPoint_eq_zero q
      have hsq : 0 < (t - (xiSpectralPoint q).re) ^ (2 : ℕ) := by positivity
      simpa using hsq
    · have hge : 1 / 2 ≤ |t - (xiSpectralPoint q).re| := not_lt.mp hw
      have hq := xiSpectralPoint_im_sq_lt_quarter q
      have habs : (0 : ℝ) ≤ |t - (xiSpectralPoint q).re| := abs_nonneg _
      have hid : |t - (xiSpectralPoint q).re| ^ (2 : ℕ)
          = (t - (xiSpectralPoint q).re) ^ (2 : ℕ) := sq_abs _
      have hsq : (1 / 4 : ℝ) ≤ (t - (xiSpectralPoint q).re) ^ (2 : ℕ) := by
        nlinarith [hge, habs, hid]
      linarith
  rw [laguerre_Xi_eq_tsum_inv_sq ht]
  have hsum := summable_inv_sq_sub_xiSpectralPoint hz
  have hre : (∑' q : XiZeroCopy, (((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re
      = ∑' q : XiZeroCopy, ((((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re :=
    Complex.re_tsum hsum
  rw [hre]
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy_xiLogDerivLineOnePositive
  have hsumre : Summable
      (fun q : XiZeroCopy => ((((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re) :=
    hsum.mapL Complex.reCLM
  have hSpos : 0 < ∑' q : XiZeroCopy, ((((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹).re :=
    hsumre.tsum_pos (fun q => (hpos q).le) q₀ (hpos q₀)
  have hXisq : 0 < Xi t ^ (2 : ℕ) := by positivity
  exact mul_pos hXisq hSpos

/-- **Unconditional low-height Laguerre positivity.**  Every copy has ordinate above `4.5` and
`(Re ρ − 1/2)² < 1/4`, so for `|t| ≤ 4` no copy's disk reaches height `t`. -/
theorem laguerre_Xi_pos_of_abs_le_four {t : ℝ} (ht : |t| ≤ 4) :
    0 < (deriv Xi t) ^ (2 : ℕ) - Xi t * deriv (deriv Xi) t := by
  have hfar : ∀ q : XiZeroCopy, 1 / 2 ≤ |t - (xiSpectralPoint q).re| := by
    intro q
    have hq := four_half_lt_abs_im_of_xiZeroCopy q
    rw [spectral_re]
    have h1 : |(q.1 : ℂ).im| - |t| ≤ |t - (q.1 : ℂ).im| := by
      have h2 := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) t
      rw [abs_sub_comm ((q.1 : ℂ).im) t] at h2
      linarith
    norm_num at hq
    linarith
  have hne : Xi t ≠ 0 := by
    intro h0
    have hz : XiC (t : ℂ) = 0 := by
      rw [XiC_ofReal, h0]
      simp
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hz
    have hfq := hfar q
    have hre : (xiSpectralPoint q).re = t := by rw [hq]; simp
    rw [hre] at hfq
    norm_num at hfq
  refine laguerre_Xi_pos_of_window_onLine hne (fun q hw => ?_)
  exact absurd hw (not_lt.mpr (hfar q))

/-! ## From an off-line height floor to a Laguerre-positive interval -/

/-- **Non-strict window converse.**  At a zero of `Ξ` the margin collapses to `(Ξ')²`, so the
nonvanishing hypothesis is unnecessary for the nonnegative form. -/
theorem laguerre_Xi_nonneg_of_window_onLine {t : ℝ}
    (hwin : ∀ q : XiZeroCopy, |t - (xiSpectralPoint q).re| < 1 / 2 →
      (xiSpectralPoint q).im = 0) :
    0 ≤ (deriv Xi t) ^ (2 : ℕ) - Xi t * deriv (deriv Xi) t := by
  by_cases ht : Xi t = 0
  · have hcollapse : (deriv Xi t) ^ (2 : ℕ) - Xi t * deriv (deriv Xi) t
        = (deriv Xi t) ^ (2 : ℕ) := by
      rw [ht]
      ring
    rw [hcollapse]
    positivity
  · exact (laguerre_Xi_pos_of_window_onLine ht hwin).le

/-- **An off-line height floor yields a Laguerre-positive interval.**  If every off-line copy has
ordinate of modulus at least `H`, then no off-line copy enters the unit window at any height `t`
with `|t| + 1/2 ≤ H`, so the first Laguerre inequality holds there.  Any improvement of the floor
widens the interval. -/
theorem laguerre_Xi_nonneg_of_offLine_floor {H t : ℝ}
    (hfloor : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → H ≤ |(q.1 : ℂ).im|)
    (ht : |t| + 1 / 2 ≤ H) :
    0 ≤ (deriv Xi t) ^ (2 : ℕ) - Xi t * deriv (deriv Xi) t := by
  refine laguerre_Xi_nonneg_of_window_onLine (fun q hw => ?_)
  by_contra hoff
  have hH := hfloor q hoff
  rw [spectral_re] at hw
  have h1 : |(q.1 : ℂ).im| - |t| ≤ |t - (q.1 : ℂ).im| := by
    have h2 := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) t
    rw [abs_sub_comm ((q.1 : ℂ).im) t] at h2
    linarith
  linarith

/-- The off-line hypothesis of the floor law in the coordinates of the Xi divisor. -/
theorem xiSpectralPoint_im_ne_zero_iff (q : XiZeroCopy) :
    (xiSpectralPoint q).im ≠ 0 ↔ (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [spectral_im]
  constructor
  · intro h hcon
    exact h (by rw [hcon]; ring)
  · intro h hcon
    exact h (by linarith [hcon])

/-- **Unconditional first Laguerre inequality below height `58/5`.**  No off-line copy has squared
ordinate below `2365/16`, so `|Im ρ| ≥ 121/10` for every off-line copy and the unit window at any
`|t| ≤ 58/5` contains only on-line copies. -/
theorem laguerre_Xi_nonneg_of_abs_le_criticalBand {t : ℝ} (ht : |t| ≤ 58 / 5) :
    0 ≤ (deriv Xi t) ^ (2 : ℕ) - Xi t * deriv (deriv Xi) t := by
  refine laguerre_Xi_nonneg_of_offLine_floor (H := 121 / 10) (fun q hoff => ?_) (by linarith)
  have hre : (q.1 : ℂ).re ≠ 1 / 2 := (xiSpectralPoint_im_ne_zero_iff q).mp hoff
  by_contra hlt
  have hlt' : |(q.1 : ℂ).im| < 121 / 10 := not_le.mp hlt
  have habs : (0 : ℝ) ≤ |(q.1 : ℂ).im| := abs_nonneg _
  have hid : |(q.1 : ℂ).im| ^ (2 : ℕ) = ((q.1 : ℂ).im) ^ (2 : ℕ) := sq_abs _
  refine not_exists_xiZeroCopy_offLine_of_im_sq_lt_2365_over_16 ⟨q, hre, ?_⟩
  nlinarith [hlt', habs, hid]

end

end RHTower
