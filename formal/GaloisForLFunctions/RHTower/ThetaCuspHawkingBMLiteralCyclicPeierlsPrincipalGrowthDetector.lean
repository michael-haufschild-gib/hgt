import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsAffineCuspIncidence
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativePrincipalPowerExpansion
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# Dominant principal-square cusp channel for literal cyclic Peierls B2

The obsolete coefficientwise B2 cancellation endgate is false on the critical
line.  Its viable replacement is a cutoff-growth detector.  This leaf proves
the source-side detector on the left half of the strip: after normalization by
the unique dominant Weyl power, the literal principal half-square has a
nonzero limit.  Thus oscillatory lower channels cannot cancel that growth.

Proof-chain role:
`off-line Xi occurrence -> nonzero dominant principal-square channel
-> cutoff-growth transport of complete metric current -> revised HB B2
-> reflected critical-line receiver -> RH`.

This does not assert the still-open transport from this source-side detector
to the complete metric-current boundary.
-/

open Filter Topology

namespace RHTower.D4BMLiteralCyclicPeierlsPrincipalGrowthDetector

open D4BMJointSource D4BMLiteralCyclicPeierlsAffineCuspIncidence

noncomputable section
set_option autoImplicit false

/-- A complex height power tends to zero at the upper cusp whenever its real
exponent is negative. -/
private theorem tendsto_cpow_atTop_zero_of_re_neg {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hpos : 0 < -w.re := neg_pos.mpr hw
  have h : Tendsto (fun y : ℝ => (y ^ (-w.re))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hpos)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  rw [← Real.rpow_neg hy.le]
  congr 1
  ring

/-- A positive real limit gives an eventual lower bound by half its value. -/
private theorem eventually_half_le_of_tendsto_pos {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (h : Tendsto f atTop (𝓝 L)) :
    ∀ᶠ y in atTop, L / 2 ≤ f y := by
  have hball : Metric.ball L (L / 2) ∈ 𝓝 L :=
    Metric.ball_mem_nhds L (by linarith)
  filter_upwards [h.eventually hball] with y hy
  rw [Real.dist_eq] at hy
  exact le_of_lt (by
    have hlower := (abs_lt.mp hy).1
    linarith)

/-- On the left half of the strip, the lower Weyl channel is the unique
dominant principal-square channel. -/
theorem principalSquare_left_normalized_tendsto (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1 / 2) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ (-(2 - 2 * (q.1 : ℂ))) *
      principalSquare q ![0, y]) atTop
      (𝓝 (reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ 2 / 2)) := by
  have hd1 : (2 * (q.1 : ℂ) - 1).re < 0 := by
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith
  have hd2 : (4 * (q.1 : ℂ) - 2).re < 0 := by
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith
  let c0 := reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ 2 / 2
  let c1 := reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) *
    reflectedCompletedLambda (2 * (q.1 : ℂ))
  let c2 := reflectedCompletedLambda (2 * (q.1 : ℂ)) ^ 2 / 2
  have h1 : Tendsto (fun y : ℝ => c1 * (y : ℂ) ^ (2 * (q.1 : ℂ) - 1))
      atTop (𝓝 0) := by
    simpa [c1] using (tendsto_cpow_atTop_zero_of_re_neg hd1).const_mul c1
  have h2 : Tendsto (fun y : ℝ => c2 * (y : ℂ) ^ (4 * (q.1 : ℂ) - 2))
      atTop (𝓝 0) := by
    simpa [c2] using (tendsto_cpow_atTop_zero_of_re_neg hd2).const_mul c2
  have h : Tendsto (fun y : ℝ => c0 +
      c1 * (y : ℂ) ^ (2 * (q.1 : ℂ) - 1) +
      c2 * (y : ℂ) ^ (4 * (q.1 : ℂ) - 2)) atTop (𝓝 c0) := by
    simpa using (tendsto_const_nhds.add h1).add h2
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [nativePrincipalSquare_eq_power_sum q hy]
  simp only [Fin.sum_univ_three, nativePrincipalPowerCoefficient,
    nativePrincipalPowerExponent, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  change c0 + c1 * (y : ℂ) ^ (2 * (q.1 : ℂ) - 1) +
      c2 * (y : ℂ) ^ (4 * (q.1 : ℂ) - 2) =
    (y : ℂ) ^ (-(2 - 2 * (q.1 : ℂ))) *
      (c0 * (y : ℂ) ^ (2 - 2 * (q.1 : ℂ)) +
        c1 * (y : ℂ) ^ (1 : ℂ) + c2 * (y : ℂ) ^ (2 * (q.1 : ℂ)))
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have h0 : (y : ℂ) ^ (-(2 - 2 * (q.1 : ℂ))) *
      (y : ℂ) ^ (2 - 2 * (q.1 : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _ hy0]
    simp
  have hm : (y : ℂ) ^ (-(2 - 2 * (q.1 : ℂ))) * (y : ℂ) ^ (1 : ℂ) =
      (y : ℂ) ^ (2 * (q.1 : ℂ) - 1) := by
    rw [← Complex.cpow_add _ _ hy0]
    congr 1
    ring
  have hp : (y : ℂ) ^ (-(2 - 2 * (q.1 : ℂ))) *
      (y : ℂ) ^ (2 * (q.1 : ℂ)) = (y : ℂ) ^ (4 * (q.1 : ℂ) - 2) := by
    rw [← Complex.cpow_add _ _ hy0]
    congr 1
    ring
  symm
  calc
    _ = c0 * ((y : ℂ) ^ (-(2 - 2 * (q.1 : ℂ))) *
        (y : ℂ) ^ (2 - 2 * (q.1 : ℂ))) +
        c1 * ((y : ℂ) ^ (-(2 - 2 * (q.1 : ℂ))) * (y : ℂ) ^ (1 : ℂ)) +
        c2 * ((y : ℂ) ^ (-(2 - 2 * (q.1 : ℂ))) *
          (y : ℂ) ^ (2 * (q.1 : ℂ))) := by ring
    _ = _ := by rw [h0, hm, hp]; ring

/-- The left-half dominant limit is nonzero.  This is the literal
principal-square cutoff-growth witness needed by a revised B2 receiver. -/
theorem principalSquare_left_normalized_tendsto_nonzero (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1 / 2) :
    (reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ 2 / 2 : ℂ) ≠ 0 ∧
      Tendsto (fun y : ℝ => (y : ℂ) ^ (-(2 - 2 * (q.1 : ℂ))) *
        principalSquare q ![0, y]) atTop
        (𝓝 (reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ 2 / 2)) := by
  have hLambda : reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ≠ 0 := by
    intro hz
    exact affine_lower_lambda_zero_not_left q ⟨hz, hleft⟩
  constructor
  · exact div_ne_zero (pow_ne_zero 2 hLambda) (by norm_num)
  · exact principalSquare_left_normalized_tendsto q hleft

/-- Real cutoff-growth form of the left-half detector.  It has a strictly
positive limiting rate, so no choice of complex phase or cusp subsequence is
needed to observe the dominant channel. -/
theorem principalSquare_left_norm_growth_tendsto (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1 / 2) :
    Tendsto (fun y : ℝ => ‖principalSquare q ![0, y]‖ /
      y ^ (2 - 2 * (q.1 : ℂ).re)) atTop
      (𝓝 ‖reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ 2 / 2‖) := by
  have h := (principalSquare_left_normalized_tendsto q hleft).norm
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (-(2 - 2 * (q.1 : ℂ))).re = -(2 - 2 * (q.1 : ℂ).re) := by
    norm_num [Complex.neg_re, Complex.sub_re, Complex.mul_re]
  rw [hre, Real.rpow_neg hy.le, div_eq_mul_inv]
  ring

/-- The observable real cutoff-growth limit on the left half is strictly
positive. -/
theorem principalSquare_left_norm_growth_tendsto_pos (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1 / 2) :
    0 < ‖reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ 2 / 2‖ ∧
      Tendsto (fun y : ℝ => ‖principalSquare q ![0, y]‖ /
        y ^ (2 - 2 * (q.1 : ℂ).re)) atTop
        (𝓝 ‖reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ 2 / 2‖) := by
  have hne := (principalSquare_left_normalized_tendsto_nonzero q hleft).1
  constructor
  · exact norm_pos_iff.mpr hne
  · exact principalSquare_left_norm_growth_tendsto q hleft

/-- The left principal square eventually has a fixed positive proportion of
its dominant Weyl growth.  This is the lower-bound form needed to rule out
transport into a genuinely lower-order physical boundary term. -/
theorem principalSquare_left_norm_growth_eventually_lower (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1 / 2) :
    ∀ᶠ y in atTop,
      (‖reflectedCompletedLambda (2 * (q.1 : ℂ) - 1) ^ 2 / 2‖ / 2) *
        y ^ (2 - 2 * (q.1 : ℂ).re) ≤ ‖principalSquare q ![0, y]‖ := by
  have hpos := (principalSquare_left_norm_growth_tendsto_pos q hleft).1
  have hlim := (principalSquare_left_norm_growth_tendsto_pos q hleft).2
  have hratio := eventually_half_le_of_tendsto_pos hpos hlim
  filter_upwards [hratio, eventually_gt_atTop (0 : ℝ)] with y hy hypos
  have hpower : 0 < y ^ (2 - 2 * (q.1 : ℂ).re) :=
    Real.rpow_pos_of_pos hypos _
  calc
    _ ≤ (‖principalSquare q ![0, y]‖ /
        y ^ (2 - 2 * (q.1 : ℂ).re)) * y ^ (2 - 2 * (q.1 : ℂ).re) :=
      mul_le_mul_of_nonneg_right hy hpower.le
    _ = _ := div_mul_cancel₀ _ hpower.ne'

/-- Every off-line Xi divisor copy yields a (possibly reflected) left-half
copy carrying the nonzero literal principal-square growth witness.  This is
the source-side receiver for a revised, growth-based B2 statement. -/
theorem exists_left_principalSquare_growth_detector_of_re_ne_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ qleft : XiZeroCopy, (qleft.1 : ℂ).re < 1 / 2 ∧
      (reflectedCompletedLambda (2 * (qleft.1 : ℂ) - 1) ^ 2 / 2 : ℂ) ≠ 0 ∧
        Tendsto (fun y : ℝ => (y : ℂ) ^ (-(2 - 2 * (qleft.1 : ℂ))) *
          principalSquare qleft ![0, y]) atTop
          (𝓝 (reflectedCompletedLambda (2 * (qleft.1 : ℂ) - 1) ^ 2 / 2)) := by
  rcases lt_or_gt_of_ne hline with hleft | hright
  · refine ⟨q, hleft, ?_, ?_⟩
    exact (principalSquare_left_normalized_tendsto_nonzero q hleft).1
    exact (principalSquare_left_normalized_tendsto_nonzero q hleft).2
  · let qleft := xiZeroCopyReflectEquiv q
    have hleft : (qleft.1 : ℂ).re < 1 / 2 := by
      dsimp only [qleft]
      rw [xiZeroCopy_reflect_val]
      norm_num [Complex.sub_re]
      linarith
    refine ⟨qleft, hleft, ?_, ?_⟩
    exact (principalSquare_left_normalized_tendsto_nonzero qleft hleft).1
    exact (principalSquare_left_normalized_tendsto_nonzero qleft hleft).2

/-- Phase-free form of the off-line detector.  A physical current-to-boundary
transport need only preserve this positive real growth rate; it need not
preserve a chosen complex phase of the principal square. -/
theorem exists_left_principalSquare_norm_growth_detector_of_re_ne_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ qleft : XiZeroCopy, (qleft.1 : ℂ).re < 1 / 2 ∧
      0 < ‖reflectedCompletedLambda (2 * (qleft.1 : ℂ) - 1) ^ 2 / 2‖ ∧
        Tendsto (fun y : ℝ => ‖principalSquare qleft ![0, y]‖ /
          y ^ (2 - 2 * (qleft.1 : ℂ).re)) atTop
          (𝓝 ‖reflectedCompletedLambda (2 * (qleft.1 : ℂ) - 1) ^ 2 / 2‖) := by
  rcases lt_or_gt_of_ne hline with hleft | hright
  · exact ⟨q, hleft, principalSquare_left_norm_growth_tendsto_pos q hleft⟩
  · let qleft := xiZeroCopyReflectEquiv q
    have hleft : (qleft.1 : ℂ).re < 1 / 2 := by
      dsimp only [qleft]
      rw [xiZeroCopy_reflect_val]
      norm_num [Complex.sub_re]
      linarith
    exact ⟨qleft, hleft, principalSquare_left_norm_growth_tendsto_pos qleft hleft⟩

/-- Global phase-free lower-bound receiver for an off-line divisor copy.
The displayed rate is an unavoidable source-side cusp channel for any literal
B2 current/boundary transport. -/
theorem exists_left_principalSquare_norm_growth_eventually_lower_of_re_ne_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ qleft : XiZeroCopy, (qleft.1 : ℂ).re < 1 / 2 ∧
      0 < ‖reflectedCompletedLambda (2 * (qleft.1 : ℂ) - 1) ^ 2 / 2‖ ∧
        ∀ᶠ y in atTop,
          (‖reflectedCompletedLambda (2 * (qleft.1 : ℂ) - 1) ^ 2 / 2‖ / 2) *
            y ^ (2 - 2 * (qleft.1 : ℂ).re) ≤ ‖principalSquare qleft ![0, y]‖ := by
  rcases exists_left_principalSquare_norm_growth_detector_of_re_ne_half q hline with
    ⟨qleft, hleft, hpos, _⟩
  exact ⟨qleft, hleft, hpos,
    principalSquare_left_norm_growth_eventually_lower qleft hleft⟩

end

end RHTower.D4BMLiteralCyclicPeierlsPrincipalGrowthDetector
