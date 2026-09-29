import GaloisForLFunctions.HTGeometry.SingularGaugeRieszCharge
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureScoreConcentration
import GaloisForLFunctions.RHTower.Sieve.LogLogAntiderivative

/-!
# The Gamma-six theta-saddle double-log clock

For `λ ≤ 0` the exact first-atom saddle degree `J_λ(x) = π x e^{2x} - λ x² - (9/4) x` is a strictly
increasing convex bijection of `[0, ∞)`; `x_j` is the unique positive saddle with
`J_λ(x_j) = j + 1/2`, and `Δ_j = x_{j+1} - x_j` satisfies `1/J'(x_{j+1}) ≤ Δ_j ≤ 1/J'(x_j)`.

* **(A)** `α_j^{(c)} = c Δ_j` is positive and decreases to zero with `j α_j^{(c)} → c/2`; the clock
  `A_λ^{(c)} = diag(α_j^{(c)})` is positive compact, weak trace class with residue `c/2`, not trace
  class, in every `S_p`, `p > 1`, and `c = 6` is the unique calibration with residue `3`.
* **(B)** with `h_j = 6/(2j+9)`, `j log j (h_j - α_j) → 3`; `B_λ = D_1 - A_λ` is eventually positive
  on the diagonal, compact and not trace class.
* **(C)** its positive part `B_λ⁺` differs from `B_λ` by finite rank, `(1/log log N) ∑ s_j → 3`, and
  `(1/log N) ∑ s_j → 0`.
* **(D)** `∑_{j<N} (h_j - α_j) - 3 log log N → 3 log(π/2) - 3ψ(9/2) + 6 x_0`.
-/

open Filter Topology Set ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## The inverse-saddle heights -/

section Saddle

variable {lam : ℝ} (hlam : lam ≤ 0)

include hlam in
/-- **(GTSD.6).**  `J'_λ(x) > 0` for `x ≥ 0`. -/
theorem saddleSlope_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam x := by
  unfold thetaCuspGaussianApertureExactTailSaddleDegreeSlope
  have h1 : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
  have h2 : 0 ≤ -2 * lam * x := by nlinarith
  have h3 : 1 ≤ Real.exp (2 * x) * (1 + 2 * x) := by nlinarith
  have h4 : Real.pi ≤ Real.pi * Real.exp (2 * x) * (1 + 2 * x) := by
    rw [mul_assoc]
    nlinarith [Real.pi_pos]
  nlinarith [Real.pi_gt_three]

include hlam in
/-- **(GTSD.6).**  `J''_λ(x) > 0` for `x ≥ 0`. -/
theorem saddleCurvature_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspGaussianApertureExactTailSaddleDegreeCurvature lam x := by
  unfold thetaCuspGaussianApertureExactTailSaddleDegreeCurvature
  have h1 : 0 < Real.exp (2 * x) := Real.exp_pos _
  have h2 : 0 < 4 * Real.pi * Real.exp (2 * x) * (1 + x) := by positivity
  linarith

include hlam in
theorem saddleSlope_monotoneOn :
    MonotoneOn (thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam) (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
  · exact fun x _ =>
      (hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam x).continuousAt
        |>.continuousWithinAt
  · exact fun x _ =>
      (hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam x).differentiableAt
        |>.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam x).deriv]
    exact (saddleCurvature_pos hlam (le_of_lt hx)).le

/-- The inverse-saddle height `x_j`. -/
abbrev saddleHeight (j : ℕ) : ℝ := thetaCuspGaussianApertureResponseCenteredSaddleHeight lam hlam j

theorem saddleHeight_pos (j : ℕ) : 0 < saddleHeight hlam j :=
  thetaCuspGaussianApertureResponseCenteredSaddleHeight_pos hlam j

/-- **(GTSD.2).**  `J_λ(x_j) = j + 1/2`. -/
theorem saddleDegree_saddleHeight (j : ℕ) :
    thetaCuspGaussianApertureExactTailSaddleDegree lam (saddleHeight hlam j) = (j : ℝ) + 1 / 2 :=
  thetaCuspGaussianApertureResponseCenteredSaddleHeight_score hlam j

theorem saddleHeight_lt_succ (j : ℕ) : saddleHeight hlam j < saddleHeight hlam (j + 1) := by
  have hm := thetaCuspGaussianApertureExactTailSaddleDegree_strictMonoOn_Ici_zero hlam
  refine (hm.lt_iff_lt (mem_Ici.mpr (saddleHeight_pos hlam j).le)
    (mem_Ici.mpr (saddleHeight_pos hlam (j + 1)).le)).mp ?_
  rw [saddleDegree_saddleHeight, saddleDegree_saddleHeight]
  push_cast
  linarith

theorem saddleHeight_strictMono : StrictMono (saddleHeight hlam) :=
  strictMono_nat_of_lt_succ (saddleHeight_lt_succ hlam)

/-- The saddle heights tend to infinity. -/
theorem tendsto_saddleHeight : Tendsto (saddleHeight hlam) atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone (saddleHeight_strictMono hlam).monotone fun b => ?_
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hm := thetaCuspGaussianApertureExactTailSaddleDegree_strictMonoOn_Ici_zero hlam
  set B := max b 0
  obtain ⟨j, hj⟩ := exists_nat_gt (thetaCuspGaussianApertureExactTailSaddleDegree lam B)
  have hlt : thetaCuspGaussianApertureExactTailSaddleDegree lam (saddleHeight hlam j) <
      thetaCuspGaussianApertureExactTailSaddleDegree lam B :=
    hm (mem_Ici.mpr (saddleHeight_pos hlam j).le) (mem_Ici.mpr (le_max_right _ _))
      ((hcon j).trans_le (le_max_left _ _))
  rw [saddleDegree_saddleHeight] at hlt
  linarith

/-- The saddle increment `Δ_j = x_{j+1} - x_j`. -/
abbrev saddleIncrement (j : ℕ) : ℝ := saddleHeight hlam (j + 1) - saddleHeight hlam j

theorem saddleIncrement_pos (j : ℕ) : 0 < saddleIncrement hlam j :=
  sub_pos.mpr (saddleHeight_lt_succ hlam j)

/-- **(GTSD.9).**  Mean-value bounds `1/J'(x_{j+1}) ≤ Δ_j ≤ 1/J'(x_j)`. -/
theorem saddleIncrement_bounds (j : ℕ) :
    1 / thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam (j + 1))
        ≤ saddleIncrement hlam j ∧
      saddleIncrement hlam j
        ≤ 1 / thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam j) := by
  have hlt := saddleHeight_lt_succ hlam j
  have h0 := (saddleHeight_pos hlam j).le
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope
    (thetaCuspGaussianApertureExactTailSaddleDegree lam)
    (thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam) hlt
    (fun x _ => (hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree lam x).continuousAt
      |>.continuousWithinAt)
    (fun x _ => hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree lam x)
  rw [saddleDegree_saddleHeight, saddleDegree_saddleHeight] at hslope
  have hΔ := saddleIncrement_pos hlam j
  have hval : thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam ξ
      = 1 / saddleIncrement hlam j := by
    rw [hslope]
    push_cast
    ring_nf
  have hmono := saddleSlope_monotoneOn hlam
  have hlo : thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam j) ≤
      thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam ξ :=
    hmono (mem_Ici.mpr h0) (mem_Ici.mpr (h0.trans hξ.1.le)) hξ.1.le
  have hhi : thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam ξ ≤
      thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam (j + 1)) :=
    hmono (mem_Ici.mpr (h0.trans hξ.1.le)) (mem_Ici.mpr (h0.trans hlt.le)) hξ.2.le
  have hs0 := saddleSlope_pos hlam h0
  have hs1 := saddleSlope_pos hlam (h0.trans hlt.le)
  rw [hval] at hlo hhi
  constructor
  · rw [div_le_iff₀ hs1]
    rw [div_le_iff₀ hΔ] at hhi
    linarith [mul_comm (saddleIncrement hlam j)
      (thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam (j + 1)))]
  · rw [le_div_iff₀ hs0]
    rw [le_div_iff₀ hΔ] at hlo
    linarith [mul_comm (saddleIncrement hlam j)
      (thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam j))]

/-- **Theorem GTSD-A.**  The increments decrease. -/
theorem saddleIncrement_antitone : Antitone (saddleIncrement hlam) :=
  antitone_nat_of_succ_le fun j =>
    (saddleIncrement_bounds hlam (j + 1)).2.trans (saddleIncrement_bounds hlam j).1

end Saddle

/-! ## First-atom asymptotics of the saddle degree -/

section Asymptotics

variable (lam : ℝ)

/-- `J_λ(x) = πxe^{2x}(1 - δ_λ(x))`. -/
def saddleDegreeDefect (x : ℝ) : ℝ := (lam * x + 9 / 4) / (Real.pi * Real.exp (2 * x))

/-- `J'_λ(x) = πe^{2x}(1 + 2x)(1 - δ'_λ(x))`. -/
def saddleSlopeDefect (x : ℝ) : ℝ :=
  (2 * lam * x + 9 / 4) / (Real.pi * Real.exp (2 * x) * (1 + 2 * x))

/-- `J_λ(x) - 1/2 = πxe^{2x} θ_λ(x)`. -/
def saddleShiftRatio (x : ℝ) : ℝ :=
  1 - saddleDegreeDefect lam x - Real.exp (-(2 * x)) / (2 * Real.pi * x)

/-- The inverse-saddle clock ratio `F(x) = 6 (J(x) - 1/2) / J'(x)`. -/
def saddleClockRatio (x : ℝ) : ℝ :=
  6 * (thetaCuspGaussianApertureExactTailSaddleDegree lam x - 1 / 2) /
    thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam x

theorem saddleDegree_sub_half_eq {x : ℝ} (hx : x ≠ 0) :
    thetaCuspGaussianApertureExactTailSaddleDegree lam x - 1 / 2
      = Real.pi * x * Real.exp (2 * x) * saddleShiftRatio lam x := by
  have hpi := Real.pi_pos.ne'
  have hexp := (Real.exp_pos (2 * x)).ne'
  have e1 : Real.pi * x * Real.exp (2 * x) * ((lam * x + 9 / 4) / (Real.pi * Real.exp (2 * x)))
      = x * (lam * x + 9 / 4) := by
    field_simp
  have e2 : Real.pi * x * Real.exp (2 * x) * (Real.exp (-(2 * x)) / (2 * Real.pi * x)) = 1 / 2 := by
    rw [Real.exp_neg]
    field_simp
  rw [saddleShiftRatio, saddleDegreeDefect, mul_sub, mul_sub, mul_one, e1, e2,
    thetaCuspGaussianApertureExactTailSaddleDegree]
  ring

theorem saddleSlope_eq {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam x
      = Real.pi * Real.exp (2 * x) * (1 + 2 * x) * (1 - saddleSlopeDefect lam x) := by
  unfold thetaCuspGaussianApertureExactTailSaddleDegreeSlope saddleSlopeDefect
  have hpi := Real.pi_pos.ne'
  have hexp := (Real.exp_pos (2 * x)).ne'
  have h1 : (1 + 2 * x) ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_pow_mul_exp_neg_two (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-(2 * x))) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2))).const_mul ((2 : ℝ) ^ n)⁻¹
  rw [mul_zero] at h
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, id, mul_pow]
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  field_simp

theorem tendsto_exp_neg_two : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 0) := by
  simpa using tendsto_pow_mul_exp_neg_two 0

theorem saddleDegreeDefect_eq (x : ℝ) :
    saddleDegreeDefect lam x = lam / Real.pi * (x * Real.exp (-(2 * x)))
      + 9 / (4 * Real.pi) * Real.exp (-(2 * x)) := by
  rw [saddleDegreeDefect, Real.exp_neg]
  have hpi := Real.pi_pos.ne'
  have hexp := (Real.exp_pos (2 * x)).ne'
  field_simp

theorem tendsto_saddleDegreeDefect : Tendsto (saddleDegreeDefect lam) atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_two 1).const_mul (lam / Real.pi)).add
    (tendsto_exp_neg_two.const_mul (9 / (4 * Real.pi)))
  simp only [mul_zero, add_zero, pow_one] at h
  exact h.congr fun x => (saddleDegreeDefect_eq lam x).symm

theorem tendsto_mul_saddleDegreeDefect :
    Tendsto (fun x => x * saddleDegreeDefect lam x) atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_two 2).const_mul (lam / Real.pi)).add
    ((tendsto_pow_mul_exp_neg_two 1).const_mul (9 / (4 * Real.pi)))
  simp only [mul_zero, add_zero, pow_one] at h
  refine h.congr fun x => ?_
  rw [saddleDegreeDefect_eq]
  ring

theorem saddleSlopeDefect_eq {x : ℝ} (hx : 0 ≤ x) :
    saddleSlopeDefect lam x = Real.exp (-(2 * x)) / Real.pi *
      (lam + (9 / 4 - lam) / (1 + 2 * x)) := by
  rw [saddleSlopeDefect, Real.exp_neg]
  have hpi := Real.pi_pos.ne'
  have hexp := (Real.exp_pos (2 * x)).ne'
  have h1 : (1 + 2 * x) ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_inv_one_add_two_mul : Tendsto (fun x : ℝ => (9 / 4 - lam) / (1 + 2 * x)) atTop
    (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop two_pos))

theorem tendsto_saddleSlopeDefect : Tendsto (saddleSlopeDefect lam) atTop (𝓝 0) := by
  have h := (tendsto_exp_neg_two.div_const Real.pi).mul
    (tendsto_const_nhds (x := lam) |>.add (tendsto_inv_one_add_two_mul lam))
  simp only [zero_div, zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  exact (saddleSlopeDefect_eq lam hx).symm

theorem tendsto_mul_saddleSlopeDefect :
    Tendsto (fun x => x * saddleSlopeDefect lam x) atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_two 1).div_const Real.pi).mul
    (tendsto_const_nhds (x := lam) |>.add (tendsto_inv_one_add_two_mul lam))
  simp only [zero_div, zero_mul, pow_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [saddleSlopeDefect_eq lam hx]
  ring

theorem tendsto_saddleShiftRatio : Tendsto (saddleShiftRatio lam) atTop (𝓝 1) := by
  have h3 : Tendsto (fun x : ℝ => Real.exp (-(2 * x)) / (2 * Real.pi * x)) atTop (𝓝 0) := by
    have h := tendsto_exp_neg_two.mul (tendsto_inv_atTop_zero.comp
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)))
    rw [zero_mul] at h
    exact h.congr fun x => by simp only [Function.comp_apply, id, div_eq_mul_inv]
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_saddleDegreeDefect lam)).sub h3
  simp only [sub_zero] at h
  exact h

/-- The saddle-degree logarithm `ℓ(x) = log(J_λ(x) - 1/2)`. -/
def saddleLog (x : ℝ) : ℝ :=
  Real.log (thetaCuspGaussianApertureExactTailSaddleDegree lam x - 1 / 2)

theorem eventually_saddleLog_eq : ∀ᶠ x in atTop, saddleLog lam x
    = Real.log Real.pi + Real.log x + 2 * x + Real.log (saddleShiftRatio lam x) := by
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_saddleShiftRatio lam).eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with x hx hθ
  rw [saddleLog, saddleDegree_sub_half_eq lam hx.ne', Real.log_mul (by positivity) hθ.ne',
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul Real.pi_pos.ne' hx.ne',
    Real.log_exp]

/-- **(GTSD.8).**  `ℓ(x)/(1 + 2x) → 1`. -/
theorem tendsto_saddleLog_div : Tendsto (fun x => saddleLog lam x / (1 + 2 * x)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / (2 * x + 1)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 2 1 1 two_ne_zero
  have hden : Tendsto (fun x : ℝ => 1 + 2 * x) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop two_pos)
  have hc : Tendsto (fun x : ℝ => (Real.log Real.pi - 1 +
      Real.log (saddleShiftRatio lam x)) / (1 + 2 * x)) atTop (𝓝 0) := by
    have hθ := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      (tendsto_saddleShiftRatio lam))
    rw [Real.log_one] at hθ
    exact ((tendsto_const_nhds (x := Real.log Real.pi - 1)).add hθ).div_atTop hden
  have h := (hlog.add hc).const_add 1
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_saddleLog_eq lam, eventually_gt_atTop 0] with x hx hx0
  rw [hx]
  have h1 : (1 + 2 * x) ≠ 0 := by positivity
  have h2 : (2 * x + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem saddleClockRatio_eq {x : ℝ} (hx : 0 < x) :
    saddleClockRatio lam x = 6 * x * saddleShiftRatio lam x /
      ((1 + 2 * x) * (1 - saddleSlopeDefect lam x)) := by
  rw [saddleClockRatio, saddleDegree_sub_half_eq lam hx.ne', saddleSlope_eq lam hx.le]
  have hpi := Real.pi_pos.ne'
  have hexp := (Real.exp_pos (2 * x)).ne'
  rw [show 6 * (Real.pi * x * Real.exp (2 * x) * saddleShiftRatio lam x)
      = Real.pi * Real.exp (2 * x) * (6 * x * saddleShiftRatio lam x) by ring,
    show Real.pi * Real.exp (2 * x) * (1 + 2 * x) * (1 - saddleSlopeDefect lam x)
      = Real.pi * Real.exp (2 * x) * ((1 + 2 * x) * (1 - saddleSlopeDefect lam x)) by ring,
    mul_div_mul_left _ _ (mul_ne_zero hpi hexp)]

theorem mul_three_sub_saddleClockRatio_eq {x : ℝ} (hx : 0 < x)
    (hδ : saddleSlopeDefect lam x ≠ 1) :
    (1 + 2 * x) * (3 - saddleClockRatio lam x)
      = (3 - 3 * saddleSlopeDefect lam x - 6 * (x * saddleSlopeDefect lam x) +
        (6 * (x * saddleDegreeDefect lam x) + 3 / Real.pi * Real.exp (-(2 * x)))) /
          (1 - saddleSlopeDefect lam x) := by
  rw [saddleClockRatio_eq lam hx, saddleShiftRatio]
  have hpi := Real.pi_pos.ne'
  have h1 : (1 + 2 * x) ≠ 0 := by positivity
  have h2 : (1 - saddleSlopeDefect lam x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hδ)
  field_simp
  ring

/-- `(1 + 2x)(3 - F(x)) → 3`. -/
theorem tendsto_mul_three_sub_saddleClockRatio :
    Tendsto (fun x => (1 + 2 * x) * (3 - saddleClockRatio lam x)) atTop (𝓝 3) := by
  have hnum := (((tendsto_const_nhds (x := (3 : ℝ))).sub
    ((tendsto_saddleSlopeDefect lam).const_mul 3)).sub
    ((tendsto_mul_saddleSlopeDefect lam).const_mul 6)).add
    (((tendsto_mul_saddleDegreeDefect lam).const_mul 6).add
      (tendsto_exp_neg_two.const_mul (3 / Real.pi)))
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_saddleSlopeDefect lam)
  have h := hnum.div hden (by norm_num)
  simp only [mul_zero, sub_zero, add_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_saddleSlopeDefect lam).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with x hx hδ
  exact (mul_three_sub_saddleClockRatio_eq lam hx (ne_of_lt hδ)).symm

/-- The inverse-saddle clock ratio tends to `3`. -/
theorem tendsto_saddleClockRatio : Tendsto (saddleClockRatio lam) atTop (𝓝 3) := by
  have hden : Tendsto (fun x : ℝ => 1 + 2 * x) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop two_pos)
  have h := ((tendsto_mul_three_sub_saddleClockRatio lam).div_atTop hden).const_sub 3
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have h1 : (1 + 2 * x) ≠ 0 := by positivity
  field_simp
  ring

/-- `ℓ(x)(3 - F(x)) → 3`. -/
theorem tendsto_saddleLog_mul_three_sub : Tendsto
    (fun x => saddleLog lam x * (3 - saddleClockRatio lam x)) atTop (𝓝 3) := by
  have h := (tendsto_saddleLog_div lam).mul (tendsto_mul_three_sub_saddleClockRatio lam)
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have h1 : (1 + 2 * x) ≠ 0 := by positivity
  field_simp

/-- **(GTSD.20).**  `3ℓ(x) - 6x - 3 log ℓ(x) → 3 log(π/2)`. -/
theorem tendsto_saddleLog_finitePart : Tendsto
    (fun x => 3 * saddleLog lam x - 6 * x - 3 * Real.log (saddleLog lam x)) atTop
      (𝓝 (3 * Real.log (Real.pi / 2))) := by
  have hratio : Tendsto (fun x => saddleLog lam x / (2 * x)) atTop (𝓝 1) := by
    have h := (tendsto_saddleLog_div lam).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_id.const_mul_atTop two_pos)))
    simp only [add_zero, mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have h1 : (1 + 2 * x) ≠ 0 := by positivity
    simp only [id]
    field_simp
    ring
  have hlogθ := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (tendsto_saddleShiftRatio lam)
  have hlogr := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  rw [Real.log_one] at hlogθ hlogr
  have h := ((tendsto_const_nhds (x := 3 * Real.log Real.pi - 3 * Real.log 2)).add
    (hlogθ.const_mul 3)).sub (hlogr.const_mul 3)
  simp only [mul_zero, add_zero, sub_zero] at h
  rw [Real.log_div Real.pi_pos.ne' two_ne_zero, mul_sub]
  refine h.congr' ?_
  filter_upwards [eventually_saddleLog_eq lam, eventually_gt_atTop 0,
    hratio.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx0 hr
  simp only [Function.comp_apply]
  have hℓ : 0 < saddleLog lam x := by
    have : 0 < saddleLog lam x / (2 * x) := hr
    exact (div_pos_iff_of_pos_right (by positivity)).mp this
  rw [Real.log_div hℓ.ne' (by positivity), Real.log_mul two_ne_zero hx0.ne', hx]
  ring

end Asymptotics

/-! ## Sequence-level transfer -/

section Transfer

variable {lam : ℝ} (hlam : lam ≤ 0)

theorem natCast_eq_saddleDegree_sub_half (j : ℕ) :
    (j : ℝ) = thetaCuspGaussianApertureExactTailSaddleDegree lam (saddleHeight hlam j) - 1 / 2 := by
  rw [saddleDegree_saddleHeight]
  ring

theorem saddleLog_saddleHeight (j : ℕ) : saddleLog lam (saddleHeight hlam j) = Real.log j := by
  rw [saddleLog, ← natCast_eq_saddleDegree_sub_half]

theorem saddleClockRatio_saddleHeight (j : ℕ) :
    saddleClockRatio lam (saddleHeight hlam j)
      = 6 * j / thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam j) := by
  rw [saddleClockRatio, ← natCast_eq_saddleDegree_sub_half]

/-- **(GTSD.8).**  `2 x_j / log j → 1`. -/
theorem tendsto_two_mul_saddleHeight_div_log :
    Tendsto (fun j : ℕ => 2 * saddleHeight hlam j / Real.log j) atTop (𝓝 1) := by
  have h := ((tendsto_saddleLog_div lam).comp (tendsto_saddleHeight hlam)).inv₀ one_ne_zero
  rw [inv_one] at h
  have hlog : Tendsto (fun j : ℕ => Real.log j) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 := h.sub (tendsto_inv_atTop_zero.comp hlog)
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with j hj
  simp only [Function.comp_apply, saddleLog_saddleHeight]
  field_simp
  ring

/-- **(GTSD.4) for `c = 6`.**  `6 j / J'(x_j) → 3`. -/
theorem tendsto_six_mul_div_slope :
    Tendsto (fun j : ℕ => 6 * j /
      thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam j)) atTop
        (𝓝 3) := by
  refine ((tendsto_saddleClockRatio lam).comp (tendsto_saddleHeight hlam)).congr fun j => ?_
  simp only [Function.comp_apply, saddleClockRatio_saddleHeight]

/-- `6 j Δ_j → 3`. -/
theorem tendsto_six_mul_saddleIncrement :
    Tendsto (fun j : ℕ => 6 * j * saddleIncrement hlam j) atTop (𝓝 3) := by
  have hup := tendsto_six_mul_div_slope hlam
  have hratio : Tendsto (fun j : ℕ => (j : ℝ) / (j + 1)) atTop (𝓝 1) := by
    simpa using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hlow := hratio.mul ((tendsto_six_mul_div_slope hlam).comp (tendsto_add_atTop_nat 1))
  rw [one_mul] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun j => ?_) (fun j => ?_)
  · have hb := (saddleIncrement_bounds hlam j).1
    have hs := saddleSlope_pos hlam (saddleHeight_pos hlam (j + 1)).le
    simp only [Function.comp_apply]
    push_cast
    have hj1 : (0 : ℝ) < j + 1 := by positivity
    rw [show (j : ℝ) / (j + 1) * (6 * (j + 1) /
        thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam (j + 1)))
        = 6 * j * (1 / thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam
          (saddleHeight hlam (j + 1))) by field_simp]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  · have hb := (saddleIncrement_bounds hlam j).2
    rw [show 6 * (j : ℝ) / thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam
        (saddleHeight hlam j) = 6 * j * (1 / thetaCuspGaussianApertureExactTailSaddleDegreeSlope
          lam (saddleHeight hlam j)) by ring]
    exact mul_le_mul_of_nonneg_left hb (by positivity)

end Transfer

/-! ## The canonical moving theta clock -/

section Clock

variable {lam : ℝ} (hlam : lam ≤ 0)

/-- **(GTSD.3).**  The calibrated saddle increments `α_j^{(c)} = c (x_{j+1} - x_j)`. -/
def saddleClock (c : ℝ) (j : ℕ) : ℝ := c * saddleIncrement hlam j

theorem saddleClock_pos {c : ℝ} (hc : 0 < c) (j : ℕ) : 0 < saddleClock hlam c j :=
  mul_pos hc (saddleIncrement_pos hlam j)

theorem saddleClock_antitone {c : ℝ} (hc : 0 < c) : Antitone (saddleClock hlam c) :=
  fun _ _ h => mul_le_mul_of_nonneg_left (saddleIncrement_antitone hlam h) hc.le

/-- **(GTSD.4).**  `j α_j^{(c)} → c/2`. -/
theorem tendsto_mul_saddleClock (c : ℝ) :
    Tendsto (fun j : ℕ => (j : ℝ) * saddleClock hlam c j) atTop (𝓝 (c / 2)) := by
  have h := (tendsto_six_mul_saddleIncrement hlam).const_mul (c / 6)
  rw [show c / 6 * 3 = c / 2 by ring] at h
  refine h.congr fun j => ?_
  rw [saddleClock]
  ring

theorem tendsto_saddleClock (c : ℝ) : Tendsto (saddleClock hlam c) atTop (𝓝 0) := by
  have h := (tendsto_mul_saddleClock hlam c).div_atTop tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with j hj
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  field_simp

theorem norm_saddleClock_le {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ‖((saddleClock hlam c j : ℝ) : ℂ)‖ ≤ saddleClock hlam c 0 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (saddleClock_pos hlam hc j)]
  exact saddleClock_antitone hlam hc (Nat.zero_le j)

/-- **(GTSD.3).**  The moving theta clock `A_λ^{(c)} = diag(α_j^{(c)})`. -/
def saddleClockOperator {c : ℝ} (hc : 0 < c) : HistoryLine →L[ℂ] HistoryLine :=
  _root_.HTGeometry.ellTwoDiagonal (fun j => ((saddleClock hlam c j : ℝ) : ℂ))
    (norm_saddleClock_le hlam hc)

theorem saddleClockOperator_basis {c : ℝ} (hc : 0 < c) (j : ℕ) :
    saddleClockOperator hlam hc (historyCoord j)
      = ((saddleClock hlam c j : ℝ) : ℂ) • historyCoord j :=
  diagonal_historyCoord _ _ j

theorem saddleClockOperator_isPositive {c : ℝ} (hc : 0 < c) :
    (saddleClockOperator hlam hc).IsPositive :=
  isPositive_ellTwoDiagonal_ofReal _ _ fun j => (saddleClock_pos hlam hc j).le

theorem isCompactOperator_saddleClockOperator {c : ℝ} (hc : 0 < c) :
    IsCompactOperator (saddleClockOperator hlam hc) := by
  refine isCompactOperator_of_diag_tendsto_cofinite historyCoord
    (c := fun j => ((saddleClock hlam c j : ℝ) : ℂ)) (saddleClockOperator_basis hlam hc) ?_
  rw [Nat.cofinite_eq_atTop]
  simpa [Real.norm_eq_abs, abs_of_pos (saddleClock_pos hlam hc _)] using
    (tendsto_saddleClock hlam c).norm

theorem approxNumber_saddleClockOperator {c : ℝ} (hc : 0 < c) (n : ℕ) :
    approxNumber (saddleClockOperator hlam hc) n = saddleClock hlam c n :=
  _root_.HTGeometry.approxNumber_ellTwoDiagonal_reindex_eq (Equiv.refl ℕ)
    (lam := fun k => ((saddleClock hlam c k : ℝ) : ℂ)) (r := saddleClock hlam c)
    (fun i => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (saddleClock_pos hlam hc i)]
      rfl)
    (fun i => (saddleClock_pos hlam hc i).le) (fun h => saddleClock_antitone hlam hc h) n

theorem tendsto_succ_mul_saddleClock (c : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * saddleClock hlam c n) atTop (𝓝 (c / 2)) := by
  have h := (tendsto_mul_saddleClock hlam c).add (tendsto_saddleClock hlam c)
  rw [add_zero] at h
  exact h.congr fun n => by ring

/-- **Theorem GTSD-A, (GTSD.5).**  `A_λ^{(c)}` is positive compact, weak trace class with honest
logarithmic residue `c/2`, not trace class, and in every `S_p`, `p > 1`. -/
theorem saddleClockOperator_residue {c : ℝ} (hc : 0 < c) :
    MemWeakSchattenClass 1 (saddleClockOperator hlam hc) ∧
      HasSchattenLogResidue 1 (saddleClockOperator hlam hc) (c / 2) ∧
      ¬MemSchattenClass 1 (saddleClockOperator hlam hc) ∧
      ∀ p : ℝ, 1 < p → MemSchattenClass p (saddleClockOperator hlam hc) := by
  obtain ⟨C, hC⟩ := (tendsto_succ_mul_saddleClock hlam c).bddAbove_range
  have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (saddleClock_pos hlam hc 0).le).trans
    (hC ⟨0, rfl⟩)
  have hweak : MemWeakSchattenClass 1 (saddleClockOperator hlam hc) :=
    ⟨C, hC0, fun n => by
      rw [Real.rpow_one, approxNumber_saddleClockOperator, le_div_iff₀ (by positivity), mul_comm]
      exact hC ⟨n, rfl⟩⟩
  have hres : HasSchattenLogResidue 1 (saddleClockOperator hlam hc) (c / 2) :=
    hasSchattenLogResidue_of_tendsto_mul_succ ((tendsto_succ_mul_saddleClock hlam c).congr
      fun n => by rw [Real.rpow_one, approxNumber_saddleClockOperator, mul_comm])
  exact ⟨hweak, hres, hres.not_memSchattenClass (by positivity),
    fun p hp => hweak.memSchattenClass_of_lt one_pos hp⟩

/-- **Theorem GTSD-A.**  The unique calibration matching the source residue `3` is `c = 6`. -/
theorem saddleClock_calibration {c : ℝ} (hc : 0 < c) :
    HasSchattenLogResidue 1 (saddleClockOperator hlam hc) 3 ↔ c = 6 := by
  have hres := (saddleClockOperator_residue hlam hc).2.1
  constructor
  · intro h3
    have := tendsto_nhds_unique hres h3
    linarith
  · rintro rfl
    rwa [show (6 : ℝ) / 2 = 3 by norm_num] at hres

end Clock

/-! ## Double-logarithmic sums -/

section DoubleLog

theorem antitoneOn_inv_mul_log : AntitoneOn (fun x : ℝ => 1 / (x * Real.log x)) (Ici 2) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) < x := by linarith [mem_Ici.mp hx]
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hly : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  exact one_div_le_one_div_of_le (mul_pos (by linarith) hlx)
    (mul_le_mul hxy hly hlx.le (by linarith))

/-- `Σ_{J ≤ n < N} 1/(n log n) ≥ log log N - log log J`. -/
theorem sum_inv_mul_log_ge {J N : ℕ} (hJ : 2 ≤ J) (hJN : J ≤ N) :
    Real.log (Real.log N) - Real.log (Real.log J) ≤
      ∑ i ∈ Finset.range (N - J), 1 / (((J + i : ℕ) : ℝ) * Real.log (J + i : ℕ)) := by
  have hJ' : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hmono : AntitoneOn (fun x : ℝ => 1 / (x * Real.log x))
      (Icc (J : ℝ) ((J : ℝ) + ((N - J : ℕ) : ℝ))) :=
    antitoneOn_inv_mul_log.mono fun x hx => mem_Ici.mpr (hJ'.trans hx.1)
  have h := hmono.integral_le_sum
  have hN : (J : ℝ) + ((N - J : ℕ) : ℝ) = N := by
    rw [Nat.cast_sub hJN]
    ring
  rw [hN, Sieve.integral_inv_mul_log_eq (by linarith) (by exact_mod_cast hJN)] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  push_cast
  rfl

/-- `Σ_{J ≤ n < N} 1/(n log n) ≤ log log N - log log (J - 1)` for `J ≥ 3`. -/
theorem sum_inv_mul_log_le {J N : ℕ} (hJ : 3 ≤ J) (hJN : J ≤ N) :
    ∑ i ∈ Finset.range (N - J), 1 / (((J + i : ℕ) : ℝ) * Real.log (J + i : ℕ)) ≤
      Real.log (Real.log N) - Real.log (Real.log ((J : ℝ) - 1)) := by
  have hJ' : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  set x₀ : ℝ := (J : ℝ) - 1
  have hmono : AntitoneOn (fun x : ℝ => 1 / (x * Real.log x))
      (Icc x₀ (x₀ + ((N - J : ℕ) : ℝ))) :=
    antitoneOn_inv_mul_log.mono fun x hx => mem_Ici.mpr (by linarith [hx.1])
  have h := hmono.sum_le_integral
  have hN : x₀ + ((N - J : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hJN]
    ring
  rw [hN, Sieve.integral_inv_mul_log_eq (by linarith) (by
    have : (J : ℝ) ≤ N := by exact_mod_cast hJN
    linarith)] at h
  have hmonoN : Real.log (Real.log ((N : ℝ) - 1)) ≤ Real.log (Real.log N) := by
    have hN3 : (3 : ℝ) ≤ N := hJ'.trans (by exact_mod_cast hJN)
    exact Real.log_le_log (Real.log_pos (by linarith))
      (Real.log_le_log (by linarith) (by linarith))
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) (h.trans (by linarith))
  simp only [x₀]
  push_cast
  ring_nf

theorem tendsto_log_log_natCast :
    Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

end DoubleLog

/-! ## The double-log relative clock -/

section Relative

variable {lam : ℝ} (hlam : lam ≤ 0)

/-- **(GTSD.11).**  The relative clock diagonal `b_j = h_j - α_j`, `h_j = 6/(2j+9)`. -/
def relativeClock (j : ℕ) : ℝ := elapsedDefect 1 j - saddleClock hlam 6 j

theorem natCast_mul_elapsedDefect_one_sub (j : ℕ) :
    (j : ℝ) * elapsedDefect 1 j - 3 = -(27 / (2 * (j : ℝ) + 9)) := by
  rw [elapsedDefect_one_eq]
  have h : (2 * (j : ℝ) + 9) ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_log_mul_elapsedDefect_one_sub :
    Tendsto (fun j : ℕ => Real.log j * ((j : ℝ) * elapsedDefect 1 j - 3)) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_log_div_mul_add_atTop 2 9 1 two_ne_zero).comp
    tendsto_natCast_atTop_atTop).const_mul (-27)
  rw [mul_zero] at h
  refine h.congr fun j => ?_
  simp only [Function.comp_apply, pow_one, natCast_mul_elapsedDefect_one_sub]
  ring

theorem tendsto_log_div_log_succ :
    Tendsto (fun j : ℕ => Real.log j / Real.log ((j + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun j : ℕ => Real.log ((j + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (Real.tendsto_log_nat_add_one_sub_log.div_atTop hlog)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with j hj
  push_cast at hj ⊢
  field_simp
  ring

theorem tendsto_log_div_succ :
    Tendsto (fun j : ℕ => Real.log j / ((j : ℝ) + 1)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun j => ?_
  simp only [Function.comp_apply, pow_one, one_mul]

/-- **Theorem GTSD-B, (GTSD.12).**  `j log j (h_j - α_j) → 3`. -/
theorem tendsto_relativeClock_doubleLog :
    Tendsto (fun j : ℕ => (j : ℝ) * Real.log j * relativeClock hlam j) atTop (𝓝 3) := by
  set P : ℕ → ℝ := fun j => 6 * j /
    thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam j)
  have hP3 : Tendsto P atTop (𝓝 3) := tendsto_six_mul_div_slope hlam
  have hsaddle : Tendsto (fun j : ℕ => Real.log j * (3 - P j)) atTop (𝓝 3) := by
    refine ((tendsto_saddleLog_mul_three_sub lam).comp (tendsto_saddleHeight hlam)).congr
      fun j => ?_
    simp only [Function.comp_apply, saddleLog_saddleHeight, saddleClockRatio_saddleHeight, P]
  have hlow : Tendsto (fun j : ℕ => Real.log j * ((j : ℝ) * elapsedDefect 1 j - 3) +
      Real.log j * (3 - P j)) atTop (𝓝 3) := by
    simpa using (tendsto_log_mul_elapsedDefect_one_sub).add hsaddle
  have hsucc : Tendsto (fun j : ℕ => Real.log j / Real.log ((j + 1 : ℕ) : ℝ) *
      (Real.log ((j + 1 : ℕ) : ℝ) * (3 - P (j + 1)))) atTop (𝓝 3) := by
    simpa using tendsto_log_div_log_succ.mul (hsaddle.comp (tendsto_add_atTop_nat 1))
  have hrem : Tendsto (fun j : ℕ => Real.log j / ((j : ℝ) + 1) * P (j + 1)) atTop (𝓝 0) := by
    simpa using tendsto_log_div_succ.mul (hP3.comp (tendsto_add_atTop_nat 1))
  have hup : Tendsto (fun j : ℕ => Real.log j * ((j : ℝ) * elapsedDefect 1 j - 3) +
      Real.log j / Real.log ((j + 1 : ℕ) : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) * (3 - P (j + 1))) +
      Real.log j / ((j : ℝ) + 1) * P (j + 1)) atTop (𝓝 3) := by
    simpa using ((tendsto_log_mul_elapsedDefect_one_sub).add hsucc).add hrem
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hlog : 0 ≤ Real.log j := Real.log_natCast_nonneg j
    have hb := (saddleIncrement_bounds hlam j).2
    have hs := saddleSlope_pos hlam (saddleHeight_pos hlam j).le
    rw [relativeClock, saddleClock]
    have hPj : 6 * (j : ℝ) * saddleIncrement hlam j ≤ P j := by
      simp only [P]
      rw [show 6 * (j : ℝ) / thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam
          (saddleHeight hlam j) = 6 * j * (1 / thetaCuspGaussianApertureExactTailSaddleDegreeSlope
            lam (saddleHeight hlam j)) by ring]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hPj hlog]
  · filter_upwards [eventually_ge_atTop 2] with j hj
    have hlog : 0 ≤ Real.log j := Real.log_natCast_nonneg j
    have hlog1 : 0 < Real.log ((j + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast Nat.lt_succ_of_le (by omega : 1 ≤ j))
    have hb := (saddleIncrement_bounds hlam j).1
    have hs := saddleSlope_pos hlam (saddleHeight_pos hlam (j + 1)).le
    rw [relativeClock, saddleClock]
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hQ : (j : ℝ) / ((j : ℝ) + 1) * P (j + 1) ≤ 6 * (j : ℝ) * saddleIncrement hlam j := by
      simp only [P]
      push_cast
      rw [show (j : ℝ) / ((j : ℝ) + 1) * (6 * ((j : ℝ) + 1) /
          thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam (j + 1)))
          = 6 * j * (1 / thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam
            (saddleHeight hlam (j + 1))) by field_simp]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    have hid : Real.log j / Real.log ((j + 1 : ℕ) : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) *
        (3 - P (j + 1))) = Real.log j * (3 - P (j + 1)) := by
      field_simp
    have hid2 : Real.log j / ((j : ℝ) + 1) * P (j + 1) + Real.log j * (3 - P (j + 1))
        = Real.log j * (3 - (j : ℝ) / ((j : ℝ) + 1) * P (j + 1)) := by
      field_simp
      ring
    rw [hid]
    nlinarith [mul_le_mul_of_nonneg_left hQ hlog]

end Relative

/-! ## Diagonal approximation numbers and double-log sums -/

section DiagonalBounds

/-- A diagonal whose entries beyond `n` are bounded by `M` has `a_n ≤ M`. -/
theorem approxNumber_ellTwoDiagonal_le_of_tail {lam : ℕ → ℂ} {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C)
    (n : ℕ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, n ≤ i → ‖lam i‖ ≤ M) :
    approxNumber (_root_.HTGeometry.ellTwoDiagonal lam hC) n ≤ M := by
  let F := _root_.HTGeometry.ellTwoDiagonal
    (_root_.HTGeometry.equivTruncMultiplier (Equiv.refl ℕ) lam n)
    (_root_.HTGeometry.norm_equivTruncMultiplier_le (Equiv.refl ℕ) hC n)
  let tail : ℕ → ℂ := fun i => if n ≤ i then lam i else 0
  have htail : ∀ i, ‖tail i‖ ≤ M := fun i => by
    dsimp [tail]
    split_ifs with hi
    · exact hM i hi
    · simpa using hM0
  have hsub : _root_.HTGeometry.ellTwoDiagonal lam hC - F =
      _root_.HTGeometry.ellTwoDiagonal tail htail := by
    ext f i
    change lam i * f i - _root_.HTGeometry.equivTruncMultiplier (Equiv.refl ℕ) lam n i * f i
      = tail i * f i
    dsimp [tail, _root_.HTGeometry.equivTruncMultiplier]
    by_cases hi : i < n
    · simp [hi, Nat.not_le.mpr hi]
    · simp [hi, Nat.le_of_not_gt hi]
  calc approxNumber (_root_.HTGeometry.ellTwoDiagonal lam hC) n
      ≤ ‖_root_.HTGeometry.ellTwoDiagonal lam hC - F‖ :=
        approxNumber_le _ n _
          (_root_.HTGeometry.hasRankLE_ellTwoDiagonal_equivTrunc (Equiv.refl ℕ) lam hC n)
    _ = ‖_root_.HTGeometry.ellTwoDiagonal tail htail‖ := by rw [hsub]
    _ ≤ M := _root_.HTGeometry.norm_ellTwoDiagonal_le tail htail hM0

/-- Ky Fan: the partial diagonal sums are bounded by the partial approximation-number sums. -/
theorem sum_le_sum_approxNumber_ellTwoDiagonal {r : ℕ → ℝ} (hr : ∀ i, 0 ≤ r i) {C : ℝ}
    (hC : ∀ i, ‖((r i : ℝ) : ℂ)‖ ≤ C)
    (hcpt : IsCompactOperator (_root_.HTGeometry.ellTwoDiagonal (fun i => ((r i : ℝ) : ℂ)) hC))
    (N : ℕ) :
    ∑ i ∈ Finset.range N, r i ≤ ∑ n ∈ Finset.range N,
      approxNumber (_root_.HTGeometry.ellTwoDiagonal (fun i => ((r i : ℝ) : ℂ)) hC) n := by
  have hkf := sum_norm_inner_le_sum_singVal hcpt (g := historyCoord) (h := historyCoord)
    (fun n => Or.inr (norm_historyCoord n))
    (fun m n hmn => by rw [inner_historyCoord, if_neg hmn])
    (fun n => Or.inr (norm_historyCoord n))
    (fun m n hmn => by rw [inner_historyCoord, if_neg hmn]) (Finset.range N)
    (le_of_eq (Finset.card_range N))
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) (hkf.trans (le_of_eq
    (Finset.sum_congr rfl fun n _ => (approxNumber_eq_singVal hcpt n).symm)))
  rw [diagonal_historyCoord, inner_smul_right, inner_historyCoord, if_pos rfl, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr i)]

/-- Upper double-log comparison. -/
theorem eventually_sum_div_log_log_lt {u : ℕ → ℝ} {R a : ℝ} (hR : 0 ≤ R) (ha : R < a)
    (hbound : ∀ ε > 0, ∃ J : ℕ, ∀ n ≥ J, u n ≤ (R + ε) / (n * Real.log n)) :
    ∀ᶠ N in atTop, (∑ n ∈ Finset.range N, u n) / Real.log (Real.log N) < a := by
  set ε := (a - R) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨J₀, hJ₀⟩ := hbound ε hε
  set J := max J₀ 3
  set K := ∑ n ∈ Finset.range J, u n - (R + ε) * Real.log (Real.log ((J : ℝ) - 1))
  have hK : Tendsto (fun N : ℕ => K / Real.log (Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_log_natCast
  filter_upwards [eventually_ge_atTop J, tendsto_log_log_natCast.eventually_gt_atTop 0,
    hK.eventually (gt_mem_nhds (show (0 : ℝ) < a - R - ε by simp only [ε]; linarith))]
    with N hN hll hKN
  have hsplit : ∑ n ∈ Finset.range N, u n = ∑ n ∈ Finset.range J, u n +
      ∑ i ∈ Finset.range (N - J), u (J + i) := by
    rw [← Finset.sum_range_add, Nat.add_sub_cancel' hN]
  have htail : ∑ i ∈ Finset.range (N - J), u (J + i) ≤
      (R + ε) * ∑ i ∈ Finset.range (N - J), 1 / (((J + i : ℕ) : ℝ) * Real.log (J + i : ℕ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := hJ₀ (J + i) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
    rw [mul_one_div]
    exact h
  have hlog := sum_inv_mul_log_le (le_max_right J₀ 3) hN
  have hRε : 0 ≤ R + ε := by linarith
  have hbnd : ∑ n ∈ Finset.range N, u n ≤ K + (R + ε) * Real.log (Real.log N) := by
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hlog hRε
    simp only [K]
    nlinarith
  rw [div_lt_iff₀ hll]
  have hK' : K < (a - R - ε) * Real.log (Real.log N) := by
    rwa [div_lt_iff₀ hll] at hKN
  nlinarith

/-- Lower double-log comparison. -/
theorem eventually_lt_sum_div_log_log {u : ℕ → ℝ} {R a : ℝ} (ha : a < R) (hu : ∀ n, 0 ≤ u n)
    (hbound : ∀ ε > 0, ∃ J : ℕ, ∀ n ≥ J, (R - ε) / (n * Real.log n) ≤ u n) :
    ∀ᶠ N in atTop, a < (∑ n ∈ Finset.range N, u n) / Real.log (Real.log N) := by
  set ε := (R - a) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨J₀, hJ₀⟩ := hbound ε hε
  set J := max J₀ 2
  rcases le_or_gt (R - ε) 0 with hneg | hpos
  · filter_upwards [tendsto_log_log_natCast.eventually_gt_atTop 0] with N hll
    have ha0 : a < 0 := by simp only [ε] at hneg; linarith
    exact ha0.trans_le (div_nonneg (Finset.sum_nonneg fun n _ => hu n) hll.le)
  · have hK : Tendsto (fun N : ℕ => (R - ε) * Real.log (Real.log J) / Real.log (Real.log N))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_log_log_natCast
    filter_upwards [eventually_ge_atTop J, tendsto_log_log_natCast.eventually_gt_atTop 0,
      hK.eventually (gt_mem_nhds (show (0 : ℝ) < R - ε - a by simp only [ε]; linarith))]
      with N hN hll hKN
    have hsplit : ∑ n ∈ Finset.range N, u n = ∑ n ∈ Finset.range J, u n +
        ∑ i ∈ Finset.range (N - J), u (J + i) := by
      rw [← Finset.sum_range_add, Nat.add_sub_cancel' hN]
    have htail : (R - ε) * ∑ i ∈ Finset.range (N - J),
        1 / (((J + i : ℕ) : ℝ) * Real.log (J + i : ℕ)) ≤
          ∑ i ∈ Finset.range (N - J), u (J + i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h := hJ₀ (J + i) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))
      rw [mul_one_div]
      exact h
    have hlog := sum_inv_mul_log_ge (le_max_right J₀ 2) hN
    have hhead : 0 ≤ ∑ n ∈ Finset.range J, u n := Finset.sum_nonneg fun n _ => hu n
    have hbnd : (R - ε) * (Real.log (Real.log N) - Real.log (Real.log J)) ≤
        ∑ n ∈ Finset.range N, u n := by
      rw [hsplit]
      have := mul_le_mul_of_nonneg_left hlog hpos.le
      linarith
    rw [lt_div_iff₀ hll]
    rw [div_lt_iff₀ hll] at hKN
    nlinarith

end DiagonalBounds

/-! ## The relative clock operator -/

section RelativeOperator

variable {lam : ℝ} (hlam : lam ≤ 0)

theorem relativeClock_le_one (j : ℕ) : relativeClock hlam j ≤ 1 := by
  have h1 := elapsedDefect_le_one 1 j
  have h2 := (saddleClock_pos hlam (by norm_num : (0 : ℝ) < 6) j).le
  rw [relativeClock]
  linarith

theorem abs_relativeClock_le (j : ℕ) : |relativeClock hlam j| ≤ 1 + saddleClock hlam 6 0 := by
  have h1 := elapsedDefect_nonneg 1 j
  have h2 := saddleClock_antitone hlam (by norm_num : (0 : ℝ) < 6) (Nat.zero_le j)
  have h3 := (saddleClock_pos hlam (by norm_num : (0 : ℝ) < 6) j).le
  have h4 := elapsedDefect_le_one 1 j
  rw [relativeClock, abs_le]
  constructor <;> linarith

/-- **(GTSD.11).**  The relative clock `B_λ = D_1 - A_λ`. -/
def relativeClockOperator : HistoryLine →L[ℂ] HistoryLine :=
  elapsedHistoryDefect 1 - saddleClockOperator hlam (by norm_num : (0 : ℝ) < 6)

theorem relativeClockOperator_basis (j : ℕ) :
    relativeClockOperator hlam (historyCoord j)
      = ((relativeClock hlam j : ℝ) : ℂ) • historyCoord j := by
  rw [relativeClockOperator, sub_apply, elapsedHistoryDefect_basis, saddleClockOperator_basis,
    ← sub_smul, relativeClock, Complex.ofReal_sub]

theorem isCompactOperator_relativeClockOperator :
    IsCompactOperator (relativeClockOperator hlam) :=
  (isCompactOperator_elapsedHistoryDefect 1).sub
    (isCompactOperator_saddleClockOperator hlam (by norm_num))

/-- **Theorem GTSD-B.**  The relative diagonal is eventually positive. -/
theorem eventually_relativeClock_pos : ∀ᶠ j : ℕ in atTop, 0 < relativeClock hlam j := by
  filter_upwards [(tendsto_relativeClock_doubleLog hlam).eventually
    (lt_mem_nhds (show (0 : ℝ) < 3 by norm_num)), eventually_ge_atTop 2] with j hj hj2
  have hjpos : (0 : ℝ) < (j : ℝ) * Real.log j :=
    mul_pos (by exact_mod_cast (by omega : 0 < j))
      (Real.log_pos (by exact_mod_cast (by omega : 1 < j)))
  exact pos_of_mul_pos_right hj hjpos.le

/-- The two-sided `ε`-bounds `(3 ∓ ε)/(j log j)` on the relative clock. -/
theorem relativeClock_bounds {ε : ℝ} (hε : 0 < ε) : ∃ J : ℕ, ∀ n ≥ J,
    (3 - ε) / (n * Real.log n) ≤ relativeClock hlam n ∧
      relativeClock hlam n ≤ (3 + ε) / (n * Real.log n) := by
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp (tendsto_relativeClock_doubleLog hlam) ε hε
  refine ⟨max J 2, fun n hn => ?_⟩
  have hd := hJ n (le_trans (le_max_left _ _) hn)
  rw [Real.dist_eq, abs_lt] at hd
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hpos : (0 : ℝ) < (n : ℝ) * Real.log n :=
    mul_pos (by exact_mod_cast (by omega : 0 < n))
      (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
  constructor
  · rw [div_le_iff₀ hpos]
    linarith [mul_comm ((n : ℝ) * Real.log n) (relativeClock hlam n)]
  · rw [le_div_iff₀ hpos]
    linarith [mul_comm ((n : ℝ) * Real.log n) (relativeClock hlam n)]

/-- **Theorem GTSD-B.**  `B_λ` is compact but not trace class. -/
theorem not_memSchattenClass_relativeClockOperator :
    ¬MemSchattenClass 1 (relativeClockOperator hlam) := by
  intro h
  have hs := h.one_summable_norm_inner_diag_basis historyCoord
  have hdiag : ∀ j, ‖⟪historyCoord j, relativeClockOperator hlam (historyCoord j)⟫_ℂ‖
      = |relativeClock hlam j| := fun j => by
    rw [relativeClockOperator_basis, inner_smul_right, inner_historyCoord, if_pos rfl, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hdiag] at hs
  obtain ⟨J₀, hJ₀⟩ := relativeClock_bounds hlam (show (0 : ℝ) < 2 by norm_num)
  set J := max J₀ 2
  have hsub := hs.comp_injective (add_right_injective J)
  obtain ⟨N, hN⟩ := (tendsto_log_log_natCast.eventually_gt_atTop
    (∑' i, |relativeClock hlam (J + i)| + Real.log (Real.log J))).exists_forall_of_atTop
  have hN' := hN (max N J) (le_max_left _ _)
  have hlog := sum_inv_mul_log_ge (le_max_right J₀ 2) (le_max_right N J)
  have hsum : ∑ i ∈ Finset.range (max N J - J), 1 / (((J + i : ℕ) : ℝ) * Real.log (J + i : ℕ))
      ≤ ∑' i, |relativeClock hlam (J + i)| := by
    refine le_trans (Finset.sum_le_sum fun i _ => ?_)
      (Summable.sum_le_tsum _ (fun i _ => abs_nonneg _) hsub)
    have h1 := (hJ₀ (J + i) (le_trans (le_max_left _ _) (Nat.le_add_right _ _))).1
    show _ ≤ |relativeClock hlam (J + i)|
    calc 1 / (((J + i : ℕ) : ℝ) * Real.log (J + i : ℕ))
        = (3 - 2) / (((J + i : ℕ) : ℝ) * Real.log (J + i : ℕ)) := by norm_num
      _ ≤ relativeClock hlam (J + i) := h1
      _ ≤ |relativeClock hlam (J + i)| := le_abs_self _
  linarith

/-- The positive part `B_λ⁺`, deleting the finite negative head of `B_λ`. -/
def relativeClockPos (j : ℕ) : ℝ := max (relativeClock hlam j) 0

theorem norm_relativeClockPos_le (j : ℕ) : ‖((relativeClockPos hlam j : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (relativeClock_le_one hlam j) zero_le_one

/-- **Corollary GTSD-C.**  `B_λ⁺ = diag(max(b_j, 0))`. -/
def relativeClockPosOperator : HistoryLine →L[ℂ] HistoryLine :=
  _root_.HTGeometry.ellTwoDiagonal (fun j => ((relativeClockPos hlam j : ℝ) : ℂ))
    (norm_relativeClockPos_le hlam)

theorem isCompactOperator_relativeClockPosOperator :
    IsCompactOperator (relativeClockPosOperator hlam) := by
  refine isCompactOperator_of_diag_tendsto_cofinite historyCoord
    (c := fun j => ((relativeClockPos hlam j : ℝ) : ℂ)) (fun j => diagonal_historyCoord _ _ j) ?_
  rw [Nat.cofinite_eq_atTop]
  have h0 : Tendsto (relativeClock hlam) atTop (𝓝 0) := by
    have h := (tendsto_relativeClock_doubleLog hlam).div_atTop
      ((tendsto_natCast_atTop_atTop).atTop_mul_atTop₀
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with j hj
    have hpos : (0 : ℝ) < (j : ℝ) * Real.log j :=
      mul_pos (by exact_mod_cast (by omega : 0 < j))
        (Real.log_pos (by exact_mod_cast (by omega : 1 < j)))
    have hl : Real.log j ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < j))).ne'
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    simp only [Function.comp_apply]
    field_simp
  have hmax : Tendsto (fun i => relativeClockPos hlam i) atTop (𝓝 0) := by
    have := h0.max (tendsto_const_nhds (x := (0 : ℝ)))
    rwa [max_self] at this
  refine hmax.congr fun i => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]

/-- **Corollary GTSD-C.**  `B_λ - B_λ⁺` has finite rank. -/
theorem exists_hasRankLE_relativeClockOperator_sub :
    ∃ K : ℕ, HasRankLE (relativeClockOperator hlam - relativeClockPosOperator hlam) K := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_relativeClock_pos hlam)
  have hC : ∀ j, ‖((min (relativeClock hlam j) 0 : ℝ) : ℂ)‖ ≤ 1 + saddleClock hlam 6 0 :=
    fun j => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine (abs_le.mpr ⟨?_, ?_⟩)
      · have := (abs_le.mp (abs_relativeClock_le hlam j)).1
        exact le_min this (by linarith [(saddleClock_pos hlam (by norm_num : (0:ℝ) < 6) 0).le])
      · exact (min_le_right _ _).trans (by linarith [(saddleClock_pos hlam
          (by norm_num : (0:ℝ) < 6) 0).le])
  refine ⟨K, ?_⟩
  have heq : relativeClockOperator hlam - relativeClockPosOperator hlam =
      _root_.HTGeometry.ellTwoDiagonal
        (_root_.HTGeometry.equivTruncMultiplier (Equiv.refl ℕ)
          (fun j => ((min (relativeClock hlam j) 0 : ℝ) : ℂ)) K)
        (_root_.HTGeometry.norm_equivTruncMultiplier_le (Equiv.refl ℕ) hC K) := by
    refine historyCoord_ext fun i k => ?_
    rw [sub_apply, relativeClockOperator_basis, relativeClockPosOperator, diagonal_historyCoord,
      diagonal_historyCoord, ← sub_smul]
    congr 2
    simp only [_root_.HTGeometry.equivTruncMultiplier, Equiv.refl_symm, Equiv.refl_apply,
      relativeClockPos]
    split_ifs with hk
    · rcases le_total (relativeClock hlam k) 0 with h | h
      · rw [max_eq_right h, min_eq_left h]
        simp
      · rw [max_eq_left h, min_eq_right h]
        simp
    · have hpos := hK k (Nat.le_of_not_gt hk)
      rw [max_eq_left hpos.le]
      simp
  rw [heq]
  exact _root_.HTGeometry.hasRankLE_ellTwoDiagonal_equivTrunc (Equiv.refl ℕ) _ hC K

/-- **Corollary GTSD-C, (GTSD.15).**  `(1/log log N) ∑_{j<N} s_j(B_λ⁺) → 3`. -/
theorem tendsto_sum_approxNumber_relativeClockPos_div_log_log :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, approxNumber (relativeClockPosOperator hlam) n) /
      Real.log (Real.log N)) atTop (𝓝 3) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hlow := eventually_lt_sum_div_log_log (u := relativeClockPos hlam) ha
      (fun n => le_max_right _ _)
      (fun ε hε => by
        obtain ⟨J, hJ⟩ := relativeClock_bounds hlam hε
        exact ⟨J, fun n hn => (hJ n hn).1.trans (le_max_left _ _)⟩)
    filter_upwards [hlow, tendsto_log_log_natCast.eventually_gt_atTop 0] with N hN hll
    refine hN.trans_le (div_le_div_of_nonneg_right ?_ hll.le)
    exact sum_le_sum_approxNumber_ellTwoDiagonal (fun n => le_max_right _ _)
      (norm_relativeClockPos_le hlam) (isCompactOperator_relativeClockPosOperator hlam) N
  · intro a ha
    exact eventually_sum_div_log_log_lt (by norm_num) ha fun ε hε => by
      obtain ⟨J, hJ⟩ := relativeClock_bounds hlam hε
      refine ⟨max J 2, fun n hn => ?_⟩
      refine approxNumber_ellTwoDiagonal_le_of_tail _ n (by
        have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
        have : (0 : ℝ) < (n : ℝ) * Real.log n := mul_pos (by exact_mod_cast (by omega : 0 < n))
          (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
        positivity) fun i hi => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      have hi2 : 2 ≤ i := le_trans (le_trans (le_max_right _ _) hn) hi
      have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
      have hnpos : (0 : ℝ) < (n : ℝ) * Real.log n := mul_pos (by exact_mod_cast (by omega : 0 < n))
        (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))
      have hmono : (n : ℝ) * Real.log n ≤ (i : ℝ) * Real.log i := mul_le_mul
        (by exact_mod_cast hi) (Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
          (by exact_mod_cast hi)) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
          (by positivity)
      have hbi := (hJ i (le_trans (le_trans (le_max_left _ _) hn) hi)).2
      refine max_le (hbi.trans (div_le_div_of_nonneg_left (by linarith) hnpos hmono)) ?_
      positivity

theorem tendsto_log_log_div_log_succ :
    Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlogN)
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
    exact div_nonneg (Real.log_nonneg (by
      rw [← Real.exp_le_exp, Real.exp_log (by linarith)]
      exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hN')) (Real.log_nonneg (by linarith))
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hl : 0 < Real.log N := Real.log_pos (by linarith)
    have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by
      rw [← Real.exp_le_exp, Real.exp_log (by linarith)]
      exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hN')
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
    exact div_le_div_of_nonneg_left hll hl (Real.log_le_log (by linarith) (by linarith))

/-- **Corollary GTSD-C, (GTSD.16).**  At ordinary weak-trace scale the anomaly has residue `0`. -/
theorem hasSchattenLogResidue_relativeClockPosOperator :
    HasSchattenLogResidue 1 (relativeClockPosOperator hlam) 0 := by
  have h := (tendsto_sum_approxNumber_relativeClockPos_div_log_log hlam).mul
    tendsto_log_log_div_log_succ
  rw [mul_zero] at h
  unfold HasSchattenLogResidue schattenPowerPartialSum
  refine h.congr' ?_
  filter_upwards [tendsto_log_log_natCast.eventually_gt_atTop 0] with N hll
  simp only [Real.rpow_one]
  field_simp

/-- **Theorem GTSD-D, (GTSD.17)–(GTSD.18).**  The double-log finite part
`lim (∑_{j<N} (h_j - α_j) - 3 log log N) = 3 log(π/2) - 3ψ(9/2) + 6 x_0`. -/
theorem tendsto_relativeClock_finitePart :
    Tendsto (fun N : ℕ => ((∑ j ∈ Finset.range N, relativeClock hlam j
      - 3 * Real.log (Real.log N) : ℝ) : ℂ)) atTop
      (𝓝 (3 * Real.log (Real.pi / 2) - 3 * Complex.digamma (9 / 2) +
        6 * saddleHeight hlam 0)) := by
  have hsrc := tendsto_sum_elapsedDefect_sub_log 1
  rw [elapsedFinitePart_one] at hsrc
  have hsad := (Complex.continuous_ofReal.tendsto _).comp
    ((tendsto_saddleLog_finitePart lam).comp (tendsto_saddleHeight hlam))
  have h := (hsrc.add hsad).add (tendsto_const_nhds (x := ((6 * saddleHeight hlam 0 : ℝ) : ℂ)))
  have hlim : -3 * Complex.digamma (9 / 2) + ((3 * Real.log (Real.pi / 2) : ℝ) : ℂ) +
      ((6 * saddleHeight hlam 0 : ℝ) : ℂ) = 3 * Real.log (Real.pi / 2) -
        3 * Complex.digamma (9 / 2) + 6 * saddleHeight hlam 0 := by
    push_cast
    ring
  rw [hlim] at h
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, saddleLog_saddleHeight]
  have htel : ∑ j ∈ Finset.range N, relativeClock hlam j = ∑ j ∈ Finset.range N, elapsedDefect 1 j
      - 6 * (saddleHeight hlam N - saddleHeight hlam 0) := by
    simp only [relativeClock, saddleClock, Finset.sum_sub_distrib, ← Finset.mul_sum,
      saddleIncrement, Finset.sum_range_sub (saddleHeight hlam)]
  rw [htel]
  push_cast
  ring

end RelativeOperator

/-! ## The two-step singular filtration -/

section Filtration

variable {lam : ℝ} (hlam : lam ≤ 0)

/-- **(GTSD.21).**  `A_λ + B_λ = D_1`. -/
theorem saddleClockOperator_add_relativeClockOperator :
    saddleClockOperator hlam (by norm_num : (0 : ℝ) < 6) + relativeClockOperator hlam
      = elapsedHistoryDefect 1 := by
  rw [relativeClockOperator, add_sub_cancel]

/-- **ULF-GTSD-001.**  The inverse-saddle increments `α_j^{(c)} = c(x_{j+1} - x_j)` of the exact
first-atom saddle degree decrease to zero with `j α_j^{(c)} → c/2`, so `A_λ^{(c)}` is positive
compact, weak trace class with residue `c/2` (and `c = 6` is the unique calibration matching the
source residue `3`); the relative clock `B_λ = D_1 - A_λ` has `j log j (h_j - α_j) → 3`, is
eventually positive, compact and not trace class; its positive part `B_λ⁺` differs from `B_λ` by
finite rank, has double-log residue `3` and ordinary log residue `0`; and the double-log finite
part is `3 log(π/2) - 3ψ(9/2) + 6 x_0`.  Together `A_λ + B_λ = D_1`. -/
theorem gamma_six_theta_saddle_double_log_clock :
    (∀ j : ℕ, 0 < saddleHeight hlam j ∧
      thetaCuspGaussianApertureExactTailSaddleDegree lam (saddleHeight hlam j) = (j : ℝ) + 1 / 2 ∧
      1 / thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam (j + 1))
          ≤ saddleIncrement hlam j ∧
      saddleIncrement hlam j
        ≤ 1 / thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam (saddleHeight hlam j)) ∧
    (∀ {x : ℝ}, 0 ≤ x → 0 < thetaCuspGaussianApertureExactTailSaddleDegreeSlope lam x ∧
      0 < thetaCuspGaussianApertureExactTailSaddleDegreeCurvature lam x) ∧
    Tendsto (fun j : ℕ => 2 * saddleHeight hlam j / Real.log j) atTop (𝓝 1) ∧
    (∀ {c : ℝ} (hc : 0 < c), (∀ j, 0 < saddleClock hlam c j) ∧ Antitone (saddleClock hlam c) ∧
      Tendsto (saddleClock hlam c) atTop (𝓝 0) ∧
      Tendsto (fun j : ℕ => (j : ℝ) * saddleClock hlam c j) atTop (𝓝 (c / 2)) ∧
      (saddleClockOperator hlam hc).IsPositive ∧
      IsCompactOperator (saddleClockOperator hlam hc) ∧
      MemWeakSchattenClass 1 (saddleClockOperator hlam hc) ∧
      HasSchattenLogResidue 1 (saddleClockOperator hlam hc) (c / 2) ∧
      ¬MemSchattenClass 1 (saddleClockOperator hlam hc) ∧
      (∀ p : ℝ, 1 < p → MemSchattenClass p (saddleClockOperator hlam hc)) ∧
      (HasSchattenLogResidue 1 (saddleClockOperator hlam hc) 3 ↔ c = 6)) ∧
    Tendsto (fun j : ℕ => (j : ℝ) * Real.log j * relativeClock hlam j) atTop (𝓝 3) ∧
    (∀ᶠ j : ℕ in atTop, 0 < relativeClock hlam j) ∧
    IsCompactOperator (relativeClockOperator hlam) ∧
    ¬MemSchattenClass 1 (relativeClockOperator hlam) ∧
    (∃ K : ℕ, HasRankLE (relativeClockOperator hlam - relativeClockPosOperator hlam) K) ∧
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      approxNumber (relativeClockPosOperator hlam) n) / Real.log (Real.log N)) atTop (𝓝 3) ∧
    HasSchattenLogResidue 1 (relativeClockPosOperator hlam) 0 ∧
    Tendsto (fun N : ℕ => ((∑ j ∈ Finset.range N, relativeClock hlam j
      - 3 * Real.log (Real.log N) : ℝ) : ℂ)) atTop
      (𝓝 (3 * Real.log (Real.pi / 2) - 3 * Complex.digamma (9 / 2) +
        6 * saddleHeight hlam 0)) ∧
    saddleClockOperator hlam (by norm_num : (0 : ℝ) < 6) + relativeClockOperator hlam
      = elapsedHistoryDefect 1 := by
  refine ⟨fun j => ⟨saddleHeight_pos hlam j, saddleDegree_saddleHeight hlam j,
      (saddleIncrement_bounds hlam j).1, (saddleIncrement_bounds hlam j).2⟩,
    fun hx => ⟨saddleSlope_pos hlam hx, saddleCurvature_pos hlam hx⟩,
    tendsto_two_mul_saddleHeight_div_log hlam, fun hc => ?_,
    tendsto_relativeClock_doubleLog hlam, eventually_relativeClock_pos hlam,
    isCompactOperator_relativeClockOperator hlam, not_memSchattenClass_relativeClockOperator hlam,
    exists_hasRankLE_relativeClockOperator_sub hlam,
    tendsto_sum_approxNumber_relativeClockPos_div_log_log hlam,
    hasSchattenLogResidue_relativeClockPosOperator hlam, tendsto_relativeClock_finitePart hlam,
    saddleClockOperator_add_relativeClockOperator hlam⟩
  obtain ⟨h1, h2, h3, h4⟩ := saddleClockOperator_residue hlam hc
  exact ⟨saddleClock_pos hlam hc, saddleClock_antitone hlam hc, tendsto_saddleClock hlam _,
    tendsto_mul_saddleClock hlam _, saddleClockOperator_isPositive hlam hc,
    isCompactOperator_saddleClockOperator hlam hc, h1, h2, h3, h4,
    saddleClock_calibration hlam hc⟩

end Filtration

end GaloisForLFunctions.HTGeometry
