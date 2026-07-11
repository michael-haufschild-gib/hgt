/-
# Simplicity of the Jacobi theta half-period divisor

The derivative at the odd half-period is a modularly covariant theta constant.  This file begins
its nonvanishing proof by pairing the defining integer series under `n ↦ -n-1`; the leading pair
is exactly `2*pi*i`, while every later pair has Gaussian decay.
-/
import GaloisForLFunctions.JacobiThetaDivisor
import GaloisForLFunctions.Bottcher.ArgumentPrinciple
import Mathlib.Analysis.SpecificLimits.Normed

namespace GaloisForLFunctions

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 4000000

/-- The paired derivative summand indexed by the nonnegative half of `ℤ`. -/
def thetaHalfPeriodDerivativePair (τ : ℂ) (n : ℕ) : ℂ :=
  jacobiTheta₂'_term (n : ℤ) (thetaHalfPeriod τ) τ +
    jacobiTheta₂'_term (-(n : ℤ) - 1) (thetaHalfPeriod τ) τ

/-- Exact norm of one derivative summand at the half-period. -/
theorem norm_jacobiTheta₂'_term_thetaHalfPeriod (τ : ℂ) (n : ℤ) :
    ‖jacobiTheta₂'_term n (thetaHalfPeriod τ) τ‖ =
      2 * Real.pi * |n| *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 + (n : ℝ)) * τ.im) := by
  rw [jacobiTheta₂'_term, norm_mul, norm_jacobiTheta₂_term]
  have him : (thetaHalfPeriod τ).im = τ.im / 2 := by
    simp only [thetaHalfPeriod, div_eq_mul_inv]
    simp
  rw [him]
  simp only [norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_I, Complex.norm_intCast, mul_one, Int.cast_abs]
  ring_nf

/-- Pairing `n` with `-n-1` converts the full integer derivative series into a natural series. -/
theorem thetaHalfPeriodDerivative_eq_tsum_pair {τ : ℂ} (hτ : 0 < τ.im) :
    thetaHalfPeriodDerivative τ = ∑' n : ℕ, thetaHalfPeriodDerivativePair τ n := by
  rw [thetaHalfPeriodDerivative, jacobiTheta₂']
  simpa only [thetaHalfPeriodDerivativePair, neg_add_rev, sub_eq_add_neg, add_comm] using
    (tsum_nat_add_neg_add_one
      (hasSum_jacobiTheta₂'_term (thetaHalfPeriod τ) hτ).summable).symm

/-- The leading paired summand is exactly `2*pi*i`. -/
theorem thetaHalfPeriodDerivativePair_zero (τ : ℂ) :
    thetaHalfPeriodDerivativePair τ 0 = 2 * Real.pi * Complex.I := by
  rw [thetaHalfPeriodDerivativePair]
  simp only [Nat.cast_zero, Int.cast_zero, neg_zero, zero_sub, jacobiTheta₂'_term,
    jacobiTheta₂_term, Int.cast_neg, Int.cast_one]
  have hexponent :
      2 * Real.pi * Complex.I * (-1 : ℂ) * thetaHalfPeriod τ +
          Real.pi * Complex.I * (-1 : ℂ) ^ 2 * τ =
        -(Real.pi * Complex.I) := by
    rw [thetaHalfPeriod]
    ring
  rw [hexponent, Complex.exp_neg_pi_mul_I]
  ring

/-- The paired natural series is summable. -/
theorem summable_thetaHalfPeriodDerivativePair {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (thetaHalfPeriodDerivativePair τ) := by
  simpa only [thetaHalfPeriodDerivativePair, neg_add_rev, sub_eq_add_neg, add_comm] using
    (hasSum_jacobiTheta₂'_term (thetaHalfPeriod τ) hτ).summable.nat_add_neg_add_one

/-- Isolating the leading pair leaves a shifted Gaussian tail. -/
theorem thetaHalfPeriodDerivative_eq_leading_add_tail {τ : ℂ} (hτ : 0 < τ.im) :
    thetaHalfPeriodDerivative τ = 2 * Real.pi * Complex.I +
      ∑' n : ℕ, thetaHalfPeriodDerivativePair τ (n + 1) := by
  rw [thetaHalfPeriodDerivative_eq_tsum_pair hτ,
    (summable_thetaHalfPeriodDerivativePair hτ).tsum_eq_zero_add,
    thetaHalfPeriodDerivativePair_zero]

/-- Exact Gaussian majorant for the `n+1`-st paired tail term. -/
theorem norm_thetaHalfPeriodDerivativePair_succ_le (τ : ℂ) (n : ℕ) :
    ‖thetaHalfPeriodDerivativePair τ (n + 1)‖ ≤
      2 * Real.pi * (2 * (n + 1 : ℝ) + 1) *
        Real.exp
          (-Real.pi * ((n + 1 : ℝ) * (n + 2 : ℝ)) * τ.im) := by
  rw [thetaHalfPeriodDerivativePair]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_jacobiTheta₂'_term_thetaHalfPeriod,
    norm_jacobiTheta₂'_term_thetaHalfPeriod]
  push_cast
  have hpos : 0 ≤ (n : ℝ) + 1 := by positivity
  have hneg : -((n : ℝ) + 1) - 1 ≤ 0 := by linarith
  rw [abs_of_nonneg hpos, abs_of_nonpos hneg]
  ring

/-- A fixed rational geometric series dominating the high-imaginary-part derivative tail sums to
`13/32`. -/
theorem tsum_thetaHalfPeriod_rational_majorant :
    (∑' n : ℕ, (2 * (n + 1 : ℝ) + 1) * ((1 : ℝ) / 9) ^ (n + 1)) =
      13 / 32 := by
  let q : ℝ := 1 / 9
  have hq : ‖q‖ < 1 := by norm_num [q]
  have hgeom : Summable (fun n : ℕ ↦ q ^ n) := summable_geometric_of_norm_lt_one hq
  have hmul : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hq).summable
  calc
    (∑' n : ℕ, (2 * (n + 1 : ℝ) + 1) * ((1 : ℝ) / 9) ^ (n + 1)) =
        ∑' n : ℕ, ((2 * q) * ((n : ℝ) * q ^ n) + (3 * q) * q ^ n) := by
      apply tsum_congr
      intro n
      dsimp [q]
      ring
    _ = (2 * q) * (∑' n : ℕ, (n : ℝ) * q ^ n) +
        (3 * q) * (∑' n : ℕ, q ^ n) := by
      rw [(hmul.mul_left (2 * q)).tsum_add (hgeom.mul_left (3 * q)),
        tsum_mul_left, tsum_mul_left]
    _ = 13 / 32 := by
      rw [tsum_coe_mul_geometric_of_norm_lt_one hq,
        tsum_geometric_of_norm_lt_one hq]
      norm_num [q]

theorem summable_thetaHalfPeriod_rational_majorant :
    Summable (fun n : ℕ ↦
      (2 * (n + 1 : ℝ) + 1) * ((1 : ℝ) / 9) ^ (n + 1)) := by
  let q : ℝ := 1 / 9
  have hq : ‖q‖ < 1 := by norm_num [q]
  have hgeom : Summable (fun n : ℕ ↦ q ^ n) := summable_geometric_of_norm_lt_one hq
  have hmul : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hq).summable
  refine ((hmul.mul_left (2 * q)).add (hgeom.mul_left (3 * q))).congr (fun n ↦ ?_)
  dsimp [q]
  ring

theorem exp_neg_twentyFour_fifths_lt_one_ninth :
    Real.exp (-(24 / 5 : ℝ)) < 1 / 9 := by
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by
    nlinarith [Real.add_one_le_exp (2 : ℝ)]
  have he12 : (3 : ℝ) < Real.exp (12 / 5) :=
    he2.trans_lt (Real.exp_lt_exp.mpr (by norm_num))
  have he24 : (9 : ℝ) < Real.exp (24 / 5) := by
    rw [show (24 / 5 : ℝ) = 12 / 5 + 12 / 5 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (12 / 5 : ℝ)]
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  convert he24 using 1
  norm_num

/-- On `im τ ≥ 4/5`, every paired tail term is dominated by the fixed rational geometric
majorant with ratio `1/9`. -/
theorem norm_thetaHalfPeriodDerivativePair_succ_le_rational
    {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) (n : ℕ) :
    ‖thetaHalfPeriodDerivativePair τ (n + 1)‖ ≤
      2 * Real.pi * (2 * (n + 1 : ℝ) + 1) *
        ((1 : ℝ) / 9) ^ (n + 1) := by
  refine (norm_thetaHalfPeriodDerivativePair_succ_le τ n).trans ?_
  let r : ℝ := n + 1
  have hr : 1 ≤ r := by simp [r]
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpiy : (12 : ℝ) / 5 ≤ Real.pi * τ.im := by
    have := mul_le_mul hpi hτ (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (by positivity : (0 : ℝ) ≤ Real.pi)
    nlinarith
  have hrr : 2 * r ≤ r * (r + 1) := by nlinarith
  have hprod : (24 / 5 : ℝ) * r ≤ Real.pi * τ.im * (r * (r + 1)) := by
    calc
      (24 / 5 : ℝ) * r = (12 / 5 : ℝ) * (2 * r) := by ring
      _ ≤ (Real.pi * τ.im) * (r * (r + 1)) :=
        mul_le_mul hpiy hrr (by positivity) (by positivity)
  have hexponent :
      -Real.pi * (r * (r + 1)) * τ.im ≤ -(24 / 5 : ℝ) * r := by
    nlinarith
  have hexp :
      Real.exp (-Real.pi * (r * (r + 1)) * τ.im) ≤
        Real.exp (-(24 / 5 : ℝ)) ^ (n + 1) := by
    calc
      Real.exp (-Real.pi * (r * (r + 1)) * τ.im) ≤
          Real.exp (-(24 / 5 : ℝ) * r) := Real.exp_le_exp.mpr hexponent
      _ = Real.exp (-(24 / 5 : ℝ)) ^ (n + 1) := by
        rw [show r = (n + 1 : ℕ) by simp [r], ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have hpow :
      Real.exp (-(24 / 5 : ℝ)) ^ (n + 1) ≤ ((1 : ℝ) / 9) ^ (n + 1) :=
    pow_le_pow_left₀ (Real.exp_nonneg _)
      exp_neg_twentyFour_fifths_lt_one_ninth.le (n + 1)
  dsimp [r] at hexp
  gcongr
  convert hexp.trans hpow using 1
  ring

/-- The entire paired derivative tail has norm strictly smaller than the leading term `2*pi*i`
throughout `im τ ≥ 4/5`. -/
theorem norm_thetaHalfPeriodDerivative_tail_lt {τ : ℂ}
    (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    ‖∑' n : ℕ, thetaHalfPeriodDerivativePair τ (n + 1)‖ < 2 * Real.pi := by
  have hτ0 : 0 < τ.im := lt_of_lt_of_le (by norm_num) hτ
  have htail : Summable (fun n : ℕ ↦ thetaHalfPeriodDerivativePair τ (n + 1)) :=
    (summable_thetaHalfPeriodDerivativePair hτ0).comp_injective (add_left_injective 1)
  let B : ℕ → ℝ := fun n ↦
    2 * Real.pi * (2 * (n + 1 : ℝ) + 1) * ((1 : ℝ) / 9) ^ (n + 1)
  have hB : Summable B := by
    simpa only [B, mul_assoc] using
      summable_thetaHalfPeriod_rational_majorant.mul_left (2 * Real.pi)
  calc
    ‖∑' n : ℕ, thetaHalfPeriodDerivativePair τ (n + 1)‖ ≤
        ∑' n : ℕ, ‖thetaHalfPeriodDerivativePair τ (n + 1)‖ :=
      norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n : ℕ, B n :=
      Summable.tsum_le_tsum (norm_thetaHalfPeriodDerivativePair_succ_le_rational hτ)
        htail.norm hB
    _ = 2 * Real.pi * (13 / 32) := by
      rw [show (∑' n : ℕ, B n) =
          2 * Real.pi *
            ∑' n : ℕ, (2 * (n + 1 : ℝ) + 1) * ((1 : ℝ) / 9) ^ (n + 1) by
        simp only [B, mul_assoc, tsum_mul_left],
        tsum_thetaHalfPeriod_rational_majorant]
    _ < 2 * Real.pi := by nlinarith [Real.pi_pos]

/-- The distinguished theta zero is simple on the high-imaginary-part region. -/
theorem thetaHalfPeriodDerivative_ne_zero_of_im_ge {τ : ℂ}
    (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    thetaHalfPeriodDerivative τ ≠ 0 := by
  have hτ0 : 0 < τ.im := lt_of_lt_of_le (by norm_num) hτ
  intro hzero
  have hsplit := thetaHalfPeriodDerivative_eq_leading_add_tail hτ0
  rw [hzero] at hsplit
  have htailEq :
      (∑' n : ℕ, thetaHalfPeriodDerivativePair τ (n + 1)) =
        -(2 * Real.pi * Complex.I) := by
    apply eq_neg_of_add_eq_zero_left
    rw [add_comm]
    exact hsplit.symm
  have hnorm := congrArg norm htailEq
  have hleadnorm : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  rw [norm_neg, hleadnorm] at hnorm
  linarith [norm_thetaHalfPeriodDerivative_tail_lt hτ]

open UpperHalfPlane ModularGroup
open scoped Modular MatrixGroups

/-- Nonvanishing of the half-period derivative is invariant under the full modular group. -/
theorem thetaHalfPeriodDerivative_ne_zero_smul_iff (g : SL(2, ℤ)) (z : ℍ) :
    thetaHalfPeriodDerivative (↑(g • z)) ≠ 0 ↔ thetaHalfPeriodDerivative (↑z) ≠ 0 := by
  have hmem : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction generalizing z with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · have hcoe : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
          rw [modular_S_smul, UpperHalfPlane.coe_mk]
          simp [neg_div, one_div, inv_neg]
        rw [hcoe]
        exact thetaHalfPeriodDerivative_S_ne_zero_iff z.im_pos
      · have hcoe : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
          rw [modular_T_smul, UpperHalfPlane.coe_vadd]
          push_cast
          ring
        rw [hcoe, thetaHalfPeriodDerivative_add_one]
  | one => rw [one_smul]
  | mul x y _ _ ihx ihy =>
      rw [mul_smul]
      exact (ihx (y • z)).trans (ihy z)
  | inv x _ ihx =>
      have h := ihx (x⁻¹ • z)
      rw [smul_inv_smul] at h
      exact h.symm

/-- **The odd half-period theta divisor is simple on the entire upper half-plane.** -/
theorem thetaHalfPeriodDerivative_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    thetaHalfPeriodDerivative τ ≠ 0 := by
  set z : ℍ := ⟨τ, hτ⟩ with hz
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have him : (4 : ℝ) / 5 ≤ ((g • z : ℍ) : ℂ).im := by
    rw [UpperHalfPlane.coe_im]
    have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := (g • z).im_pos
    nlinarith [hpos, h3]
  have hfd : thetaHalfPeriodDerivative (↑(g • z)) ≠ 0 :=
    thetaHalfPeriodDerivative_ne_zero_of_im_ge him
  have := (thetaHalfPeriodDerivative_ne_zero_smul_iff g z).mp hfd
  simpa [hz, UpperHalfPlane.coe_mk] using this

/-- The analytic `z`-derivative of theta is nonzero at the distinguished half-period. -/
theorem jacobiTheta₂'_thetaHalfPeriod_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂' (thetaHalfPeriod τ) τ ≠ 0 :=
  thetaHalfPeriodDerivative_ne_zero_of_im_pos hτ

/-- A simple theta zero remains simple after every integral multiple of the quasiperiod. -/
theorem jacobiTheta₂'_ne_zero_add_int_mul_tau {z τ : ℂ}
    (hz : jacobiTheta₂ z τ = 0) (hz' : jacobiTheta₂' z τ ≠ 0) (n : ℤ) :
    jacobiTheta₂' (z + (n : ℂ) * τ) τ ≠ 0 := by
  induction n using Int.induction_on with
  | zero => simpa using hz'
  | succ n ih =>
      have harg : z + (((n : ℤ) + 1 : ℤ) : ℂ) * τ =
          (z + ((n : ℤ) : ℂ) * τ) + τ := by
        push_cast
        ring
      rw [harg, jacobiTheta₂'_add_left',
        jacobiTheta₂_eq_zero_add_int_mul_tau hz n, mul_zero, sub_zero]
      exact mul_ne_zero (Complex.exp_ne_zero _) ih
  | pred n ih =>
      let w : ℂ := z + ((-(n : ℤ) - 1 : ℤ) : ℂ) * τ
      have harg : w + τ = z + ((-(n : ℤ) : ℤ) : ℂ) * τ := by
        dsimp [w]
        push_cast
        ring
      have hwzero : jacobiTheta₂ w τ = 0 := by
        dsimp [w]
        exact jacobiTheta₂_eq_zero_add_int_mul_tau hz (-(n : ℤ) - 1)
      intro hw'
      have hstep := jacobiTheta₂'_add_left' w τ
      rw [harg, hwzero, mul_zero, sub_zero, hw', mul_zero] at hstep
      exact ih hstep

/-- A simple theta zero remains simple after every integral period. -/
theorem jacobiTheta₂'_ne_zero_add_int {z τ : ℂ}
    (hz' : jacobiTheta₂' z τ ≠ 0) (m : ℤ) :
    jacobiTheta₂' (z + (m : ℂ)) τ ≠ 0 := by
  have hper : Function.Periodic (fun w : ℂ ↦ jacobiTheta₂' w τ) 1 :=
    fun w ↦ jacobiTheta₂'_add_left w τ
  have hm := hper.int_mul m z
  rw [mul_one] at hm
  exact hm.symm ▸ hz'

/-- Every lattice translate of the odd half-period is a simple theta zero. -/
theorem jacobiTheta₂'_thetaHalfPeriod_add_lattice_ne_zero
    {τ : ℂ} (hτ : 0 < τ.im) (m n : ℤ) :
    jacobiTheta₂' (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) τ ≠ 0 := by
  have hn := jacobiTheta₂'_ne_zero_add_int_mul_tau
    (jacobiTheta₂_thetaHalfPeriod_eq_zero τ)
    (jacobiTheta₂'_thetaHalfPeriod_ne_zero hτ) n
  have hm := jacobiTheta₂'_ne_zero_add_int hn m
  convert hm using 1
  ring

/-- **Residue-one local law.** The logarithmic derivative of theta has normalized punctured limit
`1` at the odd half-period.  This is the analytic simple-pole coefficient consumed by the
orbit-principal-part obstruction. -/
theorem tendsto_thetaLogDeriv_normalized_halfPeriod {τ : ℂ} (hτ : 0 < τ.im) :
    Tendsto
      (fun z : ℂ ↦ (z - thetaHalfPeriod τ) *
        (jacobiTheta₂' z τ / jacobiTheta₂ z τ))
      (𝓝[≠] thetaHalfPeriod τ) (𝓝 1) := by
  let z₀ := thetaHalfPeriod τ
  let θ : ℂ → ℂ := fun z ↦ jacobiTheta₂ z τ
  have hθan : AnalyticAt ℂ θ z₀ :=
    (jacobiTheta₂_analyticOnNhd_fst τ hτ) z₀ (Set.mem_univ z₀)
  have hθzero : θ z₀ = 0 := jacobiTheta₂_thetaHalfPeriod_eq_zero τ
  obtain ⟨u, huan, hfactor, huval⟩ :=
    Bottcher.analyticAt_simple_factor hθan hθzero
  have hderiv : deriv θ z₀ = jacobiTheta₂' z₀ τ :=
    (hasDerivAt_jacobiTheta₂_fst z₀ hτ).deriv
  have hu0 : u z₀ ≠ 0 := by
    rw [huval, hderiv]
    exact jacobiTheta₂'_thetaHalfPeriod_ne_zero hτ
  have hnum : Tendsto (fun z : ℂ ↦ jacobiTheta₂' z τ)
      (𝓝[≠] z₀) (𝓝 (jacobiTheta₂' z₀ τ)) :=
    ((jacobiTheta₂'_analyticOnNhd_fst τ hτ) z₀ (Set.mem_univ z₀)).continuousAt.continuousWithinAt
  have hden : Tendsto u (𝓝[≠] z₀) (𝓝 (u z₀)) :=
    huan.continuousAt.continuousWithinAt
  have hquot : Tendsto (fun z ↦ jacobiTheta₂' z τ / u z)
      (𝓝[≠] z₀) (𝓝 1) := by
    convert hnum.div hden hu0 using 1
    rw [huval, hderiv, div_self (jacobiTheta₂'_thetaHalfPeriod_ne_zero hτ)]
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  rw [show jacobiTheta₂ z τ = (z - z₀) * u z by simpa [θ] using hfactor z]
  rcases eq_or_ne (u z) 0 with huz | huz
  · simp [huz]
  dsimp [z₀]
  have hz0' : z - thetaHalfPeriod τ ≠ 0 := by simpa [z₀] using hz0
  field_simp [huz, hz0']

/-- **Residue-one orbit law.** The theta logarithmic derivative has simple-pole coefficient `1`
at every translate of the odd half-period by `ℤ + τℤ`. -/
theorem tendsto_thetaLogDeriv_normalized_lattice {τ : ℂ} (hτ : 0 < τ.im) (m n : ℤ) :
    let z₀ := thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ
    Tendsto
      (fun z : ℂ ↦ (z - z₀) * (jacobiTheta₂' z τ / jacobiTheta₂ z τ))
      (𝓝[≠] z₀) (𝓝 1) := by
  dsimp only
  let z₀ : ℂ := thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ
  let θ : ℂ → ℂ := fun z ↦ jacobiTheta₂ z τ
  have hθan : AnalyticAt ℂ θ z₀ :=
    (jacobiTheta₂_analyticOnNhd_fst τ hτ) z₀ (Set.mem_univ z₀)
  have hθzero : θ z₀ = 0 := jacobiTheta₂_thetaHalfPeriod_add_lattice_eq_zero τ m n
  have hθprime : jacobiTheta₂' z₀ τ ≠ 0 :=
    jacobiTheta₂'_thetaHalfPeriod_add_lattice_ne_zero hτ m n
  obtain ⟨u, huan, hfactor, huval⟩ :=
    Bottcher.analyticAt_simple_factor hθan hθzero
  have hderiv : deriv θ z₀ = jacobiTheta₂' z₀ τ :=
    (hasDerivAt_jacobiTheta₂_fst z₀ hτ).deriv
  have hu0 : u z₀ ≠ 0 := by
    rw [huval, hderiv]
    exact hθprime
  have hnum : Tendsto (fun z : ℂ ↦ jacobiTheta₂' z τ)
      (𝓝[≠] z₀) (𝓝 (jacobiTheta₂' z₀ τ)) :=
    ((jacobiTheta₂'_analyticOnNhd_fst τ hτ) z₀ (Set.mem_univ z₀)).continuousAt.continuousWithinAt
  have hden : Tendsto u (𝓝[≠] z₀) (𝓝 (u z₀)) :=
    huan.continuousAt.continuousWithinAt
  have hquot : Tendsto (fun z ↦ jacobiTheta₂' z τ / u z)
      (𝓝[≠] z₀) (𝓝 1) := by
    convert hnum.div hden hu0 using 1
    rw [huval, hderiv, div_self hθprime]
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  rw [show jacobiTheta₂ z τ = (z - z₀) * u z by simpa [θ] using hfactor z]
  rcases eq_or_ne (u z) 0 with huz | huz
  · simp [huz]
  dsimp [z₀]
  have hz0' : z - (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) ≠ 0 := by
    simpa [z₀] using hz0
  field_simp [huz, hz0']

end

end GaloisForLFunctions
