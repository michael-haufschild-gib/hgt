import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleStationaryError
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleBoundaryBounds
import GaloisForLFunctions.RHTower.CCMRestrictedWeilFullPoleMatrix

/-!
# The sharp constant of the diagonal pole entry

The self entry `A(a)` of the fixed exponential-pole Weil matrix is, exactly,

`A(a) = (2 + γ − log 4π) e^a − 2e^a (E_M(2a) + γ) + 2e^{−a}(ψ(e^{2a}) − e^{2a}) + r(a)`,

where `E_M(t) = Σ_{n ≤ e^t} Λ(n)/n − t` is the reciprocal Mangoldt error, `ψ` is Chebyshev's
function, and `|r(a)| ≤ (6a + 30) e^{−a}` for `a ≥ 1`.  The constant collects `κ = −γ − log 2π`,
Mertens' constant `−γ`, and the exact limit `1 − log 2` of the exponentially weighted Gamma
boundary mass `B₁(a) e^{−a}`.  The latter comes from the closed antiderivative

`∫ e^{−t} L(2t) dt = G(e^{−t})`, `G(u) = (u−1) log(1−u) + (u+1) log(1+u) − 2u`, `G'(u) = log(1−u²)`,

with `L(t) = −log(1 − e^{−t})` and `G(1) = 2 log 2 − 2`.  On paper `2 + γ − log 4π = Σ_ρ 1/(ρ(1−ρ))`
over the nontrivial zeros, so the two parity energies of the pole family are, to leading order,
`e^a Σ_{γ>0} 2(1 ± cos(2aγ − 2 arg ρ))/|ρ|²`: the fixed-pole criterion has no asymptotic margin.
No zero data, RH premise, or numerical input enters the statements below.
-/

open Real MeasureTheory intervalIntegral Set Filter Topology

namespace RHTower

noncomputable section

/-- `G(u) = (u−1) log(1−u) + (u+1) log(1+u) − 2u`, whose derivative on `(0,1)` is `log(1−u²)`. -/
def ccmPoleSelfKernelPrimitive (u : ℝ) : ℝ :=
  (u - 1) * Real.log (1 - u) + (u + 1) * Real.log (1 + u) - 2 * u

theorem hasDerivAt_ccmPoleSelfKernelPrimitive {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt ccmPoleSelfKernelPrimitive (Real.log (1 - u ^ 2)) u := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
  have h2 : HasDerivAt (fun u : ℝ => 1 + u) 1 u := by
    simpa using (hasDerivAt_id u).const_add (1 : ℝ)
  have hl1 : HasDerivAt (fun u : ℝ => Real.log (1 - u)) ((-1) / (1 - u)) u :=
    h1.log (by linarith)
  have hl2 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + u)) u :=
    h2.log (by linarith)
  have hA : HasDerivAt (fun u : ℝ => (u - 1) * Real.log (1 - u))
      (1 * Real.log (1 - u) + (u - 1) * ((-1) / (1 - u))) u :=
    ((hasDerivAt_id u).sub_const 1).mul hl1
  have hB : HasDerivAt (fun u : ℝ => (u + 1) * Real.log (1 + u))
      (1 * Real.log (1 + u) + (u + 1) * (1 / (1 + u))) u :=
    ((hasDerivAt_id u).add_const 1).mul hl2
  have hC : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have key : ccmPoleSelfKernelPrimitive =
      fun u => (u - 1) * Real.log (1 - u) + (u + 1) * Real.log (1 + u) - 2 * u := rfl
  rw [key]
  convert (hA.add hB).sub hC using 1
  have hne1 : (1 - u) ≠ 0 := by linarith
  have hne2 : (1 + u) ≠ 0 := by linarith
  rw [show (1 : ℝ) - u ^ 2 = (1 - u) * (1 + u) by ring, Real.log_mul hne1 hne2]
  field_simp
  ring

/-- `F(t) = G(e^{−t})`, an antiderivative of `e^{−t} L(2t)` on `(0,∞)`. -/
def ccmPoleSelfKernelAntiderivative (t : ℝ) : ℝ :=
  ccmPoleSelfKernelPrimitive (Real.exp (-t))

theorem hasDerivAt_ccmPoleSelfKernelAntiderivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt ccmPoleSelfKernelAntiderivative
      (Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t)) t := by
  have hu : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
    have := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    simpa using this
  have hG := hasDerivAt_ccmPoleSelfKernelPrimitive (Real.exp_pos (-t))
    (Real.exp_lt_one_iff.mpr (by linarith))
  have hcomp := hG.comp t hu
  have key : ccmPoleSelfKernelAntiderivative = ccmPoleSelfKernelPrimitive ∘ fun t => Real.exp (-t) :=
    rfl
  rw [key]
  convert hcomp using 1
  unfold ccmGammaPoleBoundaryLog
  rw [show Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf]
  ring

theorem continuous_ccmPoleSelfKernelAntiderivative :
    Continuous ccmPoleSelfKernelAntiderivative := by
  have key : ccmPoleSelfKernelAntiderivative = fun t =>
      -((1 - Real.exp (-t)) * Real.log (1 - Real.exp (-t))) +
        (Real.exp (-t) + 1) * Real.log (1 + Real.exp (-t)) - 2 * Real.exp (-t) := by
    funext t
    unfold ccmPoleSelfKernelAntiderivative ccmPoleSelfKernelPrimitive
    ring
  rw [key]
  have he : Continuous fun t : ℝ => Real.exp (-t) := Real.continuous_exp.comp continuous_neg
  have h1 : Continuous fun t : ℝ => (1 - Real.exp (-t)) * Real.log (1 - Real.exp (-t)) :=
    Real.continuous_mul_log.comp (continuous_const.sub he)
  have h2 : Continuous fun t : ℝ => Real.log (1 + Real.exp (-t)) :=
    (continuous_const.add he).log (fun t => by positivity)
  exact (h1.neg.add ((he.add continuous_const).mul h2)).sub (continuous_const.mul he)

theorem ccmPoleSelfKernelAntiderivative_zero :
    ccmPoleSelfKernelAntiderivative 0 = 2 * Real.log 2 - 2 := by
  unfold ccmPoleSelfKernelAntiderivative ccmPoleSelfKernelPrimitive
  simp only [neg_zero, Real.exp_zero, sub_self, zero_mul, zero_add]
  norm_num

/-- Closed form of the weighted boundary integral: `∫_0^{2s} e^{−t} L(2t) dt = F(2s) − (2 log 2 − 2)`. -/
theorem integral_exp_neg_mul_ccmGammaPoleBoundaryLog_two_mul {s : ℝ} (hs : 0 < s) :
    (∫ t in 0..2 * s, Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t)) =
      ccmPoleSelfKernelAntiderivative (2 * s) - (2 * Real.log 2 - 2) := by
  have hint : IntervalIntegrable (fun t => Real.exp (-t) * ccmGammaPoleBoundaryLog (2 * t))
      volume 0 (2 * s) :=
    (intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (by linarith)).continuousOn_mul
      (Real.continuous_exp.comp continuous_neg).continuousOn
  have ha : Tendsto ccmPoleSelfKernelAntiderivative (𝓝[>] 0) (𝓝 (2 * Real.log 2 - 2)) := by
    have := continuous_ccmPoleSelfKernelAntiderivative.tendsto 0
    rw [ccmPoleSelfKernelAntiderivative_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hb : Tendsto ccmPoleSelfKernelAntiderivative (𝓝[<] (2 * s))
      (𝓝 (ccmPoleSelfKernelAntiderivative (2 * s))) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_ccmPoleSelfKernelAntiderivative.tendsto _)
  exact integral_eq_sub_of_hasDerivAt_of_tendsto (by linarith)
    (fun x hx => hasDerivAt_ccmPoleSelfKernelAntiderivative hx.1) hint ha hb

/-- Small-argument bound for `G`: `|G(u)| ≤ 6u` on `[0, 1/2]`. -/
theorem abs_ccmPoleSelfKernelPrimitive_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    |ccmPoleSelfKernelPrimitive u| ≤ 6 * u := by
  unfold ccmPoleSelfKernelPrimitive
  have hpos : 0 < 1 - u := by linarith
  have hl1a : Real.log (1 - u) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hl1b : -(2 * u) ≤ Real.log (1 - u) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos
    have : 1 - (1 - u)⁻¹ ≥ -(2 * u) := by
      rw [ge_iff_le, sub_eq_add_neg, ← sub_le_iff_le_add', neg_neg,
        show (2 * u) - 1 = -(1 - 2 * u) by ring, neg_le, neg_neg, inv_le_comm₀ hpos (by linarith)]
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hl2a : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hl2b : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + u by linarith)
    linarith
  have hA1 : 0 ≤ (u - 1) * Real.log (1 - u) := by nlinarith
  have hA2 : (u - 1) * Real.log (1 - u) ≤ 2 * u := by nlinarith
  have hB1 : 0 ≤ (u + 1) * Real.log (1 + u) := by nlinarith
  have hB2 : (u + 1) * Real.log (1 + u) ≤ 3 / 2 * u := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- Pointwise bound `e^t L(t) ≤ 2 L(t) + 2` on the nonnegative ray. -/
theorem exp_mul_ccmGammaPoleBoundaryLog_le {t : ℝ} (ht : 0 ≤ t) :
    Real.exp t * ccmGammaPoleBoundaryLog t ≤ 2 * ccmGammaPoleBoundaryLog t + 2 := by
  have hL := ccmGammaPoleBoundaryLog_nonneg ht
  rcases le_or_lt (Real.exp t) 2 with h2 | h2
  · nlinarith
  · -- `e^{−t} < 1/2`, so `L(t) ≤ e^{−t}/(1 − e^{−t}) ≤ 2 e^{−t}` and `e^t L(t) ≤ 2`
    have hx : Real.exp (-t) < 1 / 2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos t) (by norm_num)]
      simpa using h2
    have hxpos := Real.exp_pos (-t)
    have hpos : 0 < 1 - Real.exp (-t) := by linarith
    have hlog : Real.log (1 - Real.exp (-t)) ≥ 1 - (1 - Real.exp (-t))⁻¹ :=
      Real.one_sub_inv_le_log_of_pos hpos
    have hinv : (1 - Real.exp (-t))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    have hL2 : ccmGammaPoleBoundaryLog t ≤ 2 * Real.exp (-t) := by
      unfold ccmGammaPoleBoundaryLog
      have : (1 - Real.exp (-t))⁻¹ - 1 ≤ 2 * Real.exp (-t) := by
        rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
        nlinarith
      linarith
    have hprod : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have : Real.exp t * ccmGammaPoleBoundaryLog t ≤ 2 := by
      calc Real.exp t * ccmGammaPoleBoundaryLog t ≤ Real.exp t * (2 * Real.exp (-t)) :=
            mul_le_mul_of_nonneg_left hL2 (Real.exp_pos t).le
        _ = 2 := by rw [mul_left_comm, hprod, mul_one]
    linarith

/-- The exponentially weighted difference integral: nonnegative and at most `2K_B + 4s`. -/
theorem integral_exp_mul_boundaryLog_diff_bounds (a : SuzukiPositiveAperture) :
    0 ≤ (∫ t in 0..2 * a.1, Real.exp t *
        (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)) ∧
      (∫ t in 0..2 * a.1, Real.exp t *
        (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)) ≤
        2 * (2 * Real.log 2 + Real.pi + 1) + 4 * a.1 := by
  have ha := a.2
  have hL := intervalIntegrable_ccmGammaPoleBoundaryLog (show 0 < 2 * a.1 by linarith)
  have hL2 := intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (show 0 < 2 * a.1 by linarith)
  have hec : ContinuousOn Real.exp (uIcc 0 (2 * a.1)) := Real.continuous_exp.continuousOn
  have hint : IntervalIntegrable (fun t => Real.exp t *
      (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)) volume 0 (2 * a.1) :=
    (hL.sub (hL2.const_mul (1 / 2)) |>.continuousOn_mul hec).congr
      (Filter.Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring)
  have hint2 : IntervalIntegrable (fun t => 2 * ccmGammaPoleBoundaryLog t + 2) volume 0 (2 * a.1) :=
    (hL.const_mul 2).add intervalIntegrable_const
  constructor
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have h1 := ccmGammaPoleBoundaryLog_two_mul_le ht.1
    have h2 := ccmGammaPoleBoundaryLog_nonneg ht.1
    have := Real.exp_pos t
    nlinarith
  · calc (∫ t in 0..2 * a.1, Real.exp t *
          (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2))
        ≤ ∫ t in 0..2 * a.1, (2 * ccmGammaPoleBoundaryLog t + 2) := by
          apply intervalIntegral.integral_mono_on (by linarith) hint hint2
          intro t ht
          have h1 := ccmGammaPoleBoundaryLog_nonneg (show 0 ≤ 2 * t by linarith [ht.1])
          have h3 := exp_mul_ccmGammaPoleBoundaryLog_le ht.1
          have := Real.exp_pos t
          nlinarith
      _ = 2 * ccmGammaPoleCrossBoundaryMass a + 2 * (2 * a.1) := by
          rw [intervalIntegral.integral_add (hL.const_mul 2) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, ccmGammaPoleCrossBoundaryMass_eq_primitive,
            ccmGammaPoleCrossBoundaryPrimitive, intervalIntegral.integral_const]
          simp
      _ ≤ 2 * (2 * Real.log 2 + Real.pi + 1) + 4 * a.1 := by
          have := ccmGammaPoleCrossBoundaryMass_le a
          linarith

/-- The sharp constant `2 + γ − log 4π` (on paper `Σ_ρ 1/(ρ(1−ρ))`). -/
def ccmWeilPoleSharpConstant : ℝ :=
  2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-- Remainder of the diagonal pole entry after the sharp main term and the two prime errors. -/
def ccmWeilPoleDiagonalRemainder (s : ℝ) : ℝ :=
  (1 - 2 * s - (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi))) * Real.exp (-s) +
    Real.exp s / 2 * ccmPoleSelfKernelAntiderivative (2 * s) +
    Real.exp (-s) * ∫ t in 0..2 * s,
      Real.exp t * (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)

/-- **Exact constant-level decomposition of the diagonal pole entry.** -/
theorem ccmWeilPoleDiagonal_eq_sharp (a : SuzukiPositiveAperture) :
    ccmWeilPoleDiagonal a =
      ccmWeilPoleSharpConstant * Real.exp a.1 -
        2 * Real.exp a.1 * (ccmReciprocalMangoldtError (2 * a.1) + Real.eulerMascheroniConstant) +
        2 * Real.exp (-a.1) * (Chebyshev.psi (Real.exp (2 * a.1)) - Real.exp (2 * a.1)) +
        ccmWeilPoleDiagonalRemainder a.1 := by
  rw [ccmWeilPoleDiagonal_eq_error, ccmGammaPoleSelfBoundaryMass_eq_primitive,
    ccmGammaPoleSelfBoundaryPrimitive, integral_exp_neg_mul_ccmGammaPoleBoundaryLog_two_mul a.2]
  unfold ccmWeilPoleSharpConstant ccmWeilPoleDiagonalRemainder
  have h4 : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    ring_nf
  have h2a : Real.exp (2 * a.1) = Real.exp a.1 * Real.exp a.1 := by
    rw [← Real.exp_add]; ring_nf
  rw [h4, Real.sinh_eq, h2a, Real.exp_neg]
  have := Real.exp_pos a.1
  field_simp
  ring

/-- The remainder is exponentially small: `|r(s)| ≤ (6s + 30) e^{−s}` for `s ≥ 1`. -/
theorem abs_ccmWeilPoleDiagonalRemainder_le (a : SuzukiPositiveAperture) (ha : 1 ≤ a.1) :
    |ccmWeilPoleDiagonalRemainder a.1| ≤ (6 * a.1 + 30) * Real.exp (-a.1) := by
  unfold ccmWeilPoleDiagonalRemainder
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hpi1 := Real.pi_gt_three
  have hpi2 := Real.pi_le_four
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hlogpi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlogpi' : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have hes := Real.exp_pos a.1
  have hens := Real.exp_pos (-a.1)
  have hprod : Real.exp a.1 * Real.exp (-a.1) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  -- the kernel term
  have hu0 : 0 ≤ Real.exp (-(2 * a.1)) := (Real.exp_pos _).le
  have hu : Real.exp (-(2 * a.1)) ≤ 1 / 2 := by
    have h1 : Real.exp (-(2 * a.1)) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-2) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    linarith
  have hF : |ccmPoleSelfKernelAntiderivative (2 * a.1)| ≤ 6 * Real.exp (-(2 * a.1)) :=
    abs_ccmPoleSelfKernelPrimitive_le hu0 hu
  have hFe : Real.exp a.1 / 2 * |ccmPoleSelfKernelAntiderivative (2 * a.1)| ≤ 3 * Real.exp (-a.1) := by
    have h := mul_le_mul_of_nonneg_left hF (show 0 ≤ Real.exp a.1 / 2 by positivity)
    have he : Real.exp (-(2 * a.1)) = Real.exp (-a.1) * Real.exp (-a.1) := by
      rw [← Real.exp_add]; ring_nf
    rw [he] at h
    calc Real.exp a.1 / 2 * |ccmPoleSelfKernelAntiderivative (2 * a.1)|
        ≤ Real.exp a.1 / 2 * (6 * (Real.exp (-a.1) * Real.exp (-a.1))) := h
      _ = 3 * Real.exp (-a.1) := by
          have : Real.exp a.1 * Real.exp (-a.1) = 1 := hprod
          nlinarith [this]
  -- the difference integral
  obtain ⟨hJ0, hJ⟩ := integral_exp_mul_boundaryLog_diff_bounds a
  have hJ' : Real.exp (-a.1) * (∫ t in 0..2 * a.1, Real.exp t *
      (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)) ≤
      (4 * a.1 + 18) * Real.exp (-a.1) := by
    have h := mul_le_mul_of_nonneg_left hJ hens.le
    have : 2 * (2 * Real.log 2 + Real.pi + 1) + 4 * a.1 ≤ 4 * a.1 + 18 := by linarith
    nlinarith
  have hJ'' : 0 ≤ Real.exp (-a.1) * (∫ t in 0..2 * a.1, Real.exp t *
      (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)) :=
    mul_nonneg hens.le hJ0
  -- the linear term
  have hlin : |(1 - 2 * a.1 - (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi))) *
      Real.exp (-a.1)| ≤ (2 * a.1 + 9) * Real.exp (-a.1) := by
    rw [abs_mul, abs_of_pos hens]
    apply mul_le_mul_of_nonneg_right _ hens.le
    rw [abs_le]
    constructor <;> linarith
  calc |(1 - 2 * a.1 - (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi))) *
          Real.exp (-a.1) + Real.exp a.1 / 2 * ccmPoleSelfKernelAntiderivative (2 * a.1) +
          Real.exp (-a.1) * ∫ t in 0..2 * a.1,
            Real.exp t * (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)|
      ≤ |(1 - 2 * a.1 - (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi))) *
          Real.exp (-a.1)| + |Real.exp a.1 / 2 * ccmPoleSelfKernelAntiderivative (2 * a.1)| +
          |Real.exp (-a.1) * ∫ t in 0..2 * a.1,
            Real.exp t * (ccmGammaPoleBoundaryLog t - ccmGammaPoleBoundaryLog (2 * t) / 2)| :=
        (abs_add_three _ _ _)
    _ ≤ (2 * a.1 + 9) * Real.exp (-a.1) + 3 * Real.exp (-a.1) + (4 * a.1 + 18) * Real.exp (-a.1) := by
        gcongr
        · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < Real.exp a.1 / 2)]
          exact hFe
        · rw [abs_of_nonneg hJ'']
          exact hJ'
    _ = (6 * a.1 + 30) * Real.exp (-a.1) := by ring

/-- **Sharp asymptotic form of the diagonal entry.** The distance of `A(a)e^{−a}` from the sharp
constant is controlled by the two prime errors and an exponentially small term. -/
theorem abs_ccmWeilPoleDiagonal_div_exp_sub_sharp_le (a : SuzukiPositiveAperture) (ha : 1 ≤ a.1) :
    |ccmWeilPoleDiagonal a / Real.exp a.1 - ccmWeilPoleSharpConstant| ≤
      2 * |ccmReciprocalMangoldtError (2 * a.1) + Real.eulerMascheroniConstant| +
        2 * Real.exp (-(2 * a.1)) * |Chebyshev.psi (Real.exp (2 * a.1)) - Real.exp (2 * a.1)| +
        (6 * a.1 + 30) * Real.exp (-(2 * a.1)) := by
  have hes := Real.exp_pos a.1
  have hr := abs_ccmWeilPoleDiagonalRemainder_le a ha
  have hkey : ccmWeilPoleDiagonal a / Real.exp a.1 - ccmWeilPoleSharpConstant =
      -(2 * (ccmReciprocalMangoldtError (2 * a.1) + Real.eulerMascheroniConstant)) +
        2 * Real.exp (-(2 * a.1)) * (Chebyshev.psi (Real.exp (2 * a.1)) - Real.exp (2 * a.1)) +
        ccmWeilPoleDiagonalRemainder a.1 / Real.exp a.1 := by
    rw [ccmWeilPoleDiagonal_eq_sharp a]
    have h2 : Real.exp (-(2 * a.1)) = Real.exp (-a.1) / Real.exp a.1 := by
      rw [Real.exp_neg, Real.exp_neg, ← Real.exp_add]
      rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      ring_nf
    rw [h2]
    field_simp
    ring
  rw [hkey]
  have hrem : |ccmWeilPoleDiagonalRemainder a.1 / Real.exp a.1| ≤
      (6 * a.1 + 30) * Real.exp (-(2 * a.1)) := by
    rw [abs_div, abs_of_pos hes, div_le_iff₀ hes]
    have h2 : Real.exp (-(2 * a.1)) * Real.exp a.1 = Real.exp (-a.1) := by
      rw [← Real.exp_add]; ring_nf
    calc |ccmWeilPoleDiagonalRemainder a.1| ≤ (6 * a.1 + 30) * Real.exp (-a.1) := hr
      _ = (6 * a.1 + 30) * Real.exp (-(2 * a.1)) * Real.exp a.1 := by rw [mul_assoc, h2]
  calc |-(2 * (ccmReciprocalMangoldtError (2 * a.1) + Real.eulerMascheroniConstant)) +
          2 * Real.exp (-(2 * a.1)) * (Chebyshev.psi (Real.exp (2 * a.1)) - Real.exp (2 * a.1)) +
          ccmWeilPoleDiagonalRemainder a.1 / Real.exp a.1|
      ≤ |-(2 * (ccmReciprocalMangoldtError (2 * a.1) + Real.eulerMascheroniConstant))| +
          |2 * Real.exp (-(2 * a.1)) * (Chebyshev.psi (Real.exp (2 * a.1)) - Real.exp (2 * a.1))| +
          |ccmWeilPoleDiagonalRemainder a.1 / Real.exp a.1| := abs_add_three _ _ _
    _ ≤ 2 * |ccmReciprocalMangoldtError (2 * a.1) + Real.eulerMascheroniConstant| +
          2 * Real.exp (-(2 * a.1)) * |Chebyshev.psi (Real.exp (2 * a.1)) - Real.exp (2 * a.1)| +
          (6 * a.1 + 30) * Real.exp (-(2 * a.1)) := by
        gcongr
        · rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
            abs_of_pos (Real.exp_pos _)]

end

end RHTower
