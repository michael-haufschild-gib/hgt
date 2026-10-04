import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveLaplace
import GaloisForLFunctions.RHTower.ThetaSourceGlobalStrictLogConvexity
import GaloisForLFunctions.HTGeometry.InverseArgumentLahFormula

/-!
# Tilted cumulants of the actual generator and the integrated-clock crossing law

With `κ_k(z) = (d/dz)^k log Φ(z)` and `H(p) = log Φ(1/p)`:

* `log Φ` is smooth on `ℝ`, and `κ₁(z) = Φ'(z)/Φ(z)` is the real centered logarithmic derivative
  of `ξ`, `κ₁(z) = Re (ξ'/ξ)(1/2 + z)`; hence `κ₁ > 0` on `z > 0` and `κ₂ ≥ 0` everywhere;
* the Lah formula `(-1)^{n+1} H^{(n+1)}(p) = Σ_k (n+1)!/(k+1)! C(n,k) z^{n+k+2} κ_{k+1}(z)`,
  in particular `-H'''(p) = z^4 (6κ₁ + 6zκ₂ + z²κ₃)`;
* the orders `0, 1, 2` of complete monotonicity hold unconditionally on `p > 0`;
* the crossing law: `F = K + tK' - P ⋆ K'` on the whole line, and at a zero `T ≥ 0` of `P`,
  `(P ⋆ K)(T) = T K(T)`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry Complex
open scoped ContDiff

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "Φ" => liClockThetaGeneratorReal

/-- The logarithmic generator `log Φ`. -/
def liClockThetaLogGenerator (z : ℝ) : ℝ := Real.log (Φ z)

theorem contDiff_liClockThetaGeneratorReal : ContDiff ℝ ∞ Φ := by
  have hΨ : ContDiff ℂ ∞ liClockThetaGenerator := differentiable_liClockThetaGenerator.contDiff
  have h : ContDiff ℝ ∞ (Complex.reCLM ∘ liClockThetaGenerator ∘ Complex.ofRealCLM) :=
    Complex.reCLM.contDiff.comp ((hΨ.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff)
  have e : Φ = Complex.reCLM ∘ liClockThetaGenerator ∘ Complex.ofRealCLM := funext fun x => by
    simp [liClockThetaGenerator_ofReal]
  rw [e]
  exact h

theorem contDiff_liClockThetaLogGenerator : ContDiff ℝ ∞ liClockThetaLogGenerator :=
  contDiff_liClockThetaGeneratorReal.log fun x =>
    (lt_of_lt_of_le one_pos (one_le_liClockThetaGeneratorReal x)).ne'

theorem differentiable_iteratedDeriv_liClockThetaLogGenerator (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k liClockThetaLogGenerator) :=
  contDiff_liClockThetaLogGenerator.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)

theorem hasDerivAt_liClockThetaLogGenerator (z : ℝ) :
    HasDerivAt liClockThetaLogGenerator (liClockThetaGeneratorRealDeriv z / Φ z) z :=
  (hasDerivAt_liClockThetaGeneratorReal z).log
    (lt_of_lt_of_le one_pos (one_le_liClockThetaGeneratorReal z)).ne'

/-- `κ₁ = Φ'/Φ`. -/
theorem iteratedDeriv_one_liClockThetaLogGenerator (z : ℝ) :
    iteratedDeriv 1 liClockThetaLogGenerator z = liClockThetaGeneratorRealDeriv z / Φ z := by
  rw [iteratedDeriv_one, (hasDerivAt_liClockThetaLogGenerator z).deriv]

theorem liClockThetaGeneratorRealDeriv_pos {z : ℝ} (hz : 0 < z) : 0 < liClockThetaGeneratorRealDeriv z := by
  rw [liClockThetaGeneratorRealDeriv_eq_mul]
  refine mul_pos hz ?_
  have h := le_hasSum (summable_liClockThetaGeneratorRealDeriv_div z).hasSum 0 fun j _ =>
    mul_nonneg (mul_nonneg (liClockThetaMomentRatio_pos j).le (liClockThetaGeneratorCoeff_pos j).le)
      (by rw [pow_mul]; positivity)
  have h0 : 0 < liClockThetaMomentRatio 0 * liClockThetaGeneratorCoeff 0 * z ^ (2 * 0) := by
    simp only [mul_zero, pow_zero, mul_one]
    exact mul_pos (liClockThetaMomentRatio_pos 0) (liClockThetaGeneratorCoeff_pos 0)
  linarith

/-- `κ₁ > 0` on `z > 0`. -/
theorem iteratedDeriv_one_liClockThetaLogGenerator_pos {z : ℝ} (hz : 0 < z) :
    0 < iteratedDeriv 1 liClockThetaLogGenerator z := by
  rw [iteratedDeriv_one_liClockThetaLogGenerator]
  exact div_pos (liClockThetaGeneratorRealDeriv_pos hz)
    (lt_of_lt_of_le one_pos (one_le_liClockThetaGeneratorReal z))

/-- `Φ(x) = ξ(1/2 + x)/ξ(1/2)` on the real line. -/
theorem liClockThetaGeneratorReal_eq_xi (x : ℝ) :
    (Φ x : ℂ) = xi (1 / 2 + (x : ℂ)) / xi (1 / 2) := by
  rw [← liClockThetaGenerator_ofReal, liClockThetaGenerator_eq_XiC]
  unfold XiC
  congr 2
  · ring_nf; rw [Complex.I_sq]; ring
  · simp

/-- **Bridge to the centered `ξ` logarithmic derivative.**  `κ₁(z) = Re (ξ'/ξ)(1/2 + z)`. -/
theorem liClockThetaGeneratorRealDeriv_div_eq_xiRealLogDeriv (z : ℝ) :
    liClockThetaGeneratorRealDeriv z / Φ z = xiRealLogDeriv z := by
  have hc : xi (1 / 2) ≠ 0 := by simpa using xi_ofReal_shift_ne_zero 0
  have hx : xi (1 / 2 + (z : ℂ)) ≠ 0 := xi_ofReal_shift_ne_zero z
  have h1 : HasDerivAt (fun x : ℝ => (Φ x : ℂ)) (liClockThetaGeneratorRealDeriv z : ℂ) z :=
    (hasDerivAt_liClockThetaGeneratorReal z).ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => (Φ x : ℂ)) (deriv xi (1 / 2 + (z : ℂ)) / xi (1 / 2)) z := by
    have hx' : HasDerivAt (fun w : ℂ => xi (1 / 2 + w) / xi (1 / 2))
        (deriv xi (1 / 2 + (z : ℂ)) * 1 / xi (1 / 2)) (z : ℂ) :=
      ((xi_differentiable (1 / 2 + (z : ℂ))).hasDerivAt.comp (z : ℂ)
        ((hasDerivAt_id (z : ℂ)).const_add (1 / 2))).div_const _
    have := hx'.comp_ofReal
    rw [mul_one] at this
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun x => liClockThetaGeneratorReal_eq_xi x)
  have hu := h1.unique h2
  have hΦ : (Φ z : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le one_pos (one_le_liClockThetaGeneratorReal z)).ne'
  have hc' : ((liClockThetaGeneratorRealDeriv z / Φ z : ℝ) : ℂ) = logDeriv xi (1 / 2 + (z : ℂ)) := by
    rw [Complex.ofReal_div, hu, liClockThetaGeneratorReal_eq_xi, logDeriv_apply]
    field_simp
  unfold xiRealLogDeriv
  rw [← hc', Complex.ofReal_re]

/-- `κ₁ = Re(ξ'/ξ)(1/2 + ·)` as functions. -/
theorem deriv_liClockThetaLogGenerator_eq_xiRealLogDeriv :
    deriv liClockThetaLogGenerator = xiRealLogDeriv := by
  funext z
  rw [(hasDerivAt_liClockThetaLogGenerator z).deriv, liClockThetaGeneratorRealDeriv_div_eq_xiRealLogDeriv]

/-- **Tilted variance.**  `κ₂ ≥ 0` on the whole line. -/
theorem iteratedDeriv_two_liClockThetaLogGenerator_nonneg (z : ℝ) :
    0 ≤ iteratedDeriv 2 liClockThetaLogGenerator z := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_liClockThetaLogGenerator_eq_xiRealLogDeriv]
  exact strictMono_xiRealLogDeriv.monotone.deriv_nonneg

/-! ## The Lah formula for `log Φ(1/p)` -/

theorem log_liClockThetaGeneratorReal_inv_eq_comp :
    (fun q => Real.log (Φ q⁻¹)) = fun q => liClockThetaLogGenerator q⁻¹ := rfl

/-- **Lah expansion (P15).**  For `p > 0`, `z = 1/p`,
`(-1)^{n+1} H^{(n+1)}(p) = Σ_{k ≤ n} (n+1)!/(k+1)! C(n,k) z^{n+k+2} κ_{k+1}(z)`. -/
theorem neg_one_pow_mul_iteratedDeriv_log_liClockThetaGeneratorReal_inv_eq_lah (n : ℕ) {p : ℝ}
    (hp : 0 < p) :
    (-1) ^ (n + 1) * iteratedDeriv (n + 1) (fun q => Real.log (Φ q⁻¹)) p =
      ∑ k ∈ Finset.range (n + 1), ((n + 1).factorial : ℝ) / ((k + 1).factorial : ℝ) *
        (n.choose k : ℝ) * p⁻¹ ^ (n + 1 + (k + 1)) *
          iteratedDeriv (k + 1) liClockThetaLogGenerator p⁻¹ :=
  neg_one_pow_mul_iteratedDeriv_comp_inv_eq_choose
    differentiable_iteratedDeriv_liClockThetaLogGenerator n hp

/-- **Third Lah bracket (P16).**  `-H'''(p) = z^4 (6κ₁ + 6zκ₂ + z²κ₃)`. -/
theorem neg_iteratedDeriv_three_log_liClockThetaGeneratorReal_inv {p : ℝ} (hp : 0 < p) :
    -iteratedDeriv 3 (fun q => Real.log (Φ q⁻¹)) p =
      p⁻¹ ^ 4 * (6 * iteratedDeriv 1 liClockThetaLogGenerator p⁻¹ +
        6 * p⁻¹ * iteratedDeriv 2 liClockThetaLogGenerator p⁻¹ +
          p⁻¹ ^ 2 * iteratedDeriv 3 liClockThetaLogGenerator p⁻¹) :=
  neg_iteratedDeriv_three_comp_inv differentiable_iteratedDeriv_liClockThetaLogGenerator hp

/-- **Order one.**  `-H'(p) = z² κ₁(z) > 0` for `p > 0`. -/
theorem neg_deriv_log_liClockThetaGeneratorReal_inv_pos {p : ℝ} (hp : 0 < p) :
    0 < -iteratedDeriv 1 (fun q => Real.log (Φ q⁻¹)) p := by
  have h := neg_one_pow_mul_iteratedDeriv_comp_inv
    differentiable_iteratedDeriv_liClockThetaLogGenerator 1 hp
  simp only [lahInverseSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have l10 : lahNumber 1 0 = 0 := rfl
  have l11 : lahNumber 1 1 = 1 := rfl
  rw [l10, l11] at h
  have hk := iteratedDeriv_one_liClockThetaLogGenerator_pos (inv_pos.2 hp)
  have hz : 0 < p⁻¹ ^ (1 + 1) := by positivity
  rw [log_liClockThetaGeneratorReal_inv_eq_comp]
  push_cast at h
  nlinarith [mul_pos hz hk]

/-- **Order two.**  `H''(p) = 2z³κ₁ + z⁴κ₂ > 0` for `p > 0`. -/
theorem iteratedDeriv_two_log_liClockThetaGeneratorReal_inv_pos {p : ℝ} (hp : 0 < p) :
    0 < iteratedDeriv 2 (fun q => Real.log (Φ q⁻¹)) p := by
  have h := neg_one_pow_mul_iteratedDeriv_comp_inv
    differentiable_iteratedDeriv_liClockThetaLogGenerator 2 hp
  simp only [lahInverseSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have l20 : lahNumber 2 0 = 0 := rfl
  have l21 : lahNumber 2 1 = 2 := rfl
  have l22 : lahNumber 2 2 = 1 := rfl
  rw [l20, l21, l22] at h
  have hk1 := iteratedDeriv_one_liClockThetaLogGenerator_pos (inv_pos.2 hp)
  have hk2 := iteratedDeriv_two_liClockThetaLogGenerator_nonneg p⁻¹
  have hz3 : 0 < p⁻¹ ^ (2 + 1) := by positivity
  have hz4 : 0 ≤ p⁻¹ ^ (2 + 2) := by positivity
  rw [log_liClockThetaGeneratorReal_inv_eq_comp]
  push_cast at h
  nlinarith [mul_pos hz3 hk1, mul_nonneg hz4 hk2]

/-! ## The crossing law -/

theorem continuous_liClockThetaKernelDeriv : Continuous liClockThetaKernelDeriv := by
  have h : deriv liClockThetaKernel = liClockThetaKernelDeriv :=
    funext fun t => (hasDerivAt_liClockThetaKernel t).deriv
  rw [← h]
  exact contDiff_liClockThetaKernel.continuous_deriv (by simp)

theorem liClockThetaKernel_zero : liClockThetaKernel 0 = 0 := by
  simp [liClockThetaKernel, oddFactorialSeries_zero]

theorem liEvenCrossActualClockPrimitive_zero : P 0 = 0 := by
  simp [liEvenCrossActualClockPrimitive]

/-- `F ⋆ K = P ⋆ K'`. -/
theorem volterraConv_response_kernel_eq (t : ℝ) :
    volterraConv liEvenCrossActualClockResponse liClockThetaKernel t =
      volterraConv P liClockThetaKernelDeriv t := by
  have h1 := hasDerivAt_volterraConv (f := P) (f' := liEvenCrossActualClockResponse)
    (g := liClockThetaKernel) hasDerivAt_liEvenCrossActualClockPrimitive
    continuous_liEvenCrossActualClockResponse continuous_liClockThetaKernel t
  have h2 := hasDerivAt_volterraConv (f := liClockThetaKernel) (f' := liClockThetaKernelDeriv)
    (g := P) hasDerivAt_liClockThetaKernel continuous_liClockThetaKernelDeriv
    continuous_liEvenCrossActualClockPrimitive t
  rw [liEvenCrossActualClockPrimitive_zero, zero_mul, zero_add] at h1
  rw [liClockThetaKernel_zero, zero_mul, zero_add, ← volterraConv_comm' P] at h2
  rw [h1.unique h2, volterraConv_comm]

/-- **Crossing law (P17).**  `F(t) = K(t) + tK'(t) - ∫_0^t P(s) K'(t-s) ds` for every `t`. -/
theorem liEvenCrossActualClockResponse_eq_crossing (t : ℝ) :
    liEvenCrossActualClockResponse t = liClockThetaKernel t + t * liClockThetaKernelDeriv t -
      ∫ s in (0 : ℝ)..t, P s * liClockThetaKernelDeriv (t - s) := by
  have h := liEvenCrossActualClockResponse_volterra_kernel t
  rw [volterraConv_response_kernel_eq, volterraConv_comm] at h
  unfold liClockThetaClockInput volterraConv at h
  rw [intervalIntegral.integral_congr (g := fun s => P s * liClockThetaKernelDeriv (t - s))
    fun s _ => mul_comm _ _] at h
  linarith

/-- At a zero `T ≥ 0` of `P`, the history equals the forcing: `∫_0^T P(s) K(T-s) ds = T K(T)`. -/
theorem integral_liEvenCrossActualClockPrimitive_mul_kernel_of_eq_zero {T : ℝ} (hT : 0 ≤ T)
    (hP : P T = 0) :
    ∫ s in (0 : ℝ)..T, P s * liClockThetaKernel (T - s) = T * liClockThetaKernel T := by
  have h := liEvenCrossActualClockPrimitive_volterra hT
  simp only [deriv_liEvenCrossActualClockBorelKernel_eq] at h
  rw [hP, zero_add] at h
  exact h

end RHTower
