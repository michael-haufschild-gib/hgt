import GaloisForLFunctions.HTGeometry.EulerQGammaGenusOneBound
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne

/-!
# The renormalised local factor is one plus a quadratically small error

Splitting Jackson's local response into its power factor, its numerator product and its
denominator product, and distributing the first-activation counterterm
`ℓ_q(s) = q(s−1) + q^{1+s}` over the three pieces, each piece becomes a genus-one renormalised
factor: the power factor is `exp(−s(log(1−q)+q))`, the numerator is `(q;q)_∞ eq` and the
denominator is `(q^{1+s};q)_∞ e^{q^{1+s}}`.  Each deviates from `1` quadratically in its own small
parameter.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The logarithmic defect of the power factor -/

/-- On the half interval the logarithm deviates from its linear term quadratically. -/
theorem abs_log_one_sub_add_self_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hxabs : |x| = x := abs_of_nonneg hx0
  have habs : |x| < 1 := by
    rw [hxabs]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  have hsum : (∑ i ∈ Finset.range 1, x ^ (i + 1) / ((i : ℝ) + 1)) = x := by
    simp
  rw [hsum, hxabs] at h
  have hle : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  rw [add_comm (Real.log (1 - x)) x]
  linarith

/-! ## The three renormalised pieces -/

/-- The renormalised power factor `(1−q)^{−s} e^{−qs}`. -/
def eqgPowerFactor (q : RealEulerNome) (s : ℂ) : ℂ :=
  ((1 - q.val : ℝ) : ℂ) ^ (-s) * Complex.exp (-((q.val : ℂ) * s))

/-- The renormalised numerator factor `(q;q)_∞ e^q`. -/
def eqgNumerFactor (q : RealEulerNome) : ℂ :=
  ((realQFactorialInf q : ℝ) : ℂ) * Complex.exp ((q.val : ℂ))

/-- The renormalised denominator factor `(q^{1+s};q)_∞ e^{q^{1+s}}`. -/
def eqgDenomFactorRenorm (q : RealEulerNome) (s : ℂ) : ℂ :=
  qDenomProduct q (1 + s) * Complex.exp ((q.val : ℂ) ^ (1 + s))

/-- **The three-factor split of the renormalised local response.** -/
theorem eqgRenormLocal_factorization (q : RealEulerNome) {s : ℂ} (hs : 1 + s ∈ qHalfPlane) :
    eqgRenormLocal q s
      = eqgPowerFactor q s * eqgNumerFactor q * (eqgDenomFactorRenorm q s)⁻¹ := by
  have hD : qDenomProduct q (1 + s) ≠ 0 := qDenomProduct_ne_zero q hs
  have hE : Complex.exp ((q.val : ℂ) ^ (1 + s)) ≠ 0 := Complex.exp_ne_zero _
  rw [eqgRenormLocal, qGammaOn, eqgPowerFactor, eqgNumerFactor, eqgDenomFactorRenorm,
    eqgActivation]
  have hpow : ((1 - q.val : ℝ) : ℂ) ^ (1 - (1 + s)) = ((1 - q.val : ℝ) : ℂ) ^ (-s) := by
    congr 1
    ring
  rw [hpow, mul_inv]
  have hexp : Complex.exp (-((q.val : ℂ) * (s - 1) + (q.val : ℂ) ^ (1 + s)))
      = Complex.exp (-((q.val : ℂ) * s)) * Complex.exp ((q.val : ℂ))
        * (Complex.exp ((q.val : ℂ) ^ (1 + s)))⁻¹ := by
    rw [← Complex.exp_add, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp

/-! ## The power factor -/

theorem eqgPowerFactor_eq_exp (q : RealEulerNome) (s : ℂ) :
    eqgPowerFactor q s
      = Complex.exp (-(s * ((Real.log (1 - q.val) + q.val : ℝ) : ℂ))) := by
  have h1 : ((1 - q.val : ℝ) : ℂ) ≠ 0 := q.one_sub_complex_ne_zero
  have h2 : (0 : ℝ) ≤ 1 - q.val := by
    have := q.lt_one
    linarith
  rw [eqgPowerFactor, Complex.cpow_def_of_ne_zero h1, ← Complex.exp_add,
    ← Complex.ofReal_log h2]
  congr 1
  push_cast
  ring

theorem norm_eqgPowerFactor_sub_one_le (q : RealEulerNome) (hq : q.val ≤ 1 / 2) (s : ℂ) :
    ‖eqgPowerFactor q s - 1‖
      ≤ Real.exp (2 * ‖s‖ * q.val ^ 2) * (2 * ‖s‖ * q.val ^ 2) := by
  rw [eqgPowerFactor_eq_exp]
  refine norm_cexp_sub_one_le_of_le ?_
  rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hlog := abs_log_one_sub_add_self_le q.pos.le hq
  have hs : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  calc ‖s‖ * |Real.log (1 - q.val) + q.val| ≤ ‖s‖ * (2 * q.val ^ 2) :=
        mul_le_mul_of_nonneg_left hlog hs
    _ = 2 * ‖s‖ * q.val ^ 2 := by ring

end

end GaloisForLFunctions.HTGeometry
