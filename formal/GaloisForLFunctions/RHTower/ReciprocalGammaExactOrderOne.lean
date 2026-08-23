import GaloisForLFunctions.RHTower.GammaInvGrowth
import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranchTaylor
import GaloisForLFunctions.HTGeometry.OrderOneEnvelope
import GaloisForLFunctions.HTGeometry.MinimalTypeNoArithmeticProgression
import GaloisForLFunctions.RHTower.ReflectedGammaCarrier

/-!
# Exact entire order of reciprocal-Gamma carriers

The explicit Weierstrass estimate for reciprocal Gamma is compressed into the project's global
order-one envelope.  A reflected pair inherits that envelope.  Its nonconstant arithmetic
progression of zeros excludes every minimal-exponential-type bound, giving a dependency-closed
certificate of classical exact entire order one.
-/

open Complex Real

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reciprocal Gamma satisfies the global order-at-most-one logarithmic envelope. -/
theorem orderOneEnvelope_reciprocalGammaEntire :
    OrderOneEnvelope reciprocalGammaEntire := by
  let logTwo : ℝ := Real.log 2
  let E : ℝ := ‖Real.eulerMascheroniConstant‖
  let C : ℝ := 4 + (E + 4) / logTwo
  have hlogTwo : 0 < logTwo := by
    dsimp [logTwo]
    exact Real.log_pos (by norm_num)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun s => ?_⟩
  let r : ℝ := ‖s‖
  let m : ℕ := HilbertSchmidt.gammaGrowthIndex s
  let W : ℝ := (1 + r) * Real.log (2 + r)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have hlogLower : logTwo ≤ Real.log (2 + r) := by
    dsimp [logTwo]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hrlog : r * logTwo ≤ W := by
    have h := mul_le_mul_of_nonneg_left hlogLower hr
    dsimp [W]
    nlinarith
  have hlogOne : Real.log (1 + r) ≤ Real.log (2 + r) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogTwoR : Real.log (2 + r) ≤ W := by
    dsimp [W]
    have hlog0 : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
    nlinarith
  have hm1 : 1 ≤ m := by
    dsimp [m, HilbertSchmidt.gammaGrowthIndex]
    omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hmle : (m : ℝ) ≤ r + 2 := by
    dsimp [m, HilbertSchmidt.gammaGrowthIndex, r]
    have hc := Nat.ceil_lt_add_one (norm_nonneg s)
    push_cast
    linarith
  have hlogm : Real.log (m : ℝ) ≤ Real.log (2 + r) :=
    Real.log_le_log hmpos (by linarith)
  have hr_exp : r ≤ Real.exp W := by
    calc
      r ≤ 2 + r := by linarith
      _ = Real.exp (Real.log (2 + r)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp W := Real.exp_le_exp.mpr hlogTwoR
  have hEr : E * r ≤ (E / logTwo) * W := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlogTwo]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hrlog hE
  have hpowExp : (1 + r) ^ m ≤ Real.exp (2 * W) := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have hlog0 : 0 ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
    have hmstep : (m : ℝ) * Real.log (1 + r) ≤
        (r + 2) * Real.log (2 + r) :=
      mul_le_mul hmle hlogOne hlog0 (by linarith)
    dsimp [W]
    nlinarith [hmstep, Real.log_nonneg (show 1 ≤ 2 + r by linarith)]
  have htailExp :
      Real.exp (r * (1 + Real.log (m : ℝ)) + 3 * r) ≤
        Real.exp ((1 + 4 / logTwo) * W) := by
    apply Real.exp_le_exp.mpr
    have hrlogm : r * Real.log (m : ℝ) ≤ W := by
      calc
        r * Real.log (m : ℝ) ≤ r * Real.log (2 + r) :=
          mul_le_mul_of_nonneg_left hlogm hr
        _ ≤ W := by
          dsimp [W]
          nlinarith [Real.log_nonneg (show 1 ≤ 2 + r by linarith)]
    have h4r : 4 * r ≤ (4 / logTwo) * W := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlogTwo]
      nlinarith
    nlinarith
  have hraw := HilbertSchmidt.norm_Gamma_inv_le_weierstrass_envelope s
  unfold GaloisForLFunctions.reciprocalGammaEntire
  calc
    ‖(Complex.Gamma s)⁻¹‖ ≤
        r * Real.exp (E * r) *
          ((1 + r) ^ m *
            Real.exp (r * (1 + Real.log (m : ℝ)) + 3 * r)) := by
          simpa [r, E, m] using hraw
    _ ≤ Real.exp W * Real.exp ((E / logTwo) * W) *
          (Real.exp (2 * W) * Real.exp ((1 + 4 / logTwo) * W)) := by
          gcongr
    _ = Real.exp (C * W) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          dsimp [C]
          ring
    _ = Real.exp (orderOneWeight C s) := by
          congr 1
          simp only [orderOneWeight, W, r]
          ring

/-- Dependency-closed classical exact-order-one certificate.  The upper half is the standard
`r log r` envelope; failure of minimal exponential type rules out every order below one. -/
def HasExactEntireOrderOne (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ OrderOneEnvelope f ∧ ¬ HasMinimalExponentialType f

/-- A reflected reciprocal-Gamma pair has order at most one. -/
theorem reflectedGammaCarrier_orderOneEnvelope (alpha : ℝ) :
    OrderOneEnvelope (reflectedGammaCarrier alpha) := by
  have hplus := orderOneEnvelope_reciprocalGammaEntire.comp_affine
    Complex.I (alpha : ℂ)
  have hminus := orderOneEnvelope_reciprocalGammaEntire.comp_affine
    (-Complex.I) (alpha : ℂ)
  refine (hplus.mul hminus).congr fun z => ?_
  simp only [reflectedGammaCarrier]
  congr 1 <;> ring_nf

/-- Positive shifts give a nonzero central anchor. -/
theorem reflectedGammaCarrier_ne_zero_zero {alpha : ℝ} (halpha : 0 < alpha) :
    reflectedGammaCarrier alpha 0 ≠ 0 := by
  have hGamma : Complex.Gamma (alpha : ℂ) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  simp only [reflectedGammaCarrier, mul_zero, add_zero, sub_zero]
  exact mul_ne_zero (inv_ne_zero hGamma) (inv_ne_zero hGamma)

/-- One half of the carrier divisor is a nonconstant arithmetic progression. -/
theorem reflectedGammaCarrier_zero_arithmeticProgression (alpha : ℝ) (n : ℕ) :
    reflectedGammaCarrier alpha
      (Complex.I * (alpha : ℂ) + n • Complex.I) = 0 := by
  rw [reflectedGammaCarrier_eq_zero_iff]
  left
  refine ⟨n, ?_⟩
  simp only [nsmul_eq_mul]
  ring

/-- The arithmetic-progression divisor excludes minimal exponential type. -/
theorem reflectedGammaCarrier_not_minimalExponentialType
    {alpha : ℝ} (halpha : 0 < alpha) :
    ¬ HasMinimalExponentialType (reflectedGammaCarrier alpha) := by
  intro hmin
  exact hmin.no_arithmeticProgression_zeros
    (reflectedGammaCarrier_ne_zero_zero halpha) Complex.I_ne_zero
    (reflectedGammaCarrier_zero_arithmeticProgression alpha)

/-- A positive-shift reflected reciprocal-Gamma carrier has classical exact entire order one. -/
theorem reflectedGammaCarrier_hasExactEntireOrderOne
    {alpha : ℝ} (halpha : 0 < alpha) :
    HasExactEntireOrderOne (reflectedGammaCarrier alpha) := by
  refine ⟨?_, reflectedGammaCarrier_orderOneEnvelope alpha,
    reflectedGammaCarrier_not_minimalExponentialType halpha⟩
  exact fun z =>
    (reflectedGammaCarrier_analyticOnNhd alpha z (Set.mem_univ z)).differentiableAt

end
end RHTower
