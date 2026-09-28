import GaloisForLFunctions.RHTower.ThetaTailCapacitySharpness

/-!
# Theta derivative packets: the entire factor and the added divisor

For `m ≥ 1` and `t ∈ ℝ` put `k_t = k + t k^{(4m)}`, where `k` is the literal theta source. Then
`∫ e^{-izx} k_t(x) dx = XiC(z) (1 + t z^{4m})` for every complex `z`, every moment of order below
`4m` is unchanged, and `∫ x^{4m}(k_t - k) = t (4m)! ∫ k`.

For `t > 0` the factor `1 + t z^{4m}` is positive on the real line, so `F_t` and `XiC` share
their real zeros, multiplicities and signs; its zeros are exactly the packet
`α_j = t^{-1/(4m)} e^{(2j+1)πi/(4m)}`, `0 ≤ j < 4m`: simple, off both axes, closed under
conjugation and negation, escaping to infinity as `t ↓ 0`. On every disc about the origin the
zero counts differ by `0` or `4m`. The packet has vanishing reciprocal power sums below order
`4m`, `Σ α_j^{-4m} = -4mt`, relative factor `|F_t/XiC - 1| ≤ t R^{4m}` on `|z| ≤ R`, and
`log(1 + t z^{4m})` vanishes to order exactly `4m` at the origin.
-/
open MeasureTheory Set Filter Topology Complex Metric
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ## The deformed source `k_t = k + t k^{(4m)}` -/

/-- The positive differential deformation `k_t = k + t k^{(4m)}` of the literal theta source. -/
def thetaDerivativePacket (m : ℕ) (t x : ℝ) : ℝ :=
  thetaCuspFullSource x + t * iteratedDeriv (4 * m) thetaCuspFullSource x

theorem iteratedDeriv_four_mul_thetaCuspFullSource_neg (m : ℕ) (x : ℝ) :
    iteratedDeriv (4 * m) thetaCuspFullSource (-x) = iteratedDeriv (4 * m) thetaCuspFullSource x := by
  have h := iteratedDeriv_thetaCuspFullSource_neg (4 * m) x
  have hpow : (-1 : ℝ) ^ (4 * m) = 1 := by
    rw [show 4 * m = 2 * (2 * m) by ring, pow_mul]; norm_num
  rw [hpow, one_mul] at h
  exact h

theorem thetaDerivativePacket_neg (m : ℕ) (t x : ℝ) :
    thetaDerivativePacket m t (-x) = thetaDerivativePacket m t x := by
  unfold thetaDerivativePacket
  rw [thetaCuspFullSource_neg, iteratedDeriv_four_mul_thetaCuspFullSource_neg]

/-- The complex form of `k_t`. -/
def thetaDerivativePacketC (m : ℕ) (t : ℝ) (x : ℝ) : ℂ := (thetaDerivativePacket m t x : ℂ)

theorem thetaDerivativePacketC_eq (m : ℕ) (t : ℝ) :
    thetaDerivativePacketC m t = fun x => thetaSourceC x + (t : ℂ) * thetaDerivSourceC (4 * m) x := by
  funext x
  simp [thetaDerivativePacketC, thetaDerivativePacket, thetaSourceC, thetaDerivSourceC]

theorem expMomentSource_const_mul_thetaDerivSourceC (n : ℕ) (c : ℂ) :
    ExpMomentSource (fun x => c * thetaDerivSourceC n x) := by
  refine ⟨continuous_const.mul (continuous_thetaDerivSourceC n), fun a => ?_⟩
  refine ((expMomentSource_thetaDerivSourceC n).moment a).const_mul ‖c‖ |>.congr
    (Eventually.of_forall fun x => ?_)
  simp only [norm_mul]
  ring

theorem expMomentSource_thetaDerivativePacketC (m : ℕ) (t : ℝ) :
    ExpMomentSource (thetaDerivativePacketC m t) := by
  rw [thetaDerivativePacketC_eq]
  have h1 := expMomentSource_thetaSourceC
  have h2 := expMomentSource_const_mul_thetaDerivSourceC (4 * m) (t : ℂ)
  refine ⟨h1.continuous.add h2.continuous, fun a => ?_⟩
  refine ((h1.moment a).add (h2.moment a)).mono'
    (by have := h1.continuous; have := h2.continuous; fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le

/-- **The entire Fourier factor.** `F_t(z) = ∫ e^{-izx} k_t(x) dx = XiC(z) (1 + t z^{4m})` for
every complex `z`. -/
theorem sourceTransform_thetaDerivativePacketC (m : ℕ) (t : ℝ) (z : ℂ) :
    sourceTransform (thetaDerivativePacketC m t) z = XiC z * (1 + t * z ^ (4 * m)) := by
  rw [thetaDerivativePacketC_eq, sourceTransform_add expMomentSource_thetaSourceC
    (expMomentSource_const_mul_thetaDerivSourceC (4 * m) (t : ℂ)), sourceTransform_thetaSourceC]
  have h := sourceTransform_thetaCapacityPacket m t z
  unfold thetaCapacityPacket at h
  rw [h]
  ring

/-! ## Moment cancellation -/

theorem integrable_pow_mul_iteratedDeriv_thetaCuspFullSource (i j : ℕ) :
    Integrable (fun x : ℝ => x ^ j * iteratedDeriv i thetaCuspFullSource x) := by
  have hI := (integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource i 1).const_mul
    (j.factorial : ℝ)
  refine hI.mono' ((continuous_pow j).mul (contDiff_thetaCuspFullSource.continuous_iteratedDeriv i
    (by exact_mod_cast le_top))).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, one_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have h := Real.pow_div_factorial_le_exp _ (abs_nonneg x) j
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  rw [div_le_iff₀ hf] at h
  linarith [mul_comm (Real.exp |x|) (j.factorial : ℝ)]

theorem hasDerivAt_iteratedDeriv_thetaCuspFullSource (i : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv i thetaCuspFullSource)
      (iteratedDeriv (i + 1) thetaCuspFullSource x) x := by
  rw [iteratedDeriv_thetaCuspFullSource, iteratedDeriv_thetaCuspFullSource]
  exact hasDerivAt_thetaCuspFullDerivative i x

/-- One integration by parts: `∫ x^j k^{(i+1)} = -j ∫ x^{j-1} k^{(i)}`. -/
theorem integral_pow_mul_iteratedDeriv_succ_thetaCuspFullSource (i j : ℕ) :
    ∫ x : ℝ, x ^ j * iteratedDeriv (i + 1) thetaCuspFullSource x =
      -(j : ℝ) * ∫ x : ℝ, x ^ (j - 1) * iteratedDeriv i thetaCuspFullSource x := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x ^ j) (v := iteratedDeriv i thetaCuspFullSource)
    (u' := fun x : ℝ => (j : ℝ) * x ^ (j - 1)) (v' := iteratedDeriv (i + 1) thetaCuspFullSource)
    (fun x _ => hasDerivAt_pow j x) (fun x _ => hasDerivAt_iteratedDeriv_thetaCuspFullSource i x)
    (integrable_pow_mul_iteratedDeriv_thetaCuspFullSource (i + 1) j)
    (((integrable_pow_mul_iteratedDeriv_thetaCuspFullSource i (j - 1)).const_mul (j : ℝ)).congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring))
    (integrable_pow_mul_iteratedDeriv_thetaCuspFullSource i j)
  rw [h, ← integral_const_mul, ← integral_neg]
  congr 1
  funext x
  ring

/-- Repeated integration by parts: `∫ x^j k^{(i)} = (-1)^i j(j-1)⋯(j-i+1) ∫ x^{j-i} k`. -/
theorem integral_pow_mul_iteratedDeriv_thetaCuspFullSource (i j : ℕ) :
    ∫ x : ℝ, x ^ j * iteratedDeriv i thetaCuspFullSource x =
      (-1) ^ i * (j.descFactorial i : ℝ) * ∫ x : ℝ, x ^ (j - i) * thetaCuspFullSource x := by
  induction i generalizing j with
  | zero => simp
  | succ i ih =>
      rw [integral_pow_mul_iteratedDeriv_succ_thetaCuspFullSource, ih]
      rcases j with _ | n
      · simp
      · rw [Nat.succ_descFactorial_succ, show n + 1 - 1 = n by omega,
          show n + 1 - (i + 1) = n - i by omega]
        push_cast
        ring

theorem integral_pow_mul_iteratedDeriv_thetaCuspFullSource_eq_zero {i j : ℕ} (hij : j < i) :
    ∫ x : ℝ, x ^ j * iteratedDeriv i thetaCuspFullSource x = 0 := by
  rw [integral_pow_mul_iteratedDeriv_thetaCuspFullSource, (Nat.descFactorial_eq_zero_iff_lt).2 hij]
  simp

theorem integrable_pow_mul_thetaDerivativePacket (m j : ℕ) (t : ℝ) :
    Integrable (fun x : ℝ => x ^ j * thetaDerivativePacket m t x) := by
  have h := (integrable_pow_mul_iteratedDeriv_thetaCuspFullSource 0 j).add
    ((integrable_pow_mul_iteratedDeriv_thetaCuspFullSource (4 * m) j).const_mul t)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [thetaDerivativePacket, iteratedDeriv_zero, Pi.add_apply]
  ring

theorem integral_pow_mul_thetaDerivativePacket (m j : ℕ) (t : ℝ) :
    ∫ x : ℝ, x ^ j * thetaDerivativePacket m t x =
      (∫ x : ℝ, x ^ j * thetaCuspFullSource x) +
        t * ∫ x : ℝ, x ^ j * iteratedDeriv (4 * m) thetaCuspFullSource x := by
  rw [← integral_const_mul, ← integral_add (by simpa using
    integrable_pow_mul_iteratedDeriv_thetaCuspFullSource 0 j)
    ((integrable_pow_mul_iteratedDeriv_thetaCuspFullSource (4 * m) j).const_mul t)]
  congr 1
  funext x
  simp only [thetaDerivativePacket]
  ring

/-- **Moment cancellation.** The deformation preserves every moment of order below `4m`. -/
theorem integral_pow_mul_thetaDerivativePacket_of_lt (m : ℕ) (t : ℝ) {j : ℕ} (hj : j < 4 * m) :
    ∫ x : ℝ, x ^ j * thetaDerivativePacket m t x = ∫ x : ℝ, x ^ j * thetaCuspFullSource x := by
  rw [integral_pow_mul_thetaDerivativePacket,
    integral_pow_mul_iteratedDeriv_thetaCuspFullSource_eq_zero hj, mul_zero, add_zero]

/-- **The first moved moment.** `∫ x^{4m} (k_t - k) = t (4m)! ∫ k`. -/
theorem integral_pow_mul_thetaDerivativePacket_sub (m : ℕ) (t : ℝ) :
    (∫ x : ℝ, x ^ (4 * m) * thetaDerivativePacket m t x) -
        ∫ x : ℝ, x ^ (4 * m) * thetaCuspFullSource x =
      t * (4 * m).factorial * ∫ x : ℝ, thetaCuspFullSource x := by
  rw [integral_pow_mul_thetaDerivativePacket, integral_pow_mul_iteratedDeriv_thetaCuspFullSource,
    Nat.descFactorial_self, Nat.sub_self]
  have hpow : (-1 : ℝ) ^ (4 * m) = 1 := by
    rw [show 4 * m = 2 * (2 * m) by ring, pow_mul]; norm_num
  simp only [pow_zero, one_mul, hpow]
  ring

theorem integral_pow_mul_thetaDerivativePacket_sub_pos (m : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < (∫ x : ℝ, x ^ (4 * m) * thetaDerivativePacket m t x) -
        ∫ x : ℝ, x ^ (4 * m) * thetaCuspFullSource x := by
  rw [integral_pow_mul_thetaDerivativePacket_sub]
  have : (0 : ℝ) < (4 * m).factorial := by exact_mod_cast (4 * m).factorial_pos
  have := integral_thetaCuspFullSource_pos
  positivity

/-! ## The real divisor is unchanged -/

theorem pow_four_mul_nonneg (m : ℕ) (x : ℝ) : 0 ≤ x ^ (4 * m) := by
  rw [show 4 * m = 2 * (2 * m) by ring, pow_mul]
  positivity

theorem thetaPacketFactor_ofReal_pos (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    0 < 1 + t * x ^ (4 * m) := by
  have := pow_four_mul_nonneg m x
  positivity

theorem sourceTransform_thetaDerivativePacketC_eq_mul (m : ℕ) (t : ℝ) :
    sourceTransform (thetaDerivativePacketC m t) = XiC * fun z => 1 + (t : ℂ) * z ^ (4 * m) :=
  funext fun z => sourceTransform_thetaDerivativePacketC m t z

theorem analyticAt_thetaPacketFactor (m : ℕ) (t : ℝ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => 1 + (t : ℂ) * w ^ (4 * m)) z := by
  fun_prop

theorem differentiable_sourceTransform_thetaDerivativePacketC (m : ℕ) (t : ℝ) :
    Differentiable ℂ (sourceTransform (thetaDerivativePacketC m t)) :=
  (expMomentSource_thetaDerivativePacketC m t).differentiable_sourceTransform

/-- Away from the zeros of `1 + t z^{4m}` the transforms `F_t` and `XiC` vanish to the same order. -/
theorem analyticOrderAt_thetaDerivativePacketC_of_factor_ne_zero (m : ℕ) (t : ℝ) {z : ℂ}
    (hz : 1 + (t : ℂ) * z ^ (4 * m) ≠ 0) :
    analyticOrderAt (sourceTransform (thetaDerivativePacketC m t)) z = analyticOrderAt XiC z := by
  rw [sourceTransform_thetaDerivativePacketC_eq_mul,
    analyticOrderAt_mul (XiC_differentiable.analyticAt z) (analyticAt_thetaPacketFactor m t z),
    (analyticOrderAt_eq_zero (f := fun w : ℂ => 1 + (t : ℂ) * w ^ (4 * m))).2 (Or.inr hz), add_zero]

/-- **The real divisor and sign pattern are preserved.** On the real line
`F_t(x) = (1 + t x^{4m}) XiC(x)` with a strictly positive factor, so `F_t` and `XiC` have the same
real zeros with the same multiplicities and signs. -/
theorem thetaDerivativePacketC_real_divisor (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    0 < 1 + t * x ^ (4 * m) ∧
      sourceTransform (thetaDerivativePacketC m t) x = ((1 + t * x ^ (4 * m) : ℝ) : ℂ) * XiC x ∧
      analyticOrderAt (sourceTransform (thetaDerivativePacketC m t)) (x : ℂ) =
        analyticOrderAt XiC x := by
  have hpos := thetaPacketFactor_ofReal_pos m ht x
  refine ⟨hpos, ?_, analyticOrderAt_thetaDerivativePacketC_of_factor_ne_zero m t ?_⟩
  · rw [sourceTransform_thetaDerivativePacketC]; push_cast; ring
  · exact_mod_cast hpos.ne'

/-! ## The added nonreal packet -/

/-- The packet root `α_j = t^{-1/(4m)} e^{(2j+1)πi/(4m)}`. -/
def thetaPacketRoot (m : ℕ) (t : ℝ) (j : ℕ) : ℂ :=
  ((t ^ (-(1 / (4 * m : ℝ))) : ℝ) : ℂ) * Complex.exp ((2 * j + 1) * Real.pi * I / (4 * m))

/-- The primitive `4m`-th root of unity `ω = e^{2πi/(4m)}`. -/
theorem isPrimitiveRoot_thetaPacket (m : ℕ) (hm : 0 < m) :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * I / (4 * m : ℕ))) (4 * m) :=
  Complex.isPrimitiveRoot_exp (4 * m) (by omega)

theorem thetaPacketRoot_eq_mul_pow (m : ℕ) (t : ℝ) (j : ℕ) :
    thetaPacketRoot m t j =
      thetaPacketRoot m t 0 * Complex.exp (2 * Real.pi * I / (4 * m : ℕ)) ^ j := by
  have h : Complex.exp ((2 * j + 1) * Real.pi * I / (4 * m)) =
      Complex.exp ((2 * ((0 : ℕ) : ℂ) + 1) * Real.pi * I / (4 * m)) *
        Complex.exp (2 * Real.pi * I / (4 * m : ℕ)) ^ j := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold thetaPacketRoot
  rw [h]
  ring

theorem thetaPacketRoot_eq_cos_sin (m : ℕ) (t : ℝ) (j : ℕ) :
    thetaPacketRoot m t j = ((t ^ (-(1 / (4 * m : ℝ))) : ℝ) : ℂ) *
      (Real.cos ((2 * j + 1) * Real.pi / (4 * m)) +
        Real.sin ((2 * j + 1) * Real.pi / (4 * m)) * I) := by
  unfold thetaPacketRoot
  congr 1
  rw [show (2 * (j : ℂ) + 1) * Real.pi * I / (4 * m) =
      (((2 * j + 1) * Real.pi / (4 * m) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  push_cast
  ring

theorem thetaPacketRoot_re (m : ℕ) (t : ℝ) (j : ℕ) :
    (thetaPacketRoot m t j).re =
      t ^ (-(1 / (4 * m : ℝ))) * Real.cos ((2 * j + 1) * Real.pi / (4 * m)) := by
  rw [thetaPacketRoot_eq_cos_sin]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem thetaPacketRoot_im (m : ℕ) (t : ℝ) (j : ℕ) :
    (thetaPacketRoot m t j).im =
      t ^ (-(1 / (4 * m : ℝ))) * Real.sin ((2 * j + 1) * Real.pi / (4 * m)) := by
  rw [thetaPacketRoot_eq_cos_sin]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem norm_thetaPacketRoot (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    ‖thetaPacketRoot m t j‖ = t ^ (-(1 / (4 * m : ℝ))) := by
  rw [thetaPacketRoot_eq_cos_sin, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht _)]
  have h : ((Real.cos ((2 * j + 1) * Real.pi / (4 * m)) : ℂ) +
      Real.sin ((2 * j + 1) * Real.pi / (4 * m)) * I) =
      Complex.exp ((((2 * j + 1) * Real.pi / (4 * m) : ℝ) : ℂ) * I) := by
    rw [Complex.exp_mul_I]; push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem thetaPacketRoot_pow (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    thetaPacketRoot m t j ^ (4 * m) = -(t : ℂ)⁻¹ := by
  unfold thetaPacketRoot
  rw [mul_pow, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le,
    ← Complex.exp_nat_mul]
  have hm' : (4 * m : ℝ) ≠ 0 := by positivity
  have hmC : (4 * m : ℂ) ≠ 0 := by exact_mod_cast (by omega : 4 * m ≠ 0)
  have hmC' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 : (-(1 / (4 * m : ℝ))) * ((4 * m : ℕ) : ℝ) = -1 := by push_cast; field_simp
  have h2 : ((4 * m : ℕ) : ℂ) * ((2 * j + 1) * Real.pi * I / (4 * m)) =
      ((2 * j + 1 : ℕ) : ℂ) * (Real.pi * I) := by push_cast; field_simp
  rw [h1, h2, Complex.exp_nat_mul, Complex.exp_pi_mul_I, Odd.neg_one_pow (by exact ⟨j, rfl⟩),
    Real.rpow_neg_one]
  push_cast
  ring

/-- Every packet root is a zero of the factor `1 + t z^{4m}`. -/
theorem thetaPacketFactor_root (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    1 + (t : ℂ) * thetaPacketRoot m t j ^ (4 * m) = 0 := by
  rw [thetaPacketRoot_pow m hm ht, mul_neg, mul_inv_cancel₀ (by exact_mod_cast ht.ne')]
  ring

theorem thetaPacketRoot_zero_ne_zero (m : ℕ) {t : ℝ} (ht : 0 < t) : thetaPacketRoot m t 0 ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_thetaPacketRoot m ht.le]
  exact (Real.rpow_pos_of_pos ht _).ne'

/-- The zeros of `1 + t z^{4m}` are exactly the `4m` packet roots. -/
theorem thetaPacketFactor_eq_zero_iff (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    1 + (t : ℂ) * z ^ (4 * m) = 0 ↔ ∃ j < 4 * m, thetaPacketRoot m t j = z := by
  constructor
  · intro hz
    haveI : NeZero (4 * m) := ⟨by omega⟩
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have h0 := thetaPacketRoot_zero_ne_zero m ht
    have hzpow : z ^ (4 * m) = -(t : ℂ)⁻¹ := by
      field_simp
      linear_combination hz
    have hunit : (z / thetaPacketRoot m t 0) ^ (4 * m) = 1 := by
      rw [div_pow, hzpow, thetaPacketRoot_pow m hm ht, div_self (by simp [htC])]
    obtain ⟨i, hi, hω⟩ := (isPrimitiveRoot_thetaPacket m hm).eq_pow_of_pow_eq_one hunit
    refine ⟨i, hi, ?_⟩
    rw [thetaPacketRoot_eq_mul_pow, hω, mul_div_cancel₀ _ h0]
  · rintro ⟨j, -, rfl⟩
    exact thetaPacketFactor_root m hm ht j

theorem thetaPacketRoot_injOn (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) {i j : ℕ}
    (hi : i < 4 * m) (hj : j < 4 * m) (h : thetaPacketRoot m t i = thetaPacketRoot m t j) :
    i = j := by
  rw [thetaPacketRoot_eq_mul_pow m t i, thetaPacketRoot_eq_mul_pow m t j] at h
  exact (isPrimitiveRoot_thetaPacket m hm).pow_inj hi hj
    (mul_left_cancel₀ (thetaPacketRoot_zero_ne_zero m ht) h)

/-- No packet root is real: an odd multiple of `π/(4m)` is not an integer multiple of `π`. -/
theorem thetaPacketRoot_im_ne_zero (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    (thetaPacketRoot m t j).im ≠ 0 := by
  rw [thetaPacketRoot_im]
  refine mul_ne_zero (Real.rpow_pos_of_pos ht _).ne' fun hs => ?_
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
  have hm' : (4 * m : ℝ) ≠ 0 := by positivity
  have hz : ((2 * j + 1 : ℤ) : ℝ) = ((4 * m * n : ℤ) : ℝ) := by
    push_cast
    field_simp at hn
    linarith [Real.pi_pos]
  have hz' : (2 * j + 1 : ℤ) = 4 * m * n := by exact_mod_cast hz
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = m * n := ⟨_, rfl⟩
  have : (2 * j + 1 : ℤ) = 4 * k := by rw [hk]; linarith
  omega

/-- No packet root is purely imaginary: an odd multiple of `π/(4m)` is not an odd multiple of
`π/2`. -/
theorem thetaPacketRoot_re_ne_zero (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    (thetaPacketRoot m t j).re ≠ 0 := by
  rw [thetaPacketRoot_re]
  refine mul_ne_zero (Real.rpow_pos_of_pos ht _).ne' fun hc => ?_
  obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.1 hc
  have hm' : (4 * m : ℝ) ≠ 0 := by positivity
  have hz : ((2 * (2 * j + 1) : ℤ) : ℝ) = ((4 * m * (2 * n + 1) : ℤ) : ℝ) := by
    push_cast
    field_simp at hn
    linarith [Real.pi_pos]
  have hz' : (2 * (2 * j + 1) : ℤ) = 4 * m * (2 * n + 1) := by exact_mod_cast hz
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = m * (2 * n + 1) := ⟨_, rfl⟩
  have : (2 * (2 * j + 1) : ℤ) = 4 * k := by rw [hk]; linarith
  omega

/-- The packet is closed under complex conjugation. -/
theorem thetaPacketFactor_conj (m : ℕ) (t : ℝ) {z : ℂ} (hz : 1 + (t : ℂ) * z ^ (4 * m) = 0) :
    1 + (t : ℂ) * (starRingEnd ℂ z) ^ (4 * m) = 0 := by
  have h := congrArg (starRingEnd ℂ) hz
  simpa [map_add, map_mul, map_pow, Complex.conj_ofReal] using h

/-- The packet is closed under `z ↦ -z`. -/
theorem thetaPacketFactor_neg (m : ℕ) (t : ℝ) {z : ℂ} (hz : 1 + (t : ℂ) * z ^ (4 * m) = 0) :
    1 + (t : ℂ) * (-z) ^ (4 * m) = 0 := by
  rwa [Even.neg_pow ⟨2 * m, by ring⟩ z]

/-- The packet escapes to infinity as `t ↓ 0`. -/
theorem tendsto_norm_thetaPacketRoot (m : ℕ) (hm : 0 < m) (j : ℕ) :
    Tendsto (fun t : ℝ => ‖thetaPacketRoot m t j‖) (𝓝[>] 0) atTop := by
  have h := tendsto_rpow_neg_nhdsGT_zero (y := -(1 / (4 * m : ℝ))) (by
    have : (0 : ℝ) < 4 * m := by positivity
    have := one_div_pos.2 this
    linarith)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (norm_thetaPacketRoot m (le_of_lt ht) j).symm

/-- A simple zero of the factor: `1 + t z^{4m} = (z - α)(t Σ z^i α^{4m-1-i})`. -/
theorem analyticOrderAt_thetaPacketFactor_root (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t)
    (j : ℕ) :
    analyticOrderAt (fun w : ℂ => 1 + (t : ℂ) * w ^ (4 * m)) (thetaPacketRoot m t j) = 1 := by
  set α := thetaPacketRoot m t j
  have hαpow : (t : ℂ) * α ^ (4 * m) = -1 := by
    have := thetaPacketFactor_root m hm ht j
    linear_combination this
  have hα : α ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega), mul_zero] at hαpow
    norm_num at hαpow
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  show analyticOrderAt _ _ = ((1 : ℕ) : ℕ∞)
  rw [(analyticAt_thetaPacketFactor m t α).analyticOrderAt_eq_natCast]
  refine ⟨fun w => (t : ℂ) * ∑ i ∈ Finset.range (4 * m), w ^ i * α ^ (4 * m - 1 - i),
    by fun_prop, ?_, Eventually.of_forall fun w => ?_⟩
  · have hsum : ∑ i ∈ Finset.range (4 * m), α ^ i * α ^ (4 * m - 1 - i) =
        (4 * m : ℕ) * α ^ (4 * m - 1) := by
      rw [Finset.sum_congr rfl (fun i hi => (show α ^ i * α ^ (4 * m - 1 - i) = α ^ (4 * m - 1) by
        rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega)), Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    simp only
    rw [hsum]
    exact mul_ne_zero htC (mul_ne_zero (by exact_mod_cast (by omega : 4 * m ≠ 0)) (pow_ne_zero _ hα))
  · have hg := geom_sum₂_mul w α (4 * m)
    simp only [pow_one, smul_eq_mul]
    linear_combination -(t : ℂ) * hg + hαpow

/-- **Each packet root is an additional simple zero of `F_t`.** -/
theorem analyticOrderAt_thetaDerivativePacketC_root (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t)
    (j : ℕ) :
    analyticOrderAt (sourceTransform (thetaDerivativePacketC m t)) (thetaPacketRoot m t j) =
      analyticOrderAt XiC (thetaPacketRoot m t j) + 1 := by
  rw [sourceTransform_thetaDerivativePacketC_eq_mul,
    analyticOrderAt_mul (XiC_differentiable.analyticAt _) (analyticAt_thetaPacketFactor m t _),
    analyticOrderAt_thetaPacketFactor_root m hm ht]

theorem sourceTransform_thetaDerivativePacketC_root (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t)
    (j : ℕ) : sourceTransform (thetaDerivativePacketC m t) (thetaPacketRoot m t j) = 0 := by
  rw [sourceTransform_thetaDerivativePacketC, thetaPacketFactor_root m hm ht, mul_zero]

/-! ## Zero counts -/

theorem analyticOrderAt_thetaPacketFactor_ne_top (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t)
    (z : ℂ) : analyticOrderAt (fun w : ℂ => 1 + (t : ℂ) * w ^ (4 * m)) z ≠ ⊤ := by
  by_cases hz : 1 + (t : ℂ) * z ^ (4 * m) = 0
  · obtain ⟨j, -, rfl⟩ := (thetaPacketFactor_eq_zero_iff m hm ht z).1 hz
    rw [analyticOrderAt_thetaPacketFactor_root m hm ht]
    exact ENat.one_ne_top
  · rw [(analyticOrderAt_eq_zero (f := fun w : ℂ => 1 + (t : ℂ) * w ^ (4 * m))).2 (Or.inr hz)]
    exact ENat.zero_ne_top

/-- The divisor of the factor `1 + t z^{4m}` on a closed disc counts the packet roots it contains. -/
theorem finsum_divisor_thetaPacketFactor (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) (R : ℝ) :
    ∑ᶠ z, MeromorphicOn.divisor (fun w : ℂ => 1 + (t : ℂ) * w ^ (4 * m)) (closedBall 0 R) z =
      if t ^ (-(1 / (4 * m : ℝ))) ≤ R then ((4 * m : ℕ) : ℤ) else 0 := by
  classical
  set p : ℂ → ℂ := fun w => 1 + (t : ℂ) * w ^ (4 * m)
  have hpA : AnalyticOnNhd ℂ p univ := fun w _ => analyticAt_thetaPacketFactor m t w
  have hval : ∀ z, MeromorphicOn.divisor p (closedBall 0 R) z =
      if z ∈ closedBall (0 : ℂ) R ∧ p z = 0 then 1 else 0 := by
    intro z
    by_cases hU : z ∈ closedBall (0 : ℂ) R
    · rw [MeromorphicOn.divisor_apply (hpA.mono (subset_univ _)).meromorphicOn hU,
        (hpA z (mem_univ z)).meromorphicOrderAt_eq]
      by_cases hz : p z = 0
      · obtain ⟨j, -, rfl⟩ := (thetaPacketFactor_eq_zero_iff m hm ht z).1 hz
        rw [analyticOrderAt_thetaPacketFactor_root m hm ht, if_pos ⟨hU, hz⟩]
        rfl
      · rw [(analyticOrderAt_eq_zero (f := p)).2 (Or.inr hz), if_neg (fun h => hz h.2)]
        rfl
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hU, if_neg (fun h => hU h.1)]
  have hsupp : Function.support (MeromorphicOn.divisor p (closedBall 0 R)) ⊆
      ↑((Finset.range (4 * m)).image (thetaPacketRoot m t)) := by
    intro z hz
    rw [Function.mem_support, hval] at hz
    split_ifs at hz with h
    · obtain ⟨j, hj, rfl⟩ := (thetaPacketFactor_eq_zero_iff m hm ht z).1 h.2
      simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio]
      exact ⟨j, hj, rfl⟩
    · exact absurd rfl hz
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun i hi j hj h =>
    thetaPacketRoot_injOn m hm ht (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h)]
  have hterm : ∀ j ∈ Finset.range (4 * m), MeromorphicOn.divisor p (closedBall 0 R)
      (thetaPacketRoot m t j) = if t ^ (-(1 / (4 * m : ℝ))) ≤ R then 1 else 0 := by
    intro j _
    rw [hval]
    have hroot : p (thetaPacketRoot m t j) = 0 := thetaPacketFactor_root m hm ht j
    simp only [mem_closedBall, dist_zero_right, norm_thetaPacketRoot m ht.le, hroot, and_true]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  split_ifs <;> simp

/-- **The zero counts differ exactly by the packet.** On every closed disc about the origin,
`F_t` has the zeros of `XiC` (with multiplicity) plus all `4m` packet roots once the radius
reaches `t^{-1/(4m)}`, and no others. -/
theorem finsum_divisor_thetaDerivativePacketC (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) (R : ℝ) :
    ∑ᶠ z, MeromorphicOn.divisor (sourceTransform (thetaDerivativePacketC m t)) (closedBall 0 R) z =
      (∑ᶠ z, MeromorphicOn.divisor XiC (closedBall 0 R) z) +
        if t ^ (-(1 / (4 * m : ℝ))) ≤ R then ((4 * m : ℕ) : ℤ) else 0 := by
  set p : ℂ → ℂ := fun w => 1 + (t : ℂ) * w ^ (4 * m)
  have hXA : AnalyticOnNhd ℂ XiC univ := fun w _ => XiC_differentiable.analyticAt w
  have hpA : AnalyticOnNhd ℂ p univ := fun w _ => analyticAt_thetaPacketFactor m t w
  have hdiv : MeromorphicOn.divisor (sourceTransform (thetaDerivativePacketC m t)) (closedBall 0 R) =
      MeromorphicOn.divisor XiC (closedBall 0 R) + MeromorphicOn.divisor p (closedBall 0 R) := by
    rw [sourceTransform_thetaDerivativePacketC_eq_mul]
    refine MeromorphicOn.divisor_mul (hXA.mono (subset_univ _)).meromorphicOn
      (hpA.mono (subset_univ _)).meromorphicOn (fun z _ => ?_) (fun z _ => ?_)
    · rw [(hXA z (mem_univ z)).meromorphicOrderAt_eq]
      simpa using XiC_order_ne_top z
    · rw [(hpA z (mem_univ z)).meromorphicOrderAt_eq]
      simpa using analyticOrderAt_thetaPacketFactor_ne_top m hm ht z
  rw [hdiv]
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [finsum_add_distrib
    ((MeromorphicOn.divisor XiC _).finiteSupport (isCompact_closedBall 0 R))
    ((MeromorphicOn.divisor p _).finiteSupport (isCompact_closedBall 0 R)),
    finsum_divisor_thetaPacketFactor m hm ht R]

theorem finsum_divisor_thetaDerivativePacketC_sub_le (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t)
    (R : ℝ) :
    0 ≤ (∑ᶠ z, MeromorphicOn.divisor (sourceTransform (thetaDerivativePacketC m t))
          (closedBall 0 R) z) - ∑ᶠ z, MeromorphicOn.divisor XiC (closedBall 0 R) z ∧
      (∑ᶠ z, MeromorphicOn.divisor (sourceTransform (thetaDerivativePacketC m t))
          (closedBall 0 R) z) - ∑ᶠ z, MeromorphicOn.divisor XiC (closedBall 0 R) z ≤ 4 * m := by
  rw [finsum_divisor_thetaDerivativePacketC m hm ht R, add_sub_cancel_left]
  split_ifs <;> constructor <;> push_cast <;> omega

/-! ## Exact information loss -/

/-- The reciprocal power sums of the packet vanish below order `4m`. -/
theorem sum_inv_thetaPacketRoot_pow (m : ℕ) (hm : 0 < m) (t : ℝ) {l : ℕ}
    (hl0 : 0 < l) (hl : l < 4 * m) :
    ∑ j ∈ Finset.range (4 * m), (thetaPacketRoot m t j)⁻¹ ^ l = 0 := by
  set ω := Complex.exp (2 * Real.pi * I / (4 * m : ℕ))
  have hω := isPrimitiveRoot_thetaPacket m hm
  have hη1 : (ω ^ l)⁻¹ ≠ 1 := by
    rw [Ne, inv_eq_one]
    exact hω.pow_ne_one_of_pos_of_lt hl0.ne' hl
  have hηr : ((ω ^ l)⁻¹) ^ (4 * m) = 1 := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, inv_one]
  have hterm : ∀ j ∈ Finset.range (4 * m), (thetaPacketRoot m t j)⁻¹ ^ l =
      (thetaPacketRoot m t 0)⁻¹ ^ l * ((ω ^ l)⁻¹) ^ j := by
    intro j _
    rw [thetaPacketRoot_eq_mul_pow, mul_inv, mul_pow]
    congr 1
    rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm j l]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, geom_sum_eq hη1, hηr, sub_self, zero_div,
    mul_zero]

/-- The first nonvanishing reciprocal power sum: `Σ α_j^{-4m} = -4m t`. -/
theorem sum_inv_thetaPacketRoot_pow_self (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    ∑ j ∈ Finset.range (4 * m), (thetaPacketRoot m t j)⁻¹ ^ (4 * m) = -(4 * m : ℕ) * (t : ℂ) := by
  have hterm : ∀ j ∈ Finset.range (4 * m), (thetaPacketRoot m t j)⁻¹ ^ (4 * m) = -(t : ℂ) := by
    intro j _
    rw [inv_pow, thetaPacketRoot_pow m hm ht, inv_neg, inv_inv]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- **Detection scale.** On `|z| ≤ R` the relative transform factor moves by at most `t R^{4m}`,
while every packet root has modulus `t^{-1/(4m)}`. -/
theorem norm_sourceTransform_thetaDerivativePacketC_div_sub_one_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t)
    {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) (hXi : XiC z ≠ 0) :
    ‖sourceTransform (thetaDerivativePacketC m t) z / XiC z - 1‖ ≤ t * R ^ (4 * m) := by
  rw [sourceTransform_thetaDerivativePacketC, mul_div_cancel_left₀ _ hXi, add_sub_cancel_left,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _) ht

/-- **Zero logarithmic jet.** `log(F_t/F) = log(1 + t z^{4m})` vanishes to order exactly `4m` at
the origin, so its Taylor jet through degree `4m - 1` is zero. -/
theorem analyticOrderAt_log_thetaPacketFactor (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : t ≠ 0) :
    analyticOrderAt (fun z : ℂ => Complex.log (1 + (t : ℂ) * z ^ (4 * m))) 0 = (4 * m : ℕ) := by
  set f : ℂ → ℂ := fun w => Complex.log (1 + w)
  set u : ℂ → ℂ := fun z => (t : ℂ) * z ^ (4 * m)
  have hu0 : u 0 = 0 := by simp [u, zero_pow (by omega : 4 * m ≠ 0)]
  have huA : AnalyticAt ℂ u 0 := by fun_prop
  have hslit : (1 + (0 : ℂ)) ∈ slitPlane := by simp
  have hfA : AnalyticAt ℂ f 0 := (analyticAt_clog hslit).comp (by fun_prop)
  obtain ⟨P, hP⟩ := hfA
  have hΛ : AnalyticAt ℂ (dslope f 0) 0 := hP.has_fpower_series_dslope_fslope.analyticAt
  have hf0 : f 0 = 0 := by simp [f]
  have hfd : HasDerivAt f 1 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).const_add 1).clog hslit
    simpa [f] using h
  have hΛ0 : dslope f 0 0 = 1 := by rw [dslope_same, hfd.deriv]
  have hfac : ∀ w, f w = w * dslope f 0 w := by
    intro w
    have h := sub_smul_dslope f 0 w
    rw [hf0, sub_zero, sub_zero, smul_eq_mul] at h
    exact h.symm
  have hlogA : AnalyticAt ℂ (f ∘ u) 0 := by
    have : AnalyticAt ℂ f (u 0) := by rw [hu0]; exact ⟨P, hP⟩
    exact this.comp huA
  have hgA : AnalyticAt ℂ (dslope f 0 ∘ u) 0 := by
    have : AnalyticAt ℂ (dslope f 0) (u 0) := by rw [hu0]; exact hΛ
    exact this.comp huA
  change analyticOrderAt (f ∘ u) 0 = _
  rw [hlogA.analyticOrderAt_eq_natCast]
  refine ⟨fun z => (t : ℂ) * (dslope f 0 ∘ u) z, analyticAt_const.mul hgA, ?_,
    Eventually.of_forall fun z => ?_⟩
  · simp only [Function.comp, hu0, hΛ0, mul_one]
    exact_mod_cast ht
  · simp only [Function.comp, sub_zero, smul_eq_mul]
    rw [hfac (u z)]
    simp only [u]
    ring

/-- In the squared spectral coordinate `w = z²` the factor is `1 + t w^{2m}`. -/
theorem thetaPacketFactor_sq_coordinate (m : ℕ) (t : ℝ) (z : ℂ) :
    1 + (t : ℂ) * z ^ (4 * m) = 1 + (t : ℂ) * (z ^ 2) ^ (2 * m) := by
  rw [← pow_mul]
  ring_nf

end

end RHTower
