import GaloisForLFunctions.RHTower.ZetaFrobeniusSurplusSplit

/-!
# The prime–pole cross term of the Frobenius norm is negligible at every bandwidth

The pole density has the closed form (`PiX_eq_closed`)

`Π_X(τ) = (√X/π) · (τ sin(τ log X) + ½ cos(τ log X)) / (¼ + τ²)`,

an oscillation of frequency `log X` with decreasing amplitude.  Integrating by parts against a
decreasing weight (`abs_integral_mul_sin_antitone_le`) gives, on every subinterval of `I = [T, 2T]`,
`|∫ cos(τy + φ) Π_X(τ) dτ| ≤ (3√X/2πT)(1/(log X + y) + 1/|log X − y|)` (`abs_integral_cos_mul_PiX_le`),
and through the shear form of `𝓜` the same bound times `∫Φ²` for `𝓜[cos(·y + φ), Π_X]`
(`abs_Mform_cos_PiX_le`).  Splitting the prime polynomial `P_X` at the resonance `log n ≈ log X`
(`abs_Mform_PX_PiX_le`):

`|𝓜[P_X, Π_X]| ≤ (3/π²) (∫Φ²) X/(Tδ) + 12 (log X)² (Xδ + 1)`     for `0 < δ ≤ 1`,

which at `X = T^{4/3}`, `δ = T^{−1/2}` is `O(T^{5/6} log² T)`, negligible against `T log³ T`.
-/

open MeasureTheory Real Set intervalIntegral Zeta23 Zeta23.PrimeSide
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace RHTower

/-- **Closed form of the pole density.** -/
theorem PiX_eq_closed {X : ℝ} (hX : 0 < X) (τ : ℝ) :
    Zeta23.PiX X τ = Real.sqrt X / π
      * ((τ * Real.sin (τ * Real.log X) + Real.cos (τ * Real.log X) / 2) / (1 / 4 + τ ^ 2)) := by
  have hv : (0:ℝ) < 1 / 4 + τ ^ 2 := by positivity
  have hcp : (X : ℂ) ^ (1 / 2 + Complex.I * τ)
      = (Real.sqrt X : ℂ) * (Real.cos (τ * Real.log X) + Real.sin (τ * Real.log X) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hX.ne'), ← Complex.ofReal_log hX.le]
    have e : (Real.log X : ℂ) * (1 / 2 + Complex.I * τ)
        = ((Real.log X / 2 : ℝ) : ℂ) + ((τ * Real.log X : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX]; congr 1; ring_nf
  have hns : Complex.normSq (1 / 2 + Complex.I * τ) = 1 / 4 + τ ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im]
    ring
  have hre : (((X : ℂ) ^ (1 / 2 + Complex.I * τ) - 1) / (1 / 2 + Complex.I * τ)).re
      = ((Real.sqrt X * Real.cos (τ * Real.log X) - 1) * (1 / 2)
          + Real.sqrt X * Real.sin (τ * Real.log X) * τ) / (1 / 4 + τ ^ 2) := by
    rw [Complex.div_re, hns, hcp]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
    field_simp
    ring
  unfold Zeta23.PiX
  simp only []
  rw [hre]
  field_simp
  ring

/-- **Integration by parts against a decreasing weight**: if `h` is `C¹` on `[a, b]` with `h' ≤ 0`
and `h(b) ≥ 0`, then `|∫_a^b h(t) sin(ωt + φ) dt| ≤ 2h(a)/|ω|`. -/
theorem abs_integral_mul_sin_antitone_le {h h' : ℝ → ℝ} {a b ω φ : ℝ} (hab : a ≤ b) (hω : ω ≠ 0)
    (hd : ∀ t ∈ uIcc a b, HasDerivAt h (h' t) t) (hc : ContinuousOn h' (uIcc a b))
    (hneg : ∀ t ∈ Icc a b, h' t ≤ 0) (hb : 0 ≤ h b) :
    |∫ t in a..b, h t * Real.sin (ω * t + φ)| ≤ 2 * h a / |ω| := by
  have hωpos : 0 < |ω| := abs_pos.mpr hω
  set F : ℝ → ℝ := fun t => -(Real.cos (ω * t + φ) / ω) with hF
  have hFd : ∀ t ∈ uIcc a b, HasDerivAt F (Real.sin (ω * t + φ)) t := by
    intro t _
    have h1 := ((((hasDerivAt_id t).const_mul ω).add_const φ).cos.div_const ω).neg
    refine h1.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
  have hh'int : IntervalIntegrable h' volume a b := hc.intervalIntegrable
  have hsint : IntervalIntegrable (fun t => Real.sin (ω * t + φ)) volume a b :=
    (by fun_prop : Continuous fun t => Real.sin (ω * t + φ)).intervalIntegrable _ _
  have hibp := integral_mul_deriv_eq_deriv_mul hd hFd hh'int hsint
  have hFb : ∀ t, |F t| ≤ 1 / |ω| := by
    intro t
    rw [hF, abs_neg, abs_div, div_le_div_iff_of_pos_right hωpos]
    exact abs_cos_le_one _
  have hFTC : ∫ t in a..b, h' t = h b - h a :=
    integral_eq_sub_of_hasDerivAt hd hh'int
  have hint_le : |∫ t in a..b, h' t * F t| ≤ (h a - h b) / |ω| := by
    have hFc : Continuous F := by rw [hF]; fun_prop
    have h1 := abs_integral_le_integral_abs (μ := volume) (f := fun t => h' t * F t) hab
    have h2 : ∫ t in a..b, |h' t * F t| ≤ ∫ t in a..b, -h' t * (1 / |ω|) := by
      apply integral_mono_on hab
      · exact ((hc.mul hFc.continuousOn).abs).intervalIntegrable
      · exact (hh'int.neg).mul_const _
      · intro t ht
        rw [abs_mul, abs_of_nonpos (hneg t ht)]
        exact mul_le_mul_of_nonneg_left (hFb t) (by linarith [hneg t ht])
    have h3 : ∫ t in a..b, -h' t * (1 / |ω|) = (h a - h b) / |ω| := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, hFTC]; field_simp; ring
    exact h1.trans (h2.trans h3.le)
  have hha : h b ≤ h a := by
    have : 0 ≤ ∫ t in a..b, -h' t :=
      intervalIntegral.integral_nonneg hab fun t ht => by linarith [hneg t ht]
    rw [intervalIntegral.integral_neg, hFTC] at this
    linarith
  rw [hibp]
  have hb1 : |h b * F b| ≤ h b / |ω| := by
    rw [abs_mul, abs_of_nonneg hb]
    calc h b * |F b| ≤ h b * (1 / |ω|) := mul_le_mul_of_nonneg_left (hFb b) hb
      _ = h b / |ω| := by ring
  have hb2 : |h a * F a| ≤ h a / |ω| := by
    rw [abs_mul, abs_of_nonneg (hb.trans hha)]
    calc h a * |F a| ≤ h a * (1 / |ω|) := mul_le_mul_of_nonneg_left (hFb a) (hb.trans hha)
      _ = h a / |ω| := by ring
  have e : 2 * h a / |ω| = h b / |ω| + h a / |ω| + (h a - h b) / |ω| := by ring
  rw [e]
  have t1 := abs_sub (h b * F b - h a * F a) (∫ t in a..b, h' t * F t)
  have t2 := abs_sub (h b * F b) (h a * F a)
  linarith

/-- The amplitude `t/(¼ + t²)` is decreasing for `t ≥ ½`. -/
theorem hasDerivAt_amp₁ (t : ℝ) :
    HasDerivAt (fun t : ℝ => t / (1 / 4 + t ^ 2)) ((1 / 4 - t ^ 2) / (1 / 4 + t ^ 2) ^ 2) t := by
  have hv : (1 / 4 + t ^ 2) ≠ 0 := by positivity
  have h := (hasDerivAt_id t).div ((hasDerivAt_pow 2 t).const_add (1 / 4)) hv
  refine h.congr_deriv ?_
  simp only [id, Nat.cast_ofNat]
  field_simp
  ring

/-- The amplitude `(¼ + t²)⁻¹/2` is decreasing for `t ≥ 0`. -/
theorem hasDerivAt_amp₂ (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹ / 2) (-t / (1 / 4 + t ^ 2) ^ 2) t := by
  have hv : (1 / 4 + t ^ 2) ≠ 0 := by positivity
  have h := (((hasDerivAt_pow 2 t).const_add (1 / 4)).inv hv).div_const 2
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  field_simp
  ring

/-- The pointwise product-to-sum identity for the pole oscillation. -/
theorem cos_mul_PiX_eq {X : ℝ} (hX : 0 < X) (t y φ : ℝ) :
    Real.cos (t * y + φ) * Zeta23.PiX X t
      = Real.sqrt X / (2 * π) * (t / (1 / 4 + t ^ 2) * Real.sin ((Real.log X + y) * t + φ)
        + t / (1 / 4 + t ^ 2) * Real.sin ((Real.log X - y) * t + -φ)
        + (1 / 4 + t ^ 2)⁻¹ / 2 * Real.sin ((Real.log X + y) * t + (φ + π / 2))
        + (1 / 4 + t ^ 2)⁻¹ / 2 * Real.sin ((Real.log X - y) * t + (-φ + π / 2))) := by
  rw [PiX_eq_closed hX]
  set L := Real.log X
  have e1 : (L + y) * t + φ = t * L + (t * y + φ) := by ring
  have e2 : (L - y) * t + -φ = t * L - (t * y + φ) := by ring
  have e3 : (L + y) * t + (φ + π / 2) = t * L + (t * y + φ) + π / 2 := by ring
  have e4 : (L - y) * t + (-φ + π / 2) = t * L - (t * y + φ) + π / 2 := by ring
  rw [e1, e2, e3, e4, Real.sin_add_pi_div_two, Real.sin_add_pi_div_two, Real.sin_add, Real.sin_sub,
    Real.cos_add (t * L), Real.cos_sub (t * L)]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The pole oscillation against a trigonometric factor**, on any interval `[α, β]` with
`1 ≤ T ≤ α ≤ β`, for `0 ≤ y ≠ log X`. -/
theorem abs_integral_cos_mul_PiX_le {X T α β y φ : ℝ} (hX : 1 < X) (hT : 1 ≤ T) (hα : T ≤ α)
    (hαβ : α ≤ β) (hy : 0 ≤ y) (hyL : y ≠ Real.log X) :
    |∫ t in α..β, Real.cos (t * y + φ) * Zeta23.PiX X t|
      ≤ 3 * Real.sqrt X / (2 * π * T) * (1 / (Real.log X + y) + 1 / |Real.log X - y|) := by
  have hL0 : 0 < Real.log X := Real.log_pos hX
  have hX0 : 0 < X := by linarith
  have hα0 : 0 < α := by linarith
  have hT0 : 0 < T := by linarith
  have hω₁0 : 0 < Real.log X + y := by linarith
  have hω₂0 : Real.log X - y ≠ 0 := by intro h; exact hyL (by linarith)
  -- weights
  have hd₁ : ∀ t ∈ uIcc α β, HasDerivAt (fun t : ℝ => t / (1 / 4 + t ^ 2))
      ((1 / 4 - t ^ 2) / (1 / 4 + t ^ 2) ^ 2) t := fun t _ => hasDerivAt_amp₁ t
  have hd₂ : ∀ t ∈ uIcc α β, HasDerivAt (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹ / 2)
      (-t / (1 / 4 + t ^ 2) ^ 2) t := fun t _ => hasDerivAt_amp₂ t
  have hcd₁ : ContinuousOn (fun t : ℝ => (1 / 4 - t ^ 2) / (1 / 4 + t ^ 2) ^ 2) (uIcc α β) :=
    (Continuous.div (by fun_prop) (by fun_prop) fun t => by positivity).continuousOn
  have hcd₂ : ContinuousOn (fun t : ℝ => -t / (1 / 4 + t ^ 2) ^ 2) (uIcc α β) :=
    (Continuous.div (by fun_prop) (by fun_prop) fun t => by positivity).continuousOn
  have hneg₁ : ∀ t ∈ Icc α β, (1 / 4 - t ^ 2) / (1 / 4 + t ^ 2) ^ 2 ≤ 0 := by
    intro t ht
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have : 1 ≤ t := by linarith [ht.1]
    nlinarith
  have hneg₂ : ∀ t ∈ Icc α β, -t / (1 / 4 + t ^ 2) ^ 2 ≤ 0 := by
    intro t ht
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    linarith [ht.1]
  have hb₁ : 0 ≤ β / (1 / 4 + β ^ 2) := div_nonneg (by linarith) (by positivity)
  have hb₂ : 0 ≤ (1 / 4 + β ^ 2)⁻¹ / 2 := by positivity
  have ha₁ : α / (1 / 4 + α ^ 2) ≤ 1 / T := by
    rw [div_le_div_iff₀ (by positivity) hT0]
    have : α * T ≤ α * α := mul_le_mul_of_nonneg_left hα hα0.le
    nlinarith
  have ha₂ : (1 / 4 + α ^ 2)⁻¹ / 2 ≤ 1 / (2 * T) := by
    have h1 : (1 / 4 + α ^ 2)⁻¹ ≤ 1 / T := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hT0]
      have : T ≤ α * α := by nlinarith
      nlinarith
    have : (1 / 4 + α ^ 2)⁻¹ / 2 ≤ 1 / T / 2 := div_le_div_of_nonneg_right h1 (by norm_num)
    have e : 1 / T / 2 = 1 / (2 * T) := by field_simp
    linarith
  have I1 := abs_integral_mul_sin_antitone_le (φ := φ) hαβ hω₁0.ne' hd₁ hcd₁ hneg₁ hb₁
  have I2 := abs_integral_mul_sin_antitone_le (φ := -φ) hαβ hω₂0 hd₁ hcd₁ hneg₁ hb₁
  have I3 := abs_integral_mul_sin_antitone_le (φ := φ + π / 2) hαβ hω₁0.ne' hd₂ hcd₂ hneg₂ hb₂
  have I4 := abs_integral_mul_sin_antitone_le (φ := -φ + π / 2) hαβ hω₂0 hd₂ hcd₂ hneg₂ hb₂
  rw [abs_of_pos hω₁0] at I1 I3
  -- integrability and the split
  have hc₁ : Continuous (fun t : ℝ => t / (1 / 4 + t ^ 2)) :=
    continuous_id.div (by fun_prop) fun t => by positivity
  have hc₂ : Continuous (fun t : ℝ => (1 / 4 + t ^ 2)⁻¹ / 2) :=
    ((by fun_prop : Continuous fun t : ℝ => 1 / 4 + t ^ 2).inv₀ fun t => by positivity).div_const 2
  have hi : ∀ (h : ℝ → ℝ) (ω ψ : ℝ), Continuous h →
      IntervalIntegrable (fun t => h t * Real.sin (ω * t + ψ)) volume α β :=
    fun h ω ψ hc => (hc.mul (by fun_prop)).intervalIntegrable _ _
  set A₁ := ∫ t in α..β, t / (1 / 4 + t ^ 2) * Real.sin ((Real.log X + y) * t + φ) with hA₁
  set A₂ := ∫ t in α..β, t / (1 / 4 + t ^ 2) * Real.sin ((Real.log X - y) * t + -φ) with hA₂
  set A₃ := ∫ t in α..β, (1 / 4 + t ^ 2)⁻¹ / 2 * Real.sin ((Real.log X + y) * t + (φ + π / 2))
    with hA₃
  set A₄ := ∫ t in α..β, (1 / 4 + t ^ 2)⁻¹ / 2 * Real.sin ((Real.log X - y) * t + (-φ + π / 2))
    with hA₄
  have hsplit : ∫ t in α..β, Real.cos (t * y + φ) * Zeta23.PiX X t
      = Real.sqrt X / (2 * π) * (A₁ + A₂ + A₃ + A₄) := by
    simp_rw [cos_mul_PiX_eq hX0]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (((hi _ _ _ hc₁).add (hi _ _ _ hc₁)).add (hi _ _ _ hc₂)) (hi _ _ _ hc₂),
      intervalIntegral.integral_add ((hi _ _ _ hc₁).add (hi _ _ _ hc₁)) (hi _ _ _ hc₂),
      intervalIntegral.integral_add (hi _ _ _ hc₁) (hi _ _ _ hc₁)]
  have hw1 : 2 * (α / (1 / 4 + α ^ 2)) / (Real.log X + y) ≤ 2 / T / (Real.log X + y) := by
    apply div_le_div_of_nonneg_right _ hω₁0.le
    have e : 2 / T = 2 * (1 / T) := by ring
    linarith [ha₁]
  have hw2 : 2 * (α / (1 / 4 + α ^ 2)) / |Real.log X - y| ≤ 2 / T / |Real.log X - y| := by
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    have e : 2 / T = 2 * (1 / T) := by ring
    linarith [ha₁]
  have hw3 : 2 * ((1 / 4 + α ^ 2)⁻¹ / 2) / (Real.log X + y) ≤ 1 / T / (Real.log X + y) := by
    apply div_le_div_of_nonneg_right _ hω₁0.le
    have e : 2 * (1 / (2 * T)) = 1 / T := by field_simp
    linarith [ha₂]
  have hw4 : 2 * ((1 / 4 + α ^ 2)⁻¹ / 2) / |Real.log X - y| ≤ 1 / T / |Real.log X - y| := by
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    have e : 2 * (1 / (2 * T)) = 1 / T := by field_simp
    linarith [ha₂]
  have htot : |A₁ + A₂ + A₃ + A₄| ≤ 3 / T * (1 / (Real.log X + y) + 1 / |Real.log X - y|) := by
    have s1 := abs_add_le (A₁ + A₂ + A₃) A₄
    have s2 := abs_add_le (A₁ + A₂) A₃
    have s3 := abs_add_le A₁ A₂
    have e : 3 / T * (1 / (Real.log X + y) + 1 / |Real.log X - y|)
        = 2 / T / (Real.log X + y) + 2 / T / |Real.log X - y| + 1 / T / (Real.log X + y)
          + 1 / T / |Real.log X - y| := by ring
    linarith [I1, I2, I3, I4, hw1, hw2, hw3, hw4]
  rw [hsplit, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt X / (2 * π))]
  calc Real.sqrt X / (2 * π) * |A₁ + A₂ + A₃ + A₄|
      ≤ Real.sqrt X / (2 * π) * (3 / T * (1 / (Real.log X + y) + 1 / |Real.log X - y|)) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ = 3 * Real.sqrt X / (2 * π * T) * (1 / (Real.log X + y) + 1 / |Real.log X - y|) := by
        field_simp

/-- **The pole oscillation in the bilinear form**, through the shear form of `𝓜`. -/
theorem abs_Mform_cos_PiX_le {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    {X T y φ : ℝ} (hX : 1 < X) (hT : 1 ≤ T) (hy : 0 ≤ y) (hyL : y ≠ Real.log X) :
    |Mform Φ T (fun τ => Real.cos (τ * y + φ)) (Zeta23.PiX X)|
      ≤ (∫ x, Φ x ^ 2)
        * (3 * Real.sqrt X / (2 * π * T) * (1 / (Real.log X + y) + 1 / |Real.log X - y|)) := by
  set B := 3 * Real.sqrt X / (2 * π * T) * (1 / (Real.log X + y) + 1 / |Real.log X - y|) with hB
  have hX0 : 0 < X := by linarith
  have hB0 : 0 ≤ B := by
    have : 0 < Real.log X + y := by linarith [Real.log_pos hX]
    rw [hB]; positivity
  have hPi : Continuous (Zeta23.PiX X) := PiX_continuous hX0
  set G : ℝ × ℝ → ℝ := fun q => Real.cos (q.1 * y + φ) * Zeta23.PiX X q.2 with hG
  have hcos : Continuous fun q : ℝ × ℝ => Real.cos (q.1 * y + φ) := by fun_prop
  have hGc : Continuous G := by rw [hG]; exact hcos.mul (hPi.comp continuous_snd)
  have hM : Mform Φ T (fun τ => Real.cos (τ * y + φ)) (Zeta23.PiX X)
      = ∫ x, Φ x ^ 2 * ∫ τ' in Ix T x, G (x + τ', τ') := by
    unfold Mform
    rw [← sqIntegral_shear hΦ hGc]
    refine setIntegral_congr_fun ((measurableSet_Icc).prod measurableSet_Icc) fun q _ => ?_
    simp only [hG]; ring
  -- the inner integral
  have hinner : ∀ x, |∫ τ' in Ix T x, G (x + τ', τ')| ≤ B := by
    intro x
    unfold Ix
    set α := max (T - x) T
    set β := min (2 * T - x) (2 * T)
    rcases le_or_gt α β with hαβ | hαβ
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hαβ]
      have e : (fun τ' => G (x + τ', τ'))
          = fun τ' => Real.cos (τ' * y + (x * y + φ)) * Zeta23.PiX X τ' := by
        funext τ'; simp only [hG]; ring_nf
      rw [e]
      exact abs_integral_cos_mul_PiX_le hX hT (le_max_right _ _) hαβ hy hyL
    · rw [Set.Icc_eq_empty (not_le.mpr hαβ), Measure.restrict_empty, integral_zero_measure,
        abs_zero]
      exact hB0
  rw [hM]
  have hint : Integrable (fun x => Φ x ^ 2 * B) := hΦ2.mul_const B
  have h := MeasureTheory.norm_integral_le_of_norm_le
    (f := fun x => Φ x ^ 2 * ∫ τ' in Ix T x, G (x + τ', τ')) hint
    (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hinner x) (sq_nonneg _))
  rw [Real.norm_eq_abs, MeasureTheory.integral_mul_const] at h
  exact h

/-- `𝓜` is linear in the prime polynomial. -/
theorem Mform_PX_left_eq_sum {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {v : ℝ → ℝ} (hv : Continuous v)
    (T X : ℝ) :
    Mform Φ T (Zeta23.PX X) v
      = -(1 / π) * ∑ n ∈ primeRange X, acoef n * Mform Φ T (fun τ => Real.cos (τ * Real.log n)) v := by
  have hint : ∀ n : ℕ, IntegrableOn (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2
      * Real.cos (q.1 * Real.log n) * v q.2) ((Icc T (2 * T)) ×ˢ (Icc T (2 * T))) := fun n =>
    Mform_integrableOn hΦ (u := fun τ => Real.cos (τ * Real.log n)) (by fun_prop) hv
  have hpt : ∀ q : ℝ × ℝ, Φ (q.1 - q.2) ^ 2 * Zeta23.PX X q.1 * v q.2
      = -(1 / π) * ∑ n ∈ primeRange X, acoef n
          * (Φ (q.1 - q.2) ^ 2 * Real.cos (q.1 * Real.log n) * v q.2) := by
    intro q
    simp only [PX_eq, ycoef, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  unfold Mform
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, integral_finsetSum _ (fun n _ => (hint n).const_mul _)]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MeasureTheory.integral_const_mul]

/-- **The prime–pole cross term**, for every `0 < δ ≤ 1` (resonance width), `X ≥ 3`, `T ≥ 1`, given
Chebyshev's `Σ_{n ≤ X} Λ(n)/√n ≤ 3√X`. -/
theorem abs_Mform_PX_PiX_le {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    {X T δ : ℝ} (hX : 3 ≤ X) (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsum : ∑ n ∈ primeRange X, acoef n ≤ 3 * Real.sqrt X) :
    |Mform Φ T (Zeta23.PX X) (Zeta23.PiX X)|
      ≤ (∫ x, Φ x ^ 2) / π * (9 * X / (π * T * δ) + 6 * Real.log X * (X * δ + 1)) := by
  set L := Real.log X with hL
  set W := ∫ x, Φ x ^ 2 with hW
  have hW0 : 0 ≤ W := integral_nonneg fun x => sq_nonneg _
  have hX0 : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hT0 : 0 < T := by linarith
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hPi : Continuous (Zeta23.PiX X) := PiX_continuous hX0
  rw [Mform_PX_left_eq_sum hΦ hPi, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / π)]
  -- per-prime bounds
  set R := (primeRange X).filter (fun n : ℕ => L - Real.log n < δ) with hR
  have hres : ∀ n ∈ primeRange X, |Mform Φ T (fun τ => Real.cos (τ * Real.log n)) (Zeta23.PiX X)|
      ≤ 3 * Real.sqrt X * W := by
    intro n _
    have hcos : ∀ τ ∈ Icc T (2 * T), |Real.cos (τ * Real.log n)| ≤ 1 := fun τ _ => abs_cos_le_one _
    have hpi : ∀ τ ∈ Icc T (2 * T), |Zeta23.PiX X τ| ≤ 3 * Real.sqrt X / T := by
      intro τ hτ
      refine (PiX_abs_le hX1.le τ).trans ?_
      apply div_le_div_of_nonneg_left (by positivity) hT0
      rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.1]
    have h := abs_Mform_le hT0.le hΦ (by fun_prop) hPi hΦ2 hcos hpi
    calc |Mform Φ T (fun τ => Real.cos (τ * Real.log n)) (Zeta23.PiX X)|
        ≤ 1 * (3 * Real.sqrt X / T) * (T * W) := h
      _ = 3 * Real.sqrt X * W := by field_simp
  have hnonres : ∀ n ∈ primeRange X, δ ≤ L - Real.log n →
      |Mform Φ T (fun τ => Real.cos (τ * Real.log n)) (Zeta23.PiX X)|
        ≤ W * (3 * Real.sqrt X / (π * T * δ)) := by
    intro n hn hδn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hne : Real.log n ≠ L := by intro h; rw [h] at hδn; linarith
    have hφ : (fun τ => Real.cos (τ * Real.log n)) = fun τ => Real.cos (τ * Real.log n + 0) := by
      funext τ; rw [add_zero]
    rw [hφ]
    refine (abs_Mform_cos_PiX_le hΦ hΦ2 hX1 hT hlog0 hne).trans ?_
    apply mul_le_mul_of_nonneg_left _ hW0
    have h1 : 1 / (L + Real.log n) ≤ 1 / δ := by
      apply one_div_le_one_div_of_le hδ0; linarith
    have h2 : 1 / |L - Real.log n| ≤ 1 / δ := by
      rw [abs_of_pos (by linarith)]; exact one_div_le_one_div_of_le hδ0 hδn
    have h3 : 3 * Real.sqrt X / (2 * π * T) * (1 / (L + Real.log n) + 1 / |L - Real.log n|)
        ≤ 3 * Real.sqrt X / (2 * π * T) * (2 / δ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 2 / δ = 1 / δ + 1 / δ := by ring
      linarith
    have e : 3 * Real.sqrt X / (2 * π * T) * (2 / δ) = 3 * Real.sqrt X / (π * T * δ) := by
      field_simp
    linarith
  -- the resonant mass
  have hacoef : ∀ n ∈ R, acoef n ≤ 2 * L / Real.sqrt X := by
    intro n hn
    obtain ⟨hn, hnr⟩ := Finset.mem_filter.mp hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
      (Nat.floor_le hX0.le)
    have hlogn : Real.log n ≤ L := Real.log_le_log (by linarith) hnX
    -- `n ≥ X/e`
    have hnX' : X / 4 ≤ n := by
      have h1 : L - 1 < Real.log n := by linarith
      have h2 : Real.log (X / 4) ≤ L - 1 := by
        rw [Real.log_div hX0.ne' (by norm_num)]
        have : 1 ≤ Real.log 4 := by
          rw [← Real.log_exp 1]
          exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
        linarith
      have h3 : Real.log (X / 4) < Real.log n := by linarith
      exact ((Real.log_lt_log_iff (by positivity) (by linarith)).mp h3).le
    unfold acoef
    have hΛ : (Λ n : ℝ) ≤ L := (ArithmeticFunction.vonMangoldt_le_log).trans hlogn
    have hsn : Real.sqrt X / 2 ≤ Real.sqrt n := by
      have : Real.sqrt (X / 4) = Real.sqrt X / 2 := by
        rw [Real.sqrt_div' X (by norm_num : (0:ℝ) ≤ 4), show (4:ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [← this]; exact Real.sqrt_le_sqrt hnX'
    rw [div_le_div_iff₀ (by positivity) hsX]
    have hΛ0 : (0:ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith [hΛ, hsn, hΛ0]
  have hcard : (R.card : ℝ) ≤ X * δ + 1 := by
    have hsub : R ⊆ Finset.Ioc ⌊X * Real.exp (-δ)⌋₊ ⌊X⌋₊ := by
      intro n hn
      obtain ⟨hn, hnr⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_Ioc.mpr ⟨?_, (Finset.mem_Ioc.mp hn).2⟩
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
      have h1 : Real.log (X * Real.exp (-δ)) < Real.log n := by
        rw [Real.log_mul hX0.ne' (Real.exp_pos _).ne', Real.log_exp]; linarith
      have h2 : X * Real.exp (-δ) < n :=
        (Real.log_lt_log_iff (by positivity) (by linarith)).mp h1
      exact (Nat.floor_lt (by positivity)).mpr h2
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at hc
    have hc' : (R.card : ℝ) ≤ (⌊X⌋₊ : ℝ) - ⌊X * Real.exp (-δ)⌋₊ := by
      have he1 : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have he2 : X * Real.exp (-δ) ≤ X := by nlinarith
      have hle : ⌊X * Real.exp (-δ)⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor he2
      rw [← Nat.cast_sub hle]; exact_mod_cast hc
    have h1 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
    have h2 : X * Real.exp (-δ) - 1 ≤ ⌊X * Real.exp (-δ)⌋₊ := by
      have := Nat.lt_floor_add_one (X * Real.exp (-δ)); linarith
    have h3 : X * (1 - δ) ≤ X * Real.exp (-δ) := by
      apply mul_le_mul_of_nonneg_left _ hX0.le
      have := Real.add_one_le_exp (-δ); linarith
    nlinarith
  have hRmass : ∑ n ∈ R, acoef n ≤ (X * δ + 1) * (2 * L / Real.sqrt X) := by
    calc ∑ n ∈ R, acoef n ≤ ∑ _n ∈ R, 2 * L / Real.sqrt X := Finset.sum_le_sum hacoef
      _ = R.card * (2 * L / Real.sqrt X) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X * δ + 1) * (2 * L / Real.sqrt X) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  -- assemble
  have hsplit : |∑ n ∈ primeRange X, acoef n * Mform Φ T (fun τ => Real.cos (τ * Real.log n))
        (Zeta23.PiX X)|
      ≤ ∑ n ∈ primeRange X, acoef n * (W * (3 * Real.sqrt X / (π * T * δ)))
        + ∑ n ∈ R, acoef n * (3 * Real.sqrt X * W) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not (primeRange X) (fun n : ℕ => L - Real.log n < δ)]
    have hA : ∑ n ∈ (primeRange X).filter (fun n : ℕ => ¬ L - Real.log n < δ),
          |acoef n * Mform Φ T (fun τ => Real.cos (τ * Real.log n)) (Zeta23.PiX X)|
        ≤ ∑ n ∈ primeRange X, acoef n * (W * (3 * Real.sqrt X / (π * T * δ))) := by
      refine (Finset.sum_le_sum fun n hn => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) fun n _ _ => mul_nonneg (acoef_nonneg n) (by positivity))
      obtain ⟨hn, hnr⟩ := Finset.mem_filter.mp hn
      rw [abs_mul, abs_of_nonneg (acoef_nonneg n)]
      exact mul_le_mul_of_nonneg_left (hnonres n hn (not_lt.mp hnr)) (acoef_nonneg n)
    have hB : ∑ n ∈ R, |acoef n * Mform Φ T (fun τ => Real.cos (τ * Real.log n)) (Zeta23.PiX X)|
        ≤ ∑ n ∈ R, acoef n * (3 * Real.sqrt X * W) := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [abs_mul, abs_of_nonneg (acoef_nonneg n)]
      exact mul_le_mul_of_nonneg_left (hres n (Finset.mem_filter.mp hn).1) (acoef_nonneg n)
    rw [hR] at hB
    linarith
  have e1 : ∑ n ∈ primeRange X, acoef n * (W * (3 * Real.sqrt X / (π * T * δ)))
      = (∑ n ∈ primeRange X, acoef n) * (W * (3 * Real.sqrt X / (π * T * δ))) := by
    rw [Finset.sum_mul]
  have e2 : ∑ n ∈ R, acoef n * (3 * Real.sqrt X * W) = (∑ n ∈ R, acoef n) * (3 * Real.sqrt X * W) := by
    rw [Finset.sum_mul]
  have h1 : (∑ n ∈ primeRange X, acoef n) * (W * (3 * Real.sqrt X / (π * T * δ)))
      ≤ 3 * Real.sqrt X * (W * (3 * Real.sqrt X / (π * T * δ))) :=
    mul_le_mul_of_nonneg_right hsum (by positivity)
  have h2 : (∑ n ∈ R, acoef n) * (3 * Real.sqrt X * W)
      ≤ (X * δ + 1) * (2 * L / Real.sqrt X) * (3 * Real.sqrt X * W) :=
    mul_le_mul_of_nonneg_right hRmass (by positivity)
  have e3 : 3 * Real.sqrt X * (W * (3 * Real.sqrt X / (π * T * δ))) = W * (9 * X / (π * T * δ)) := by
    have : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
    field_simp; nlinarith [this]
  have e4 : (X * δ + 1) * (2 * L / Real.sqrt X) * (3 * Real.sqrt X * W) = W * (6 * L * (X * δ + 1)) := by
    field_simp; ring
  have hfin : |∑ n ∈ primeRange X, acoef n * Mform Φ T (fun τ => Real.cos (τ * Real.log n))
        (Zeta23.PiX X)| ≤ W * (9 * X / (π * T * δ) + 6 * L * (X * δ + 1)) := by
    linarith [hsplit, e1, e2, h1, h2, e3, e4]
  calc 1 / π * |∑ n ∈ primeRange X, acoef n * Mform Φ T (fun τ => Real.cos (τ * Real.log n))
        (Zeta23.PiX X)|
      ≤ 1 / π * (W * (9 * X / (π * T * δ) + 6 * L * (X * δ + 1))) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = W / π * (9 * X / (π * T * δ) + 6 * L * (X * δ + 1)) := by ring

end RHTower
