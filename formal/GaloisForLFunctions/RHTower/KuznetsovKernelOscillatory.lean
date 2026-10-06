import GaloisForLFunctions.RHTower.KuznetsovSameSignGaussKernel

/-!
# The two oscillatory forms of the large-sieve kernel

With `𝒢_K(w) = (√π K³/2) w e^{−K²w²}`, `G_K = 𝒢_K'` and `R_K = (G_K − 𝒢_K tanh)/cosh = (𝒢_K/cosh)'`,
one integration by parts gives DI (5.7):

`X ∫ 𝒢_K(w) tanh w sin(X cosh w) dw = ∫ R_K(w) cos(X cosh w) dw`   (`X > 0`)

(`mul_integral_gaussPrim_tanh_sin`).  The weights satisfy `∫|𝒢_K tanh| ≤ π/4`, `∫|R_K| ≤ (π + √π) K²`
for `K ≥ 1` (`integral_abs_gaussPrim_tanh_le`, `integral_abs_cosWeight_le`).
-/

open MeasureTheory Set Filter Complex

namespace GaloisForLFunctions.RHTower.DeckPointPair

open KuznetsovGauss

noncomputable section

/-! ## Gaussian moments -/

theorem integral_abs_mul_exp_neg_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, |x| * Real.exp (-b * x ^ 2) = 1 / b := by
  have h := integral_comp_abs (f := fun y : ℝ => y * Real.exp (-b * y ^ 2))
  simp only [sq_abs] at h
  rw [h]
  have h2 := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := b) (by norm_num) (by norm_num) hb
  have hc : ∫ x in Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ (1 : ℝ) * Real.exp (-b * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [Real.rpow_one]
    rw [show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
  rw [hc, h2]
  norm_num
  rw [Real.rpow_neg_one]
  ring

theorem integral_sq_mul_exp_neg_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) = Real.sqrt Real.pi / 2 * b ^ (-(3 / 2 : ℝ)) := by
  have h := integral_comp_abs (f := fun y : ℝ => y ^ 2 * Real.exp (-b * y ^ 2))
  simp only [sq_abs] at h
  rw [h]
  have h2 := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := b) (by norm_num) (by norm_num) hb
  have hc : ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-b * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ (2 : ℝ) * Real.exp (-b * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [show x ^ (2 : ℝ) = x ^ 2 by norm_cast]
  rw [hc, h2, show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  norm_num
  ring

theorem integral_sq_mul_exp_neg_K_sq {K : ℝ} (hK : 0 < K) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-K ^ 2 * x ^ 2) = Real.sqrt Real.pi / (2 * K ^ 3) := by
  rw [integral_sq_mul_exp_neg_sq (by positivity : (0 : ℝ) < K ^ 2)]
  have h : (K ^ 2 : ℝ) ^ (-(3 / 2 : ℝ)) = (K ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast K 2, ← Real.rpow_mul hK.le, show ((2 : ℕ) : ℝ) * -(3 / 2 : ℝ) = -3 by norm_num,
      Real.rpow_neg hK.le, show K ^ (3 : ℝ) = K ^ 3 by norm_cast]
  rw [h]; field_simp

theorem integral_exp_neg_K_sq {K : ℝ} (hK : 0 < K) :
    ∫ x : ℝ, Real.exp (-K ^ 2 * x ^ 2) = Real.sqrt Real.pi / K := by
  rw [integral_gaussian, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hK.le]

/-! ## Elementary hyperbolic bounds -/

theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh h
    Real.continuous_sinh.continuousOn fun y _ => Real.hasDerivAt_sinh y
  rw [Real.sinh_zero, sub_zero, sub_zero] at hd
  have hle : Real.cosh ξ ≤ Real.cosh x := Real.cosh_le_cosh.2 (by
    rw [abs_of_pos hξ.1, abs_of_pos h]; exact hξ.2.le)
  rw [eq_div_iff h.ne'] at hd
  nlinarith

theorem abs_tanh_le_abs (x : ℝ) : |Real.tanh x| ≤ |x| := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos x), div_le_iff₀ (Real.cosh_pos x),
    Real.abs_sinh, ← Real.cosh_abs]
  exact sinh_le_mul_cosh (abs_nonneg x)

theorem abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [Real.tanh_lt_one (-x), Real.tanh_neg x], (Real.tanh_lt_one x).le⟩

/-! ## The cosine form -/

theorem continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh fun w => (Real.cosh_pos w).ne'

/-- `R_K = (G_K − 𝒢_K tanh)/cosh`. -/
def cosWeight (K w : ℝ) : ℝ := (gaussDeriv K w - gaussPrim K w * Real.tanh w) / Real.cosh w

theorem hasDerivAt_gaussPrim_div_cosh (K w : ℝ) :
    HasDerivAt (fun w => gaussPrim K w / Real.cosh w) (cosWeight K w) w := by
  have h := (hasDerivAt_gaussPrim K w).div (Real.hasDerivAt_cosh w) (Real.cosh_pos w).ne'
  refine h.congr_deriv ?_
  rw [cosWeight, Real.tanh_eq_sinh_div_cosh]
  have := (Real.cosh_pos w).ne'
  field_simp

theorem abs_cosWeight_le (K w : ℝ) : |cosWeight K w| ≤ |gaussDeriv K w| + |gaussPrim K w| := by
  rw [cosWeight, abs_div, abs_of_pos (Real.cosh_pos w)]
  refine (div_le_self (abs_nonneg _) (Real.one_le_cosh w)).trans ?_
  refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_tanh_le_one w)

theorem integrable_cosWeight {K : ℝ} (hK : 0 < K) : Integrable (cosWeight K) := by
  refine ((integrable_gaussDeriv hK).abs.add (integrable_gaussPrim hK).abs).mono' ?_
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact abs_cosWeight_le K w)
  unfold cosWeight gaussDeriv gaussPrim
  have ht := continuous_tanh
  exact Continuous.aestronglyMeasurable (by
    refine Continuous.div (by fun_prop) Real.continuous_cosh fun w => (Real.cosh_pos w).ne')

/-- **DI (5.7)**: `X ∫ 𝒢_K tanh w sin(X cosh w) dw = ∫ R_K(w) cos(X cosh w) dw`. -/
theorem mul_integral_gaussPrim_tanh_sin {K X : ℝ} (hK : 0 < K) (hX : 0 < X) :
    X * ∫ w : ℝ, gaussPrim K w * Real.tanh w * Real.sin (X * Real.cosh w) =
      ∫ w : ℝ, cosWeight K w * Real.cos (X * Real.cosh w) := by
  have hv : ∀ w, HasDerivAt (fun w => Real.cos (X * Real.cosh w))
      (-Real.sin (X * Real.cosh w) * (X * Real.sinh w)) w := fun w =>
    ((Real.hasDerivAt_cosh w).const_mul X).cos
  have hP := integrable_gaussPrim hK
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun w => gaussPrim K w / Real.cosh w) (u' := cosWeight K)
    (v := fun w => Real.cos (X * Real.cosh w))
    (v' := fun w => -Real.sin (X * Real.cosh w) * (X * Real.sinh w))
    (fun w _ => hasDerivAt_gaussPrim_div_cosh K w) (fun w _ => hv w)
    ((hP.abs.const_mul X).mono' (by
        unfold gaussPrim
        exact Continuous.aestronglyMeasurable (by
          refine Continuous.mul (Continuous.div (by fun_prop) Real.continuous_cosh
            fun w => (Real.cosh_pos w).ne') (by fun_prop)))
      (Eventually.of_forall fun w => by
        simp only [Pi.mul_apply, Real.norm_eq_abs]
        rw [abs_mul, abs_div, abs_of_pos (Real.cosh_pos w), abs_mul, abs_neg, abs_mul,
          abs_of_pos hX]
        have h1 : |Real.sin (X * Real.cosh w)| ≤ 1 := Real.abs_sin_le_one _
        have h2 : |Real.sinh w| / Real.cosh w ≤ 1 := by
          rw [div_le_one (Real.cosh_pos w), Real.abs_sinh, ← Real.cosh_abs]
          exact (Real.sinh_lt_cosh _).le
        calc |gaussPrim K w| / Real.cosh w * (|Real.sin (X * Real.cosh w)| * (X * |Real.sinh w|))
            = X * |gaussPrim K w| * |Real.sin (X * Real.cosh w)| * (|Real.sinh w| / Real.cosh w) := by
              ring
          _ ≤ X * |gaussPrim K w| * 1 * 1 := by gcongr
          _ = X * |gaussPrim K w| := by ring))
    (((integrable_cosWeight hK)).norm.mono' ((integrable_cosWeight hK).aestronglyMeasurable.mul
      (by fun_prop : Continuous fun w => Real.cos (X * Real.cosh w)).aestronglyMeasurable)
      (Eventually.of_forall fun w => by
        simp only [Pi.mul_apply, Real.norm_eq_abs]
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)))
    (hP.abs.mono' (by
        unfold gaussPrim
        exact Continuous.aestronglyMeasurable (by
          refine Continuous.mul (Continuous.div (by fun_prop) Real.continuous_cosh
            fun w => (Real.cosh_pos w).ne') (by fun_prop)))
      (Eventually.of_forall fun w => by
        simp only [Pi.mul_apply, Real.norm_eq_abs]
        rw [abs_mul, abs_div, abs_of_pos (Real.cosh_pos w)]
        calc |gaussPrim K w| / Real.cosh w * |Real.cos (X * Real.cosh w)|
            ≤ |gaussPrim K w| / 1 * 1 := by
              gcongr
              · exact Real.one_le_cosh w
              · exact Real.abs_cos_le_one _
          _ = |gaussPrim K w| := by ring))
  have hl : ∫ w : ℝ, gaussPrim K w / Real.cosh w * (-Real.sin (X * Real.cosh w) * (X * Real.sinh w)) =
      -(X * ∫ w : ℝ, gaussPrim K w * Real.tanh w * Real.sin (X * Real.cosh w)) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1; funext w
    rw [Real.tanh_eq_sinh_div_cosh]
    ring
  rw [hl, neg_inj] at h
  exact h

/-! ## Size of the weights -/

theorem integrable_sq_mul_exp_neg_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2) :=
  integrable_pow_mul_exp_neg_sq hb 2

theorem abs_gaussPrim (K w : ℝ) (hK : 0 ≤ K) :
    |gaussPrim K w| = Real.sqrt Real.pi * K ^ 3 / 2 * (|w| * Real.exp (-K ^ 2 * w ^ 2)) := by
  rw [gaussPrim, abs_mul, abs_of_nonneg (by positivity), abs_mul, abs_of_pos (Real.exp_pos _)]
  congr 3; ring

/-- `∫|𝒢_K tanh| ≤ π/4`. -/
theorem integral_abs_gaussPrim_tanh_le {K : ℝ} (hK : 0 < K) :
    ∫ w : ℝ, |gaussPrim K w * Real.tanh w| ≤ Real.pi / 4 := by
  have hb : (0 : ℝ) < K ^ 2 := by positivity
  have hmaj : Integrable fun w : ℝ => Real.sqrt Real.pi * K ^ 3 / 2 * (w ^ 2 * Real.exp (-K ^ 2 * w ^ 2)) :=
    (integrable_sq_mul_exp_neg_sq hb).const_mul _
  calc ∫ w : ℝ, |gaussPrim K w * Real.tanh w|
      ≤ ∫ w : ℝ, Real.sqrt Real.pi * K ^ 3 / 2 * (w ^ 2 * Real.exp (-K ^ 2 * w ^ 2)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun w => abs_nonneg _) hmaj
          (Eventually.of_forall fun w => ?_)
        dsimp only
        rw [abs_mul, abs_gaussPrim K w hK.le]
        have h1 := abs_tanh_le_abs w
        have h2 : |w| * |w| = w ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
        calc Real.sqrt Real.pi * K ^ 3 / 2 * (|w| * Real.exp (-K ^ 2 * w ^ 2)) * |Real.tanh w|
            ≤ Real.sqrt Real.pi * K ^ 3 / 2 * (|w| * Real.exp (-K ^ 2 * w ^ 2)) * |w| := by gcongr
          _ = _ := by rw [← h2]; ring
    _ = Real.pi / 4 := by
        rw [integral_const_mul, integral_sq_mul_exp_neg_K_sq hK]
        have hπ := Real.sq_sqrt Real.pi_pos.le
        field_simp
        rw [hπ]; ring

/-- `∫|𝒢_K| = √π K / 2`. -/
theorem integral_abs_gaussPrim {K : ℝ} (hK : 0 < K) :
    ∫ w : ℝ, |gaussPrim K w| = Real.sqrt Real.pi * K / 2 := by
  have hb : (0 : ℝ) < K ^ 2 := by positivity
  simp_rw [abs_gaussPrim K _ hK.le]
  rw [integral_const_mul, integral_abs_mul_exp_neg_sq hb]
  field_simp

/-- `∫|G_K| ≤ π K²`. -/
theorem integral_abs_gaussDeriv_le {K : ℝ} (hK : 0 < K) :
    ∫ w : ℝ, |gaussDeriv K w| ≤ Real.pi * K ^ 2 := by
  have hb : (0 : ℝ) < K ^ 2 := by positivity
  have hmaj : Integrable fun w : ℝ => Real.sqrt Real.pi * K ^ 3 / 2 *
      (Real.exp (-K ^ 2 * w ^ 2) + 2 * K ^ 2 * (w ^ 2 * Real.exp (-K ^ 2 * w ^ 2))) :=
    ((integrable_exp_neg_mul_sq hb).add ((integrable_sq_mul_exp_neg_sq hb).const_mul _)).const_mul _
  calc ∫ w : ℝ, |gaussDeriv K w|
      ≤ ∫ w : ℝ, Real.sqrt Real.pi * K ^ 3 / 2 *
          (Real.exp (-K ^ 2 * w ^ 2) + 2 * K ^ 2 * (w ^ 2 * Real.exp (-K ^ 2 * w ^ 2))) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun w => abs_nonneg _) hmaj
          (Eventually.of_forall fun w => ?_)
        dsimp only
        rw [gaussDeriv, abs_mul, abs_of_nonneg (by positivity), abs_mul,
          abs_of_pos (Real.exp_pos _), show -(K * w) ^ 2 = -K ^ 2 * w ^ 2 by ring]
        gcongr
        have : |1 - 2 * (K * w) ^ 2| ≤ 1 + 2 * K ^ 2 * w ^ 2 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (K * w)]
        nlinarith [Real.exp_pos (-K ^ 2 * w ^ 2)]
    _ = Real.pi * K ^ 2 := by
        rw [integral_const_mul, integral_add (integrable_exp_neg_mul_sq hb)
          ((integrable_sq_mul_exp_neg_sq hb).const_mul _), integral_const_mul,
          integral_exp_neg_K_sq hK, integral_sq_mul_exp_neg_K_sq hK]
        have hπ := Real.mul_self_sqrt Real.pi_pos.le
        field_simp
        nlinarith [hπ]

/-- `∫|R_K| ≤ (π + √π) K²` for `K ≥ 1`. -/
theorem integral_abs_cosWeight_le {K : ℝ} (hK : 1 ≤ K) :
    ∫ w : ℝ, |cosWeight K w| ≤ (Real.pi + Real.sqrt Real.pi) * K ^ 2 := by
  have hK0 : 0 < K := by linarith
  calc ∫ w : ℝ, |cosWeight K w| ≤ ∫ w : ℝ, (|gaussDeriv K w| + |gaussPrim K w|) :=
        integral_mono_of_nonneg (Eventually.of_forall fun w => abs_nonneg _)
          ((integrable_gaussDeriv hK0).abs.add (integrable_gaussPrim hK0).abs)
          (Eventually.of_forall fun w => abs_cosWeight_le K w)
    _ = (∫ w : ℝ, |gaussDeriv K w|) + ∫ w : ℝ, |gaussPrim K w| :=
        integral_add (integrable_gaussDeriv hK0).abs (integrable_gaussPrim hK0).abs
    _ ≤ Real.pi * K ^ 2 + Real.sqrt Real.pi * K / 2 := by
        rw [integral_abs_gaussPrim hK0]; linarith [integral_abs_gaussDeriv_le hK0]
    _ ≤ (Real.pi + Real.sqrt Real.pi) * K ^ 2 := by
        have hs := Real.sqrt_nonneg Real.pi
        have hk2 : K ≤ K ^ 2 := by nlinarith
        have : Real.sqrt Real.pi * K / 2 ≤ Real.sqrt Real.pi * K ^ 2 := by nlinarith
        nlinarith

end

end GaloisForLFunctions.RHTower.DeckPointPair
