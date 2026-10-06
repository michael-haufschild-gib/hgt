import GaloisForLFunctions.RHTower.KuznetsovKernelOscillatory

/-!
# Gaussian tails of the large-sieve kernel

With the tail factor `T_K(w) = (1 + cosh w) e^{K²(w² − 1)/2}`, which dominates `1 + cosh w` for `|w| ≥ 1`,
and `K ≥ 1`:

* `e^{−K²w²} T_K(w) ≤ 2e · e^{−K²/2} e^{−K²w²/4}` (`exp_mul_tailFactor_le`);
* `∫ |𝒢_K| T_K ≤ 4√π e · K e^{−K²/2}` (`integral_abs_gaussPrim_mul_tailFactor_le`);
* `∫ |R_K| T_K ≤ (10π + 4√π) e · K² e^{−K²/2}` (`integral_abs_cosWeight_mul_tailFactor_le`);
* `∫ |𝒢_K sinh| ≤ 2πe` and `∫ |𝒢_K tanh| (1 + cosh) ≤ π/4 + 2πe` (`gaussSinhMass_le`,
  `integral_abs_gaussPrim_tanh_mul_one_add_cosh_le`).
-/

open MeasureTheory Set Filter

namespace GaloisForLFunctions.RHTower.DeckPointPair

open KuznetsovGauss

noncomputable section

/-- The tail factor `(1 + cosh w) e^{K²(w² − 1)/2}`. -/
def tailFactor (K w : ℝ) : ℝ := (1 + Real.cosh w) * Real.exp (K ^ 2 * (w ^ 2 - 1) / 2)

theorem tailFactor_nonneg (K w : ℝ) : 0 ≤ tailFactor K w := by
  unfold tailFactor; have := Real.cosh_pos w; positivity

theorem continuous_tailFactor (K : ℝ) : Continuous (tailFactor K) := by
  unfold tailFactor; fun_prop

theorem one_add_cosh_le_tailFactor (K : ℝ) {w : ℝ} (hw : 1 ≤ |w|) :
    1 + Real.cosh w ≤ tailFactor K w := by
  unfold tailFactor
  have hw2 : 1 ≤ w ^ 2 := by nlinarith [sq_abs w, abs_nonneg w]
  have h1 : 0 ≤ K ^ 2 * (w ^ 2 - 1) / 2 :=
    div_nonneg (mul_nonneg (sq_nonneg K) (by linarith)) (by norm_num)
  have h2 := Real.one_le_exp h1
  have := Real.cosh_pos w
  nlinarith

theorem one_add_cosh_le (w : ℝ) : 1 + Real.cosh w ≤ 2 * Real.exp |w| := by
  have h1 := cosh_le_exp_abs w
  have h2 := Real.one_le_exp (abs_nonneg w)
  linarith

/-- `|w| − K²w²/2 ≤ 1 − K²w²/4` for `K ≥ 1`. -/
theorem abs_sub_le_of_one_le {K : ℝ} (hK : 1 ≤ K) (w : ℝ) :
    |w| - K ^ 2 * w ^ 2 / 2 ≤ 1 - K ^ 2 / 4 * w ^ 2 := by
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have h1 : w ^ 2 ≤ K ^ 2 * w ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hK2) (sq_nonneg w)]
  have h2 : 0 ≤ (|w| / 2 - 1) ^ 2 := sq_nonneg _
  have h3 : |w| ^ 2 = w ^ 2 := sq_abs w
  nlinarith

theorem exp_mul_tailFactor_le {K : ℝ} (hK : 1 ≤ K) (w : ℝ) :
    Real.exp (-K ^ 2 * w ^ 2) * tailFactor K w ≤
      2 * Real.exp 1 * Real.exp (-K ^ 2 / 2) * Real.exp (-(K ^ 2 / 4) * w ^ 2) := by
  unfold tailFactor
  have h1 := one_add_cosh_le w
  have h2 := abs_sub_le_of_one_le hK w
  calc Real.exp (-K ^ 2 * w ^ 2) * ((1 + Real.cosh w) * Real.exp (K ^ 2 * (w ^ 2 - 1) / 2))
      ≤ Real.exp (-K ^ 2 * w ^ 2) * ((2 * Real.exp |w|) * Real.exp (K ^ 2 * (w ^ 2 - 1) / 2)) := by
        gcongr
    _ = 2 * Real.exp (-K ^ 2 * w ^ 2 + |w| + K ^ 2 * (w ^ 2 - 1) / 2) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ 2 * Real.exp (1 + (-K ^ 2 / 2) + (-(K ^ 2 / 4) * w ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
        linarith
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

/-! ## The two tail masses -/

theorem integrable_abs_mul_exp_neg_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun w : ℝ => |w| * Real.exp (-b * w ^ 2) := by
  refine (integrable_mul_exp_neg_mul_sq hb).norm.congr (Eventually.of_forall fun w => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

theorem abs_gaussPrim_mul_tailFactor_le {K : ℝ} (hK : 1 ≤ K) (w : ℝ) :
    |gaussPrim K w| * tailFactor K w ≤
      Real.sqrt Real.pi * K ^ 3 * Real.exp 1 * Real.exp (-K ^ 2 / 2) *
        (|w| * Real.exp (-(K ^ 2 / 4) * w ^ 2)) := by
  rw [abs_gaussPrim K w (by linarith)]
  have h := exp_mul_tailFactor_le hK w
  have hw := abs_nonneg w
  calc Real.sqrt Real.pi * K ^ 3 / 2 * (|w| * Real.exp (-K ^ 2 * w ^ 2)) * tailFactor K w
      = Real.sqrt Real.pi * K ^ 3 / 2 * |w| * (Real.exp (-K ^ 2 * w ^ 2) * tailFactor K w) := by ring
    _ ≤ Real.sqrt Real.pi * K ^ 3 / 2 * |w| *
          (2 * Real.exp 1 * Real.exp (-K ^ 2 / 2) * Real.exp (-(K ^ 2 / 4) * w ^ 2)) := by
        have : 0 ≤ Real.sqrt Real.pi * K ^ 3 / 2 * |w| := by
          have : 0 ≤ K := by linarith
          positivity
        exact mul_le_mul_of_nonneg_left h this
    _ = _ := by ring

theorem integrable_abs_gaussPrim_mul_tailFactor {K : ℝ} (hK : 1 ≤ K) :
    Integrable fun w => |gaussPrim K w| * tailFactor K w := by
  have hb : (0 : ℝ) < K ^ 2 / 4 := by positivity
  refine ((integrable_abs_mul_exp_neg_sq hb).const_mul
    (Real.sqrt Real.pi * K ^ 3 * Real.exp 1 * Real.exp (-K ^ 2 / 2))).mono'
    (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun w => ?_)
  · have := continuous_tailFactor K; unfold gaussPrim; fun_prop
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (tailFactor_nonneg K w))]
  exact abs_gaussPrim_mul_tailFactor_le hK w

/-- `∫ |𝒢_K| T_K ≤ 4√π e K e^{−K²/2}`. -/
theorem integral_abs_gaussPrim_mul_tailFactor_le {K : ℝ} (hK : 1 ≤ K) :
    ∫ w, |gaussPrim K w| * tailFactor K w ≤
      4 * Real.sqrt Real.pi * Real.exp 1 * K * Real.exp (-K ^ 2 / 2) := by
  have hK0 : 0 < K := by linarith
  have hb : (0 : ℝ) < K ^ 2 / 4 := by positivity
  calc ∫ w, |gaussPrim K w| * tailFactor K w
      ≤ ∫ w, Real.sqrt Real.pi * K ^ 3 * Real.exp 1 * Real.exp (-K ^ 2 / 2) *
          (|w| * Real.exp (-(K ^ 2 / 4) * w ^ 2)) :=
        integral_mono (integrable_abs_gaussPrim_mul_tailFactor hK)
          ((integrable_abs_mul_exp_neg_sq hb).const_mul _) fun w => abs_gaussPrim_mul_tailFactor_le hK w
    _ = _ := by
        rw [integral_const_mul, integral_abs_mul_exp_neg_sq hb]
        field_simp

theorem abs_gaussDeriv_le (K w : ℝ) (hK : 0 ≤ K) :
    |gaussDeriv K w| ≤ Real.sqrt Real.pi * K ^ 3 / 2 *
      (Real.exp (-K ^ 2 * w ^ 2) + 2 * K ^ 2 * (w ^ 2 * Real.exp (-K ^ 2 * w ^ 2))) := by
  rw [gaussDeriv, abs_mul, abs_of_nonneg (by positivity), abs_mul,
    abs_of_pos (Real.exp_pos _), show -(K * w) ^ 2 = -K ^ 2 * w ^ 2 by ring]
  gcongr
  have : |1 - 2 * (K * w) ^ 2| ≤ 1 + 2 * K ^ 2 * w ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (K * w)]
  nlinarith [Real.exp_pos (-K ^ 2 * w ^ 2)]

theorem abs_gaussDeriv_mul_tailFactor_le {K : ℝ} (hK : 1 ≤ K) (w : ℝ) :
    |gaussDeriv K w| * tailFactor K w ≤
      Real.sqrt Real.pi * K ^ 3 * Real.exp 1 * Real.exp (-K ^ 2 / 2) *
        (Real.exp (-(K ^ 2 / 4) * w ^ 2) + 2 * K ^ 2 * (w ^ 2 * Real.exp (-(K ^ 2 / 4) * w ^ 2))) := by
  have h := exp_mul_tailFactor_le hK w
  have h1 := abs_gaussDeriv_le K w (by linarith)
  have ht := tailFactor_nonneg K w
  calc |gaussDeriv K w| * tailFactor K w
      ≤ Real.sqrt Real.pi * K ^ 3 / 2 *
          (Real.exp (-K ^ 2 * w ^ 2) + 2 * K ^ 2 * (w ^ 2 * Real.exp (-K ^ 2 * w ^ 2))) *
            tailFactor K w := mul_le_mul_of_nonneg_right h1 ht
    _ = Real.sqrt Real.pi * K ^ 3 / 2 * (1 + 2 * K ^ 2 * w ^ 2) *
          (Real.exp (-K ^ 2 * w ^ 2) * tailFactor K w) := by ring
    _ ≤ Real.sqrt Real.pi * K ^ 3 / 2 * (1 + 2 * K ^ 2 * w ^ 2) *
          (2 * Real.exp 1 * Real.exp (-K ^ 2 / 2) * Real.exp (-(K ^ 2 / 4) * w ^ 2)) := by
        have : 0 ≤ Real.sqrt Real.pi * K ^ 3 / 2 * (1 + 2 * K ^ 2 * w ^ 2) := by
          have : 0 ≤ K := by linarith
          positivity
        exact mul_le_mul_of_nonneg_left h this
    _ = _ := by ring

/-- `∫ |R_K| T_K ≤ (10π + 4√π) e K² e^{−K²/2}`. -/
theorem integral_abs_cosWeight_mul_tailFactor_le {K : ℝ} (hK : 1 ≤ K) :
    Integrable (fun w => |cosWeight K w| * tailFactor K w) ∧
      ∫ w, |cosWeight K w| * tailFactor K w ≤
        (10 * Real.pi + 4 * Real.sqrt Real.pi) * Real.exp 1 * K ^ 2 * Real.exp (-K ^ 2 / 2) := by
  have hK0 : 0 < K := by linarith
  have hb : (0 : ℝ) < K ^ 2 / 4 := by positivity
  set g : ℝ → ℝ := fun w => Real.sqrt Real.pi * K ^ 3 * Real.exp 1 * Real.exp (-K ^ 2 / 2) *
      (Real.exp (-(K ^ 2 / 4) * w ^ 2) + 2 * K ^ 2 * (w ^ 2 * Real.exp (-(K ^ 2 / 4) * w ^ 2)))
  have hg : Integrable g :=
    ((integrable_exp_neg_mul_sq hb).add ((integrable_pow_mul_exp_neg_sq hb 2).const_mul _)).const_mul _
  have hDint : Integrable fun w => |gaussDeriv K w| * tailFactor K w := by
    refine hg.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun w => ?_)
    · have := continuous_tailFactor K; unfold gaussDeriv; fun_prop
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (tailFactor_nonneg K w))]
    exact abs_gaussDeriv_mul_tailFactor_le hK w
  have hPint := integrable_abs_gaussPrim_mul_tailFactor hK
  have hle : ∀ w, |cosWeight K w| * tailFactor K w ≤
      |gaussDeriv K w| * tailFactor K w + |gaussPrim K w| * tailFactor K w := fun w => by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_cosWeight_le K w) (tailFactor_nonneg K w)
  have hmeas : AEStronglyMeasurable (fun w => |cosWeight K w| * tailFactor K w) := by
    have h1 := (integrable_cosWeight hK0).aestronglyMeasurable
    exact h1.norm.mul (continuous_tailFactor K).aestronglyMeasurable
  have hint : Integrable fun w => |cosWeight K w| * tailFactor K w :=
    (hDint.add hPint).mono' hmeas (Eventually.of_forall fun w => by
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (tailFactor_nonneg K w))]
      exact hle w)
  refine ⟨hint, ?_⟩
  have hgint : ∫ w, g w = 10 * Real.pi * Real.exp 1 * K ^ 2 * Real.exp (-K ^ 2 / 2) := by
    simp only [g]
    rw [integral_const_mul, integral_add (integrable_exp_neg_mul_sq hb)
      ((integrable_pow_mul_exp_neg_sq hb 2).const_mul _), integral_const_mul,
      integral_gaussian, integral_sq_mul_exp_neg_sq hb]
    have h1 : Real.sqrt (Real.pi / (K ^ 2 / 4)) = 2 * Real.sqrt Real.pi / K := by
      rw [Real.sqrt_div' _ hb.le, show K ^ 2 / 4 = (K / 2) ^ 2 by ring, Real.sqrt_sq (by linarith)]
      field_simp
    have h2 : (K ^ 2 / 4) ^ (-(3 / 2 : ℝ)) = 8 / K ^ 3 := by
      rw [show K ^ 2 / 4 = (K / 2) ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
        ← Real.rpow_mul (by linarith), show (2 : ℝ) * -(3 / 2) = -3 by norm_num,
        Real.rpow_neg (by linarith), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
      ring
    rw [h1, h2]
    have hπ := Real.mul_self_sqrt Real.pi_pos.le
    have e : Real.sqrt Real.pi * K ^ 3 * Real.exp 1 * Real.exp (-K ^ 2 / 2) *
        (2 * Real.sqrt Real.pi / K + 2 * K ^ 2 * (Real.sqrt Real.pi / 2 * (8 / K ^ 3))) =
        10 * (Real.sqrt Real.pi * Real.sqrt Real.pi) * Real.exp 1 * K ^ 2 * Real.exp (-K ^ 2 / 2) := by
      field_simp
      ring
    rw [e, hπ]
  calc ∫ w, |cosWeight K w| * tailFactor K w
      ≤ ∫ w, (|gaussDeriv K w| * tailFactor K w + |gaussPrim K w| * tailFactor K w) :=
        integral_mono hint (hDint.add hPint) hle
    _ = (∫ w, |gaussDeriv K w| * tailFactor K w) + ∫ w, |gaussPrim K w| * tailFactor K w :=
        integral_add hDint hPint
    _ ≤ (∫ w, g w) + 4 * Real.sqrt Real.pi * Real.exp 1 * K * Real.exp (-K ^ 2 / 2) := by
        gcongr
        · exact fun w => abs_gaussDeriv_mul_tailFactor_le hK w
        · exact integral_abs_gaussPrim_mul_tailFactor_le hK
    _ ≤ _ := by
        rw [hgint]
        have hKK : K ≤ K ^ 2 := by nlinarith
        have : 0 ≤ 4 * Real.sqrt Real.pi * Real.exp 1 * Real.exp (-K ^ 2 / 2) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hKK this]

/-! ## The `sinh` mass -/

theorem abs_sinh_le_mul_exp_abs (w : ℝ) : |Real.sinh w| ≤ |w| * Real.exp |w| := by
  rw [Real.abs_sinh]
  have h1 := sinh_le_mul_cosh (abs_nonneg w)
  have h2 := cosh_le_exp_abs |w|
  rw [abs_abs] at h2
  have := abs_nonneg w
  nlinarith

theorem abs_gaussPrim_mul_sinh_le {K : ℝ} (hK : 1 ≤ K) (w : ℝ) :
    |gaussPrim K w * Real.sinh w| ≤
      Real.sqrt Real.pi * K ^ 3 / 2 * Real.exp 1 * (w ^ 2 * Real.exp (-(K ^ 2 / 4) * w ^ 2)) := by
  rw [abs_mul, abs_gaussPrim K w (by linarith)]
  have h1 := abs_sinh_le_mul_exp_abs w
  have h2 : Real.exp (-K ^ 2 * w ^ 2) * Real.exp |w| ≤ Real.exp 1 * Real.exp (-(K ^ 2 / 4) * w ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := abs_sub_le_of_one_le hK w
    nlinarith [sq_nonneg w, sq_nonneg K]
  have hw : |w| * |w| = w ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
  have hc : 0 ≤ Real.sqrt Real.pi * K ^ 3 / 2 := by
    have : 0 ≤ K := by linarith
    positivity
  calc Real.sqrt Real.pi * K ^ 3 / 2 * (|w| * Real.exp (-K ^ 2 * w ^ 2)) * |Real.sinh w|
      ≤ Real.sqrt Real.pi * K ^ 3 / 2 * (|w| * Real.exp (-K ^ 2 * w ^ 2)) * (|w| * Real.exp |w|) := by
        gcongr
    _ = Real.sqrt Real.pi * K ^ 3 / 2 * (|w| * |w|) * (Real.exp (-K ^ 2 * w ^ 2) * Real.exp |w|) := by
        ring
    _ ≤ Real.sqrt Real.pi * K ^ 3 / 2 * (|w| * |w|) *
          (Real.exp 1 * Real.exp (-(K ^ 2 / 4) * w ^ 2)) := by gcongr
    _ = _ := by rw [hw]; ring

theorem integrable_abs_gaussPrim_mul_sinh {K : ℝ} (hK : 1 ≤ K) :
    Integrable fun w => |gaussPrim K w * Real.sinh w| := by
  have hb : (0 : ℝ) < K ^ 2 / 4 := by have : 0 < K := by linarith
                                      positivity
  refine ((integrable_pow_mul_exp_neg_sq hb 2).const_mul
    (Real.sqrt Real.pi * K ^ 3 / 2 * Real.exp 1)).mono'
    (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun w => ?_)
  · unfold gaussPrim; fun_prop
  rw [Real.norm_of_nonneg (abs_nonneg _)]
  exact abs_gaussPrim_mul_sinh_le hK w

/-- `∫ |𝒢_K sinh| ≤ 2πe` for `K ≥ 1`. -/
theorem gaussSinhMass_le {K : ℝ} (hK : 1 ≤ K) : gaussSinhMass K ≤ 2 * Real.pi * Real.exp 1 := by
  have hK0 : 0 < K := by linarith
  have hb : (0 : ℝ) < K ^ 2 / 4 := by positivity
  unfold gaussSinhMass
  calc ∫ w : ℝ, |gaussPrim K w * Real.sinh w|
      ≤ ∫ w : ℝ, Real.sqrt Real.pi * K ^ 3 / 2 * Real.exp 1 *
          (w ^ 2 * Real.exp (-(K ^ 2 / 4) * w ^ 2)) :=
        integral_mono (integrable_abs_gaussPrim_mul_sinh hK)
          ((integrable_pow_mul_exp_neg_sq hb 2).const_mul _) fun w => abs_gaussPrim_mul_sinh_le hK w
    _ = 2 * Real.pi * Real.exp 1 := by
        rw [integral_const_mul, integral_sq_mul_exp_neg_sq hb]
        have h2 : (K ^ 2 / 4) ^ (-(3 / 2 : ℝ)) = 8 / K ^ 3 := by
          rw [show K ^ 2 / 4 = (K / 2) ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
            ← Real.rpow_mul (by linarith), show (2 : ℝ) * -(3 / 2) = -3 by norm_num,
            Real.rpow_neg (by linarith), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          field_simp
          ring
        rw [h2]
        have hπ := Real.mul_self_sqrt Real.pi_pos.le
        have e : Real.sqrt Real.pi * K ^ 3 / 2 * Real.exp 1 * (Real.sqrt Real.pi / 2 * (8 / K ^ 3)) =
            2 * (Real.sqrt Real.pi * Real.sqrt Real.pi) * Real.exp 1 := by
          field_simp
          ring
        rw [e, hπ]

theorem integrable_abs_gaussPrim_tanh {K : ℝ} (hK : 0 < K) :
    Integrable fun w => |gaussPrim K w * Real.tanh w| := by
  refine (integrable_gaussPrim hK).norm.mono'
    (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun w => ?_)
  · have := continuous_tanh; unfold gaussPrim; fun_prop
  rw [Real.norm_of_nonneg (abs_nonneg _), Real.norm_eq_abs, abs_mul]
  have := abs_tanh_le_one w
  have := abs_nonneg (gaussPrim K w)
  nlinarith

/-- `∫ |𝒢_K tanh| (1 + cosh) ≤ π/4 + 2πe` for `K ≥ 1`. -/
theorem integral_abs_gaussPrim_tanh_mul_one_add_cosh_le {K : ℝ} (hK : 1 ≤ K) :
    Integrable (fun w => |gaussPrim K w * Real.tanh w| * (1 + Real.cosh w)) ∧
      ∫ w, |gaussPrim K w * Real.tanh w| * (1 + Real.cosh w) ≤
        Real.pi / 4 + 2 * Real.pi * Real.exp 1 := by
  have hK0 : 0 < K := by linarith
  have heq : (fun w => |gaussPrim K w * Real.tanh w| * (1 + Real.cosh w)) =
      fun w => |gaussPrim K w * Real.tanh w| + |gaussPrim K w * Real.sinh w| := by
    funext w
    have hc := Real.cosh_pos w
    rw [mul_add, mul_one, Real.tanh_eq_sinh_div_cosh, abs_mul, abs_mul, abs_div,
      abs_of_pos hc]
    field_simp
  have h1 := integrable_abs_gaussPrim_tanh hK0
  have h2 := integrable_abs_gaussPrim_mul_sinh hK
  rw [heq]
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2]
  have := integral_abs_gaussPrim_tanh_le hK0
  have := gaussSinhMass_le hK
  unfold gaussSinhMass at this
  linarith

end

end GaloisForLFunctions.RHTower.DeckPointPair
