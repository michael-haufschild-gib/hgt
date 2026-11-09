import GaloisForLFunctions.RHTower.ThetaZeroDivisionRealization

/-!
# Uniform relative bounds for real zero division

The outward sine operator at a real frequency has norm at most a universal
constant times the frequency on sources dominated by the theta source.
After division by the squared frequency, its norm is therefore `O(1/γ)`.
The constant is independent of the chosen zero and of separations between zeros.
-/

noncomputable section
set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology RHTower

namespace GaloisForLFunctions.ArithmeticPositiveDuality

private theorem norm_real_zeroDivision_le_mass {f : ℝ → ℂ}
    (hf : ExpMomentSource f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C * thetaCuspFullSource x) (γ x : ℝ) :
    ‖zeroDivision (γ : ℂ) f x‖ ≤
      |γ| * C * ∫ t : ℝ, thetaCuspFullSource t := by
  have hk : Integrable thetaCuspFullSource :=
    (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource 0).congr
      (Filter.Eventually.of_forall fun t => by simp)
  have hs (t : ℝ) : ‖Complex.sin ((γ : ℂ) * ((t : ℂ) - ((|x| : ℝ) : ℂ)))‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_sin,
      Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hb (t : ℝ) :
      ‖Complex.sin ((γ : ℂ) * ((t : ℂ) - ((|x| : ℝ) : ℂ))) * f t‖ ≤
        C * thetaCuspFullSource t := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hs t)).trans (hC t)
  have hg : IntegrableOn
      (fun t : ℝ => Complex.sin ((γ : ℂ) * ((t : ℂ) - ((|x| : ℝ) : ℂ))) * f t)
      (Ioi |x|) := by
    refine (hk.const_mul C).integrableOn.mono' ?_ (Filter.Eventually.of_forall hb)
    exact ((by fun_prop : Continuous fun t : ℝ =>
      Complex.sin ((γ : ℂ) * ((t : ℂ) - ((|x| : ℝ) : ℂ)))).mul hf.continuous).aestronglyMeasurable
      |>.restrict
  have hi : ‖∫ t in Ioi |x|,
      Complex.sin ((γ : ℂ) * ((t : ℂ) - ((|x| : ℝ) : ℂ))) * f t‖ ≤
        C * ∫ t : ℝ, thetaCuspFullSource t := by
    calc
      _ ≤ ∫ t in Ioi |x|,
          ‖Complex.sin ((γ : ℂ) * ((t : ℂ) - ((|x| : ℝ) : ℂ))) * f t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi |x|, C * thetaCuspFullSource t :=
        setIntegral_mono_on hg.norm (hk.const_mul C).integrableOn measurableSet_Ioi
          (fun t _ => hb t)
      _ = C * ∫ t in Ioi |x|, thetaCuspFullSource t := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hk (Filter.Eventually.of_forall
          (fun t => (thetaCuspFullSource_pos t).le))) hC0
  unfold zeroDivision
  rw [outwardSine_eq_integral_Ioi, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (abs_nonneg γ)

/-- A single constant controls every real zero division on theta-dominated sources. -/
theorem exists_uniform_real_zeroDivision_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (γ : ℝ) (f : ℝ → ℂ) (C : ℝ),
      ExpMomentSource f → 0 ≤ C →
      (∀ x, ‖f x‖ ≤ C * thetaCuspFullSource x) →
      ∀ x, ‖zeroDivision (γ : ℂ) f x‖ ≤ B * |γ| * C * thetaCuspFullSource x := by
  have hk : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
  have hrec : ContinuousOn (fun x => 1 / thetaCuspFullSource x) (Icc (-1 : ℝ) 1) :=
    (continuous_const.div hk (fun x => (thetaCuspFullSource_pos x).ne')).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hrec
  let J := ∫ t : ℝ, thetaCuspFullSource t
  have hJ : 0 ≤ J := integral_nonneg (fun t => (thetaCuspFullSource_pos t).le)
  let T := 2 * HedenmalmThetaSource.thetaEnvelopeUpper /
    (Real.pi * HedenmalmThetaSource.thetaEnvelopeLower)
  have hT : 0 ≤ T := by
    have hU := HedenmalmThetaSource.thetaEnvelopeUpper_pos
    have hV := HedenmalmThetaSource.thetaEnvelopeLower_pos
    dsimp only [T]
    positivity
  let B := 1 + |M| * J + T
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith only [mul_nonneg (abs_nonneg M) hJ, hT]
  refine ⟨B, hB, fun γ f C hf hC0 hC x => ?_⟩
  have hγC : 0 ≤ |γ| * C := mul_nonneg (abs_nonneg γ) hC0
  have hkx := thetaCuspFullSource_pos x
  by_cases hx : |x| ≤ 1
  · have hrecb := hM x (abs_le.mp hx)
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hkx), div_le_iff₀ hkx] at hrecb
    have hMk : 1 ≤ |M| * thetaCuspFullSource x := hrecb.trans
      (mul_le_mul_of_nonneg_right (le_abs_self M) hkx.le)
    have hmass := norm_real_zeroDivision_le_mass hf hC0 hC γ x
    have hJM : J ≤ (|M| * J) * thetaCuspFullSource x := by
      have h := mul_le_mul_of_nonneg_left hMk hJ
      nlinarith only [h]
    have hMB : |M| * J ≤ B := by dsimp only [B]; linarith only [hT]
    have hJB : J ≤ B * thetaCuspFullSource x :=
      hJM.trans (mul_le_mul_of_nonneg_right hMB hkx.le)
    have h := mul_le_mul_of_nonneg_left hJB hγC
    dsimp only [J] at h
    nlinarith only [hmass, h]
  · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
    have ht := norm_outwardSine_le_tail_of_le hf hC (γ : ℂ) hx1 (by
      simp only [Complex.ofReal_im, abs_zero]
      exact abs_nonneg x)
    have hke : thetaCuspFullSource |x| = thetaCuspFullSource x := by
      rcases abs_choice x with he | he <;> rw [he]
      exact thetaCuspFullSource_neg x
    rw [Complex.norm_real, Real.norm_eq_abs, hke] at ht
    have he : Real.exp (-(2 * |x|)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith only [abs_nonneg x])
    have hTB : T ≤ B := by
      dsimp only [B]
      nlinarith only [mul_nonneg (abs_nonneg M) hJ]
    have hco : C * (2 * |γ| * HedenmalmThetaSource.thetaEnvelopeUpper /
        (Real.pi * HedenmalmThetaSource.thetaEnvelopeLower)) = T * |γ| * C := by
      dsimp only [T]
      ring
    rw [hco] at ht
    have he' := mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg hT (abs_nonneg γ)) hC0)
    have hb := mul_le_mul_of_nonneg_right hTB hγC
    change ‖outwardSine (γ : ℂ) f |x|‖ ≤ _
    nlinarith only [ht, mul_le_mul_of_nonneg_right he' hkx.le,
      mul_le_mul_of_nonneg_right hb hkx.le]

/-- A fixed universal operator constant, chosen from the proved uniform bound. -/
def realZeroDivisionConstant : ℝ := Classical.choose exists_uniform_real_zeroDivision_bound

theorem one_le_realZeroDivisionConstant : 1 ≤ realZeroDivisionConstant :=
  (Classical.choose_spec exists_uniform_real_zeroDivision_bound).1

theorem realZeroDivisionConstant_bound (γ : ℝ) (f : ℝ → ℂ) (C : ℝ)
    (hf : ExpMomentSource f) (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C * thetaCuspFullSource x) (x : ℝ) :
    ‖zeroDivision (γ : ℂ) f x‖ ≤
      realZeroDivisionConstant * |γ| * C * thetaCuspFullSource x :=
  (Classical.choose_spec exists_uniform_real_zeroDivision_bound).2 γ f C hf hC0 hC x

/-- The real source resolvent whose transform divides by `γ²-z²` at a donor zero. -/
def realZeroResolvent (γ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (γ ^ 2)⁻¹ * (γ * ∫ t in Ioi (0 : ℝ), Real.sin (γ * t) * f (|x| + t))

theorem ofReal_realZeroResolvent (γ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    (realZeroResolvent γ f x : ℂ) =
      ((γ : ℂ) ^ 2)⁻¹ * zeroDivision (γ : ℂ) (fun t => (f t : ℂ)) x := by
  unfold realZeroResolvent zeroDivision outwardSine
  push_cast
  congr 2
  rw [← integral_complex_ofReal]
  apply integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [Complex.ofReal_mul, Complex.ofReal_sin]

theorem realZeroResolvent_even (γ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    realZeroResolvent γ f (-x) = realZeroResolvent γ f x := by
  simp only [realZeroResolvent, abs_neg]

theorem expMomentSource_realZeroResolvent (γ : ℝ) {f : ℝ → ℝ}
    (hf : ExpMomentSource (fun x => (f x : ℂ))) :
    ExpMomentSource (fun x => (realZeroResolvent γ f x : ℂ)) := by
  have he : (fun x => (realZeroResolvent γ f x : ℂ)) =
      fun x => ((γ : ℂ) ^ 2)⁻¹ * zeroDivision (γ : ℂ) (fun t => (f t : ℂ)) x :=
    funext (ofReal_realZeroResolvent γ f)
  rw [he]
  exact (expMomentSource_zeroDivision hf (γ : ℂ)).const_mul _

theorem smooth_realZeroResolvent (γ : ℝ) {f : ℝ → ℝ}
    (hf : ExpMomentSource (fun x => (f x : ℂ)))
    (heven : ∀ x, f (-x) = f x)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => (f x : ℂ)))
    (hz : sourceTransform (fun x => (f x : ℂ)) (γ : ℂ) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (realZeroResolvent γ f x : ℂ)) := by
  have he : (fun x => (realZeroResolvent γ f x : ℂ)) =
      fun x => ((γ : ℂ) ^ 2)⁻¹ * zeroDivision (γ : ℂ) (fun t => (f t : ℂ)) x :=
    funext (ofReal_realZeroResolvent γ f)
  rw [he]
  exact contDiff_const.mul
    (zeroDivision_smooth_green hf (fun x => congrArg Complex.ofReal (heven x)) hs hz).1

/-- The resolvent division identity is global, including at the divided zero. -/
theorem realZeroResolvent_transform_mul {γ : ℝ} (hγ : γ ≠ 0) {f : ℝ → ℝ}
    (hf : ExpMomentSource (fun x => (f x : ℂ))) (heven : ∀ x, f (-x) = f x)
    (hz : sourceTransform (fun x => (f x : ℂ)) (γ : ℂ) = 0) (z : ℂ) :
    sourceTransform (fun x => (realZeroResolvent γ f x : ℂ)) z *
      ((γ : ℂ) ^ 2 - z ^ 2) = sourceTransform (fun x => (f x : ℂ)) z := by
  have he : (fun x => (realZeroResolvent γ f x : ℂ)) =
      fun x => ((γ : ℂ) ^ 2)⁻¹ * zeroDivision (γ : ℂ) (fun t => (f t : ℂ)) x :=
    funext (ofReal_realZeroResolvent γ f)
  rw [he, sourceTransform_const_mul]
  have h := hf.sourceTransform_zeroDivision
    (fun x => congrArg Complex.ofReal (heven x)) (γ : ℂ) z
  rw [hz, sub_zero] at h
  calc
    _ = ((γ : ℂ) ^ 2)⁻¹ * (((γ : ℂ) ^ 2 - z ^ 2) *
        sourceTransform (zeroDivision (γ : ℂ) (fun t => (f t : ℂ))) z) := by ring
    _ = ((γ : ℂ) ^ 2)⁻¹ * ((γ : ℂ) ^ 2 * sourceTransform (fun x => (f x : ℂ)) z) := by rw [h]
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hγ)),
      one_mul]

/-- Unnormalized division gains one inverse power of the real donor height. -/
theorem realZeroResolvent_bound {γ : ℝ} (hγ : 0 < γ) {f : ℝ → ℝ}
    (hf : ExpMomentSource (fun x => (f x : ℂ))) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |f x| ≤ C * thetaCuspFullSource x) (x : ℝ) :
    |realZeroResolvent γ f x| ≤ (realZeroDivisionConstant * C / γ) * thetaCuspFullSource x := by
  have h := realZeroDivisionConstant_bound γ (fun t => (f t : ℂ)) C hf hC0 (fun t => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hC t) x
  rw [abs_of_pos hγ] at h
  calc
    _ = ‖(realZeroResolvent γ f x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = (γ ^ 2)⁻¹ * ‖zeroDivision (γ : ℂ) (fun t => (f t : ℂ)) x‖ := by
      rw [ofReal_realZeroResolvent, norm_mul, norm_inv, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hγ]
    _ ≤ (γ ^ 2)⁻¹ * (realZeroDivisionConstant * γ * C * thetaCuspFullSource x) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (sq_nonneg γ))
    _ = _ := by field_simp

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.exists_uniform_real_zeroDivision_bound
