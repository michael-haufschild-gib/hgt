import GaloisForLFunctions.RHTower.HedenmalmTwoPrimeNormalFrame
import GaloisForLFunctions.RHTower.CCMTwoPoleSourceCriterion

/-!
# The two positive-kernel self-adjoint prime channels

Convolution by the centered prime window `c_n` acts on the Fourier side as multiplication by the
real symbol `hat c_n = a_n Xi_C`.  Since `c_n` is positive, even and integrable the symbol is real
and bounded by the total mass of `c_n`, so the channel is a bounded self-adjoint operator on
`L²(ℝ)`.  Its symbol is exactly the multiplier of the divisor factorization, so the two prime
channels see the whole `Xi` divisor.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmIntervalAnomaly

/-! ### The centered prime window is an integrable positive even kernel -/

theorem centeredWindow_eq_cdf {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    centeredWindow thetaSource n x
      = ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        * (thetaSource.mass * (thetaSource.cdfFun (x + Real.log n / 2)
            - thetaSource.cdfFun (x - Real.log n / 2))) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  rw [centeredWindow, mass_mul_cdfFun_sub thetaSource (by linarith : x - Real.log n / 2
    ≤ x + Real.log n / 2)]

theorem continuous_centeredWindow {n : ℕ} (hn : 1 ≤ n) :
    Continuous (centeredWindow thetaSource n) := by
  have h : Continuous fun x : ℝ => ((n : ℝ) ^ (-(1 / 2 : ℝ)))
      * (thetaSource.mass * (thetaSource.cdfFun (x + Real.log n / 2)
          - thetaSource.cdfFun (x - Real.log n / 2))) :=
    continuous_const.mul (continuous_const.mul
      ((thetaSource.continuous_cdfFun.comp (continuous_id.add continuous_const)).sub
        (thetaSource.continuous_cdfFun.comp (continuous_id.sub continuous_const))))
  exact h.congr fun x => (centeredWindow_eq_cdf hn x).symm

/-- The exponential envelope constant of the centered prime window. -/
def channelBoundConstant (n : ℕ) : ℝ :=
  ((n : ℝ) ^ (-(1 / 2 : ℝ)))
    * (Real.log n * (thetaBound * Real.exp (Real.log n)) * Real.exp (Real.log n / 2))

theorem centeredWindow_le_exp {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    centeredWindow thetaSource n x ≤ channelBoundConstant n * Real.exp (-|x|) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hpow : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hshift : centeredWindow thetaSource n x
      = ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        * intervalMass thetaSource (x - Real.log n / 2)
            ((x - Real.log n / 2) + Real.log n) := by
    rw [centeredWindow]
    congr 2
    ring
  have hmass := intervalMass_le_exp hL (x - Real.log n / 2)
  have habs : Real.exp (-|x - Real.log n / 2|)
      ≤ Real.exp (Real.log n / 2) * Real.exp (-|x|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h := abs_sub_abs_le_abs_sub x (x - Real.log n / 2)
    have habs2 : |x - (x - Real.log n / 2)| = Real.log n / 2 := by
      rw [show x - (x - Real.log n / 2) = Real.log n / 2 by ring, abs_of_nonneg (by linarith)]
    rw [habs2] at h
    linarith
  have hCnn : (0 : ℝ) ≤ Real.log n * (thetaBound * Real.exp (Real.log n)) := by
    have := thetaBound_nonneg
    positivity
  rw [hshift, channelBoundConstant]
  calc ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        * intervalMass thetaSource (x - Real.log n / 2) ((x - Real.log n / 2) + Real.log n)
      ≤ ((n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log n * (thetaBound * Real.exp (Real.log n))
          * Real.exp (-|x - Real.log n / 2|)) := mul_le_mul_of_nonneg_left hmass hpow.le
    _ ≤ ((n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log n * (thetaBound * Real.exp (Real.log n))
          * (Real.exp (Real.log n / 2) * Real.exp (-|x|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hCnn) hpow.le
    _ = ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log n * (thetaBound * Real.exp (Real.log n))
          * Real.exp (Real.log n / 2))) * Real.exp (-|x|) := by ring

theorem centeredWindow_nonneg (n : ℕ) (x : ℝ) : 0 ≤ centeredWindow thetaSource n x := by
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  exact mul_nonneg hpow (intervalMass_nonneg _ _)

theorem integrable_centeredWindow {n : ℕ} (hn : 1 ≤ n) :
    Integrable (centeredWindow thetaSource n) (volume : Measure ℝ) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (by norm_num : (0:ℝ) < 1)).const_mul (channelBoundConstant n))
    (continuous_centeredWindow hn).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (centeredWindow_nonneg n x), one_mul]
  exact centeredWindow_le_exp hn x


/-! ### The channel symbol -/

/-- The Fourier symbol of the centered prime channel, `hat c_n = a_n Xi_C`. -/
def channelSymbol (n : ℕ) (t : ℝ) : ℂ := centeredMultiplier n (t : ℂ) * XiC (t : ℂ)

theorem channelSymbol_zero (n : ℕ) : channelSymbol n 0 = 0 := by
  simp [channelSymbol, centeredMultiplier]

theorem channelSymbol_eq_integral {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ≠ 0) :
    channelSymbol n t
      = ∫ x : ℝ, ((centeredWindow thetaSource n x : ℝ) : ℂ) * sourceChar (t : ℂ) x := by
  rw [channelSymbol,
    ← integral_centeredWindow_sourceChar hn (by simp) (by exact_mod_cast ht)]

theorem continuous_XiC : Continuous XiC :=
  continuous_iff_continuousAt.mpr fun z => (XiC_analytic z (Set.mem_univ z)).continuousAt

theorem measurable_channelSymbol (n : ℕ) : Measurable (channelSymbol n) := by
  have hnum : Measurable fun t : ℝ => ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
      * (Complex.exp (Complex.I * (t : ℂ) * ((Real.log n / 2 : ℝ) : ℂ))
        - Complex.exp (-(Complex.I * (t : ℂ) * ((Real.log n / 2 : ℝ) : ℂ)))) := by
    fun_prop
  have hden : Measurable fun t : ℝ => Complex.I * (t : ℂ) := by fun_prop
  have hXi : Measurable fun t : ℝ => XiC (t : ℂ) :=
    (continuous_XiC.comp Complex.continuous_ofReal).measurable
  exact (hnum.div hden).mul hXi

theorem norm_channelSymbol_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ‖channelSymbol n t‖ ≤ ∫ x : ℝ, centeredWindow thetaSource n x := by
  have hnn : (0 : ℝ) ≤ ∫ x : ℝ, centeredWindow thetaSource n x :=
    integral_nonneg fun x => centeredWindow_nonneg n x
  rcases eq_or_ne t 0 with rfl | ht
  · rw [channelSymbol_zero]
    simpa using hnn
  · rw [channelSymbol_eq_integral hn ht]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖((centeredWindow thetaSource n x : ℝ) : ℂ) * sourceChar (t : ℂ) x‖
      = centeredWindow thetaSource n x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (centeredWindow_nonneg n x), norm_sourceChar]
    simp

/-- **The channel symbol is real.**  The kernel is real and even, so its transform is real on the
real axis. -/
theorem conj_channelSymbol {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (starRingEnd ℂ) (channelSymbol n t) = channelSymbol n t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [channelSymbol_zero, map_zero]
  · rw [channelSymbol_eq_integral hn ht, ← integral_conj]
    have hpt : ∀ x : ℝ, (starRingEnd ℂ) (((centeredWindow thetaSource n x : ℝ) : ℂ)
        * sourceChar (t : ℂ) x)
        = ((centeredWindow thetaSource n (-x) : ℝ) : ℂ) * sourceChar (t : ℂ) (-x) := by
      intro x
      rw [map_mul, Complex.conj_ofReal,
        centeredWindow_neg thetaSource thetaSource_even hn x, sourceChar, sourceChar,
        ← Complex.exp_conj]
      congr 2
      push_cast
      simp [Complex.conj_I, Complex.conj_ofReal]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact MeasureTheory.integral_neg_eq_self
      (fun u : ℝ => ((centeredWindow thetaSource n u : ℝ) : ℂ) * sourceChar (t : ℂ) u) volume

/-! ### The two self-adjoint prime channels -/

/-- **The prime channel.**  Multiplication by the real bounded symbol `hat c_n` on `L²(ℝ)`; on the
kernel side this is convolution by the positive even window `c_n`. -/
def channelOperator (n : ℕ) (hn : 1 ≤ n) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) (measurable_channelSymbol n)
    (integral_nonneg fun x => centeredWindow_nonneg n x) (norm_channelSymbol_le hn)

/-- **The prime channels are bounded and self-adjoint.** -/
theorem channelOperator_inner {n : ℕ} (hn : 1 ≤ n) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ (channelOperator n hn f) g : ℂ) = inner ℂ f (channelOperator n hn g) :=
  lpBoundedMulCLM_inner_general (measurable_channelSymbol n)
    (integral_nonneg fun x => centeredWindow_nonneg n x) (norm_channelSymbol_le hn)
    (conj_channelSymbol hn) f g

/-- **The channel symbol is exactly the divisor multiplier.**  The two prime channels therefore
carry the whole `Xi` divisor: their common symbol zero set on the real axis is the real divisor of
`Xi_C`, since `a_2` and `a_3` have no common zero. -/
theorem channelSymbol_eq_zero_iff {t : ℝ} (ht : t ≠ 0) :
    (channelSymbol 2 t = 0 ∧ channelSymbol 3 t = 0) ↔ XiC (t : ℂ) = 0 := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  constructor
  · rintro ⟨h2, h3⟩
    rcases mul_eq_zero.mp h2 with h | h
    · rcases mul_eq_zero.mp h3 with h' | h'
      · exact absurd (no_common_zero_centered_two_three h h') htc
      · exact h'
    · exact h
  · intro h
    exact ⟨by rw [channelSymbol, h, mul_zero], by rw [channelSymbol, h, mul_zero]⟩

end HedenmalmThetaSource

end

end RHTower
