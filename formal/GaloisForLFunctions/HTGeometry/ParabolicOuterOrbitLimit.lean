import GaloisForLFunctions.HTGeometry.StieltjesTranslationCollapse

/-!
# The parabolic outer orbit collapses to a constant

Read a Herglotz transform on the disc through the Cayley maps and exponentiate: the resulting
bounded outer function, composed with the parabolic disc automorphisms, converges to a constant.

The proof is quantitative and uses no Hardy theory.  When the transform is small the Cayley
quotient is within `4‖m‖` of `-1`, and exponentiating a perturbation of size at most one costs a
factor two, so the `N`-th power of the orbit stays within `8 N ‖m‖` of `exp (-N)`.  Uniform
smallness of `m` on the Cayley image of a compact disc set is the translation collapse of a finite
measure.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Set

open scoped Topology

noncomputable section

/-- The Cayley map from the open unit disc onto the open upper half plane. -/
def cayleyToUpper (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
  intro h
  have hw1 : w = 1 := by
    have := sub_eq_zero.mp h
    exact this.symm
  rw [hw1] at hw
  simp at hw

/-- The Cayley map lands in the open upper half plane. -/
theorem im_cayleyToUpper_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayleyToUpper w).im := by
  have hne : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero_of_norm_lt_one hw
  have hsq : 0 < Complex.normSq ((1 : ℂ) - w) := by
    rw [Complex.normSq_pos]
    exact hne
  have hnorm : Complex.normSq w < 1 := by
    have h := Complex.normSq_eq_norm_sq w
    nlinarith [norm_nonneg w, hw, h]
  have hval : (cayleyToUpper w).im = (1 - Complex.normSq w) / Complex.normSq ((1 : ℂ) - w) := by
    rw [cayleyToUpper, mul_div_assoc, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [Complex.div_re]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.normSq_apply, zero_mul, one_mul, zero_add, zero_sub]
    field_simp
    ring
  rw [hval]
  have hnum : 0 < 1 - Complex.normSq w := by linarith
  positivity

/-- The Cayley map is continuous on the open unit disc. -/
theorem continuousOn_cayleyToUpper : ContinuousOn cayleyToUpper {w : ℂ | ‖w‖ < 1} := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro w hw
  exact one_sub_ne_zero_of_norm_lt_one hw

/-- The Cayley quotient of a small value is close to `-1`. -/
theorem norm_cayleyQuotient_add_one_le {m : ℂ} (hm : ‖m‖ ≤ 1 / 2) :
    ‖(m - Complex.I) / (m + Complex.I) + 1‖ ≤ 4 * ‖m‖ := by
  have hden : (1 : ℝ) / 2 ≤ ‖m + Complex.I‖ := by
    have hI : ‖Complex.I‖ ≤ ‖m + Complex.I‖ + ‖m‖ := by
      have hsplit : Complex.I = (m + Complex.I) - m := by ring
      calc ‖Complex.I‖ = ‖(m + Complex.I) - m‖ := by rw [← hsplit]
        _ ≤ ‖m + Complex.I‖ + ‖m‖ := norm_sub_le _ _
    rw [Complex.norm_I] at hI
    linarith
  have hne : m + Complex.I ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    linarith
  have hval : (m - Complex.I) / (m + Complex.I) + 1 = 2 * m / (m + Complex.I) := by
    field_simp
    ring
  rw [hval, norm_div, norm_mul]
  rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖m + Complex.I‖)]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  nlinarith [norm_nonneg m, hden]

/-- Exponentiating a perturbation of size at most one costs at most a factor two. -/
private theorem norm_exp_sub_exp_le {a b : ℂ} (hb : b.re ≤ 0) (h : ‖a - b‖ ≤ 1) :
    ‖Complex.exp a - Complex.exp b‖ ≤ 2 * ‖a - b‖ := by
  have hfac : Complex.exp a - Complex.exp b
      = Complex.exp b * (Complex.exp (a - b) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    ring_nf
  have hexp : ‖Complex.exp b‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr hb
  rw [hfac, norm_mul]
  have hsub : ‖Complex.exp (a - b) - 1‖ ≤ 2 * ‖a - b‖ := Complex.norm_exp_sub_one_le h
  calc ‖Complex.exp b‖ * ‖Complex.exp (a - b) - 1‖
      ≤ 1 * (2 * ‖a - b‖) := by
        refine mul_le_mul hexp hsub (norm_nonneg _) (by norm_num)
    _ = 2 * ‖a - b‖ := by ring

/-- The Cayley/Herglotz exponent of a measure, read on the disc and translated by `t`. -/
def discExponent (ν : Measure ℝ) (t : ℝ) (w : ℂ) : ℂ :=
  (cauchyTransform ν (cayleyToUpper w + (t : ℂ)) - Complex.I) /
    (cauchyTransform ν (cayleyToUpper w + (t : ℂ)) + Complex.I)

/-- The `N`-th power of the parabolic orbit of the outer function of a measure. -/
def parabolicOuterOrbit (ν : Measure ℝ) (N : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((N : ℂ) * discExponent ν t w)

/-- **Quantitative collapse of the parabolic orbit.**  Once the translated transform is small the
orbit is within `8 N` times its size of the constant `exp (-N)`. -/
theorem norm_parabolicOuterOrbit_sub_le (ν : Measure ℝ) (N : ℕ) (t : ℝ) (w : ℂ)
    (hm : ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖ ≤ 1 / 2)
    (hsmall : 4 * (N : ℝ) * ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖ ≤ 1) :
    ‖parabolicOuterOrbit ν N t w - Complex.exp (-(N : ℂ))‖
      ≤ 8 * (N : ℝ) * ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖ := by
  set m : ℂ := cauchyTransform ν (cayleyToUpper w + (t : ℂ)) with hmdef
  have hquot : ‖discExponent ν t w + 1‖ ≤ 4 * ‖m‖ := by
    rw [discExponent]
    exact norm_cayleyQuotient_add_one_le hm
  have hdiff : (N : ℂ) * discExponent ν t w - (-(N : ℂ))
      = (N : ℂ) * (discExponent ν t w + 1) := by ring
  have hnorm : ‖(N : ℂ) * discExponent ν t w - (-(N : ℂ))‖ ≤ 4 * (N : ℝ) * ‖m‖ := by
    rw [hdiff, norm_mul, Complex.norm_natCast]
    calc (N : ℝ) * ‖discExponent ν t w + 1‖ ≤ (N : ℝ) * (4 * ‖m‖) :=
          mul_le_mul_of_nonneg_left hquot (Nat.cast_nonneg N)
      _ = 4 * (N : ℝ) * ‖m‖ := by ring
  have hle1 : ‖(N : ℂ) * discExponent ν t w - (-(N : ℂ))‖ ≤ 1 := le_trans hnorm hsmall
  have hre : (-(N : ℂ)).re ≤ 0 := by
    simp only [Complex.neg_re, Complex.natCast_re]
    exact neg_nonpos.mpr (Nat.cast_nonneg N)
  refine le_trans (norm_exp_sub_exp_le hre hle1) ?_
  calc 2 * ‖(N : ℂ) * discExponent ν t w - (-(N : ℂ))‖ ≤ 2 * (4 * (N : ℝ) * ‖m‖) :=
        mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = 8 * (N : ℝ) * ‖m‖ := by ring

/-- **Locally uniform collapse of the parabolic orbit.**  For every finite measure and every power,
the parabolic orbit of its outer function converges to the constant `exp (-N)` uniformly on every
compact subset of the open unit disc, as the translation escapes to infinity in either
direction. -/
theorem tendstoUniformlyOn_parabolicOuterOrbit (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ)
    {K : Set ℂ} (hK : IsCompact K) (hKD : ∀ w ∈ K, ‖w‖ < 1) :
    TendstoUniformlyOn (parabolicOuterOrbit ν N) (fun _ => Complex.exp (-(N : ℂ)))
      (cocompact ℝ) K := by
  have hcont : ContinuousOn cayleyToUpper K :=
    continuousOn_cayleyToUpper.mono fun w hw => hKD w hw
  have himage : IsCompact (cayleyToUpper '' K) := hK.image_of_continuousOn hcont
  have himpos : ∀ z ∈ cayleyToUpper '' K, 0 < z.im := by
    rintro _ ⟨w, hw, rfl⟩
    exact im_cayleyToUpper_pos (hKD w hw)
  have hcollapse := tendstoUniformlyOn_cauchyTransform_translate_isCompact ν himage himpos
  rw [Metric.tendstoUniformlyOn_iff] at hcollapse ⊢
  intro ε hε
  set eta : ℝ := min (1 / 2) (min (1 / (4 * (N : ℝ) + 1)) (ε / (8 * (N : ℝ) + 8))) with heta
  have hetapos : 0 < eta := by
    refine lt_min (by norm_num) (lt_min ?_ ?_)
    · positivity
    · positivity
  filter_upwards [hcollapse eta hetapos] with t ht
  intro w hw
  have hmsmall : ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖ < eta := by
    have hzmem : cayleyToUpper w ∈ cayleyToUpper '' K := ⟨w, hw, rfl⟩
    have := ht (cayleyToUpper w) hzmem
    simpa [dist_zero_left] using this
  have hm2 : ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖ ≤ 1 / 2 := by
    refine le_of_lt (lt_of_lt_of_le hmsmall ?_)
    rw [heta]
    exact min_le_left _ _
  have hmN : 4 * (N : ℝ) * ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖ ≤ 1 := by
    have hstep : ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖ ≤ 1 / (4 * (N : ℝ) + 1) := by
      refine le_of_lt (lt_of_lt_of_le hmsmall ?_)
      rw [heta]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hpos : 0 < 4 * (N : ℝ) + 1 := by positivity
    have := mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 4 * (N : ℝ))
    calc 4 * (N : ℝ) * ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖
        ≤ 4 * (N : ℝ) * (1 / (4 * (N : ℝ) + 1)) := this
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one hpos]
          linarith
  have hmε : 8 * (N : ℝ) * ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖ < ε := by
    have hstep : ‖cauchyTransform ν (cayleyToUpper w + (t : ℂ))‖ < ε / (8 * (N : ℝ) + 8) := by
      refine lt_of_lt_of_le hmsmall ?_
      rw [heta]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hpos : 0 < 8 * (N : ℝ) + 8 := by positivity
    have hN0 : (0 : ℝ) ≤ 8 * (N : ℝ) := by positivity
    rcases eq_or_lt_of_le hN0 with hzero | hposN
    · rw [← hzero]
      simpa using hε
    · have := mul_lt_mul_of_pos_left hstep hposN
      refine lt_of_lt_of_le this ?_
      rw [mul_div_assoc']
      rw [div_le_iff₀ hpos]
      nlinarith [hε.le]
  have hbound := norm_parabolicOuterOrbit_sub_le ν N t w hm2 hmN
  have hdist : dist ((fun _ : ℂ => Complex.exp (-(N : ℂ))) w) (parabolicOuterOrbit ν N t w)
      = ‖parabolicOuterOrbit ν N t w - Complex.exp (-(N : ℂ))‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  rw [hdist]
  exact lt_of_le_of_lt hbound hmε

end

end GaloisForLFunctions.HTGeometry
