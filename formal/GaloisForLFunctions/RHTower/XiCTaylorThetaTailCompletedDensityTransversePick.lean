import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityProjectiveCollision

/-!
# Transverse Pick cone and the zero-free damped Xi channel

The strictly decreasing completed theta density has a derivative completion with positive real
part.  A pointwise two-coordinate estimate strengthens that scalar fact to the transverse cone

`Im(z) * ‖F(z)‖ ≤ Im(z * F(z))`.

The completion target `E(z) = (z^(2 : ℕ) + 1/4)F(z) - 1/4` cannot vanish off the imaginary axis because
the cone would force `‖z^(2 : ℕ) + 1/4‖ ≤ 1/4 - ‖z‖^(2 : ℕ)`, whose squared defect is exactly `Re(z)^(2 : ℕ)`.
On the positive imaginary axis, positivity and unit mass of the density exclude the remaining
case.  Hence `E` is zero-free on the whole open upper half-plane.

The final declarations package the affine pencil joining `E` to its sharp reflection.  Its center
is `2 z^(2 : ℕ) XiC(z)`, so the unresolved RH mechanism is now zero transport from a zero-free endpoint,
not a meromorphic projective chart.  All results here are unconditional.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

lemma phase_re (t : ℝ) (z : ℂ) :
    (spectralTranslationPhase t z).re =
      Real.exp (-t * z.im) * Real.cos (t * z.re) := by
  unfold spectralTranslationPhase
  rw [Complex.exp_re]
  congr 1
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]

lemma phase_im (t : ℝ) (z : ℂ) :
    (spectralTranslationPhase t z).im =
      Real.exp (-t * z.im) * Real.sin (t * z.re) := by
  unfold spectralTranslationPhase
  rw [Complex.exp_im]
  congr 1
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]

lemma pointwise_cone
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 0 < z.im) :
    ‖(I / z) * (1 - spectralTranslationPhase t z)‖ ≤
      (1 - (spectralTranslationPhase t z).re) / z.im := by
  let a : ℝ := Real.exp (-t * z.im)
  let c : ℝ := Real.cos (t * z.re)
  let s : ℝ := Real.sin (t * z.re)
  let d : ℝ := 1 - a * c
  have ha : 0 < a := by exact Real.exp_pos _
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hc : c ≤ 1 := by exact Real.cos_le_one _
  have hd : 0 ≤ d := by
    dsimp [d]
    nlinarith [mul_le_mul_of_nonneg_left hc ha.le]
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hphaseRe : (spectralTranslationPhase t z).re = a * c := by
    simpa [a, c] using phase_re t z
  have hphaseIm : (spectralTranslationPhase t z).im = a * s := by
    simpa [a, s] using phase_im t z
  have hv : 0 ≤ t * z.im := mul_nonneg ht hz.le
  have hexp : Real.exp (t * z.im) * a = 1 := by
    dsimp [a]
    rw [← Real.exp_add]
    ring_nf
    simp
  have had : a * (t * z.im) ≤ d := by
    have h := Real.add_one_le_exp (t * z.im)
    have hm := mul_le_mul_of_nonneg_right h ha.le
    rw [add_mul, hexp] at hm
    have hac : a * c ≤ a := mul_le_of_le_one_right ha.le hc
    dsimp [d]
    nlinarith
  have hsin : |s| ≤ t * |z.re| := by
    dsimp [s]
    calc
      |Real.sin (t * z.re)| ≤ |t * z.re| := Real.abs_sin_le_abs
      _ = t * |z.re| := by rw [abs_mul, abs_of_nonneg ht]
  have hcone : z.im * |a * s| ≤ |z.re| * d := by
    rw [abs_mul, abs_of_pos ha]
    calc
      z.im * (a * |s|) ≤ z.im * (a * (t * |z.re|)) := by gcongr
      _ = |z.re| * (a * (t * z.im)) := by ring
      _ ≤ |z.re| * d := by gcongr
  have hleft : 0 ≤ z.im * ‖1 - spectralTranslationPhase t z‖ :=
    mul_nonneg hz.le (norm_nonneg _)
  have hright : 0 ≤ d * ‖z‖ := mul_nonneg hd (norm_nonneg _)
  have hsquares :
      (z.im * ‖1 - spectralTranslationPhase t z‖) ^ (2 : ℕ) ≤
        (d * ‖z‖) ^ (2 : ℕ) := by
    rw [mul_pow, mul_pow, Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    rw [hphaseRe, hphaseIm]
    have hconeSq := (sq_le_sq₀
      (mul_nonneg hz.le (abs_nonneg (a * s)))
      (mul_nonneg (abs_nonneg z.re) hd)).2 hcone
    rw [mul_pow, mul_pow, sq_abs, sq_abs] at hconeSq
    dsimp [d]
    nlinarith
  have hcross :
      z.im * ‖1 - spectralTranslationPhase t z‖ ≤ d * ‖z‖ :=
    (sq_le_sq₀ hleft hright).1 hsquares
  rw [norm_mul, norm_div, norm_I, one_div, hphaseRe]
  change ‖z‖⁻¹ * ‖1 - spectralTranslationPhase t z‖ ≤ d / z.im
  calc
    ‖z‖⁻¹ * ‖1 - spectralTranslationPhase t z‖ =
        ‖1 - spectralTranslationPhase t z‖ / ‖z‖ := by
          rw [div_eq_mul_inv, mul_comm]
    _ ≤ d / z.im :=
      (div_le_div_iff₀ hznorm hz).2 (by simpa [mul_comm] using hcross)

lemma pointwise_weighted_cone
    {h : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hht : 0 ≤ h t)
    {z : ℂ} (hz : 0 < z.im) :
    ‖(I / z) * ((h t : ℂ) * (1 - spectralTranslationPhase t z))‖ ≤
      (((h t : ℂ) * (1 - spectralTranslationPhase t z)).re) / z.im := by
  have hpoint := pointwise_cone ht hz
  calc
    ‖(I / z) * ((h t : ℂ) * (1 - spectralTranslationPhase t z))‖ =
        h t * ‖(I / z) * (1 - spectralTranslationPhase t z)‖ := by
      rw [show (I / z) * ((h t : ℂ) * (1 - spectralTranslationPhase t z)) =
          (h t : ℂ) * ((I / z) * (1 - spectralTranslationPhase t z)) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hht]
    _ ≤ h t * ((1 - (spectralTranslationPhase t z).re) / z.im) := by
      gcongr
    _ = (((h t : ℂ) * (1 - spectralTranslationPhase t z)).re) / z.im := by
      simp [Complex.mul_re]
      ring

theorem norm_I_div_mul_positiveTailCompletion_le_re_div
    {h : ℝ → ℝ} {z : ℂ} (hz : 0 < z.im)
    (hh : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ h t)
    (hcompletion : IntegrableOn (fun t : ℝ =>
      (h t : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0)) :
    ‖(I / z) * positiveTailCompletion h z‖ ≤
      (positiveTailCompletion h z).re / z.im := by
  let f : ℝ → ℂ := fun t =>
    (h t : ℂ) * (1 - spectralTranslationPhase t z)
  let q : ℂ := I / z
  have hf : Integrable f (volume.restrict (Ioi 0)) := hcompletion
  have hqf : Integrable (fun t => q * f t) (volume.restrict (Ioi 0)) :=
    hf.const_mul q
  have hmajor : Integrable (fun t => (f t).re / z.im)
      (volume.restrict (Ioi 0)) := hf.re.div_const z.im
  calc
    ‖(I / z) * positiveTailCompletion h z‖ =
        ‖∫ t : ℝ in Ioi 0, q * f t‖ := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ ≤ ∫ t : ℝ in Ioi 0, ‖q * f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 0, (f t).re / z.im := by
      apply MeasureTheory.integral_mono_ae hqf.norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact pointwise_weighted_cone ht.le (hh t ht) hz
    _ = (positiveTailCompletion h z).re / z.im := by
      rw [MeasureTheory.integral_div]
      have hre :
          (∫ t : ℝ in Ioi 0, (f t).re) =
            (∫ t : ℝ in Ioi 0, f t).re :=
        integral_re (μ := volume.restrict (Ioi 0)) hf
      rw [hre]
      rfl

/-- Transverse Pick cone for the canonical completed-density phase. -/
theorem thetaCuspTailSecondDensityPhaseValue_transversePickCone
    {z : ℂ} (hz : 0 < z.im) :
    ‖thetaCuspTailSecondDensityPhaseValue z‖ ≤
      (z * thetaCuspTailSecondDensityPhaseValue z).im / z.im := by
  let h : ℝ → ℝ := fun t => -(4 * thetaCuspTailDerivative 3 t)
  have hcone := norm_I_div_mul_positiveTailCompletion_le_re_div hz
    (h := h)
    (fun t ht => (neg_thetaCuspTailSecondDensityDerivative_pos ht.le).le)
    (by simpa only [h] using
      integrableOn_neg_thetaCuspTailSecondDensityDerivative_mul_one_sub_phase hz.le)
  have hcompletion : positiveTailCompletion h z =
      -I * z * thetaCuspTailSecondDensityPhaseValue z := by
    simpa only [h] using
      positiveTailCompletion_neg_thetaCuspTailSecondDensityDerivative_eq hz.le
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  have hleft : (I / z) * positiveTailCompletion h z =
      thetaCuspTailSecondDensityPhaseValue z := by
    rw [hcompletion]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hright : (positiveTailCompletion h z).re =
      (z * thetaCuspTailSecondDensityPhaseValue z).im := by
    rw [hcompletion]
    simp only [Complex.mul_re, Complex.mul_im, neg_re, neg_im, I_re, I_im]
    ring
  rwa [hleft, hright] at hcone

lemma completedQuadraticTarget_not_in_transversePickCone
    {z f : ℂ} (hz : 0 < z.im) (hx : z.re ≠ 0)
    (htarget : (z ^ (2 : ℕ) + 1 / 4) * f = 1 / 4) :
    ¬ ‖f‖ ≤ (z * f).im / z.im := by
  intro hcone
  let q : ℂ := z ^ (2 : ℕ) + 1 / 4
  let x : ℝ := z.re
  let y : ℝ := z.im
  let u : ℝ := f.re
  let v : ℝ := f.im
  let a : ℝ := x ^ (2 : ℕ) - y ^ (2 : ℕ) + 1 / 4
  let b : ℝ := 2 * x * y
  let D : ℝ := a ^ (2 : ℕ) + b ^ (2 : ℕ)
  have hqtarget : q * f = 1 / 4 := by simpa only [q] using htarget
  have hq0 : q ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hqtarget
    norm_num at hqtarget
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hqre : q.re = a := by
    dsimp [q, a, x, y]
    simp only [pow_two, Complex.mul_re]
    norm_num
  have hqim : q.im = b := by
    dsimp [q, b, x, y]
    simp only [pow_two, Complex.mul_im]
    norm_num
    ring
  have hD : Complex.normSq q = D := by
    rw [Complex.normSq_apply, hqre, hqim]
    dsimp only [D]
    ring
  have hDnorm : D = ‖q‖ ^ (2 : ℕ) := by
    rw [← hD, ← Complex.sq_norm]
  have hDpos : 0 < D := by rw [hDnorm]; positivity
  have hre := congrArg Complex.re hqtarget
  have him := congrArg Complex.im hqtarget
  have hre' : a * u - b * v = 1 / 4 := by
    norm_num [Complex.mul_re, hqre, hqim, u, v] at hre
    exact hre
  have him' : a * v + b * u = 0 := by
    norm_num [Complex.mul_im, hqre, hqim, u, v] at him
    exact him
  have hDu : 4 * D * u = a := by
    dsimp only [D]
    linear_combination 4 * a * hre' + 4 * b * him'
  have hDv : 4 * D * v = -b := by
    dsimp only [D]
    linear_combination 4 * a * him' - 4 * b * hre'
  have hphase : 4 * D * (z * f).im =
      y * (1 / 4 - (x ^ (2 : ℕ) + y ^ (2 : ℕ))) := by
    simp only [Complex.mul_im]
    change 4 * D * (x * v + y * u) =
      y * (1 / 4 - (x ^ (2 : ℕ) + y ^ (2 : ℕ)))
    dsimp only [a, b] at hDu hDv
    linear_combination x * hDv + y * hDu
  have hnormtarget := congrArg norm hqtarget
  have hqfNorm : 4 * ‖q‖ * ‖f‖ = 1 := by
    norm_num [norm_mul] at hnormtarget
    nlinarith
  have hscaledNorm : 4 * D * ‖f‖ = ‖q‖ := by
    rw [hDnorm]
    nlinarith
  have hcross : y * ‖f‖ ≤ (z * f).im := by
    have h := (le_div_iff₀ hz).mp hcone
    simpa only [y, mul_comm] using h
  have hscaled : y * ‖q‖ ≤ y * (1 / 4 - (x ^ (2 : ℕ) + y ^ (2 : ℕ))) := by
    have hm := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 4 * D by positivity)
    rw [show 4 * D * (y * ‖f‖) = y * (4 * D * ‖f‖) by ring,
      hscaledNorm, hphase] at hm
    exact hm
  have hqle : ‖q‖ ≤ 1 / 4 - (x ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
    exact le_of_mul_le_mul_left (by simpa only [y] using hscaled) hz
  have hrightnonneg : 0 ≤ 1 / 4 - (x ^ (2 : ℕ) + y ^ (2 : ℕ)) :=
    le_trans (norm_nonneg q) hqle
  have hsquare : ‖q‖ ^ (2 : ℕ) ≤ (1 / 4 - (x ^ (2 : ℕ) + y ^ (2 : ℕ))) ^ (2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg q) hrightnonneg).2 hqle
  have hidentity : D - (1 / 4 - (x ^ (2 : ℕ) + y ^ (2 : ℕ))) ^ (2 : ℕ) = x ^ (2 : ℕ) := by
    dsimp only [D, a, b]
    ring
  rw [← hDnorm] at hsquare
  have hxSq : x ^ (2 : ℕ) ≤ 0 := by nlinarith only [hsquare, hidentity]
  have hxzero : x = 0 := sq_eq_zero_iff.mp (le_antisymm hxSq (sq_nonneg x))
  exact hx (by simpa only [x] using hxzero)

theorem thetaCuspTailSecondDensityDeBrangesE_ne_zero_of_re_ne_zero
    {z : ℂ} (hz : 0 < z.im) (hx : z.re ≠ 0) :
    thetaCuspTailSecondDensityDeBrangesE z ≠ 0 := by
  intro hE
  have htarget : (z ^ (2 : ℕ) + 1 / 4) *
      thetaCuspTailSecondDensityPhaseValue z = 1 / 4 := by
    unfold thetaCuspTailSecondDensityDeBrangesE at hE
    exact sub_eq_zero.mp hE
  exact (completedQuadraticTarget_not_in_transversePickCone hz hx htarget)
    (thetaCuspTailSecondDensityPhaseValue_transversePickCone hz)

theorem thetaCuspTailSecondDensityRealLaplace_nonneg
    (v : ℝ) :
    0 ≤ thetaCuspTailSecondDensityRealLaplace v := by
  unfold thetaCuspTailSecondDensityRealLaplace
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (thetaCuspTailSecondDensity_pos hx).le (Real.exp_pos _).le

theorem thetaCuspTailSecondDensityRealLaplace_le_one
    {v : ℝ} (hv : 0 ≤ v) :
    thetaCuspTailSecondDensityRealLaplace v ≤ 1 := by
  have hf := integrableOn_thetaCuspTailSecondDensity_mul_exp_neg
    (v := v) (by linarith)
  have hg : IntegrableOn thetaCuspTailSecondDensity (Ioi 0) := by
    simpa only [pow_zero, one_mul] using
      integrableOn_pow_mul_thetaCuspTailSecondDensity 0
  unfold thetaCuspTailSecondDensityRealLaplace
  rw [← integral_thetaCuspTailSecondDensity]
  apply integral_mono_ae hf hg
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hrho := (thetaCuspTailSecondDensity_pos hx).le
  have hexp : Real.exp (-v * x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) hx.le
  exact mul_le_of_le_one_right hrho hexp

theorem thetaCuspTailSecondDensityDeBrangesE_I_mul_ne_zero
    {v : ℝ} (hv : 0 < v) :
    thetaCuspTailSecondDensityDeBrangesE (I * (v : ℂ)) ≠ 0 := by
  rw [thetaCuspTailSecondDensityDeBrangesE_I_mul]
  intro hzero
  have htarget : (1 / 4 - v ^ (2 : ℕ)) *
      thetaCuspTailSecondDensityRealLaplace v = 1 / 4 := by
    have hreal : (1 / 4 - v ^ (2 : ℕ)) *
        thetaCuspTailSecondDensityRealLaplace v - 1 / 4 = 0 := by
      exact_mod_cast hzero
    exact sub_eq_zero.mp hreal
  by_cases hvhalf : v < 1 / 2
  · have hqpos : 0 < 1 / 4 - v ^ (2 : ℕ) := by nlinarith
    have hLle := thetaCuspTailSecondDensityRealLaplace_le_one hv.le
    have hprodle : (1 / 4 - v ^ (2 : ℕ)) *
        thetaCuspTailSecondDensityRealLaplace v ≤ 1 / 4 - v ^ (2 : ℕ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hLle hqpos.le
    nlinarith [sq_pos_of_pos hv]
  · have hqnonpos : 1 / 4 - v ^ (2 : ℕ) ≤ 0 := by nlinarith
    have hLnonneg := thetaCuspTailSecondDensityRealLaplace_nonneg v
    have hprodnonpos : (1 / 4 - v ^ (2 : ℕ)) *
        thetaCuspTailSecondDensityRealLaplace v ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hqnonpos hLnonneg
    nlinarith

/-- The completed-density source channel has no zero in the open upper half-plane. -/
theorem thetaCuspTailSecondDensityDeBrangesE_ne_zero
    {z : ℂ} (hz : 0 < z.im) :
    thetaCuspTailSecondDensityDeBrangesE z ≠ 0 := by
  by_cases hx : z.re = 0
  · have hzform : z = I * (z.im : ℂ) := by
      apply Complex.ext
      · simp [hx]
      · simp
    rw [hzform]
    exact thetaCuspTailSecondDensityDeBrangesE_I_mul_ne_zero hz
  · exact thetaCuspTailSecondDensityDeBrangesE_ne_zero_of_re_ne_zero hz hx

/-- Affine source-to-reflection pencil.  Its center is the completed Xi channel and its positive
endpoint is the upper-zero-free damped channel. -/
def thetaCuspTailSecondDensityDeBrangesAffinePencil (tau : ℝ) (z : ℂ) : ℂ :=
  ((1 + tau) / 2 : ℝ) * thetaCuspTailSecondDensityDeBrangesE z +
    ((1 - tau) / 2 : ℝ) * thetaCuspTailSecondDensityDeBrangesESharp z

theorem thetaCuspTailSecondDensityDeBrangesAffinePencil_one (z : ℂ) :
    thetaCuspTailSecondDensityDeBrangesAffinePencil 1 z =
      thetaCuspTailSecondDensityDeBrangesE z := by
  simp [thetaCuspTailSecondDensityDeBrangesAffinePencil]

theorem thetaCuspTailSecondDensityDeBrangesAffinePencil_neg_one (z : ℂ) :
    thetaCuspTailSecondDensityDeBrangesAffinePencil (-1) z =
      thetaCuspTailSecondDensityDeBrangesESharp z := by
  simp [thetaCuspTailSecondDensityDeBrangesAffinePencil]

theorem thetaCuspTailSecondDensityDeBrangesAffinePencil_zero
    {z : ℂ} (hz : |z.im| < 1) :
    thetaCuspTailSecondDensityDeBrangesAffinePencil 0 z =
      2 * z ^ (2 : ℕ) * XiC z := by
  have hsum := thetaCuspTailSecondDensityDeBrangesE_add_sharp hz
  unfold thetaCuspTailSecondDensityDeBrangesAffinePencil
  norm_num
  linear_combination (1 / 2 : ℂ) * hsum

/-- Upper zero-freeness removes the regular-chart premise from the projective Xi collision law. -/
theorem thetaCuspTailSecondDensityDeBrangesProjectiveRatio_eq_neg_one_iff_upper
    {z : ℂ} (hz : 0 < z.im) (hz1 : z.im < 1) :
    thetaCuspTailSecondDensityDeBrangesProjectiveRatio z = -1 ↔ XiC z = 0 := by
  have hzstrip : |z.im| < 1 := by
    rw [abs_of_pos hz]
    exact hz1
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  exact thetaCuspTailSecondDensityDeBrangesProjectiveRatio_eq_neg_one_iff
    hzstrip hz0 (thetaCuspTailSecondDensityDeBrangesE_ne_zero hz)

end

end RHTower
