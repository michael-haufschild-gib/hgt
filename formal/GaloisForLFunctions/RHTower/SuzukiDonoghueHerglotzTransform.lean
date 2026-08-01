import GaloisForLFunctions.RHTower.SuzukiEndpointNevanlinnaMass

/-!
# The Donoghue transform is a Herglotz function, and its Cayley transform is Schur

The rigidity chain of a Suzuki carrier runs

`jets -> Donoghue probability -> m -> Theta -> phi`.

This module builds the two middle objects and proves the properties that make them what they are.

The Donoghue kernel is a *probability* kernel because its imaginary part above the real axis is

`Im K_z (t) = Im z * (t² + 1) / |t - z|²`,

strictly positive for every real `t`.  Integrating against a compactified spectral probability
therefore lands strictly inside the upper half plane, so the Donoghue transform is a Herglotz
function.  Its Cayley transform then lands strictly inside the unit disc, so it is a Schur function.

Both facts are unconditional and use nothing about the carrier beyond the measure being a
probability measure on the compact projective interval.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory Filter Topology

/-! ## The Donoghue kernel is a probability kernel -/

/-- **Exact imaginary part of the Donoghue kernel.**  Read through the Möbius form, the imaginary
part is the height times `t² + 1` over the squared distance to the spectral parameter. -/
theorem im_suzukiDonoghueKernel {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    (suzukiDonoghueKernel t z).im
      = z.im * (t ^ 2 + 1) / Complex.normSq ((t : ℂ) - z) := by
  have hd : ((t : ℂ) - z) ≠ 0 := suzukiDonoghueDenom_ne_zero hz t
  have hns : Complex.normSq ((t : ℂ) - z) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hd)
  rw [suzukiDonoghueKernel_eq_mobius hd, Complex.div_im]
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  field_simp
  ring

/-- The Donoghue kernel maps the upper half plane into itself, for every real spectral point. -/
theorem im_suzukiDonoghueKernel_pos {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    0 < (suzukiDonoghueKernel t z).im := by
  have hd : ((t : ℂ) - z) ≠ 0 := suzukiDonoghueDenom_ne_zero hz t
  have hns : 0 < Complex.normSq ((t : ℂ) - z) := Complex.normSq_pos.mpr hd
  rw [im_suzukiDonoghueKernel hz t]
  refine div_pos ?_ hns
  nlinarith [sq_nonneg t]

theorem im_projectiveDonoghueKernel_pos {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    0 < (projectiveDonoghueKernel t z).im :=
  im_suzukiDonoghueKernel_pos hz _

/-- The extended kernel is in the open upper half plane at every point of the closed projective
interval, including the two endpoints, where it equals the spectral parameter itself. -/
theorem im_extendedProjectiveKernel_pos {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    0 < (extendedProjectiveKernel t z).im := by
  rw [extendedProjectiveKernel]
  split_ifs with h
  · exact im_projectiveDonoghueKernel_pos hz t
  · exact hz

/-! ## The Donoghue transform -/

instance : Nonempty ↥projectiveInterval := ⟨projectiveLeft⟩

/-- The Donoghue transform of a compactified spectral probability. -/
noncomputable def donoghueTransform (nu : Measure ↥projectiveInterval) (z : ℂ) : ℂ :=
  ∫ t, extendedProjectiveKernel (t : ℝ) z ∂nu

/-- **The Donoghue transform is a Herglotz function.**  The kernel is strictly in the upper half
plane at every point of the compact projective interval, so a continuous positive minimum exists
and the integral against a probability measure inherits it. -/
theorem im_donoghueTransform_pos (nu : Measure ↥projectiveInterval) [IsProbabilityMeasure nu]
    {z : ℂ} (hz : 0 < z.im) : 0 < (donoghueTransform nu z).im := by
  have hint := integrable_extendedProjectiveKernel nu hz
  have hcont : Continuous (fun t : ↥projectiveInterval =>
      (extendedProjectiveKernel (t : ℝ) z).im) :=
    Complex.continuous_im.comp ((continuousOn_extendedProjectiveKernel hz).restrict)
  obtain ⟨t0, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
  have hcpos : 0 < (extendedProjectiveKernel (t0 : ℝ) z).im :=
    im_extendedProjectiveKernel_pos hz _
  have hle : ∀ t : ↥projectiveInterval,
      (extendedProjectiveKernel (t0 : ℝ) z).im ≤ (extendedProjectiveKernel (t : ℝ) z).im :=
    fun t => hmin (Set.mem_univ t)
  have hIm : (donoghueTransform nu z).im
      = ∫ t, (extendedProjectiveKernel (t : ℝ) z).im ∂nu := (integral_im hint).symm
  have hconst : ∫ (_ : ↥projectiveInterval), (extendedProjectiveKernel (t0 : ℝ) z).im ∂nu
      = (extendedProjectiveKernel (t0 : ℝ) z).im := by simp
  have hge : (extendedProjectiveKernel (t0 : ℝ) z).im
      ≤ ∫ t, (extendedProjectiveKernel (t : ℝ) z).im ∂nu := by
    rw [← hconst]
    exact integral_mono (integrable_const _) hint.im hle
  rw [hIm]
  linarith

/-! ## The Cayley transform is Schur -/

/-- The Cayley transform carrying the upper half plane to the unit disc. -/
noncomputable def cayleyOfHerglotz (m : ℂ) : ℂ := (m - Complex.I) / (m + Complex.I)

theorem cayleyOfHerglotz_denom_ne_zero {m : ℂ} (hm : 0 < m.im) : m + Complex.I ≠ 0 := by
  intro h
  have him : (m + Complex.I).im = 0 := by rw [h]; simp
  simp only [Complex.add_im, Complex.I_im] at him
  linarith

/-- **The Cayley transform of a Herglotz value is Schur.**  A point strictly above the real axis is
strictly closer to `i` than to `-i`. -/
theorem normSq_cayleyOfHerglotz_lt_one {m : ℂ} (hm : 0 < m.im) :
    Complex.normSq (cayleyOfHerglotz m) < 1 := by
  have hne := cayleyOfHerglotz_denom_ne_zero hm
  have hpos : 0 < Complex.normSq (m + Complex.I) := Complex.normSq_pos.mpr hne
  rw [cayleyOfHerglotz, Complex.normSq_div, div_lt_one hpos]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im]
  nlinarith [hm]

/-- **The Cayley transform of the Donoghue transform is Schur.**  This is the inner function `Theta`
of the rigidity chain, built from the spectral probability alone. -/
theorem normSq_cayleyOfHerglotz_donoghueTransform_lt_one
    (nu : Measure ↥projectiveInterval) [IsProbabilityMeasure nu] {z : ℂ} (hz : 0 < z.im) :
    Complex.normSq (cayleyOfHerglotz (donoghueTransform nu z)) < 1 :=
  normSq_cayleyOfHerglotz_lt_one (im_donoghueTransform_pos nu hz)

/-! ## The Cayley transform is invertible

The inverse is the parent card's `(1)`, `m = i (1 + Theta) / (1 - Theta)`.  The Cayley value is
never `1`, so the inversion has no side condition beyond the one already needed to form it. -/

/-- The inverse Cayley transform, carrying the disc back to the upper half plane. -/
noncomputable def herglotzOfCayley (Θ : ℂ) : ℂ := Complex.I * (1 + Θ) / (1 - Θ)

/-- **Derivative of the Cayley--Herglotz transform.**  `d/dΘ [I(1+Θ)/(1-Θ)] = 2I/(1-Θ)^2`, away
from the excluded value `Θ = 1`.  This is the factor that converts a logarithmic derivative of the
characteristic into a derivative of the Herglotz function. -/
theorem hasDerivAt_herglotzOfCayley {Θ : ℂ} (h : Θ ≠ 1) :
    HasDerivAt herglotzOfCayley (2 * Complex.I / (1 - Θ) ^ 2) Θ := by
  have hv : (1 : ℂ) - Θ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hu : HasDerivAt (fun w : ℂ => Complex.I * (1 + w)) Complex.I Θ := by
    simpa using ((hasDerivAt_id Θ).const_add (1 : ℂ)).const_mul Complex.I
  have hvd : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) Θ := by
    simpa using (hasDerivAt_id Θ).const_sub (1 : ℂ)
  have hdiv := hu.div hvd hv
  have hfun : herglotzOfCayley
      = (fun w : ℂ => Complex.I * (1 + w)) / (fun w : ℂ => (1 : ℂ) - w) := rfl
  rw [hfun, show (2 : ℂ) * Complex.I / (1 - Θ) ^ 2
      = (Complex.I * (1 - Θ) - Complex.I * (1 + Θ) * (-1)) / (1 - Θ) ^ 2 by ring]
  exact hdiv

/-- **Chain rule for the Cayley--Herglotz transform.**  Composing with a characteristic multiplies
the transform's derivative by the characteristic's, which is the form `(16)`--`(18)` use. -/
theorem hasDerivAt_herglotzOfCayley_comp {Θ : ℂ → ℂ} {Θ' z : ℂ}
    (hΘ : HasDerivAt Θ Θ' z) (h : Θ z ≠ 1) :
    HasDerivAt (fun w => herglotzOfCayley (Θ w))
      (2 * Complex.I / (1 - Θ z) ^ 2 * Θ') z :=
  (hasDerivAt_herglotzOfCayley h).comp z hΘ

/-- **Derivative of the inverse Cayley transform.**  `d/dm [(m - I)/(m + I)] = 2I/(m + I)^2`, away
from the excluded value `m = -I`. -/
theorem hasDerivAt_cayleyOfHerglotz {m : ℂ} (h : m + Complex.I ≠ 0) :
    HasDerivAt cayleyOfHerglotz (2 * Complex.I / (m + Complex.I) ^ 2) m := by
  have hu : HasDerivAt (fun w : ℂ => w - Complex.I) 1 m := by
    simpa using (hasDerivAt_id m).sub_const Complex.I
  have hv : HasDerivAt (fun w : ℂ => w + Complex.I) 1 m := by
    simpa using (hasDerivAt_id m).add_const Complex.I
  have hdiv := hu.div hv h
  have hfun : cayleyOfHerglotz
      = (fun w : ℂ => w - Complex.I) / (fun w : ℂ => w + Complex.I) := rfl
  rw [hfun, show (2 : ℂ) * Complex.I / (m + Complex.I) ^ 2
      = (1 * (m + Complex.I) - (m - Complex.I) * 1) / (m + Complex.I) ^ 2 by ring]
  exact hdiv

/-- Chain rule for the inverse Cayley transform, completing the pair. -/
theorem hasDerivAt_cayleyOfHerglotz_comp {m : ℂ → ℂ} {m' z : ℂ}
    (hm : HasDerivAt m m' z) (h : m z + Complex.I ≠ 0) :
    HasDerivAt (fun w => cayleyOfHerglotz (m w))
      (2 * Complex.I / (m z + Complex.I) ^ 2 * m') z :=
  (hasDerivAt_cayleyOfHerglotz h).comp z hm

/-- The inverse Cayley transform is differentiable away from its excluded value. -/
theorem differentiableAt_cayleyOfHerglotz {m : ℂ} (h : m + Complex.I ≠ 0) :
    DifferentiableAt ℂ cayleyOfHerglotz m :=
  (hasDerivAt_cayleyOfHerglotz h).differentiableAt

/-- The Cayley--Herglotz transform is differentiable away from the excluded value, which is the
form the chain rule needs when it is composed with a characteristic. -/
theorem differentiableAt_herglotzOfCayley {Θ : ℂ} (h : Θ ≠ 1) :
    DifferentiableAt ℂ herglotzOfCayley Θ :=
  (hasDerivAt_herglotzOfCayley h).differentiableAt

/-- The Cayley value is never `1`. -/
theorem cayleyOfHerglotz_ne_one {m : ℂ} (h : m + Complex.I ≠ 0) : cayleyOfHerglotz m ≠ 1 := by
  intro hc
  rw [cayleyOfHerglotz, div_eq_one_iff_eq h] at hc
  have : (2 : ℂ) * Complex.I = 0 := by linear_combination -hc
  simp at this

theorem one_sub_cayleyOfHerglotz {m : ℂ} (h : m + Complex.I ≠ 0) :
    1 - cayleyOfHerglotz m = (2 * Complex.I) / (m + Complex.I) := by
  rw [cayleyOfHerglotz, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h, one_mul]
  ring

/-- **`(1)`.**  The Cayley transform inverts to `m = i (1 + Theta) / (1 - Theta)`. -/
theorem herglotzOfCayley_cayleyOfHerglotz {m : ℂ} (h : m + Complex.I ≠ 0) :
    herglotzOfCayley (cayleyOfHerglotz m) = m := by
  have hne : (1 : ℂ) - cayleyOfHerglotz m ≠ 0 := by
    rw [one_sub_cayleyOfHerglotz h]
    exact div_ne_zero (by simp) h
  rw [herglotzOfCayley, div_eq_iff hne, one_sub_cayleyOfHerglotz h, cayleyOfHerglotz]
  field_simp
  ring

/-- The other direction: every disc value other than `1` comes from a Herglotz value. -/
theorem cayleyOfHerglotz_herglotzOfCayley {Θ : ℂ} (h : Θ ≠ 1) :
    cayleyOfHerglotz (herglotzOfCayley Θ) = Θ := by
  have hne : (1 : ℂ) - Θ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hden : herglotzOfCayley Θ + Complex.I = (2 * Complex.I) / (1 - Θ) := by
    rw [herglotzOfCayley, div_add' _ _ _ hne]
    field_simp
    ring
  have hdne : herglotzOfCayley Θ + Complex.I ≠ 0 := by
    rw [hden]
    exact div_ne_zero (by simp) hne
  rw [cayleyOfHerglotz, div_eq_iff hdne, hden, herglotzOfCayley]
  field_simp
  ring

/-- **Exact imaginary part of the inverse Cayley transform.**  `Im (i(1+w)/(1-w))` is
`Re ((1+w)/(1-w))`, which is `(1 - |w|²)/|1-w|²`. -/
theorem im_herglotzOfCayley {w : ℂ} (hw : w ≠ 1) :
    (herglotzOfCayley w).im = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hns : Complex.normSq ((1 : ℂ) - w) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hne)
  rw [herglotzOfCayley, Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  field_simp
  ring

/-- **The inverse Cayley transform carries the disc into the upper half plane.**  Together with the
Schur bound this makes the correspondence a bijection between the two domains, not merely between
values. -/
theorem im_herglotzOfCayley_pos {w : ℂ} (hw : Complex.normSq w < 1) :
    0 < (herglotzOfCayley w).im := by
  have hne : w ≠ 1 := by
    intro h
    rw [h] at hw
    simp at hw
  rw [im_herglotzOfCayley hne]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hne)))

/-- The anchor: the Cayley transform vanishes exactly at `i`, which is the point the Blaschke factor
of `(8)` is anchored at. -/
theorem cayleyOfHerglotz_I : cayleyOfHerglotz Complex.I = 0 := by
  rw [cayleyOfHerglotz, sub_self, zero_div]

theorem herglotzOfCayley_zero : herglotzOfCayley 0 = Complex.I := by
  rw [herglotzOfCayley]
  norm_num

/-- **`(8)`, the Blaschke bound.**  An inner function of the upper half plane anchored at `i` is
dominated by the Blaschke factor `b_i = (z-i)/(z+i)`.  Transferring to the disc by the inverse
Cayley transform turns the statement into the Schwarz lemma at the origin, since the anchor `i` is
the inverse Cayley image of `0`.

This is what makes the quotient `Theta / b_i` of `(8)` a Schur function: it is exactly the
inequality `|Theta| <= |b_i|`. -/
theorem norm_le_norm_cayleyOfHerglotz_of_mapsTo {Θ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ (fun w => Θ (herglotzOfCayley w)) (Metric.ball 0 1))
    (hmaps : Set.MapsTo (fun w => Θ (herglotzOfCayley w))
      (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hanchor : Θ Complex.I = 0) {z : ℂ} (hz : 0 < z.im) :
    ‖Θ z‖ ≤ ‖cayleyOfHerglotz z‖ := by
  have hden : z + Complex.I ≠ 0 := by
    intro hc
    have him : (z + Complex.I).im = 0 := by rw [hc]; simp
    simp only [Complex.add_im, Complex.I_im] at him
    linarith
  have hball : ‖cayleyOfHerglotz z‖ < 1 := by
    have hsq := normSq_cayleyOfHerglotz_lt_one hz
    have hnn : 0 ≤ ‖cayleyOfHerglotz z‖ := norm_nonneg _
    nlinarith [Complex.normSq_eq_norm_sq (cayleyOfHerglotz z)]
  have hzero : (fun w => Θ (herglotzOfCayley w)) 0 = 0 := by
    simp only [herglotzOfCayley_zero]
    exact hanchor
  have hschwarz := Complex.norm_le_norm_of_mapsTo_ball hd hmaps hzero hball
  rwa [herglotzOfCayley_cayleyOfHerglotz hden] at hschwarz

/-! ## The middle links of the rigidity chain -/

/-- Equal spectral probabilities give equal Herglotz transforms: the `sigma -> m` link. -/
theorem donoghueTransform_congr {nu1 nu2 : Measure ↥projectiveInterval}
    (h : nu1 = nu2) (z : ℂ) : donoghueTransform nu1 z = donoghueTransform nu2 z := by
  rw [h]

/-- Equal spectral probabilities give equal inner functions: the `sigma -> m -> Theta` links
composed.  These are the two links the rigidity chain calls function applications; with the
Herglotz and Schur properties above they are now genuine objects rather than notation. -/
theorem cayleyOfHerglotz_donoghueTransform_congr {nu1 nu2 : Measure ↥projectiveInterval}
    (h : nu1 = nu2) (z : ℂ) :
    cayleyOfHerglotz (donoghueTransform nu1 z) = cayleyOfHerglotz (donoghueTransform nu2 z) := by
  rw [h]

end GaloisForLFunctions.RHTower
