import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.SymmetricHalfCollisionLaw

/-!
# The local de Bruijn–Newman pincer cannot see the strip

At height `X` the local constant is pinched by `c d²/log X ≤ Λ_X ≤ (6600/9991 + ε)/log X` for a
zero of depth `d`. The pincer excludes the depth `d` exactly when `c d² > 6600/9991`; at the
strip depth `8999/24000` this needs `c > 4.69`.

The pair model `F(z) = (z² + δ²) cos(Lz/2)` obeys the Lindelöf-level size bound and has real zeros at
the Riemann–von Mangoldt spacing `2π/L`. At its collision heat `t_* < δ/L` the heated function is

  `H_{t_*}(z) = e^{t_* L²/4} · z · (z cos(Lz/2) + 2 L t_* sin(Lz/2))`  (`pairModelHeat_critical_eq`),

and `w cos w + k sin w` has only real zeros for `k > 0`. So the pair model is real-rooted at `t_*`
(`im_eq_zero_of_pairModelHeat_critical_eq_zero`): its off-line pair lives for less than `δ/L`.
A persistence law `c δ²/L` that also holds for the pair model therefore has `c δ < 1`
(`mul_lt_one_of_pairModel_persistence`), hence `c δ² < δ ≤ ½ < 6600/9991`: the pincer excludes no
depth (`pairModel_persistence_misses_pincer_threshold`). Strip information from `Λ_X` needs a lower
law that fails for the pair model, i.e. one that uses arithmetic.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open RHTower RHTower.DeBruijn

/-- **Collision-heat factorization.** At `t_*` the two branches combine into
`e^{t_* L²/4} z (z cos(Lz/2) + 2 L t_* sin(Lz/2))`. -/
theorem pairModelHeat_critical_eq {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (z : ℂ) :
    pairModelHeat L δ (pairCriticalHeat L δ) z =
      ((Real.exp (pairCriticalHeat L δ * L ^ 2 / 4) : ℝ) : ℂ) * z *
        (z * Complex.cos ((L:ℂ) * z / 2) +
          2 * (L:ℂ) * (pairCriticalHeat L δ : ℂ) * Complex.sin ((L:ℂ) * z / 2)) := by
  obtain ⟨ht, hquad, -, -⟩ := pairCriticalHeat_pos_and_bounds hL hδ
  set t := pairCriticalHeat L δ
  rw [pairModelHeat_eq_closed ht z]
  unfold pairBranch
  have hq : (δ:ℂ) ^ 2 = ((L:ℂ) * (t:ℂ)) ^ 2 + 2 * (t:ℂ) := by exact_mod_cast hquad.symm
  have hneg : (L:ℂ) * (-z) / 2 * I = (-((L:ℂ) * z / 2)) * I := by ring
  rw [hneg, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  linear_combination ((Real.exp (t * L ^ 2 / 4) : ℝ) : ℂ) * Complex.cos ((L:ℂ) * z / 2) * hq +
    (((Real.exp (t * L ^ 2 / 4) : ℝ) : ℂ) * Complex.cos ((L:ℂ) * z / 2) * (L:ℂ) ^ 2 * (t:ℂ) ^ 2 -
      2 * ((Real.exp (t * L ^ 2 / 4) : ℝ) : ℂ) * (L:ℂ) * (t:ℂ) * z *
        Complex.sin ((L:ℂ) * z / 2)) * Complex.I_sq

private theorem re_im_cos (w : ℂ) : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im ∧
    (Complex.cos w).im = -(Real.sin w.re * Real.sinh w.im) := by
  rw [Complex.cos_eq, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]
  constructor
  · simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring

private theorem re_im_sin (w : ℂ) : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im ∧
    (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
  rw [Complex.sin_eq, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]
  constructor
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring

/-- For `k > 0` the function `w cos w + k sin w` vanishes only on the real axis: the imaginary part
of `(w cos w + k sin w) · conj(cos w)` is `Im w · |cos w|² + k cosh(Im w) sinh(Im w)`. -/
theorem mul_cos_add_mul_sin_ne_zero {k : ℝ} (hk : 0 < k) {w : ℂ} (hw : w.im ≠ 0) :
    w * Complex.cos w + (k:ℂ) * Complex.sin w ≠ 0 := by
  intro h
  have hkey : ((w * Complex.cos w + (k:ℂ) * Complex.sin w) * (starRingEnd ℂ) (Complex.cos w)).im =
      w.im * ((Complex.cos w).re ^ 2 + (Complex.cos w).im ^ 2) +
        k * ((Complex.sin w).im * (Complex.cos w).re -
          (Complex.sin w).re * (Complex.cos w).im) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  obtain ⟨hcr, hci⟩ := re_im_cos w
  obtain ⟨hsr, hsi⟩ := re_im_sin w
  rw [h, zero_mul, Complex.zero_im, hcr, hci, hsr, hsi] at hkey
  have hbs : 0 < w.im * Real.sinh w.im := by
    rcases lt_or_gt_of_ne hw with hb | hb
    · exact mul_pos_of_neg_of_neg hb (Real.sinh_neg_iff.mpr hb)
    · exact mul_pos hb (Real.sinh_pos_iff.mpr hb)
  have hpos := mul_pos hk (mul_pos (Real.cosh_pos w.im) hbs)
  have hprod : k * Real.cosh w.im * (w.im * Real.sinh w.im) *
      (Real.sin w.re ^ 2 + Real.cos w.re ^ 2) = k * Real.cosh w.im * (w.im * Real.sinh w.im) := by
    rw [Real.sin_sq_add_cos_sq, mul_one]
  have h2 := congrArg (w.im * ·) hkey
  simp only [mul_zero] at h2
  nlinarith [h2, hprod, hpos, sq_nonneg (w.im * (Real.cos w.re * Real.cosh w.im)),
    sq_nonneg (w.im * (Real.sin w.re * Real.sinh w.im))]

/-- **The pair model is real-rooted at its collision heat.** -/
theorem im_eq_zero_of_pairModelHeat_critical_eq_zero {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {z : ℂ}
    (hz : pairModelHeat L δ (pairCriticalHeat L δ) z = 0) : z.im = 0 := by
  by_contra hne
  obtain ⟨ht, -, -, -⟩ := pairCriticalHeat_pos_and_bounds hL hδ
  set t := pairCriticalHeat L δ
  rw [pairModelHeat_critical_eq hL hδ z] at hz
  have he : ((Real.exp (t * L ^ 2 / 4) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hz0 : z ≠ 0 := fun h => hne (by rw [h, Complex.zero_im])
  set w : ℂ := ((L/2 : ℝ) : ℂ) * z with hwdef
  have hw : w.im ≠ 0 := by
    rw [hwdef, Complex.im_ofReal_mul]
    exact mul_ne_zero (by positivity) hne
  have hLz : (L:ℂ) * z / 2 = w := by rw [hwdef]; push_cast; ring
  rw [hLz] at hz
  have hscale : (L:ℂ) * (z * Complex.cos w + 2 * (L:ℂ) * (t:ℂ) * Complex.sin w) =
      2 * (w * Complex.cos w + ((L ^ 2 * t : ℝ) : ℂ) * Complex.sin w) := by
    rw [hwdef]; push_cast; ring
  have hfac : z * Complex.cos w + 2 * (L:ℂ) * (t:ℂ) * Complex.sin w = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (mul_ne_zero he hz0)
    · exact h
  rw [hfac, mul_zero] at hscale
  exact mul_cos_add_mul_sin_ne_zero (by positivity) hw
    ((mul_eq_zero.mp hscale.symm).resolve_left two_ne_zero)

/-- **Ceiling on persistence laws.** If the pair model keeps a nonreal zero at every heat
`t ∈ (0, c δ²/L]`, then `c δ < 1`: its off-line pair is gone by `t_* < δ/L`. -/
theorem mul_lt_one_of_pairModel_persistence {L δ c : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hpers : ∀ t : ℝ, 0 < t → t ≤ c * δ ^ 2 / L →
      ∃ z : ℂ, pairModelHeat L δ t z = 0 ∧ z.im ≠ 0) :
    c * δ < 1 := by
  by_contra! hc
  obtain ⟨ht, -, -, htL⟩ := pairCriticalHeat_pos_and_bounds hL hδ
  have hδc : δ ≤ c * δ ^ 2 := by nlinarith
  have hle : pairCriticalHeat L δ ≤ c * δ ^ 2 / L :=
    htL.le.trans (div_le_div_of_nonneg_right hδc hL.le)
  obtain ⟨z, hz, him⟩ := hpers _ ht hle
  exact him (im_eq_zero_of_pairModelHeat_critical_eq_zero hL hδ hz)

/-- **The pincer threshold is out of reach.** A persistence constant valid for the pair model at
depth `δ ≤ ½` has `c δ² < 6600/9991`, so with the upper constant `6600/9991` the pincer
`c δ²/log X ≤ Λ_X ≤ (6600/9991 + ε)/log X` excludes no depth. -/
theorem pairModel_persistence_misses_pincer_threshold {L δ c : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1/2)
    (hpers : ∀ t : ℝ, 0 < t → t ≤ c * δ ^ 2 / L →
      ∃ z : ℂ, pairModelHeat L δ t z = 0 ∧ z.im ≠ 0) :
    c * δ ^ 2 < 6600 / 9991 := by
  have h := mul_lt_one_of_pairModel_persistence hL hδ hpers
  have hδδ : c * δ * δ < 1 * δ := mul_lt_mul_of_pos_right h hδ
  nlinarith

/-- At the strip depth `8999/24000` the pincer needs `c > (6600/9991)/(8999/24000)²`, above the
pair-model ceiling `c < 24000/8999`. -/
theorem strip_depth_pincer_gap : (24000/8999 : ℝ) < (6600/9991) / (8999/24000) ^ 2 := by
  norm_num

#print axioms pairModelHeat_critical_eq
#print axioms im_eq_zero_of_pairModelHeat_critical_eq_zero
#print axioms mul_lt_one_of_pairModel_persistence
#print axioms pairModel_persistence_misses_pincer_threshold

end GaloisForLFunctions.ZeroConfigurationGeometry
