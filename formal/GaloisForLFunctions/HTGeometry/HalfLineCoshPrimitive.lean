import Mathlib
import GaloisForLFunctions.HTGeometry.HalfLineAutocorrelationPrimitive

/-!
# The decaying branch and the cosh combination

The growing branch of the autocorrelation needs the primitive identity, because `exp(h/2)` is not
integrable.  The decaying branch needs nothing: `exp(-h/2)` has total mass `2` on the half-line, so
a uniform bound on the autocorrelation bounds its weighted integral outright.

Adding the two branches gives the `cosh` combination, which is the form the polar source estimate
consumes.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace HTGeometry

theorem integral_exp_neg_half_le_two {H : ℝ} (hH : 0 ≤ H) :
    (∫ h in Ioc (0 : ℝ) H, Real.exp (-h / 2)) ≤ 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) H,
      HasDerivAt (fun t : ℝ => -2 * Real.exp (-t / 2)) (Real.exp (-x / 2)) x := by
    intro x _
    have hinner : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2 : ℝ) x := by
      simpa using ((hasDerivAt_id x).neg.div_const 2)
    have h := (hinner.exp).const_mul (-2 : ℝ)
    have hval : (-2 : ℝ) * (Real.exp (-x / 2) * (-1 / 2)) = Real.exp (-x / 2) := by ring
    rwa [hval] at h
  have hint : IntervalIntegrable (fun h : ℝ => Real.exp (-h / 2)) volume 0 H := by
    refine ContinuousOn.intervalIntegrable ?_
    exact (Real.continuous_exp.comp (continuous_neg.div_const 2)).continuousOn
  have hftc : (∫ h in (0 : ℝ)..H, Real.exp (-h / 2))
      = -2 * Real.exp (-H / 2) - -2 * Real.exp (-(0 : ℝ) / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hIoc : (∫ h in Ioc (0 : ℝ) H, Real.exp (-h / 2))
      = ∫ h in (0 : ℝ)..H, Real.exp (-h / 2) := (intervalIntegral.integral_of_le hH).symm
  rw [hIoc, hftc]
  have hpos : (0 : ℝ) < Real.exp (-H / 2) := Real.exp_pos _
  norm_num
  linarith

/-- **The decaying branch.**  A uniform bound on the autocorrelation bounds its `exp(-h/2)`-weighted
integral by twice that bound, with no primitive and no Fubini. -/
theorem abs_integral_exp_neg_half_mul_autocorrelation_le
    (R : ℝ → ℝ) {H N : ℝ} (hH : 0 ≤ H) (hN : 0 ≤ N)
    (hbound : ∀ h : ℝ, 0 ≤ h → |halfLineAutocorrelation R h| ≤ N)
    (hint : IntegrableOn
      (fun h : ℝ => Real.exp (-h / 2) * halfLineAutocorrelation R h) (Ioc 0 H)) :
    |∫ h in Ioc (0 : ℝ) H, Real.exp (-h / 2) * halfLineAutocorrelation R h| ≤ 2 * N := by
  have hexpII : IntervalIntegrable (fun h : ℝ => Real.exp (-h / 2)) volume 0 H := by
    refine ContinuousOn.intervalIntegrable ?_
    exact (Real.continuous_exp.comp (continuous_neg.div_const 2)).continuousOn
  have hexpint : IntegrableOn (fun h : ℝ => N * Real.exp (-h / 2)) (Ioc 0 H) :=
    (hexpII.1).const_mul N
  calc |∫ h in Ioc (0 : ℝ) H, Real.exp (-h / 2) * halfLineAutocorrelation R h|
      ≤ ∫ h in Ioc (0 : ℝ) H, |Real.exp (-h / 2) * halfLineAutocorrelation R h| := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := volume.restrict (Ioc (0 : ℝ) H))
            (fun h : ℝ => Real.exp (-h / 2) * halfLineAutocorrelation R h))
    _ ≤ ∫ h in Ioc (0 : ℝ) H, N * Real.exp (-h / 2) := by
        refine integral_mono_ae hint.abs hexpint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have := hbound h (le_of_lt hh.1)
        nlinarith [Real.exp_pos (-h / 2), abs_nonneg (halfLineAutocorrelation R h)]
    _ = N * ∫ h in Ioc (0 : ℝ) H, Real.exp (-h / 2) := integral_const_mul N _
    _ ≤ N * 2 := mul_le_mul_of_nonneg_left (integral_exp_neg_half_le_two hH) hN
    _ = 2 * N := by ring

/-- **The cosh combination.**  The two branches add: the growing one is controlled by whatever
bound the primitive identity supplies, the decaying one by the uniform autocorrelation bound. -/
theorem abs_integral_cosh_mul_autocorrelation_le
    (R : ℝ → ℝ) {H N B : ℝ} (hH : 0 ≤ H) (hN : 0 ≤ N)
    (hbound : ∀ h : ℝ, 0 ≤ h → |halfLineAutocorrelation R h| ≤ N)
    (hgrow : |∫ h in Ioc (0 : ℝ) H, Real.exp (h / 2) * halfLineAutocorrelation R h| ≤ B)
    (hintg : IntegrableOn
      (fun h : ℝ => Real.exp (h / 2) * halfLineAutocorrelation R h) (Ioc 0 H))
    (hintd : IntegrableOn
      (fun h : ℝ => Real.exp (-h / 2) * halfLineAutocorrelation R h) (Ioc 0 H)) :
    |∫ h in Ioc (0 : ℝ) H, 2 * Real.cosh (h / 2) * halfLineAutocorrelation R h|
      ≤ B + 2 * N := by
  have hsplit : (∫ h in Ioc (0 : ℝ) H, 2 * Real.cosh (h / 2) * halfLineAutocorrelation R h)
      = (∫ h in Ioc (0 : ℝ) H, Real.exp (h / 2) * halfLineAutocorrelation R h)
        + ∫ h in Ioc (0 : ℝ) H, Real.exp (-h / 2) * halfLineAutocorrelation R h := by
    rw [← integral_add hintg hintd]
    refine integral_congr_ae ?_
    filter_upwards with h
    rw [Real.cosh_eq]
    have hneg : -(h / 2) = -h / 2 := by ring
    rw [hneg]
    ring
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have hdec := abs_integral_exp_neg_half_mul_autocorrelation_le R hH hN hbound hintd
  linarith [hgrow, hdec]


/-- **The growing branch, bounded.**  `(7)` turns the growing branch into a pairing against a
primitive increment and `(8)` bounds that pairing; composing them is the whole content of the
oscillatory cancellation. -/
theorem abs_integral_exp_half_mul_autocorrelation_le
    (R : ℝ → ℝ) {H M : ℝ} (hH : 0 ≤ H)
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive R t| ≤ M)
    (hlocal : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume a b)
    (hprod : Integrable
      (Function.uncurry (fun h s : ℝ => Real.exp (h / 2) * R (s + h) * R s))
      ((volume.restrict (Ioc (0 : ℝ) H)).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hG : IntegrableOn (fun s : ℝ => Real.exp (-s / 2) * R s) (Ioi 0))
    (hT : IntegrableOn (fun s : ℝ => (Real.exp (-s / 2) * R s)
      * (halfLineExpPrimitive R (s + H) - halfLineExpPrimitive R s)) (Ioi 0)) :
    |∫ h in Ioc (0 : ℝ) H, Real.exp (h / 2) * halfLineAutocorrelation R h|
      ≤ 2 * M * ∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s| := by
  rw [integral_exp_half_mul_halfLineAutocorrelation_eq_primitive R hH hlocal hprod]
  exact abs_integral_mul_primitive_sub_le R (halfLineExpPrimitive R) hH hA hG hT

/-- **The polar source estimate.**  Both branches, in the corpus's own terms: the growing one
through the bounded primitive, the decaying one through the uniform autocorrelation bound. -/
theorem abs_integral_cosh_mul_autocorrelation_full_le
    (R : ℝ → ℝ) {H M N : ℝ} (hH : 0 ≤ H) (hN : 0 ≤ N)
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive R t| ≤ M)
    (hbound : ∀ h : ℝ, 0 ≤ h → |halfLineAutocorrelation R h| ≤ N)
    (hlocal : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume a b)
    (hprod : Integrable
      (Function.uncurry (fun h s : ℝ => Real.exp (h / 2) * R (s + h) * R s))
      ((volume.restrict (Ioc (0 : ℝ) H)).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hG : IntegrableOn (fun s : ℝ => Real.exp (-s / 2) * R s) (Ioi 0))
    (hT : IntegrableOn (fun s : ℝ => (Real.exp (-s / 2) * R s)
      * (halfLineExpPrimitive R (s + H) - halfLineExpPrimitive R s)) (Ioi 0))
    (hintg : IntegrableOn
      (fun h : ℝ => Real.exp (h / 2) * halfLineAutocorrelation R h) (Ioc 0 H))
    (hintd : IntegrableOn
      (fun h : ℝ => Real.exp (-h / 2) * halfLineAutocorrelation R h) (Ioc 0 H)) :
    |∫ h in Ioc (0 : ℝ) H, 2 * Real.cosh (h / 2) * halfLineAutocorrelation R h|
      ≤ 2 * M * (∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s|) + 2 * N :=
  abs_integral_cosh_mul_autocorrelation_le R hH hN hbound
    (abs_integral_exp_half_mul_autocorrelation_le R hH hA hlocal hprod hG hT) hintg hintd


/-- The translated square integrates over the shifted ray. -/
theorem integral_sq_comp_add_right (R : ℝ → ℝ) (h : ℝ) :
    (∫ s in Ioi (0 : ℝ), R (s + h) ^ 2) = ∫ u in Ioi h, R u ^ 2 := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self
      (fun u : ℝ => (Ioi h).indicator (fun v : ℝ => R v ^ 2) u) h]
  refine integral_congr_ae ?_
  filter_upwards with s
  simp only [Set.indicator_apply, Set.mem_Ioi]
  by_cases hs : (0 : ℝ) < s
  · rw [if_pos hs, if_pos (by linarith)]
  · rw [if_neg hs, if_neg (by linarith)]

/-- **The uniform autocorrelation bound.**  By the arithmetic–geometric mean inequality and the
fact that a nonnegative integrand over a shifted ray has smaller mass, the autocorrelation is
bounded by the source's square mass -- the same constant Cauchy–Schwarz gives, with no `L^p`
machinery. -/
theorem abs_halfLineAutocorrelation_le (R : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hR2 : IntegrableOn (fun s : ℝ => R s ^ 2) (Ioi 0))
    (hR2h : IntegrableOn (fun s : ℝ => R (s + h) ^ 2) (Ioi 0))
    (hprod : IntegrableOn (fun s : ℝ => R (s + h) * R s) (Ioi 0)) :
    |halfLineAutocorrelation R h| ≤ ∫ s in Ioi (0 : ℝ), R s ^ 2 := by
  have hshift : (∫ s in Ioi (0 : ℝ), R (s + h) ^ 2) ≤ ∫ s in Ioi (0 : ℝ), R s ^ 2 := by
    rw [integral_sq_comp_add_right R h]
    refine setIntegral_mono_set hR2 ?_ ?_
    · filter_upwards with s using sq_nonneg (R s)
    · filter_upwards with s hs using lt_of_le_of_lt hh hs
  have hamgm : IntegrableOn
      (fun s : ℝ => (R (s + h) ^ 2 + R s ^ 2) / 2) (Ioi 0) := (hR2h.add hR2).div_const 2
  have hstep : (∫ s in Ioi (0 : ℝ), |R (s + h) * R s|)
      ≤ ∫ s in Ioi (0 : ℝ), (R (s + h) ^ 2 + R s ^ 2) / 2 := by
    refine integral_mono_ae hprod.abs hamgm ?_
    filter_upwards with s
    nlinarith [sq_nonneg (|R (s + h)| - |R s|), abs_mul (R (s + h)) (R s),
      sq_abs (R (s + h)), sq_abs (R s), abs_nonneg (R (s + h)), abs_nonneg (R s)]
  have hval : (∫ s in Ioi (0 : ℝ), (R (s + h) ^ 2 + R s ^ 2) / 2)
      = ((∫ s in Ioi (0 : ℝ), R (s + h) ^ 2) + ∫ s in Ioi (0 : ℝ), R s ^ 2) / 2 := by
    rw [MeasureTheory.integral_div, integral_add hR2h hR2]
  calc |halfLineAutocorrelation R h|
      ≤ ∫ s in Ioi (0 : ℝ), |R (s + h) * R s| := by
        rw [halfLineAutocorrelation]
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
            (fun s : ℝ => R (s + h) * R s))
    _ ≤ ∫ s in Ioi (0 : ℝ), (R (s + h) ^ 2 + R s ^ 2) / 2 := hstep
    _ = ((∫ s in Ioi (0 : ℝ), R (s + h) ^ 2) + ∫ s in Ioi (0 : ℝ), R s ^ 2) / 2 := hval
    _ ≤ ∫ s in Ioi (0 : ℝ), R s ^ 2 := by linarith [hshift]


/-- **The polar source estimate with both constants concrete.**  The growing branch is controlled
by the bounded primitive, the decaying branch by the source's own square mass.  Nothing is assumed
beyond the natural Fubini and integrability side conditions. -/
theorem abs_integral_cosh_mul_autocorrelation_source_le
    (R : ℝ → ℝ) {H M : ℝ} (hH : 0 ≤ H)
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive R t| ≤ M)
    (hR2 : IntegrableOn (fun s : ℝ => R s ^ 2) (Ioi 0))
    (hR2h : ∀ h : ℝ, 0 ≤ h → IntegrableOn (fun s : ℝ => R (s + h) ^ 2) (Ioi 0))
    (hprodh : ∀ h : ℝ, 0 ≤ h → IntegrableOn (fun s : ℝ => R (s + h) * R s) (Ioi 0))
    (hlocal : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume a b)
    (hprod : Integrable
      (Function.uncurry (fun h s : ℝ => Real.exp (h / 2) * R (s + h) * R s))
      ((volume.restrict (Ioc (0 : ℝ) H)).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hG : IntegrableOn (fun s : ℝ => Real.exp (-s / 2) * R s) (Ioi 0))
    (hT : IntegrableOn (fun s : ℝ => (Real.exp (-s / 2) * R s)
      * (halfLineExpPrimitive R (s + H) - halfLineExpPrimitive R s)) (Ioi 0))
    (hintg : IntegrableOn
      (fun h : ℝ => Real.exp (h / 2) * halfLineAutocorrelation R h) (Ioc 0 H))
    (hintd : IntegrableOn
      (fun h : ℝ => Real.exp (-h / 2) * halfLineAutocorrelation R h) (Ioc 0 H)) :
    |∫ h in Ioc (0 : ℝ) H, 2 * Real.cosh (h / 2) * halfLineAutocorrelation R h|
      ≤ 2 * M * (∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s|)
        + 2 * ∫ s in Ioi (0 : ℝ), R s ^ 2 := by
  have hN : (0 : ℝ) ≤ ∫ s in Ioi (0 : ℝ), R s ^ 2 :=
    integral_nonneg fun s => sq_nonneg (R s)
  exact abs_integral_cosh_mul_autocorrelation_full_le R hH hN hA
    (fun h hh => abs_halfLineAutocorrelation_le R hh hR2 (hR2h h hh) (hprodh h hh))
    hlocal hprod hG hT hintg hintd


end HTGeometry
