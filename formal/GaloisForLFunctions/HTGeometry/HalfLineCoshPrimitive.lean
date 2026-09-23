import Mathlib
import GaloisForLFunctions.HTGeometry.ExponentialSubstitution
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
    (∫ s in Ioi (0 : ℝ), R (s + h) ^ (2 : ℕ)) = ∫ u in Ioi h, R u ^ (2 : ℕ) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self
      (fun u : ℝ => (Ioi h).indicator (fun v : ℝ => R v ^ (2 : ℕ)) u) h]
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
    (hR2 : IntegrableOn (fun s : ℝ => R s ^ (2 : ℕ)) (Ioi 0))
    (hR2h : IntegrableOn (fun s : ℝ => R (s + h) ^ (2 : ℕ)) (Ioi 0))
    (hprod : IntegrableOn (fun s : ℝ => R (s + h) * R s) (Ioi 0)) :
    |halfLineAutocorrelation R h| ≤ ∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ) := by
  have hshift : (∫ s in Ioi (0 : ℝ), R (s + h) ^ (2 : ℕ)) ≤ ∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ) := by
    rw [integral_sq_comp_add_right R h]
    refine setIntegral_mono_set hR2 ?_ ?_
    · filter_upwards with s using sq_nonneg (R s)
    · filter_upwards with s hs using lt_of_le_of_lt hh hs
  have hamgm : IntegrableOn
      (fun s : ℝ => (R (s + h) ^ (2 : ℕ) + R s ^ (2 : ℕ)) / 2) (Ioi 0) := (hR2h.add hR2).div_const 2
  have hstep : (∫ s in Ioi (0 : ℝ), |R (s + h) * R s|)
      ≤ ∫ s in Ioi (0 : ℝ), (R (s + h) ^ (2 : ℕ) + R s ^ (2 : ℕ)) / 2 := by
    refine integral_mono_ae hprod.abs hamgm ?_
    filter_upwards with s
    nlinarith [sq_nonneg (|R (s + h)| - |R s|), abs_mul (R (s + h)) (R s),
      sq_abs (R (s + h)), sq_abs (R s), abs_nonneg (R (s + h)), abs_nonneg (R s)]
  have hval : (∫ s in Ioi (0 : ℝ), (R (s + h) ^ (2 : ℕ) + R s ^ (2 : ℕ)) / 2)
      = ((∫ s in Ioi (0 : ℝ), R (s + h) ^ (2 : ℕ)) + ∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ)) / 2 := by
    rw [MeasureTheory.integral_div, integral_add hR2h hR2]
  calc |halfLineAutocorrelation R h|
      ≤ ∫ s in Ioi (0 : ℝ), |R (s + h) * R s| := by
        rw [halfLineAutocorrelation]
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
            (fun s : ℝ => R (s + h) * R s))
    _ ≤ ∫ s in Ioi (0 : ℝ), (R (s + h) ^ (2 : ℕ) + R s ^ (2 : ℕ)) / 2 := hstep
    _ = ((∫ s in Ioi (0 : ℝ), R (s + h) ^ (2 : ℕ)) + ∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ)) / 2 := hval
    _ ≤ ∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ) := by linarith [hshift]


/-- **The polar source estimate with both constants concrete.**  The growing branch is controlled
by the bounded primitive, the decaying branch by the source's own square mass.  Nothing is assumed
beyond the natural Fubini and integrability side conditions. -/
theorem abs_integral_cosh_mul_autocorrelation_source_le
    (R : ℝ → ℝ) {H M : ℝ} (hH : 0 ≤ H)
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive R t| ≤ M)
    (hR2 : IntegrableOn (fun s : ℝ => R s ^ (2 : ℕ)) (Ioi 0))
    (hR2h : ∀ h : ℝ, 0 ≤ h → IntegrableOn (fun s : ℝ => R (s + h) ^ (2 : ℕ)) (Ioi 0))
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
        + 2 * ∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ) := by
  have hN : (0 : ℝ) ≤ ∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ) :=
    integral_nonneg fun s => sq_nonneg (R s)
  exact abs_integral_cosh_mul_autocorrelation_full_le R hH hN hA
    (fun h hh => abs_halfLineAutocorrelation_le R hh hR2 (hR2h h hh) (hprodh h hh))
    hlocal hprod hG hT hintg hintd


/-- **The logarithmic primitive is the radial primitive.**  Transporting a source through
`x = exp s` turns its growing half-line primitive into the `x^{-1/2}`-weighted radial primitive. -/
theorem halfLineExpPrimitive_comp_exp (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hf : ContinuousOn f (Set.Icc 1 (Real.exp t))) :
    halfLineExpPrimitive (fun s : ℝ => f (Real.exp s)) t
      = ∫ x in (1 : ℝ)..Real.exp t, f x / Real.sqrt x :=
  integral_exp_half_comp_exp f ht hf

/-- **The bridge from the radial primitive to the polar source estimate's constant.**  A bound on
the radial primitive, uniform in its endpoint, is exactly the bound on the growing half-line
primitive that `(10)` consumes. -/
theorem abs_halfLineExpPrimitive_le_of_radial (f : ℝ → ℝ) {M : ℝ}
    (hf : ∀ Y : ℝ, 1 ≤ Y → ContinuousOn f (Set.Icc 1 Y))
    (hbound : ∀ X : ℝ, 1 ≤ X → |∫ x in (1 : ℝ)..X, f x / Real.sqrt x| ≤ M) :
    ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive (fun s : ℝ => f (Real.exp s)) t| ≤ M := by
  intro t ht
  have hexp1 : (1 : ℝ) ≤ Real.exp t := by
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr ht
  rw [halfLineExpPrimitive_comp_exp f ht (hf _ hexp1)]
  exact hbound _ hexp1


/-- The continuous polar charge of a real half-line source on the lower exterior tail. -/
def polarCharge (R : ℝ → ℝ) (a : ℝ) : ℝ :=
  4 * ∫ h in Ioc (0 : ℝ) (2 * a), Real.cosh (h / 2) * halfLineAutocorrelation R h

theorem polarCharge_eq (R : ℝ → ℝ) (a : ℝ) :
    polarCharge R a
      = 2 * ∫ h in Ioc (0 : ℝ) (2 * a),
          2 * Real.cosh (h / 2) * halfLineAutocorrelation R h := by
  rw [polarCharge]
  have hpull : (∫ h in Ioc (0 : ℝ) (2 * a),
      2 * Real.cosh (h / 2) * halfLineAutocorrelation R h)
      = 2 * ∫ h in Ioc (0 : ℝ) (2 * a),
          Real.cosh (h / 2) * halfLineAutocorrelation R h := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with h
    ring
  rw [hpull]
  ring

/-- **The polar charge estimate.**  The card's `(10)`: the polar charge of a source with bounded
growing primitive is at most `4 M ‖G‖₁ + 4 ‖R‖₂²`. -/
theorem abs_polarCharge_le
    (R : ℝ → ℝ) {a M : ℝ} (ha : 0 ≤ a)
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive R t| ≤ M)
    (hR2 : IntegrableOn (fun s : ℝ => R s ^ (2 : ℕ)) (Ioi 0))
    (hR2h : ∀ h : ℝ, 0 ≤ h → IntegrableOn (fun s : ℝ => R (s + h) ^ (2 : ℕ)) (Ioi 0))
    (hprodh : ∀ h : ℝ, 0 ≤ h → IntegrableOn (fun s : ℝ => R (s + h) * R s) (Ioi 0))
    (hlocal : ∀ x y : ℝ,
      IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume x y)
    (hprod : Integrable
      (Function.uncurry (fun h s : ℝ => Real.exp (h / 2) * R (s + h) * R s))
      ((volume.restrict (Ioc (0 : ℝ) (2 * a))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hG : IntegrableOn (fun s : ℝ => Real.exp (-s / 2) * R s) (Ioi 0))
    (hT : IntegrableOn (fun s : ℝ => (Real.exp (-s / 2) * R s)
      * (halfLineExpPrimitive R (s + 2 * a) - halfLineExpPrimitive R s)) (Ioi 0))
    (hintg : IntegrableOn
      (fun h : ℝ => Real.exp (h / 2) * halfLineAutocorrelation R h) (Ioc 0 (2 * a)))
    (hintd : IntegrableOn
      (fun h : ℝ => Real.exp (-h / 2) * halfLineAutocorrelation R h) (Ioc 0 (2 * a))) :
    |polarCharge R a|
      ≤ 4 * M * (∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s|)
        + 4 * ∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ) := by
  have h2a : (0 : ℝ) ≤ 2 * a := by linarith
  have hmain := abs_integral_cosh_mul_autocorrelation_source_le R h2a hA hR2 hR2h hprodh
    hlocal hprod hG hT hintg hintd
  rw [polarCharge_eq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith [hmain]


/-- The growing primitive is additive over finite sums of sources. -/
theorem halfLineExpPrimitive_finset_sum {S : ℕ → ℝ → ℝ} (N : ℕ) {t : ℝ}
    (hint : ∀ k ∈ Finset.range N,
      IntervalIntegrable (fun u : ℝ => Real.exp (u / 2) * S k u) volume 0 t) :
    halfLineExpPrimitive (fun u : ℝ => ∑ k ∈ Finset.range N, S k u) t
      = ∑ k ∈ Finset.range N, halfLineExpPrimitive (S k) t := by
  rw [halfLineExpPrimitive]
  have hcongr : (∫ u in (0 : ℝ)..t, Real.exp (u / 2) * ∑ k ∈ Finset.range N, S k u)
      = ∫ u in (0 : ℝ)..t, ∑ k ∈ Finset.range N, Real.exp (u / 2) * S k u := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [Finset.mul_sum]
  rw [hcongr, intervalIntegral.integral_finsetSum hint]
  rfl

/-- **The truncation bound.**  A summable family of primitives bounds every finite truncation by
the same constant, so the bound survives the passage to the limit. -/
theorem abs_halfLineExpPrimitive_finset_sum_le {S : ℕ → ℝ → ℝ} {B : ℝ} (N : ℕ) {t : ℝ}
    (hint : ∀ k : ℕ, IntervalIntegrable (fun u : ℝ => Real.exp (u / 2) * S k u) volume 0 t)
    (hsummable : Summable fun k : ℕ => |halfLineExpPrimitive (S k) t|)
    (hbound : ∑' k : ℕ, |halfLineExpPrimitive (S k) t| ≤ B) :
    |halfLineExpPrimitive (fun u : ℝ => ∑ k ∈ Finset.range N, S k u) t| ≤ B := by
  rw [halfLineExpPrimitive_finset_sum N (fun k _ => hint k)]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (hsummable.sum_le_tsum _ (fun k _ => abs_nonneg _)) hbound


/-- **The bound passes to the limit.**  If the truncations' primitives converge, a bound uniform
in the truncation is a bound on the limit. -/
theorem abs_halfLineExpPrimitive_le_of_tendsto {S : ℕ → ℝ → ℝ} {T : ℝ → ℝ} {B t : ℝ}
    (hconv : Filter.Tendsto (fun N : ℕ => halfLineExpPrimitive (S N) t) Filter.atTop
      (nhds (halfLineExpPrimitive T t)))
    (hbound : ∀ N : ℕ, |halfLineExpPrimitive (S N) t| ≤ B) :
    |halfLineExpPrimitive T t| ≤ B :=
  le_of_tendsto hconv.abs (Filter.Eventually.of_forall hbound)

/-- **The primitive functional is Lipschitz on `L¹` of the compact range.**  The weight is bounded
by `exp(t/2)` there, so the primitive of a difference is controlled by the difference's mass. -/
theorem abs_halfLineExpPrimitive_sub_le {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf : IntervalIntegrable (fun s : ℝ => Real.exp (s / 2) * f s) volume 0 t)
    (hg : IntervalIntegrable (fun s : ℝ => Real.exp (s / 2) * g s) volume 0 t)
    (hd : IntervalIntegrable (fun s : ℝ => |f s - g s|) volume 0 t) :
    |halfLineExpPrimitive f t - halfLineExpPrimitive g t|
      ≤ Real.exp (t / 2) * ∫ s in (0 : ℝ)..t, |f s - g s| := by
  have hsub : halfLineExpPrimitive f t - halfLineExpPrimitive g t
      = ∫ s in (0 : ℝ)..t, Real.exp (s / 2) * (f s - g s) := by
    rw [halfLineExpPrimitive, halfLineExpPrimitive, ← intervalIntegral.integral_sub hf hg]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    ring
  rw [hsub]
  have hprod : IntervalIntegrable (fun s : ℝ => Real.exp (s / 2) * (f s - g s)) volume 0 t := by
    refine (hf.sub hg).congr ?_
    intro s _
    ring
  have habs1 : |∫ s in (0 : ℝ)..t, Real.exp (s / 2) * (f s - g s)|
      ≤ ∫ s in (0 : ℝ)..t, |Real.exp (s / 2) * (f s - g s)| :=
    intervalIntegral.abs_integral_le_integral_abs (μ := volume) ht
  have hmono : (∫ s in (0 : ℝ)..t, |Real.exp (s / 2) * (f s - g s)|)
      ≤ ∫ s in (0 : ℝ)..t, Real.exp (t / 2) * |f s - g s| := by
    refine intervalIntegral.integral_mono_on ht hprod.abs (hd.const_mul _) (fun s hs => ?_)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hle : Real.exp (s / 2) ≤ Real.exp (t / 2) :=
      Real.exp_le_exp.mpr (by linarith [hs.2])
    nlinarith [abs_nonneg (f s - g s)]
  refine le_trans habs1 (le_trans hmono (le_of_eq ?_))
  rw [intervalIntegral.integral_const_mul]


/-- **The passage, assembled.**  A bound on every truncation, uniform in the truncation and in the
point, together with pointwise convergence of the truncations' primitives, bounds the limit
source's primitive by the same constant. -/
theorem abs_halfLineExpPrimitive_limit_le {S : ℕ → ℝ → ℝ} {T : ℝ → ℝ} {B : ℝ}
    (hbound : ∀ (N : ℕ) (t : ℝ), 0 ≤ t →
      |halfLineExpPrimitive (fun u : ℝ => ∑ k ∈ Finset.range N, S k u) t| ≤ B)
    (hconv : ∀ t : ℝ, 0 ≤ t → Filter.Tendsto
      (fun N : ℕ => halfLineExpPrimitive (fun u : ℝ => ∑ k ∈ Finset.range N, S k u) t)
      Filter.atTop (nhds (halfLineExpPrimitive T t))) :
    ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive T t| ≤ B :=
  fun t ht => abs_halfLineExpPrimitive_le_of_tendsto (hconv t ht) (fun N => hbound N t ht)


/-- **The `L¹` mass of the decaying branch, by parametrised AM-GM.**  For every `ε > 0`,
`‖G‖₁ ≤ (ε + ‖R‖₂²/ε)/2`; optimising in `ε` recovers the Cauchy–Schwarz bound `‖G‖₁ ≤ ‖R‖₂` with
no `L^p` machinery. -/
theorem integral_abs_exp_neg_half_mul_le {R : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hR2 : IntegrableOn (fun s : ℝ => R s ^ (2 : ℕ)) (Ioi 0))
    (hG : IntegrableOn (fun s : ℝ => Real.exp (-s / 2) * R s) (Ioi 0))
    (hexp : IntegrableOn (fun s : ℝ => Real.exp (-s)) (Ioi 0))
    (hmass : (∫ s in Ioi (0 : ℝ), Real.exp (-s)) ≤ 1) :
    (∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s|)
      ≤ (ε + (∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ)) * ε⁻¹) / 2 := by
  have hinv : ε * ε⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hε)
  have hmaj : IntegrableOn
      (fun s : ℝ => (ε * Real.exp (-s) + R s ^ (2 : ℕ) * ε⁻¹) / 2) (Ioi 0) :=
    ((hexp.const_mul ε).add (hR2.mul_const ε⁻¹)).div_const 2
  have hstep : (∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s|)
      ≤ ∫ s in Ioi (0 : ℝ), (ε * Real.exp (-s) + R s ^ (2 : ℕ) * ε⁻¹) / 2 := by
    refine integral_mono_ae hG.abs hmaj ?_
    filter_upwards with s
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hhalf : Real.exp (-s / 2) ^ (2 : ℕ) = Real.exp (-s) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    have hexpr : ε * Real.exp (-s) + R s ^ (2 : ℕ) * ε⁻¹ - 2 * (Real.exp (-s / 2) * |R s|)
        = ε⁻¹ * (ε * Real.exp (-s / 2) - |R s|) ^ (2 : ℕ) := by
      rw [← hhalf, ← sq_abs (R s)]
      field_simp
      ring
    have hnn : 0 ≤ ε⁻¹ * (ε * Real.exp (-s / 2) - |R s|) ^ (2 : ℕ) :=
      mul_nonneg (inv_pos.mpr hε).le (sq_nonneg _)
    linarith [hexpr, hnn]
  refine le_trans hstep ?_
  rw [MeasureTheory.integral_div, integral_add (hexp.const_mul ε) (hR2.mul_const ε⁻¹),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
  have hmul : ε * (∫ s in Ioi (0 : ℝ), Real.exp (-s)) ≤ ε * 1 :=
    mul_le_mul_of_nonneg_left hmass hε.le
  linarith [hmul]


end HTGeometry
