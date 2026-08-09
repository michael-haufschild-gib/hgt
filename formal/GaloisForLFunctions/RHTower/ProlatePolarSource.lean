import GaloisForLFunctions.HTGeometry.HalfLineCoshPrimitive
import GaloisForLFunctions.RHTower.ProlateExactChannel

/-!
# The radial mode as a polar source

The channel source in the logarithmic variable is `s ↦ √(exp s) · R(k exp s)`, whose growing
half-line primitive is, by the exponential substitution, the radial primitive `∫₁^X R(k x) dx`.
The all-radial primitive bound therefore supplies exactly the constant the polar source estimate
consumes.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-- The `k`-th channel source in the logarithmic variable. -/
def channelSource (k : ℝ) (R : ℝ → ℝ) (u : ℝ) : ℝ := Real.sqrt (Real.exp u) * R (k * Real.exp u)

/-- **The channel source has a uniformly bounded growing primitive.**  This is the hypothesis
`(10)` needs, supplied by `(16)` for the exact mode. -/
theorem abs_halfLineExpPrimitive_channelSource_le {s c k : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hk : 2 ≤ k)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    ∀ t : ℝ, 0 ≤ t → |HTGeometry.halfLineExpPrimitive (channelSource k R) t|
      ≤ 4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * (c * k ^ 2)) := by
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  refine HTGeometry.abs_halfLineExpPrimitive_le_of_radial
    (f := fun x : ℝ => Real.sqrt x * R (k * x)) ?_ ?_
  · intro Y _
    exact Real.continuous_sqrt.continuousOn.mul
      (hRc.comp (continuous_const.mul continuous_id)).continuousOn
  · intro X hX
    have hcongr : (∫ x in (1 : ℝ)..X, Real.sqrt x * R (k * x) / Real.sqrt x)
        = ∫ x in (1 : ℝ)..X, R (k * x) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le hX] at hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx.1
      have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx0)
      field_simp
    rw [hcongr]
    have h := norm_integral_radialProlate_dilate_left_le (DDR := DDR) (k := k) (L := 1) (X := X)
      hs0 hs1 hc hk1 le_rfl (by linarith) hX hR hDR hode
    rw [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    refine le_trans h (le_of_eq ?_)
    have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr (by linarith)
    have hk0 : (0 : ℝ) < k := by linarith
    field_simp

/-- **The polar source estimate for a radial channel.**  Every constant is now the mode's own: the
growing branch is controlled by `(16)` through the exponential substitution, the decaying branch by
the source's square mass. -/
theorem abs_integral_cosh_mul_autocorrelation_channelSource_le {s c k H : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hk : 2 ≤ k) (hH : 0 ≤ H)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hR2 : IntegrableOn (fun u : ℝ => channelSource k R u ^ 2) (Ioi 0))
    (hR2h : ∀ h : ℝ, 0 ≤ h →
      IntegrableOn (fun u : ℝ => channelSource k R (u + h) ^ 2) (Ioi 0))
    (hprodh : ∀ h : ℝ, 0 ≤ h →
      IntegrableOn (fun u : ℝ => channelSource k R (u + h) * channelSource k R u) (Ioi 0))
    (hlocal : ∀ a b : ℝ, IntervalIntegrable
      (fun u : ℝ => Real.exp (u / 2) * channelSource k R u) MeasureTheory.volume a b)
    (hprod : Integrable
      (Function.uncurry (fun h u : ℝ =>
        Real.exp (h / 2) * channelSource k R (u + h) * channelSource k R u))
      ((MeasureTheory.volume.restrict (Ioc (0 : ℝ) H)).prod
        (MeasureTheory.volume.restrict (Ioi (0 : ℝ)))))
    (hG : IntegrableOn (fun u : ℝ => Real.exp (-u / 2) * channelSource k R u) (Ioi 0))
    (hT : IntegrableOn (fun u : ℝ => (Real.exp (-u / 2) * channelSource k R u)
      * (HTGeometry.halfLineExpPrimitive (channelSource k R) (u + H)
        - HTGeometry.halfLineExpPrimitive (channelSource k R) u)) (Ioi 0))
    (hintg : IntegrableOn (fun h : ℝ =>
      Real.exp (h / 2) * HTGeometry.halfLineAutocorrelation (channelSource k R) h) (Ioc 0 H))
    (hintd : IntegrableOn (fun h : ℝ =>
      Real.exp (-h / 2) * HTGeometry.halfLineAutocorrelation (channelSource k R) h) (Ioc 0 H)) :
    |∫ h in Ioc (0 : ℝ) H,
        2 * Real.cosh (h / 2) * HTGeometry.halfLineAutocorrelation (channelSource k R) h|
      ≤ 2 * (4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * (c * k ^ 2)))
          * (∫ u in Ioi (0 : ℝ), |Real.exp (-u / 2) * channelSource k R u|)
        + 2 * ∫ u in Ioi (0 : ℝ), channelSource k R u ^ 2 :=
  HTGeometry.abs_integral_cosh_mul_autocorrelation_source_le (channelSource k R) hH
    (abs_halfLineExpPrimitive_channelSource_le (DDR := DDR) hs0 hs1 hc hk hR hDR hode)
    hR2 hR2h hprodh hlocal hprod hG hT hintg hintd


/-- **The channel sources' primitives sum.**  At every point of the logarithmic half-line the
channels `k >= 2` contribute a convergent series of primitives, bounded by one constant free of
the point. -/
theorem tsum_abs_halfLineExpPrimitive_channelSource_le {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    ∀ t : ℝ, 0 ≤ t →
      ∑' j : ℕ, |HTGeometry.halfLineExpPrimitive (channelSource (2 + (j : ℝ)) R) t|
        ≤ 4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c) := by
  intro t ht
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  set B : ℝ := 4500 * M / (Real.sqrt c * c) with hBdef
  have hB : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  have hterm : ∀ j : ℕ,
      |HTGeometry.halfLineExpPrimitive (channelSource (2 + (j : ℝ)) R) t|
        ≤ B * (1 / (2 + (j : ℝ)) ^ 2) := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hk : (2 : ℝ) ≤ 2 + (j : ℝ) := by linarith
    have h := abs_halfLineExpPrimitive_channelSource_le (DDR := DDR) (k := 2 + (j : ℝ))
      hs0 hs1 hc hk hR hDR hode t ht
    rw [← hMdef] at h
    refine le_trans h (le_of_eq ?_)
    rw [hBdef]
    have hne : (2 + (j : ℝ)) ≠ 0 := by positivity
    field_simp
  have hnn : ∀ j : ℕ,
      (0 : ℝ) ≤ |HTGeometry.halfLineExpPrimitive (channelSource (2 + (j : ℝ)) R) t| :=
    fun j => abs_nonneg _
  have hmaj : Summable fun j : ℕ => B * (1 / (2 + (j : ℝ)) ^ 2) :=
    (GaloisForLFunctions.HTGeometry.summable_inv_sq_shift (σ := 2) (by norm_num)).mul_left B
  have hsummable : Summable fun j : ℕ =>
      |HTGeometry.halfLineExpPrimitive (channelSource (2 + (j : ℝ)) R) t| :=
    hmaj.of_nonneg_of_le hnn hterm
  calc ∑' j : ℕ, |HTGeometry.halfLineExpPrimitive (channelSource (2 + (j : ℝ)) R) t|
      ≤ ∑' j : ℕ, B * (1 / (2 + (j : ℝ)) ^ 2) := hsummable.tsum_le_tsum hterm hmaj
    _ = B * ∑' j : ℕ, 1 / (2 + (j : ℝ)) ^ 2 := tsum_mul_left
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left
        GaloisForLFunctions.HTGeometry.tsum_inv_sq_shift_two_le_one hB
    _ = 4500 * M / (Real.sqrt c * c) := by rw [hBdef]; ring


/-- **The first channel source's primitive.**  `k = 1` uses the full first-channel bound, which
carries the endpoint term. -/
theorem abs_halfLineExpPrimitive_firstChannelSource_le {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    ∀ t : ℝ, 0 ≤ t → |HTGeometry.halfLineExpPrimitive (channelSource 1 R) t|
      ≤ prolateEndpointConstant / (c * Real.sqrt c)
        + 2250 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c) := by
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  refine HTGeometry.abs_halfLineExpPrimitive_le_of_radial
    (f := fun x : ℝ => Real.sqrt x * R (1 * x)) ?_ ?_
  · intro Y _
    exact Real.continuous_sqrt.continuousOn.mul
      (hRc.comp (continuous_const.mul continuous_id)).continuousOn
  · intro X hX
    have hcongr : (∫ x in (1 : ℝ)..X, Real.sqrt x * R (1 * x) / Real.sqrt x)
        = ∫ x in (1 : ℝ)..X, R x := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le hX] at hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx.1
      have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx0)
      rw [one_mul]
      field_simp
    rw [hcongr]
    have h := norm_integral_radialProlate_first_channel_le (DDR := DDR) (X := X)
      hs0 hs1 hc hR1 hX hR hDR hode
    rwa [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs] at h

/-- **All channel sources' primitives, summed.**  The whole radial object's growing primitive is
bounded by one constant, uniformly along the logarithmic half-line. -/
theorem tsum_abs_halfLineExpPrimitive_allChannelSource_le {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    ∀ t : ℝ, 0 ≤ t →
      |HTGeometry.halfLineExpPrimitive (channelSource 1 R) t|
          + ∑' j : ℕ, |HTGeometry.halfLineExpPrimitive (channelSource (2 + (j : ℝ)) R) t|
        ≤ prolateEndpointConstant / (c * Real.sqrt c)
          + 6750 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c) := by
  intro t ht
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have h1 := abs_halfLineExpPrimitive_firstChannelSource_le (DDR := DDR) hs0 hs1 hc hR1
    hR hDR hode t ht
  have h2 := tsum_abs_halfLineExpPrimitive_channelSource_le (DDR := DDR) hs0 hs1 hc1
    hR hDR hode t ht
  have hsum : 2250 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c)
      + 4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c)
      = 6750 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c) := by ring
  linarith [h1, h2, hsum]


/-- **`(18)` for a single radial channel.**  The polar charge of the `k`-th channel source is
controlled by the mode's own energy, with the `1/(c^{3/2} k^2)` gain of `(16)`. -/
theorem abs_polarCharge_channelSource_le {s c k a : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (hk : 2 ≤ k) (ha : 0 ≤ a)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hR2 : IntegrableOn (fun u : ℝ => channelSource k R u ^ 2) (Ioi 0))
    (hR2h : ∀ h : ℝ, 0 ≤ h →
      IntegrableOn (fun u : ℝ => channelSource k R (u + h) ^ 2) (Ioi 0))
    (hprodh : ∀ h : ℝ, 0 ≤ h →
      IntegrableOn (fun u : ℝ => channelSource k R (u + h) * channelSource k R u) (Ioi 0))
    (hlocal : ∀ x y : ℝ, IntervalIntegrable
      (fun u : ℝ => Real.exp (u / 2) * channelSource k R u) MeasureTheory.volume x y)
    (hprod : Integrable
      (Function.uncurry (fun h u : ℝ =>
        Real.exp (h / 2) * channelSource k R (u + h) * channelSource k R u))
      ((MeasureTheory.volume.restrict (Ioc (0 : ℝ) (2 * a))).prod
        (MeasureTheory.volume.restrict (Ioi (0 : ℝ)))))
    (hG : IntegrableOn (fun u : ℝ => Real.exp (-u / 2) * channelSource k R u) (Ioi 0))
    (hT : IntegrableOn (fun u : ℝ => (Real.exp (-u / 2) * channelSource k R u)
      * (HTGeometry.halfLineExpPrimitive (channelSource k R) (u + 2 * a)
        - HTGeometry.halfLineExpPrimitive (channelSource k R) u)) (Ioi 0))
    (hintg : IntegrableOn (fun h : ℝ =>
      Real.exp (h / 2) * HTGeometry.halfLineAutocorrelation (channelSource k R) h)
      (Ioc 0 (2 * a)))
    (hintd : IntegrableOn (fun h : ℝ =>
      Real.exp (-h / 2) * HTGeometry.halfLineAutocorrelation (channelSource k R) h)
      (Ioc 0 (2 * a))) :
    |HTGeometry.polarCharge (channelSource k R) a|
      ≤ 4 * (4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * (c * k ^ 2)))
          * (∫ u in Ioi (0 : ℝ), |Real.exp (-u / 2) * channelSource k R u|)
        + 4 * ∫ u in Ioi (0 : ℝ), channelSource k R u ^ 2 :=
  HTGeometry.abs_polarCharge_le (channelSource k R) ha
    (abs_halfLineExpPrimitive_channelSource_le (DDR := DDR) hs0 hs1 hc hk hR hDR hode)
    hR2 hR2h hprodh hlocal hprod hG hT hintg hintd

/-- **`(18)` for the first channel.** -/
theorem abs_polarCharge_firstChannelSource_le {s c a : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) (hR1 : R 1 = 1) (ha : 0 ≤ a)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hR2 : IntegrableOn (fun u : ℝ => channelSource 1 R u ^ 2) (Ioi 0))
    (hR2h : ∀ h : ℝ, 0 ≤ h →
      IntegrableOn (fun u : ℝ => channelSource 1 R (u + h) ^ 2) (Ioi 0))
    (hprodh : ∀ h : ℝ, 0 ≤ h →
      IntegrableOn (fun u : ℝ => channelSource 1 R (u + h) * channelSource 1 R u) (Ioi 0))
    (hlocal : ∀ x y : ℝ, IntervalIntegrable
      (fun u : ℝ => Real.exp (u / 2) * channelSource 1 R u) MeasureTheory.volume x y)
    (hprod : Integrable
      (Function.uncurry (fun h u : ℝ =>
        Real.exp (h / 2) * channelSource 1 R (u + h) * channelSource 1 R u))
      ((MeasureTheory.volume.restrict (Ioc (0 : ℝ) (2 * a))).prod
        (MeasureTheory.volume.restrict (Ioi (0 : ℝ)))))
    (hG : IntegrableOn (fun u : ℝ => Real.exp (-u / 2) * channelSource 1 R u) (Ioi 0))
    (hT : IntegrableOn (fun u : ℝ => (Real.exp (-u / 2) * channelSource 1 R u)
      * (HTGeometry.halfLineExpPrimitive (channelSource 1 R) (u + 2 * a)
        - HTGeometry.halfLineExpPrimitive (channelSource 1 R) u)) (Ioi 0))
    (hintg : IntegrableOn (fun h : ℝ =>
      Real.exp (h / 2) * HTGeometry.halfLineAutocorrelation (channelSource 1 R) h)
      (Ioc 0 (2 * a)))
    (hintd : IntegrableOn (fun h : ℝ =>
      Real.exp (-h / 2) * HTGeometry.halfLineAutocorrelation (channelSource 1 R) h)
      (Ioc 0 (2 * a))) :
    |HTGeometry.polarCharge (channelSource 1 R) a|
      ≤ 4 * (prolateEndpointConstant / (c * Real.sqrt c)
            + 2250 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c))
          * (∫ u in Ioi (0 : ℝ), |Real.exp (-u / 2) * channelSource 1 R u|)
        + 4 * ∫ u in Ioi (0 : ℝ), channelSource 1 R u ^ 2 :=
  HTGeometry.abs_polarCharge_le (channelSource 1 R) ha
    (abs_halfLineExpPrimitive_firstChannelSource_le (DDR := DDR) hs0 hs1 hc hR1 hR hDR hode)
    hR2 hR2h hprodh hlocal hprod hG hT hintg hintd


theorem summable_abs_halfLineExpPrimitive_channelSource {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    ∀ t : ℝ, 0 ≤ t → Summable fun j : ℕ =>
      |HTGeometry.halfLineExpPrimitive (channelSource (2 + (j : ℝ)) R) t| := by
  intro t ht
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set M : ℝ := exactEnergyBudget s c R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  set B : ℝ := 4500 * M / (Real.sqrt c * c) with hBdef
  have hterm : ∀ j : ℕ,
      |HTGeometry.halfLineExpPrimitive (channelSource (2 + (j : ℝ)) R) t|
        ≤ B * (1 / (2 + (j : ℝ)) ^ 2) := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hk : (2 : ℝ) ≤ 2 + (j : ℝ) := by linarith
    have h := abs_halfLineExpPrimitive_channelSource_le (DDR := DDR) (k := 2 + (j : ℝ))
      hs0 hs1 hc hk hR hDR hode t ht
    rw [← hMdef] at h
    refine le_trans h (le_of_eq ?_)
    rw [hBdef]
    have hne : (2 + (j : ℝ)) ≠ 0 := by positivity
    field_simp
  exact ((GaloisForLFunctions.HTGeometry.summable_inv_sq_shift (σ := 2)
    (by norm_num)).mul_left B).of_nonneg_of_le (fun j => abs_nonneg _) hterm

/-- **The truncation bound for the radial object.**  Every finite sum of channels has growing
primitive bounded by the same constant, uniformly along the half-line and in the truncation. -/
theorem abs_halfLineExpPrimitive_channelTruncation_le {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) (N : ℕ) :
    ∀ t : ℝ, 0 ≤ t →
      |HTGeometry.halfLineExpPrimitive
          (fun u : ℝ => ∑ j ∈ Finset.range N, channelSource (2 + (j : ℝ)) R u) t|
        ≤ 4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c) := by
  intro t ht
  have hRc : Continuous R := continuous_iff_continuousAt.mpr fun u => (hR u).continuousAt
  have hint : ∀ j : ℕ, IntervalIntegrable
      (fun u : ℝ => Real.exp (u / 2) * channelSource (2 + (j : ℝ)) R u)
      MeasureTheory.volume 0 t := by
    intro j
    refine Continuous.intervalIntegrable ?_ 0 t
    refine (Real.continuous_exp.comp (continuous_id.div_const 2)).mul ?_
    rw [show channelSource (2 + (j : ℝ)) R = fun u : ℝ =>
        Real.sqrt (Real.exp u) * R ((2 + (j : ℝ)) * Real.exp u) from rfl]
    exact (Real.continuous_sqrt.comp Real.continuous_exp).mul
      (hRc.comp (continuous_const.mul Real.continuous_exp))
  exact HTGeometry.abs_halfLineExpPrimitive_finset_sum_le N hint
    (summable_abs_halfLineExpPrimitive_channelSource (DDR := DDR) hs0 hs1 hc hR hDR hode t ht)
    (tsum_abs_halfLineExpPrimitive_channelSource_le (DDR := DDR) hs0 hs1 hc hR hDR hode t ht)


/-- **`(11)` for the limit radial object.**  Once the truncations' primitives converge, the whole
radial source's growing primitive obeys the channel-sum bound.  The convergence is the only input
from outside the radial analysis. -/
theorem abs_halfLineExpPrimitive_radialLimit_le {s c : ℝ} {R DR DDR : ℝ → ℝ} {T : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hconv : ∀ t : ℝ, 0 ≤ t → Filter.Tendsto
      (fun N : ℕ => HTGeometry.halfLineExpPrimitive
        (fun u : ℝ => ∑ j ∈ Finset.range N, channelSource (2 + (j : ℝ)) R u) t)
      Filter.atTop (nhds (HTGeometry.halfLineExpPrimitive T t))) :
    ∀ t : ℝ, 0 ≤ t → |HTGeometry.halfLineExpPrimitive T t|
      ≤ 4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c) :=
  HTGeometry.abs_halfLineExpPrimitive_limit_le
    (fun N t ht => abs_halfLineExpPrimitive_channelTruncation_le (DDR := DDR) hs0 hs1 hc
      hR hDR hode N t ht) hconv


/-- **`(18)` for the limit radial object.**  The continuous polar charge of the whole radial source
is bounded by the mode's own energy times the source's masses, with the channel index summed out
and the endpoint of integration free. -/
theorem abs_polarCharge_radialLimit_le {s c a : ℝ} {R DR DDR T : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 1 ≤ c) (ha : 0 ≤ a)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hconv : ∀ t : ℝ, 0 ≤ t → Filter.Tendsto
      (fun N : ℕ => HTGeometry.halfLineExpPrimitive
        (fun u : ℝ => ∑ j ∈ Finset.range N, channelSource (2 + (j : ℝ)) R u) t)
      Filter.atTop (nhds (HTGeometry.halfLineExpPrimitive T t)))
    (hT2 : IntegrableOn (fun u : ℝ => T u ^ 2) (Ioi 0))
    (hT2h : ∀ h : ℝ, 0 ≤ h → IntegrableOn (fun u : ℝ => T (u + h) ^ 2) (Ioi 0))
    (hprodh : ∀ h : ℝ, 0 ≤ h → IntegrableOn (fun u : ℝ => T (u + h) * T u) (Ioi 0))
    (hlocal : ∀ x y : ℝ, IntervalIntegrable
      (fun u : ℝ => Real.exp (u / 2) * T u) MeasureTheory.volume x y)
    (hprod : Integrable
      (Function.uncurry (fun h u : ℝ => Real.exp (h / 2) * T (u + h) * T u))
      ((MeasureTheory.volume.restrict (Ioc (0 : ℝ) (2 * a))).prod
        (MeasureTheory.volume.restrict (Ioi (0 : ℝ)))))
    (hG : IntegrableOn (fun u : ℝ => Real.exp (-u / 2) * T u) (Ioi 0))
    (hTT : IntegrableOn (fun u : ℝ => (Real.exp (-u / 2) * T u)
      * (HTGeometry.halfLineExpPrimitive T (u + 2 * a)
        - HTGeometry.halfLineExpPrimitive T u)) (Ioi 0))
    (hintg : IntegrableOn (fun h : ℝ =>
      Real.exp (h / 2) * HTGeometry.halfLineAutocorrelation T h) (Ioc 0 (2 * a)))
    (hintd : IntegrableOn (fun h : ℝ =>
      Real.exp (-h / 2) * HTGeometry.halfLineAutocorrelation T h) (Ioc 0 (2 * a))) :
    |HTGeometry.polarCharge T a|
      ≤ 4 * (4500 * exactEnergyBudget s c R DR 2 / (Real.sqrt c * c))
          * (∫ u in Ioi (0 : ℝ), |Real.exp (-u / 2) * T u|)
        + 4 * ∫ u in Ioi (0 : ℝ), T u ^ 2 :=
  HTGeometry.abs_polarCharge_le T ha
    (abs_halfLineExpPrimitive_radialLimit_le (DDR := DDR) hs0 hs1 hc hR hDR hode hconv)
    hT2 hT2h hprodh hlocal hprod hG hTT hintg hintd


end GaloisForLFunctions.RHTower
