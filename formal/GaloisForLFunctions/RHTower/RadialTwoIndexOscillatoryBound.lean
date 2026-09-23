import GaloisForLFunctions.HTGeometry.TwoPhaseOscillatoryProduct
import GaloisForLFunctions.RHTower.RadialDilatedPhaseSeparation

/-!
# The two-index exterior radial oscillatory bound

Two exterior radial solutions dilated by indices `j > k ≥ 2` carry the phases `ξ_s(jx)` and
`ξ_s(kx)`.  Their speeds separate by `(2/3)(j − k)` and add up to at least `j + k`, so both the
difference and the sum phase of the product are nonstationary with the same explicit constant.
Feeding that into the first-derivative test gives, for any two-branch representations of the two
solutions,

```text
|∫_a^b U_j U_k| ≤ (four endpoint-and-variation budgets) / c ,
```

with every budget divided by `(2/3)(j − k)`.  This is the `1/(c|j − k|)` gain of the exterior
off-diagonal radial Gram entry: the constants are absolute and uniform in the radius, in the turning
parameter, and in the two indices.
-/

open Set MeasureTheory intervalIntegral

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The exterior radial phase dilated by an index. -/
def dilatedRadialPhase (s r x : ℝ) : ℝ := xiEndpointPhase s (r * x)

/-- The second derivative of the dilated phase. -/
def dilatedRadialPhaseAccel (s r x : ℝ) : ℝ := r ^ (2 : ℕ) * xiSpeedDeriv s (r * x)

theorem xiSpeed_pos_of_le_half {s t : ℝ} (hs1 : s ≤ 1 / 2) (ht : 1 < t) : 0 < xiSpeed s t := by
  have h1 : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  have h2 : (0 : ℝ) < t ^ (2 : ℕ) - s := by nlinarith
  rw [xiSpeed]
  exact Real.sqrt_pos.mpr (div_pos h2 h1)

theorem continuousAt_xiSpeedDeriv {s t : ℝ} (hs1 : s ≤ 1 / 2) (ht : 1 < t) :
    ContinuousAt (xiSpeedDeriv s) t := by
  have h1 : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  have hsq : 0 < xiSpeed s t := xiSpeed_pos_of_le_half hs1 ht
  have hden : ((t ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s t) ≠ 0 := by positivity
  have hnum : ContinuousAt (fun u : ℝ => u * (s - 1)) t := by fun_prop
  have hd : ContinuousAt (fun u : ℝ => (u ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s u) t :=
    (by fun_prop : ContinuousAt (fun u : ℝ => (u ^ (2 : ℕ) - 1) ^ (2 : ℕ)) t).mul
      (continuousAt_xiSpeed ht)
  exact hnum.div hd hden

theorem hasDerivAt_dilatedRadialPhase {s r x : ℝ} (hs : 0 ≤ s) (hrx : 1 < r * x) :
    HasDerivAt (dilatedRadialPhase s r) (dilatedPhaseSpeed s r x) x := by
  have h := hasDerivAt_xiEndpointPhase_dilate (s := s) (r := r) (x := x) hs hrx
  rw [dilatedPhaseSpeed_eq]
  exact h

theorem hasDerivAt_dilatedPhaseSpeed {s r x : ℝ} (hs1 : s ≤ 1) (hrx : 1 < r * x) :
    HasDerivAt (dilatedPhaseSpeed s r) (dilatedRadialPhaseAccel s r x) x := by
  have hlin : HasDerivAt (fun t : ℝ => r * t) r x := by
    simpa using (hasDerivAt_id x).const_mul r
  have h2 : HasDerivAt (fun t : ℝ => xiSpeed s (r * t)) (xiSpeedDeriv s (r * x) * r) x :=
    (hasDerivAt_xiSpeed hs1 hrx).comp x hlin
  have h3 := h2.const_mul r
  have hval : r * (xiSpeedDeriv s (r * x) * r) = dilatedRadialPhaseAccel s r x := by
    rw [dilatedRadialPhaseAccel]; ring
  rw [hval] at h3
  exact h3

theorem one_lt_mul_of_two_le {r a x : ℝ} (hr : 2 ≤ r) (ha : 1 ≤ a) (hx : a ≤ x) : 1 < r * x := by
  have hx1 : (1 : ℝ) ≤ x := le_trans ha hx
  nlinarith

theorem continuousOn_dilatedPhaseSpeed {s r a b : ℝ} (hr : 2 ≤ r) (ha : 1 ≤ a) :
    ContinuousOn (dilatedPhaseSpeed s r) (Icc a b) := by
  intro x hx
  have hrx : 1 < r * x := one_lt_mul_of_two_le hr ha hx.1
  have hlin : ContinuousAt (fun t : ℝ => r * t) x := by fun_prop
  have h : ContinuousAt (fun t : ℝ => r * xiSpeed s (r * t)) x :=
    (((continuousAt_xiSpeed hrx).comp hlin).const_smul r)
  exact h.continuousWithinAt

theorem continuousOn_dilatedRadialPhaseAccel {s r a b : ℝ} (hs1 : s ≤ 1 / 2) (hr : 2 ≤ r)
    (ha : 1 ≤ a) :
    ContinuousOn (dilatedRadialPhaseAccel s r) (Icc a b) := by
  intro x hx
  have hrx : 1 < r * x := one_lt_mul_of_two_le hr ha hx.1
  have hlin : ContinuousAt (fun t : ℝ => r * t) x := by fun_prop
  have h : ContinuousAt (fun t : ℝ => r ^ (2 : ℕ) * xiSpeedDeriv s (r * t)) x :=
    (((continuousAt_xiSpeedDeriv hs1 hrx).comp hlin).const_smul (r ^ (2 : ℕ)))
  exact h.continuousWithinAt

/-! ## The curvature of the dilated phase -/

theorem one_le_xiSpeed_of_le_one {s t : ℝ} (hs1 : s ≤ 1) (ht : 1 < t) : 1 ≤ xiSpeed s t := by
  have h1 : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by nlinarith
  have hratio : (1 : ℝ) ≤ (t ^ (2 : ℕ) - s) / (t ^ (2 : ℕ) - 1) := by
    rw [le_div_iff₀ h1]
    linarith
  have h := Real.sqrt_le_sqrt hratio
  rwa [Real.sqrt_one, ← xiSpeed] at h

/-! ## The phase grows at least linearly -/

/-- The exterior phase dominates the arclength: `ξ_s(z) ≥ z − 1`. -/
theorem sub_one_le_xiEndpointPhase {s z : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hz : 1 ≤ z) :
    z - 1 ≤ xiEndpointPhase s z := by
  have hint : IntervalIntegrable (xiSpeed s) MeasureTheory.volume 1 z :=
    intervalIntegrable_xiSpeed hs hz
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 1 z :=
    intervalIntegrable_const
  have hae : (fun _ : ℝ => (1 : ℝ))
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (1 : ℝ) z)] xiSpeed s := by
    have hnull : MeasureTheory.volume.restrict (Set.Icc (1 : ℝ) z) {(1 : ℝ)} = 0 := by
      simp
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
      MeasureTheory.compl_mem_ae_iff.mpr hnull] with t ht hne
    have ht1 : (1 : ℝ) < t := lt_of_le_of_ne ht.1 (by
      intro h
      exact hne (by simp [h.symm]))
    exact one_le_xiSpeed_of_le_one hs1 ht1
  have hmono := intervalIntegral.integral_mono_ae_restrict hz hone hint hae
  have hconst : (∫ _ in (1 : ℝ)..z, (1 : ℝ)) = z - 1 := by
    simp
  rw [hconst] at hmono
  exact hmono

/-- **The dilated phase dominates the radius.** -/
theorem le_dilatedRadialPhase {s r x : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hr : 2 ≤ r) (hx : 1 ≤ x) :
    x ≤ dilatedRadialPhase s r x := by
  have hrx : (1 : ℝ) ≤ r * x := by nlinarith
  have h := sub_one_le_xiEndpointPhase hs hs1 hrx
  have hlin : x ≤ r * x - 1 := by nlinarith
  exact le_trans hlin (by rw [dilatedRadialPhase]; exact h)

/-- **The dilated phase curvature decays like `1/(r x³)`.** -/
theorem abs_dilatedRadialPhaseAccel_le {s r x : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hr : 2 ≤ r) (hx : 1 ≤ x) :
    |dilatedRadialPhaseAccel s r x| ≤ 16 / 9 / (r * x ^ (3 : ℕ)) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hu : (2 : ℝ) ≤ r * x := by nlinarith
  have hu1 : (1 : ℝ) < r * x := by linarith
  have hu0 : (0 : ℝ) < r * x := by linarith
  have husq : (4 : ℝ) ≤ (r * x) ^ (2 : ℕ) := by nlinarith
  have hden : (0 : ℝ) < (r * x) ^ (2 : ℕ) - 1 := by linarith
  have hspeed : (1 : ℝ) ≤ xiSpeed s (r * x) := one_le_xiSpeed_of_le_one (by linarith) hu1
  have hspeed0 : (0 : ℝ) < xiSpeed s (r * x) := lt_of_lt_of_le zero_lt_one hspeed
  have hnum : |(r * x) * (s - 1)| = (r * x) * (1 - s) := by
    rw [abs_mul, abs_of_pos hu0, abs_of_nonpos (by linarith : s - 1 ≤ 0)]
    ring
  have hval : |xiSpeedDeriv s (r * x)|
      = (r * x) * (1 - s) / (((r * x) ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s (r * x)) := by
    rw [xiSpeedDeriv, abs_div, hnum, abs_of_pos (by positivity)]
  have hquotient : (r * x) * (1 - s) / (((r * x) ^ (2 : ℕ) - 1) ^ (2 : ℕ) * xiSpeed s (r * x))
      ≤ 16 / 9 / (r * x) ^ (3 : ℕ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (9 : ℝ) / 16 * (r * x) ^ (4 : ℕ) ≤ ((r * x) ^ (2 : ℕ) - 1) ^ (2 : ℕ) := by
      have h34 : (3 : ℝ) / 4 * (r * x) ^ (2 : ℕ) ≤ (r * x) ^ (2 : ℕ) - 1 := by nlinarith
      nlinarith [h34, husq]
    have hs1' : (1 : ℝ) - s ≤ 1 := by linarith
    nlinarith [hsq, hspeed, hs1', hu0, pow_pos hu0 3, pow_pos hu0 4,
      mul_pos (pow_pos hu0 3) hspeed0]
  have hfinal : |dilatedRadialPhaseAccel s r x| ≤ r ^ (2 : ℕ) * (16 / 9 / (r * x) ^ (3 : ℕ)) := by
    rw [dilatedRadialPhaseAccel, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ (2 : ℕ))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_trans (le_of_eq hval) hquotient
  have hid : r ^ (2 : ℕ) * (16 / 9 / (r * x) ^ (3 : ℕ)) = 16 / 9 / (r * x ^ (3 : ℕ)) := by
    field_simp
  rwa [hid] at hfinal

theorem abs_dilatedRadialPhaseAccel_sub_le {s j k x : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hj : 2 ≤ j) (hk : 2 ≤ k) (hx : 1 ≤ x) :
    |dilatedRadialPhaseAccel s j x - dilatedRadialPhaseAccel s k x| ≤ 16 / 9 / x ^ (3 : ℕ) := by
  have hj0 : (0 : ℝ) < j := lt_of_lt_of_le (by norm_num) hj
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hk
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hbj := abs_dilatedRadialPhaseAccel_le hs hs1 hj hx
  have hbk := abs_dilatedRadialPhaseAccel_le hs hs1 hk hx
  have hstep : |dilatedRadialPhaseAccel s j x - dilatedRadialPhaseAccel s k x|
      ≤ |dilatedRadialPhaseAccel s j x| + |dilatedRadialPhaseAccel s k x| := abs_sub _ _
  have hx3 : (0 : ℝ) < x ^ (3 : ℕ) := by positivity
  have hj2 : 16 / 9 / (j * x ^ (3 : ℕ)) ≤ 16 / 9 / (2 * x ^ (3 : ℕ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [hx3, hj]
  have hk2 : 16 / 9 / (k * x ^ (3 : ℕ)) ≤ 16 / 9 / (2 * x ^ (3 : ℕ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [hx3, hk]
  have hid : 16 / 9 / (2 * x ^ (3 : ℕ)) + 16 / 9 / (2 * x ^ (3 : ℕ)) = 16 / 9 / x ^ (3 : ℕ) := by
    field_simp
    ring
  linarith

theorem abs_dilatedRadialPhaseAccel_add_le {s j k x : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hj : 2 ≤ j) (hk : 2 ≤ k) (hx : 1 ≤ x) :
    |dilatedRadialPhaseAccel s j x + dilatedRadialPhaseAccel s k x| ≤ 16 / 9 / x ^ (3 : ℕ) := by
  have hj0 : (0 : ℝ) < j := lt_of_lt_of_le (by norm_num) hj
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hk
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hbj := abs_dilatedRadialPhaseAccel_le hs hs1 hj hx
  have hbk := abs_dilatedRadialPhaseAccel_le hs hs1 hk hx
  have hstep : |dilatedRadialPhaseAccel s j x + dilatedRadialPhaseAccel s k x|
      ≤ |dilatedRadialPhaseAccel s j x| + |dilatedRadialPhaseAccel s k x| := abs_add_le _ _
  have hx3 : (0 : ℝ) < x ^ (3 : ℕ) := by positivity
  have hj2 : 16 / 9 / (j * x ^ (3 : ℕ)) ≤ 16 / 9 / (2 * x ^ (3 : ℕ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [hx3, hj]
  have hk2 : 16 / 9 / (k * x ^ (3 : ℕ)) ≤ 16 / 9 / (2 * x ^ (3 : ℕ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [hx3, hk]
  have hid : 16 / 9 / (2 * x ^ (3 : ℕ)) + 16 / 9 / (2 * x ^ (3 : ℕ)) = 16 / 9 / x ^ (3 : ℕ) := by
    field_simp
    ring
  linarith

/-- **The two-index exterior radial oscillatory bound.**  Any two two-branch representations
carried by the phases `ξ_s(jx)` and `ξ_s(kx)` with `j > k ≥ 2` have an overlap of size `1/c` times
the four amplitude budgets, each divided by `(2/3)(j − k)`. -/
theorem abs_integral_radial_twoBranch_product_le
    {s j k a b c : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hk : 2 ≤ k) (hkj : k < j) (ha : 1 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    {g₁ g₂ g₃ g₄ g₁' g₂' g₃' g₄' : ℝ → ℝ}
    (hg₁ : ∀ x ∈ Icc a b, HasDerivAt g₁ (g₁' x) x)
    (hg₁c : ContinuousOn g₁ (Icc a b)) (hg₁'c : ContinuousOn g₁' (Icc a b))
    (hg₂ : ∀ x ∈ Icc a b, HasDerivAt g₂ (g₂' x) x)
    (hg₂c : ContinuousOn g₂ (Icc a b)) (hg₂'c : ContinuousOn g₂' (Icc a b))
    (hg₃ : ∀ x ∈ Icc a b, HasDerivAt g₃ (g₃' x) x)
    (hg₃c : ContinuousOn g₃ (Icc a b)) (hg₃'c : ContinuousOn g₃' (Icc a b))
    (hg₄ : ∀ x ∈ Icc a b, HasDerivAt g₄ (g₄' x) x)
    (hg₄c : ContinuousOn g₄ (Icc a b)) (hg₄'c : ContinuousOn g₄' (Icc a b)) :
    |∫ x in a..b,
        (g₁ x * Real.cos (c * dilatedRadialPhase s j x) + g₂ x * Real.sin (c * dilatedRadialPhase s j x))
          * (g₃ x * Real.cos (c * dilatedRadialPhase s k x)
            + g₄ x * Real.sin (c * dilatedRadialPhase s k x))|
      ≤ (oscBudget a b (2 / 3 * (j - k)) (fun x => 1 / 2 * (g₁ x * g₃ x + g₂ x * g₄ x))
            (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x + (g₂' x * g₄ x + g₂ x * g₄' x)))
            (fun x => dilatedRadialPhaseAccel s j x - dilatedRadialPhaseAccel s k x)
        + oscBudget a b (2 / 3 * (j - k)) (fun x => 1 / 2 * (g₁ x * g₃ x - g₂ x * g₄ x))
            (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x - (g₂' x * g₄ x + g₂ x * g₄' x)))
            (fun x => dilatedRadialPhaseAccel s j x + dilatedRadialPhaseAccel s k x)
        + oscBudget a b (2 / 3 * (j - k)) (fun x => 1 / 2 * (g₂ x * g₃ x - g₁ x * g₄ x))
            (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x - (g₁' x * g₄ x + g₁ x * g₄' x)))
            (fun x => dilatedRadialPhaseAccel s j x - dilatedRadialPhaseAccel s k x)
        + oscBudget a b (2 / 3 * (j - k)) (fun x => 1 / 2 * (g₂ x * g₃ x + g₁ x * g₄ x))
            (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x + (g₁' x * g₄ x + g₁ x * g₄' x)))
            (fun x => dilatedRadialPhaseAccel s j x + dilatedRadialPhaseAccel s k x)) / c := by
  have hj : (2 : ℝ) ≤ j := le_trans hk hkj.le
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hk
  have hm : (0 : ℝ) < 2 / 3 * (j - k) := by
    have : (0 : ℝ) < j - k := by linarith
    positivity
  have hs1' : s ≤ 1 := by linarith
  have hdiff : ∀ x ∈ Icc a b,
      2 / 3 * (j - k) ≤ |dilatedPhaseSpeed s j x - dilatedPhaseSpeed s k x| := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := le_trans ha hx.1
    have hsep := sub_dilatedPhaseSpeed_ge (s := s) hs hs1 hk hkj.le hx1
    have : (0 : ℝ) ≤ dilatedPhaseSpeed s j x - dilatedPhaseSpeed s k x := by
      have : (0 : ℝ) ≤ 2 / 3 * (j - k) := hm.le
      linarith
    rwa [abs_of_nonneg this]
  have hsum : ∀ x ∈ Icc a b,
      2 / 3 * (j - k) ≤ |dilatedPhaseSpeed s j x + dilatedPhaseSpeed s k x| := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := le_trans ha hx.1
    have hadd := le_add_dilatedPhaseSpeed (s := s) hs1 hk hj hx1
    have hnn : (0 : ℝ) ≤ dilatedPhaseSpeed s j x + dilatedPhaseSpeed s k x := by linarith
    rw [abs_of_nonneg hnn]
    linarith
  exact abs_integral_twoBranch_product_le_on hab hc hm
    hg₁ hg₁c hg₁'c hg₂ hg₂c hg₂'c hg₃ hg₃c hg₃'c hg₄ hg₄c hg₄'c
    (fun x hx => hasDerivAt_dilatedRadialPhase hs (one_lt_mul_of_two_le hj ha hx.1))
    (continuousOn_dilatedPhaseSpeed hj ha)
    (fun x hx => hasDerivAt_dilatedPhaseSpeed hs1' (one_lt_mul_of_two_le hj ha hx.1))
    (continuousOn_dilatedRadialPhaseAccel hs1 hj ha)
    (fun x hx => hasDerivAt_dilatedRadialPhase hs (one_lt_mul_of_two_le hk ha hx.1))
    (continuousOn_dilatedPhaseSpeed hk ha)
    (fun x hx => hasDerivAt_dilatedPhaseSpeed hs1' (one_lt_mul_of_two_le hk ha hx.1))
    (continuousOn_dilatedRadialPhaseAccel hs1 hk ha)
    hdiff hsum

end GaloisForLFunctions.RHTower

end
