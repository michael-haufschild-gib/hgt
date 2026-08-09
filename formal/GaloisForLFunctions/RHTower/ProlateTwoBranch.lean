import GaloisForLFunctions.RHTower.BesselNormalForm
import GaloisForLFunctions.RHTower.ProlateEnvelopeIntegral
import GaloisForLFunctions.RHTower.ProlateDunsterBesselOffDiagonal
import GaloisForLFunctions.RHTower.ProlateDilatedChannel

/-!
# The two-branch expansion of the prolate Bessel profile

Composing the sharp Bessel asymptotic with the Liouville–Green amplitude turns the regular profile
into a genuine two-branch form.  The composition is exact in one respect worth isolating: the
amplitude that comes out is `ampFourth`, because `xiAmplitude/sqrt(xi)` *is* `ampFourth` by
definition, so no approximation enters at that step.

The remainder is `ampFourth(s,x)` times a constant over the base frequency, i.e. relative `O(1/c)` —
the rate the exterior estimate needs, and one full power better than the corpus's fourth-root
bridge.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- **The Liouville–Green amplitude divided by the root phase is the leading amplitude.** -/
theorem xiAmplitude_div_sqrt_phase {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiAmplitude s x / Real.sqrt (xiEndpointPhase s x) = ampFourth s x := by
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hsph : 0 < Real.sqrt (xiEndpointPhase s x) := Real.sqrt_pos.mpr hph
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ 2 - 1) * (x ^ 2 - s) := mul_pos hd hn
  have hroot : (0 : ℝ) < Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hP)
  rw [xiAmplitude, ampFourth]
  field_simp

/-- **The two-branch expansion of the regular profile.**  The amplitude is `ampFourth`, the branches
are `cos` and `sin` of the exterior phase, and the remainder is relative `O(1/c)`. -/
theorem abs_radialProlateBesselProfile_sub_twoBranch_le
    {s c x x₀ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx0 : 1 < x₀) (hx : x₀ ≤ x) :
    |radialProlateBesselProfile s c x
        - ampFourth s x * (besselCosCoeff (c * xiEndpointPhase s x₀)
            * Real.cos (c * xiEndpointPhase s x)
          + besselSinCoeff (c * xiEndpointPhase s x₀)
            * Real.sin (c * xiEndpointPhase s x))|
      ≤ ampFourth s x
        * (2 * Real.sqrt (besselEnergy (c * xiEndpointPhase s x₀)
              * Real.exp (1 / (4 * (c * xiEndpointPhase s x₀))))
          * (1 / (4 * (c * xiEndpointPhase s x₀)))) := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le hx0 hx
  have hph0 : 0 < xiEndpointPhase s x₀ := xiEndpointPhase_pos hs0 hs1 hx0
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx1
  have hmono : xiEndpointPhase s x₀ ≤ xiEndpointPhase s x :=
    (strictMonoOn_xiEndpointPhase hs0 hs1).monotoneOn (mem_Ici.mpr (le_of_lt hx0))
      (mem_Ici.mpr (le_of_lt hx1)) hx
  set a : ℝ := c * xiEndpointPhase s x₀ with hadef
  set u : ℝ := c * xiEndpointPhase s x with hudef
  have ha : 0 < a := by rw [hadef]; positivity
  have hau : a ≤ u := by
    rw [hadef, hudef]
    exact mul_le_mul_of_nonneg_left hmono hc.le
  have hu : 0 < u := lt_of_lt_of_le ha hau
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hbase := abs_besselJ0_sub_fixed_le ha hau
  -- factor the profile
  have hamp : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hx1
  have hsph : 0 < Real.sqrt (xiEndpointPhase s x) := Real.sqrt_pos.mpr hph
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsplit : Real.sqrt u = Real.sqrt c * Real.sqrt (xiEndpointPhase s x) := by
    rw [hudef, Real.sqrt_mul hc.le]
  have hampf : ampFourth s x = xiAmplitude s x / Real.sqrt (xiEndpointPhase s x) :=
    (xiAmplitude_div_sqrt_phase hs0 hs1 hx1).symm
  have hfactor : radialProlateBesselProfile s c x
      - ampFourth s x * (besselCosCoeff a * Real.cos u + besselSinCoeff a * Real.sin u)
      = (Real.sqrt c * xiAmplitude s x)
        * (besselJ0 u - (besselCosCoeff a * Real.cos u + besselSinCoeff a * Real.sin u)
            / Real.sqrt u) := by
    rw [radialProlateBesselProfile, hampf, hsplit, ← hudef]
    field_simp
  rw [hfactor, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt c * xiAmplitude s x)]
  have hstep : Real.sqrt c * xiAmplitude s x
      * |besselJ0 u - (besselCosCoeff a * Real.cos u + besselSinCoeff a * Real.sin u)
          / Real.sqrt u|
      ≤ Real.sqrt c * xiAmplitude s x
        * (2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
          * (1 / (4 * a) - 1 / (4 * u)) / Real.sqrt u) :=
    mul_le_mul_of_nonneg_left hbase (by positivity)
  refine le_trans hstep ?_
  have hE : (0 : ℝ) ≤ Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) := Real.sqrt_nonneg _
  have htail : (1 : ℝ) / (4 * a) - 1 / (4 * u) ≤ 1 / (4 * a) := by
    have : (0 : ℝ) < 1 / (4 * u) := by positivity
    linarith
  have hvalue : Real.sqrt c * xiAmplitude s x
      * (2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
        * (1 / (4 * a)) / Real.sqrt u)
      = ampFourth s x * (2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
        * (1 / (4 * a))) := by
    rw [hampf, hsplit]
    field_simp
  calc Real.sqrt c * xiAmplitude s x
        * (2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
          * (1 / (4 * a) - 1 / (4 * u)) / Real.sqrt u)
      ≤ Real.sqrt c * xiAmplitude s x
        * (2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
          * (1 / (4 * a)) / Real.sqrt u) := by
        gcongr
    _ = ampFourth s x * (2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a)))
          * (1 / (4 * a))) := hvalue

theorem hasDerivAt_neg_two_div_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun v : ℝ => -2 * (Real.sqrt v)⁻¹) (1 / (x * Real.sqrt x)) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hinv := hsq.inv (ne_of_gt hs)
  have h := hinv.const_mul (-2 : ℝ)
  have hval : (-2 : ℝ) * (-(1 / (2 * Real.sqrt x)) / Real.sqrt x ^ 2)
      = 1 / (x * Real.sqrt x) := by
    rw [Real.sq_sqrt hx.le]
    field_simp
  rwa [hval] at h

/-- The `x^{-3/2}` tail on the exterior range. -/
theorem integral_inv_x_mul_sqrt_le {X : ℝ} (hX : 2 ≤ X) :
    (∫ x in (2 : ℝ)..X, 1 / (x * Real.sqrt x)) ≤ 2 := by
  have hpos : ∀ x ∈ Set.uIcc (2 : ℝ) X, (0 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    linarith [hx.1]
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (x * Real.sqrt x))
      MeasureTheory.volume 2 X := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn) ?_
    intro x hx
    have h := hpos x hx
    have hs := Real.sqrt_pos.mpr h
    positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_neg_two_div_sqrt (hpos x hx)) hint
  rw [h]
  have hX0 : (0 : ℝ) < X := by linarith
  have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h1 : (0 : ℝ) < 2 * (Real.sqrt X)⁻¹ := by positivity
  have h2 : (-2 : ℝ) * (Real.sqrt 2)⁻¹ ≥ -2 := by
    have : (Real.sqrt 2)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hs2
    nlinarith [this, hs2]
  linarith [h1, h2]


theorem continuousOn_ampFourth_Ioi {s : ℝ} (hs1 : s ≤ 1 / 2) :
    ContinuousOn (ampFourth s) (Set.Ioi 1) :=
  fun _ hx => ((hasDerivAt_ampFourth hs1 hx).continuousAt).continuousWithinAt

/-- **The integrated two-branch error.**  With the polar weight `x^{-1/2}` the remainder integrates
to `O(1/c)`, uniformly in the endpoint: the `ampFourth` factor supplies `x^{-1}` and the weight the
remaining half power, which is exactly integrable. -/
theorem abs_integral_profile_sub_twoBranch_le {s c X x₀ : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx0 : 1 < x₀) (hx02 : x₀ ≤ 2) (hX : 2 ≤ X) :
    |∫ x in (2 : ℝ)..X,
        (radialProlateBesselProfile s c x
          - ampFourth s x * (besselCosCoeff (c * xiEndpointPhase s x₀)
              * Real.cos (c * xiEndpointPhase s x)
            + besselSinCoeff (c * xiEndpointPhase s x₀)
              * Real.sin (c * xiEndpointPhase s x))) / Real.sqrt x|
      ≤ 4 * (2 * Real.sqrt (besselEnergy (c * xiEndpointPhase s x₀)
            * Real.exp (1 / (4 * (c * xiEndpointPhase s x₀)))))
        * (1 / (4 * (c * xiEndpointPhase s x₀))) := by
  set a : ℝ := c * xiEndpointPhase s x₀ with hadef
  set K : ℝ := 2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) with hKdef
  have hph0 : 0 < xiEndpointPhase s x₀ := xiEndpointPhase_pos hs0 hs1 hx0
  have ha : 0 < a := by rw [hadef]; positivity
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hsub : Set.uIcc (2 : ℝ) X ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hX]
    intro x hx
    exact Set.mem_Ioi.mpr (by linarith [hx.1])
  -- continuity of the integrand
  have hprof : ContinuousOn (radialProlateBesselProfile s c) (Set.uIcc (2 : ℝ) X) := by
    refine (continuousOn_const.mul ((continuousOn_xiAmplitude hs0 hs1).mono hsub)).mul ?_
    exact continuous_besselJ0.comp_continuousOn
      (continuousOn_const.mul ((continuousOn_xiEndpointPhase hs0).mono hsub))
  have hphc : ContinuousOn (fun x : ℝ => c * xiEndpointPhase s x) (Set.uIcc (2 : ℝ) X) :=
    continuousOn_const.mul ((continuousOn_xiEndpointPhase hs0).mono hsub)
  have hTB : ContinuousOn (fun x : ℝ => ampFourth s x
      * (besselCosCoeff a * Real.cos (c * xiEndpointPhase s x)
        + besselSinCoeff a * Real.sin (c * xiEndpointPhase s x))) (Set.uIcc (2 : ℝ) X) := by
    refine ((continuousOn_ampFourth_Ioi hs1).mono hsub).mul ?_
    exact (continuousOn_const.mul (Real.continuous_cos.comp_continuousOn hphc)).add
      (continuousOn_const.mul (Real.continuous_sin.comp_continuousOn hphc))
  have hsqc : ContinuousOn (fun x : ℝ => Real.sqrt x) (Set.uIcc (2 : ℝ) X) :=
    Real.continuous_sqrt.continuousOn
  have hne : ∀ x ∈ Set.uIcc (2 : ℝ) X, Real.sqrt x ≠ 0 := by
    intro x hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [Set.mem_Ioi.mp (hsub hx)]))
  have hint : IntervalIntegrable
      (fun x : ℝ => (radialProlateBesselProfile s c x
        - ampFourth s x * (besselCosCoeff a * Real.cos (c * xiEndpointPhase s x)
          + besselSinCoeff a * Real.sin (c * xiEndpointPhase s x))) / Real.sqrt x)
      MeasureTheory.volume 2 X :=
    ((hprof.sub hTB).div hsqc hne).intervalIntegrable
  have hmajint : IntervalIntegrable
      (fun x : ℝ => 2 * K * (1 / (4 * a)) * (1 / (x * Real.sqrt x)))
      MeasureTheory.volume 2 X := by
    refine (continuousOn_const.mul ?_).intervalIntegrable
    refine continuousOn_const.div (continuousOn_id.mul hsqc) ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [Set.mem_Ioi.mp (hsub hx)]
    have hs := Real.sqrt_pos.mpr hx0
    positivity
  -- pointwise
  have hpt : ∀ x ∈ Set.Icc (2 : ℝ) X,
      |(radialProlateBesselProfile s c x
        - ampFourth s x * (besselCosCoeff a * Real.cos (c * xiEndpointPhase s x)
          + besselSinCoeff a * Real.sin (c * xiEndpointPhase s x))) / Real.sqrt x|
        ≤ 2 * K * (1 / (4 * a)) * (1 / (x * Real.sqrt x)) := by
    intro x hx
    have hx2' : (2 : ℝ) ≤ x := hx.1
    have hxpos : (0 : ℝ) < x := by linarith
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hbase := abs_radialProlateBesselProfile_sub_twoBranch_le hs0 hs1 hc hx0
      (le_trans hx02 hx2')
    have hamp := ampFourth_le_two_div hs0 hs1 hx2'
    have hamp0 : (0 : ℝ) < ampFourth s x := ampFourth_pos hs1 (by linarith)
    rw [abs_div, abs_of_pos hsx, div_le_iff₀ hsx]
    have hstep : ampFourth s x * (K * (1 / (4 * a))) ≤ 2 / x * (K * (1 / (4 * a))) :=
      mul_le_mul_of_nonneg_right hamp (by positivity)
    have hfin : 2 / x * (K * (1 / (4 * a)))
        = 2 * K * (1 / (4 * a)) * (1 / (x * Real.sqrt x)) * Real.sqrt x := by
      field_simp
    calc |radialProlateBesselProfile s c x
            - ampFourth s x * (besselCosCoeff a * Real.cos (c * xiEndpointPhase s x)
              + besselSinCoeff a * Real.sin (c * xiEndpointPhase s x))|
        ≤ ampFourth s x * (K * (1 / (4 * a))) := hbase
      _ ≤ 2 / x * (K * (1 / (4 * a))) := hstep
      _ = 2 * K * (1 / (4 * a)) * (1 / (x * Real.sqrt x)) * Real.sqrt x := hfin
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs
    (μ := MeasureTheory.volume) hX) ?_
  have hmono := intervalIntegral.integral_mono_on hX hint.abs hmajint hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have htail := integral_inv_x_mul_sqrt_le hX
  have hnn : (0 : ℝ) ≤ 2 * K * (1 / (4 * a)) := by positivity
  have hstep2 : 2 * K * (1 / (4 * a)) * (∫ x in (2 : ℝ)..X, 1 / (x * Real.sqrt x))
      ≤ 2 * K * (1 / (4 * a)) * 2 := mul_le_mul_of_nonneg_left htail hnn
  have hval : 2 * K * (1 / (4 * a)) * 2 = 4 * K * (1 / (4 * a)) := by ring
  linarith [hmono, hstep2, hval.le, hval.symm.le]


/-- **The exact two-branch representation of the profile.**  No remainder: the coefficients are
evaluated at the running phase rather than frozen at a base point, and the identity is exact.  This
is `(13)`'s actual shape -- the card states it as an identity with amplitudes, not as a leading term
with an error. -/
theorem radialProlateBesselProfile_eq_twoBranch {s c x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    radialProlateBesselProfile s c x
      = ampFourth s x
        * (besselCosCoeff (c * xiEndpointPhase s x) * Real.cos (c * xiEndpointPhase s x)
          + besselSinCoeff (c * xiEndpointPhase s x) * Real.sin (c * xiEndpointPhase s x)) := by
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hu : 0 < c * xiEndpointPhase s x := by positivity
  have hsu : 0 < Real.sqrt (c * xiEndpointPhase s x) := Real.sqrt_pos.mpr hu
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsph : 0 < Real.sqrt (xiEndpointPhase s x) := Real.sqrt_pos.mpr hph
  have hrep := besselNormalForm_eq_coeff (c * xiEndpointPhase s x)
  rw [besselNormalForm] at hrep
  have hJ : besselJ0 (c * xiEndpointPhase s x)
      = (besselCosCoeff (c * xiEndpointPhase s x) * Real.cos (c * xiEndpointPhase s x)
        + besselSinCoeff (c * xiEndpointPhase s x) * Real.sin (c * xiEndpointPhase s x))
        / Real.sqrt (c * xiEndpointPhase s x) := by
    rw [← hrep]
    field_simp
  have hampf : ampFourth s x = xiAmplitude s x / Real.sqrt (xiEndpointPhase s x) :=
    (xiAmplitude_div_sqrt_phase hs0 hs1 hx).symm
  have hsplit : Real.sqrt (c * xiEndpointPhase s x)
      = Real.sqrt c * Real.sqrt (xiEndpointPhase s x) := Real.sqrt_mul hc.le _
  rw [radialProlateBesselProfile, hJ, hampf, hsplit]
  field_simp


/-- The exterior phase speed is bounded on the exterior range. -/
theorem xiSpeed_le_two {s t : ℝ} (hs0 : 0 ≤ s) (ht : 2 ≤ t) : xiSpeed s t ≤ 2 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hd : (0 : ℝ) < t ^ 2 - 1 := by nlinarith
  have hq : (t ^ 2 - s) / (t ^ 2 - 1) ≤ 4 := by
    rw [div_le_iff₀ hd]
    nlinarith [ht, hs0]
  rw [xiSpeed]
  have h : Real.sqrt ((t ^ 2 - s) / (t ^ 2 - 1)) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hq
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h4] at h

/-- The scaled dilated phase, differentiated. -/
theorem hasDerivAt_scaled_dilated_phase {s c k x : ℝ} (hs0 : 0 ≤ s) (hkx : 1 < k * x) :
    HasDerivAt (fun y : ℝ => c * xiEndpointPhase s (k * y))
      (c * (k * xiSpeed s (k * x))) x := by
  have h := hasDerivAt_xiEndpointPhase_dilate (s := s) (r := k) (x := x) hs0 hkx
  have hval : k * Real.sqrt ((k ^ 2 * x ^ 2 - s) / (k ^ 2 * x ^ 2 - 1))
      = k * xiSpeed s (k * x) := by
    rw [xiSpeed]
    ring_nf
  rw [hval] at h
  exact h.const_mul c

/-- **The branch coefficient along the dilated phase, differentiated.** -/
theorem hasDerivAt_besselCosCoeff_comp {s c k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hkx : 1 < k * x) :
    HasDerivAt (fun y : ℝ => besselCosCoeff (c * xiEndpointPhase s (k * y)))
      (1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2)
          * besselNormalForm (c * xiEndpointPhase s (k * x))
          * Real.sin (c * xiEndpointPhase s (k * x))
        * (c * (k * xiSpeed s (k * x)))) x := by
  have hph : 0 < xiEndpointPhase s (k * x) := xiEndpointPhase_pos hs0 hs1 hkx
  have hu : 0 < c * xiEndpointPhase s (k * x) := by positivity
  exact (hasDerivAt_besselCosCoeff hu).comp x (hasDerivAt_scaled_dilated_phase hs0 hkx)

/-- **The branch coefficient's drift along the dilated phase is `O(1/(c k x^2))`.** -/
theorem abs_deriv_besselCosCoeff_comp_le {s c k x a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hx : 2 ≤ x) (ha : 0 < a)
    (hau : a ≤ c * xiEndpointPhase s (k * x)) :
    |1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2)
        * besselNormalForm (c * xiEndpointPhase s (k * x))
        * Real.sin (c * xiEndpointPhase s (k * x))
      * (c * (k * xiSpeed s (k * x)))|
      ≤ 2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) / (c * k * x ^ 2) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hkx2 : (2 : ℝ) ≤ k * x := by nlinarith [hk, hx]
  have hkx : (1 : ℝ) < k * x := by linarith
  have hph : 0 < xiEndpointPhase s (k * x) := xiEndpointPhase_pos hs0 hs1 hkx
  set u : ℝ := c * xiEndpointPhase s (k * x) with hudef
  have hu : 0 < u := by rw [hudef]; positivity
  have hM : (0 : ℝ) ≤ Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) := Real.sqrt_nonneg _
  obtain ⟨hdrift, -⟩ := abs_deriv_besselCoeff_le_base ha hau
  have hspeed : xiSpeed s (k * x) ≤ 2 := xiSpeed_le_two hs0 hkx2
  have hspeed0 : (0 : ℝ) ≤ xiSpeed s (k * x) :=
    le_trans zero_le_one (one_le_xiSpeed (by linarith) hkx)
  -- the phase is at least `c k x / 2`
  have hphase : k * x / 2 ≤ xiEndpointPhase s (k * x) :=
    half_mul_le_xiEndpointPhase hs0 hs1 hkx2
  have hulow : c * (k * x) / 2 ≤ u := by
    rw [hudef]
    have := mul_le_mul_of_nonneg_left hphase hc.le
    linarith [this]
  have hulow0 : (0 : ℝ) < c * (k * x) / 2 := by positivity
  rw [abs_mul]
  have hfac : |c * (k * xiSpeed s (k * x))| ≤ c * (k * 2) := by
    rw [abs_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_left hspeed hk0.le
    nlinarith [this, hc.le]
  have hstep : |1 / (4 * u ^ 2) * besselNormalForm u * Real.sin u|
      * |c * (k * xiSpeed s (k * x))|
      ≤ (1 / (4 * u ^ 2) * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))))
        * (c * (k * 2)) :=
    mul_le_mul hdrift hfac (abs_nonneg _) (by positivity)
  refine le_trans hstep ?_
  have hq : 1 / (4 * u ^ 2) ≤ 1 / (c ^ 2 * (k * x) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hulow, hulow0, hu]
  have hfin : 1 / (c ^ 2 * (k * x) ^ 2)
      * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) * (c * (k * 2))
      = 2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) / (c * k * x ^ 2) := by
    field_simp
  calc 1 / (4 * u ^ 2) * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) * (c * (k * 2))
      ≤ 1 / (c ^ 2 * (k * x) ^ 2)
        * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) * (c * (k * 2)) := by
        gcongr
    _ = 2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) / (c * k * x ^ 2) := hfin


/-- The exact channel amplitude of the cosine branch. -/
def channelAmplitude (s c k x : ℝ) : ℝ :=
  ampFourth s (k * x) * besselCosCoeff (c * xiEndpointPhase s (k * x))

/-- Its derivative. -/
def channelAmplitudeDeriv (s c k x : ℝ) : ℝ :=
  k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
      / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))
    * besselCosCoeff (c * xiEndpointPhase s (k * x))
  + ampFourth s (k * x) * (1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2)
      * besselNormalForm (c * xiEndpointPhase s (k * x))
      * Real.sin (c * xiEndpointPhase s (k * x))
    * (c * (k * xiSpeed s (k * x))))

theorem hasDerivAt_channelAmplitude {s c k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hx : 2 ≤ x) :
    HasDerivAt (channelAmplitude s c k) (channelAmplitudeDeriv s c k x) x := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hkx : (1 : ℝ) < k * x := by nlinarith [hk, hx]
  have hlin : HasDerivAt (fun u : ℝ => k * u) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have hamp : HasDerivAt (fun u : ℝ => ampFourth s (k * u))
      (k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
        / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))) x := by
    have h := (hasDerivAt_ampFourth hs1 hkx).comp x hlin
    have hv : -(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
        / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x) * k
        = k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
          / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x)) := by ring
    rwa [hv] at h
  exact hamp.mul (hasDerivAt_besselCosCoeff_comp hs0 hs1 hc hkx)

/-- **The channel amplitude carries the `1/k`.** -/
theorem abs_channelAmplitude_le {s c k x a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hk : 1 ≤ k) (hx : 2 ≤ x) (ha : 0 < a)
    (hau : a ≤ c * xiEndpointPhase s (k * x)) :
    |channelAmplitude s c k x|
      ≤ 2 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) / k / x := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hkx : (1 : ℝ) < k * x := by nlinarith [hk, hx]
  have hamp := ampFourth_dilate_le hs0 hs1 hk hx
  have hamp0 : (0 : ℝ) < ampFourth s (k * x) := ampFourth_pos hs1 hkx
  obtain ⟨hA, -⟩ := abs_besselCoeff_le_base ha hau
  have hM : (0 : ℝ) ≤ Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) := Real.sqrt_nonneg _
  rw [channelAmplitude, abs_mul, abs_of_pos hamp0]
  have hstep : ampFourth s (k * x) * |besselCosCoeff (c * xiEndpointPhase s (k * x))|
      ≤ 2 / (k * x) * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) :=
    mul_le_mul hamp hA (abs_nonneg _) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp


/-- **The channel amplitude's derivative also carries the `1/k`.**  This is `(14)`'s second half for
the exact representation. -/
theorem abs_channelAmplitudeDeriv_le {s c k x a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hx : 2 ≤ x) (ha : 0 < a)
    (hau : a ≤ c * xiEndpointPhase s (k * x)) :
    |channelAmplitudeDeriv s c k x|
      ≤ 36 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) / k / x ^ 2 := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hkx : (1 : ℝ) < k * x := by nlinarith [hk, hx]
  have hamp0 : (0 : ℝ) < ampFourth s (k * x) := ampFourth_pos hs1 hkx
  set M : ℝ := Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  obtain ⟨hA, -⟩ := abs_besselCoeff_le_base ha hau
  have hampd := abs_deriv_ampFourth_dilate_le hs0 hs1 hk hx
  have hampb := ampFourth_dilate_le hs0 hs1 hk hx
  have hdrift := abs_deriv_besselCosCoeff_comp_le hs0 hs1 hc0 hk hx ha hau
  rw [channelAmplitudeDeriv]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
        / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))
      * besselCosCoeff (c * xiEndpointPhase s (k * x))|
      ≤ 32 * M / (k * x ^ 2) := by
    rw [abs_mul]
    calc |k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
            / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))|
          * |besselCosCoeff (c * xiEndpointPhase s (k * x))|
        ≤ 32 / (k * x ^ 2) * M := mul_le_mul hampd hA (abs_nonneg _) (by positivity)
      _ = 32 * M / (k * x ^ 2) := by ring
  have h2 : |ampFourth s (k * x) * (1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2)
        * besselNormalForm (c * xiEndpointPhase s (k * x))
        * Real.sin (c * xiEndpointPhase s (k * x))
      * (c * (k * xiSpeed s (k * x))))|
      ≤ 4 * M / (k * x ^ 2) := by
    rw [abs_mul, abs_of_pos hamp0]
    have hstep : ampFourth s (k * x) * |1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2)
          * besselNormalForm (c * xiEndpointPhase s (k * x))
          * Real.sin (c * xiEndpointPhase s (k * x))
        * (c * (k * xiSpeed s (k * x)))|
        ≤ 2 / (k * x) * (2 * M / (c * k * x ^ 2)) :=
      mul_le_mul hampb hdrift (abs_nonneg _) (by positivity)
    refine le_trans hstep ?_
    have hval : 2 / (k * x) * (2 * M / (c * k * x ^ 2)) = 4 * M / (c * k ^ 2 * x ^ 3) := by
      field_simp
      ring
    rw [hval, div_le_div_iff₀ (by positivity) (by positivity)]
    have hckx : (1 : ℝ) ≤ c * k * x := by nlinarith [hc, hk, hx]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * M) hk0.le)
      (sq_nonneg x)) (by linarith : (0 : ℝ) ≤ c * k * x - 1)]
  have hsum : 32 * M / (k * x ^ 2) + 4 * M / (k * x ^ 2) = 36 * M / k / x ^ 2 := by
    field_simp
    ring
  linarith [h1, h2, hsum]


/-- The channel amplitude in the exterior estimate's normalization. -/
def channelAmp (s c k x : ℝ) : ℝ := Real.sqrt x * channelAmplitude s c k x

/-- Its derivative. -/
def channelAmpDeriv (s c k x : ℝ) : ℝ :=
  1 / (2 * Real.sqrt x) * channelAmplitude s c k x
    + Real.sqrt x * channelAmplitudeDeriv s c k x

theorem hasDerivAt_channelAmp {s c k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hx : 2 ≤ x) :
    HasDerivAt (channelAmp s c k) (channelAmpDeriv s c k x) x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt (ne_of_gt hx0)
  exact hsq.mul (hasDerivAt_channelAmplitude hs0 hs1 hc hk hx)

theorem abs_channelAmp_le {s c k x a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hk : 1 ≤ k) (hx : 2 ≤ x) (ha : 0 < a)
    (hau : a ≤ c * xiEndpointPhase s (k * x)) :
    ‖((channelAmp s c k x : ℝ) : ℂ)‖
      ≤ 37 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) / k / Real.sqrt x := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  set M : ℝ := Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have hbase := abs_channelAmplitude_le hs0 hs1 hk hx ha hau
  rw [Complex.norm_real, Real.norm_eq_abs, channelAmp, abs_mul, abs_of_pos hsx]
  have hstep : Real.sqrt x * |channelAmplitude s c k x| ≤ Real.sqrt x * (2 * M / k / x) :=
    mul_le_mul_of_nonneg_left hbase hsx.le
  refine le_trans hstep ?_
  have hval : Real.sqrt x * (2 * M / k / x) = 2 * M / k / Real.sqrt x := by
    field_simp
    linear_combination M * hss
  rw [hval]
  gcongr
  linarith [hM]

theorem abs_channelAmpDeriv_le {s c k x a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hx : 2 ≤ x) (ha : 0 < a)
    (hau : a ≤ c * xiEndpointPhase s (k * x)) :
    ‖((channelAmpDeriv s c k x : ℝ) : ℂ)‖
      ≤ 37 * Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) / k
        / (x * Real.sqrt x) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsq2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  set M : ℝ := Real.sqrt (besselEnergy a * Real.exp (1 / (4 * a))) with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have hamp := abs_channelAmplitude_le hs0 hs1 hk hx ha hau
  have hder := abs_channelAmplitudeDeriv_le hs0 hs1 hc hk hx ha hau
  rw [Complex.norm_real, Real.norm_eq_abs, channelAmpDeriv]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |1 / (2 * Real.sqrt x) * channelAmplitude s c k x| ≤ M / k / (x * Real.sqrt x) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.sqrt x))]
    have hstep : 1 / (2 * Real.sqrt x) * |channelAmplitude s c k x|
        ≤ 1 / (2 * Real.sqrt x) * (2 * M / k / x) :=
      mul_le_mul_of_nonneg_left hamp (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  have h2 : |Real.sqrt x * channelAmplitudeDeriv s c k x| ≤ 36 * M / k / (x * Real.sqrt x) := by
    rw [abs_mul, abs_of_pos hsx]
    have hstep : Real.sqrt x * |channelAmplitudeDeriv s c k x|
        ≤ Real.sqrt x * (36 * M / k / x ^ 2) :=
      mul_le_mul_of_nonneg_left hder hsx.le
    refine le_trans hstep (le_of_eq ?_)
    field_simp
    linear_combination M * hsq2
  have hsum : M / k / (x * Real.sqrt x) + 36 * M / k / (x * Real.sqrt x)
      = 37 * M / k / (x * Real.sqrt x) := by
    field_simp
    ring
  linarith [h1, h2, hsum]


theorem continuousOn_channelAmplitudeDeriv {s c k X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X) :
    ContinuousOn (channelAmplitudeDeriv s c k) (Set.uIcc (2 : ℝ) X) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hkx : ∀ x ∈ Set.uIcc (2 : ℝ) X, (1 : ℝ) < k * x := by
    intro x hx
    nlinarith [hx2 x hx, hk]
  have hphpos : ∀ x ∈ Set.uIcc (2 : ℝ) X, 0 < c * xiEndpointPhase s (k * x) := by
    intro x hx
    have := xiEndpointPhase_pos hs0 hs1 (hkx x hx)
    positivity
  have hlin : ContinuousOn (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) :=
    continuousOn_const.mul continuousOn_id
  have hmaps : Set.MapsTo (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) (Set.Ioi 1) :=
    fun x hx => hkx x hx
  have hampc : ContinuousOn (fun x : ℝ => ampFourth s (k * x)) (Set.uIcc (2 : ℝ) X) :=
    (continuousOn_ampFourth_Ioi hs1).comp hlin hmaps
  have hphc : ContinuousOn (fun x : ℝ => c * xiEndpointPhase s (k * x)) (Set.uIcc (2 : ℝ) X) :=
    continuousOn_const.mul (((continuousOn_xiEndpointPhase hs0).comp hlin hmaps))
  have hphmaps : Set.MapsTo (fun x : ℝ => c * xiEndpointPhase s (k * x))
      (Set.uIcc (2 : ℝ) X) (Set.Ioi 0) := fun x hx => hphpos x hx
  have hAbase : ContinuousOn besselCosCoeff (Set.Ioi (0 : ℝ)) :=
    fun _ hu => ((hasDerivAt_besselCosCoeff hu).continuousAt).continuousWithinAt
  have hwbase : ContinuousOn besselNormalForm (Set.Ioi (0 : ℝ)) :=
    fun _ hu => ((hasDerivAt_besselNormalForm hu).continuousAt).continuousWithinAt
  have hAc : ContinuousOn (fun x : ℝ => besselCosCoeff (c * xiEndpointPhase s (k * x)))
      (Set.uIcc (2 : ℝ) X) := hAbase.comp hphc hphmaps
  have hwc : ContinuousOn (fun x : ℝ => besselNormalForm (c * xiEndpointPhase s (k * x)))
      (Set.uIcc (2 : ℝ) X) := hwbase.comp hphc hphmaps
  have hspc : ContinuousOn (fun x : ℝ => xiSpeed s (k * x)) (Set.uIcc (2 : ℝ) X) :=
    (continuousOn_xiSpeed s).comp hlin hmaps
  have hratc : ContinuousOn (fun x : ℝ => -(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
      / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s)))) (Set.uIcc (2 : ℝ) X) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    have h1 : (1 : ℝ) < k * x := hkx x hx
    have hd : (0 : ℝ) < (k * x) ^ 2 - 1 := by nlinarith
    have hn : (0 : ℝ) < (k * x) ^ 2 - s := by nlinarith
    positivity
  have hQc : ContinuousOn (fun x : ℝ => 1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2))
      (Set.uIcc (2 : ℝ) X) := by
    refine continuousOn_const.div (continuousOn_const.mul (hphc.pow 2)) ?_
    intro x hx
    have := hphpos x hx
    positivity
  rw [show channelAmplitudeDeriv s c k = fun x : ℝ =>
      k * (-(2 * (k * x) * (2 * (k * x) ^ 2 - s - 1))
        / (4 * (((k * x) ^ 2 - 1) * ((k * x) ^ 2 - s))) * ampFourth s (k * x))
      * besselCosCoeff (c * xiEndpointPhase s (k * x))
    + ampFourth s (k * x) * (1 / (4 * (c * xiEndpointPhase s (k * x)) ^ 2)
        * besselNormalForm (c * xiEndpointPhase s (k * x))
        * Real.sin (c * xiEndpointPhase s (k * x))
      * (c * (k * xiSpeed s (k * x)))) from rfl]
  refine ContinuousOn.add ?_ ?_
  · exact ((continuousOn_const.mul (hratc.mul hampc)).mul hAc)
  · refine hampc.mul (((hQc.mul hwc).mul
      (Real.continuous_sin.comp_continuousOn hphc)).mul ?_)
    exact continuousOn_const.mul (continuousOn_const.mul hspc)

theorem continuousOn_channelAmpDeriv {s c k X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hk : 1 ≤ k) (hX : 2 ≤ X) :
    ContinuousOn (channelAmpDeriv s c k) (Set.uIcc (2 : ℝ) X) := by
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hampc : ContinuousOn (channelAmplitude s c k) (Set.uIcc (2 : ℝ) X) :=
    fun x hx => ((hasDerivAt_channelAmplitude hs0 hs1 hc hk (hx2 x hx)).continuousAt
      ).continuousWithinAt
  have hsqc : ContinuousOn (fun x : ℝ => 1 / (2 * Real.sqrt x)) (Set.uIcc (2 : ℝ) X) := by
    refine continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn) ?_
    intro x hx
    have h := hx2 x hx
    have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    positivity
  rw [show channelAmpDeriv s c k = fun x : ℝ =>
      1 / (2 * Real.sqrt x) * channelAmplitude s c k x
        + Real.sqrt x * channelAmplitudeDeriv s c k x from rfl]
  exact (hsqc.mul hampc).add
    (Real.continuous_sqrt.continuousOn.mul (continuousOn_channelAmplitudeDeriv hs0 hs1 hc hk hX))


/-- The inner edge of the dilated channel, where the Bessel energy is measured.  Every point of
the channel has phase at least this large, so a single energy constant serves the whole range. -/
def channelBase (s c k : ℝ) : ℝ := c * xiEndpointPhase s (2 * k)

theorem channelBase_pos {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) :
    0 < channelBase s c k := by
  have h2k : (1 : ℝ) < 2 * k := by linarith
  have := xiEndpointPhase_pos hs0 hs1 h2k
  unfold channelBase
  positivity

theorem channelBase_le {s c k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k)
    (hx : 2 ≤ x) : channelBase s c k ≤ c * xiEndpointPhase s (k * x) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hle : 2 * k ≤ k * x := by nlinarith
  have hmono := (strictMonoOn_xiEndpointPhase hs0 hs1).monotoneOn
    (Set.mem_Ici.mpr (by linarith : (1 : ℝ) ≤ 2 * k))
    (Set.mem_Ici.mpr (by linarith : (1 : ℝ) ≤ k * x)) hle
  exact mul_le_mul_of_nonneg_left hmono hc.le

/-- **The dilated-channel oscillatory integral with the explicit Bessel amplitude.**  The
amplitude of a single channel is `O(1/k)` and the exterior estimate contributes a further
`1/(c k)`, so the channel integral is `O(1/(c k^2))`: summable over the channel index with room
to spare. -/
theorem norm_integral_channel_le {s c k X eps : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hX : 2 ≤ X) (heps : |eps| = 1) :
    ‖∫ t in (2 : ℝ)..X, (((channelAmp s c k t : ℝ) : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ))‖
      ≤ 111 * Real.sqrt (besselEnergy (channelBase s c k)
          * Real.exp (1 / (4 * channelBase s c k))) / (c * k ^ 2) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hbpos : 0 < channelBase s c k := channelBase_pos hs0 hs1 hc0 hk
  set M : ℝ := Real.sqrt (besselEnergy (channelBase s c k)
    * Real.exp (1 / (4 * channelBase s c k))) with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) X,
      HasDerivAt (fun t : ℝ => ((channelAmp s c k t : ℝ) : ℂ))
        (((channelAmpDeriv s c k x : ℝ) : ℂ)) x := by
    intro x hx
    exact ((hasDerivAt_channelAmp hs0 hs1 hc0 hk (hx2 x hx)).ofReal_comp)
  have hac : ContinuousOn (fun t : ℝ => ((channelAmp s c k t : ℝ) : ℂ))
      (Set.uIcc (2 : ℝ) X) := fun x hx => ((hderiv x hx).continuousAt).continuousWithinAt
  have ha'c : ContinuousOn (fun t : ℝ => ((channelAmpDeriv s c k t : ℝ) : ℂ))
      (Set.uIcc (2 : ℝ) X) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_channelAmpDeriv hs0 hs1 hc0 hk hX)
  have hCa : (0 : ℝ) ≤ 37 * M / k := by positivity
  have hmain := norm_integral_exterior_dilated_sharp_le (Ca := 37 * M / k)
    (a := fun t : ℝ => ((channelAmp s c k t : ℝ) : ℂ))
    (a' := fun t : ℝ => ((channelAmpDeriv s c k t : ℝ) : ℂ))
    hX hCa hc0 hk heps hs0 hs1 hderiv hac ha'c
    (fun x hx => by
      have h := abs_channelAmp_le (a := channelBase s c k) hs0 hs1 hk (hx2 x hx) hbpos
        (channelBase_le hs0 hs1 hc0 hk (hx2 x hx))
      rw [← hMdef] at h
      simpa [div_div] using h)
    (fun x hx => by
      have h := abs_channelAmpDeriv_le (a := channelBase s c k) hs0 hs1 hc hk (hx2 x hx) hbpos
        (channelBase_le hs0 hs1 hc0 hk (hx2 x hx))
      rw [← hMdef] at h
      simpa [div_div] using h)
  have hval : 3 * (37 * M / k) / (c * k) = 111 * M / (c * k ^ 2) := by
    field_simp
    ring
  rw [hval] at hmain
  exact hmain


/-- The channel energy constant: the Bessel energy measured at the innermost channel.  Because
`besselEnergy u * exp (1/(4u))` is antitone, this single number dominates every channel. -/
def channelEnergyConstant (s c : ℝ) : ℝ :=
  Real.sqrt (besselEnergy (channelBase s c 1) * Real.exp (1 / (4 * channelBase s c 1)))

theorem channelBase_mono {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) :
    channelBase s c 1 ≤ channelBase s c k := by
  have hmono := (strictMonoOn_xiEndpointPhase hs0 hs1).monotoneOn
    (Set.mem_Ici.mpr (by norm_num : (1 : ℝ) ≤ 2 * 1))
    (Set.mem_Ici.mpr (by linarith : (1 : ℝ) ≤ 2 * k)) (by linarith : 2 * (1 : ℝ) ≤ 2 * k)
  exact mul_le_mul_of_nonneg_left hmono hc.le

/-- The energy at any channel is dominated by the energy at the innermost one. -/
theorem channelEnergy_le {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) :
    Real.sqrt (besselEnergy (channelBase s c k)
        * Real.exp (1 / (4 * channelBase s c k))) ≤ channelEnergyConstant s c := by
  have h1 : 0 < channelBase s c 1 := channelBase_pos hs0 hs1 hc le_rfl
  have hle : channelBase s c 1 ≤ channelBase s c k := channelBase_mono hs0 hs1 hc hk
  have hk1 : 0 < channelBase s c k := lt_of_lt_of_le h1 hle
  have hE := besselEnergy_le_exp h1 hle
  have hstep : besselEnergy (channelBase s c k) * Real.exp (1 / (4 * channelBase s c k))
      ≤ besselEnergy (channelBase s c 1) * Real.exp (1 / (4 * channelBase s c 1)) := by
    have hpos : (0 : ℝ) < Real.exp (1 / (4 * channelBase s c k)) := Real.exp_pos _
    have := mul_le_mul_of_nonneg_right hE hpos.le
    refine le_trans this (le_of_eq ?_)
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  exact Real.sqrt_le_sqrt hstep

/-- **(16)**, with a channel-uniform constant.  The bound `O(1/(c k^2))` has a constant that does
not depend on the channel index, so the channels sum. -/
theorem norm_integral_channel_uniform_le {s c k X eps : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hX : 2 ≤ X) (heps : |eps| = 1) :
    ‖∫ t in (2 : ℝ)..X, (((channelAmp s c k t : ℝ) : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ))‖
      ≤ 111 * channelEnergyConstant s c / (c * k ^ 2) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  refine le_trans (norm_integral_channel_le hs0 hs1 hc hk hX heps) ?_
  have hEle := channelEnergy_le hs0 hs1 hc0 hk
  have hden : (0 : ℝ) < c * k ^ 2 := by positivity
  gcongr


end GaloisForLFunctions.RHTower
