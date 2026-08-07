import GaloisForLFunctions.RHTower.ProlateDunsterDensityTransfer

/-!
# Weak radial limit for exact endpoint-normalized prolate solutions

The exact Dunster/Bessel density is averaged on compact intervals and controlled by a uniform
integrable tail.  The `L¹` transfer from `ProlateDunsterDensityTransfer` then carries the same tail
law to every exact endpoint-normalized radial prolate solution.
-/

noncomputable section

open Filter MeasureTheory Set

namespace GaloisForLFunctions.RHTower

theorem tendsto_profileWeight_fixed_radius
    {ι : Type*} {l : Filter ι} {s : ι → ℝ} (hs : Tendsto s l (nhds 0))
    {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => profileWeight (s i) a) l (nhds (profileWeight 0 a)) := by
  have hleft : 0 < a ^ 2 - 1 := by nlinarith
  have hden : Real.pi * Real.sqrt ((a ^ 2 - 1) * (a ^ 2 - 0)) ≠ 0 := by
    have ha0 : 0 < a := by linarith
    have : 0 < (a ^ 2 - 1) * (a ^ 2 - 0) :=
      by simpa using mul_pos hleft (sq_pos_of_pos ha0)
    positivity
  have hcont : ContinuousAt (fun u : ℝ => profileWeight u a) 0 := by
    rw [show (fun u : ℝ => profileWeight u a) =
        fun u => 1 / (Real.pi * Real.sqrt ((a ^ 2 - 1) * (a ^ 2 - u))) by
      funext u
      rw [profileWeight]]
    exact continuousAt_const.div
      (continuousAt_const.mul
        (Real.continuous_sqrt.continuousAt.comp
          (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)))) hden
  exact hcont.tendsto.comp hs

theorem tendsto_ampFourth_fixed_radius
    {ι : Type*} {l : Filter ι} {s : ι → ℝ} (hs : Tendsto s l (nhds 0))
    {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => ampFourth (s i) a) l (nhds (ampFourth 0 a)) := by
  have hden : Real.sqrt (Real.sqrt ((a ^ 2 - 1) * (a ^ 2 - 0))) ≠ 0 := by
    have hleft : 0 < a ^ 2 - 1 := by nlinarith
    have ha0 : 0 < a := by linarith
    have : 0 < (a ^ 2 - 1) * (a ^ 2 - 0) :=
      by simpa using mul_pos hleft (sq_pos_of_pos ha0)
    positivity
  have hcont : ContinuousAt (fun u : ℝ => ampFourth u a) 0 := by
    rw [show (fun u : ℝ => ampFourth u a) =
        fun u => 1 / Real.sqrt (Real.sqrt ((a ^ 2 - 1) * (a ^ 2 - u))) by
      funext u
      rw [ampFourth]]
    exact continuousAt_const.div
      (Real.continuous_sqrt.continuousAt.comp
        (Real.continuous_sqrt.continuousAt.comp
          (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)))) hden
  exact hcont.tendsto.comp hs

/-- At every fixed strict exterior radius, the Dunster oscillatory argument diverges with the
bandwidth. -/
theorem tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i) {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => c i * xiEndpointPhase (s i) a) l atTop := by
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcPos : ∀ᶠ i in l, 0 < c i := hc.eventually (eventually_gt_atTop 0)
  have hq : 0 < (2 / 3 : ℝ) * Real.sqrt (a ^ 2 - 1) := by
    have : 0 < a ^ 2 - 1 := by nlinarith
    positivity
  have hlinear : Tendsto
      (fun i => ((2 / 3 : ℝ) * Real.sqrt (a ^ 2 - 1)) * c i) l atTop :=
    hc.const_mul_atTop hq
  refine tendsto_atTop_mono' l ?_ hlinear
  filter_upwards [hs0, hsHalf, hcPos] with i hsi0 hsi1 hci
  have hphase := sqrt_div_sqrt_two_le_xiEndpointPhase hsi0 hsi1 ha.le
  have h23 : (2 / 3 : ℝ) * Real.sqrt (a ^ 2 - 1) ≤
      Real.sqrt (a ^ 2 - 1) / Real.sqrt 2 := by
    have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hroot : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
    have hcoeff : (2 / 3 : ℝ) ≤ 1 / Real.sqrt 2 := by
      rw [le_div_iff₀ hsqrt2pos]
      nlinarith
    calc
      (2 / 3 : ℝ) * Real.sqrt (a ^ 2 - 1)
          ≤ (1 / Real.sqrt 2) * Real.sqrt (a ^ 2 - 1) :=
        mul_le_mul_of_nonneg_right hcoeff hroot
      _ = Real.sqrt (a ^ 2 - 1) / Real.sqrt 2 := by
        rw [div_eq_mul_inv]
        ring
  nlinarith

/-- On every fixed compact exterior interval, the explicit squared-profile error tends to zero. -/
theorem tendsto_profileSqError_zero
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    {a b : ℝ} (ha : 1 < a) :
    Tendsto (fun i => profileSqError (s i) (c i) a b) l (nhds 0) := by
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcPos : ∀ᶠ i in l, 0 < c i := hc.eventually (eventually_gt_atTop 0)
  have harg := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hrootTop : Tendsto
      (fun i => Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) l atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp harg)
  have hinvRoot : Tendsto
      (fun i => (Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a)))⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hrootTop
  have hinvC : Tendsto (fun i => (c i)⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hc
  have hW := tendsto_profileWeight_fixed_radius hs ha
  have hA := tendsto_ampFourth_fixed_radius hs ha
  have hterm1 : Tendsto (fun i => 2 * profileWeight (s i) a / c i) l (nhds 0) := by
    simpa [div_eq_mul_inv] using (hW.const_mul 2).mul hinvC
  have hE : Tendsto (fun i =>
      5 * ampFourth (s i) a /
        Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) l (nhds 0) := by
    simpa [div_eq_mul_inv] using (hA.const_mul 5).mul hinvRoot
  have hB : Tendsto (fun i =>
      2 * Real.sqrt (2 / Real.pi) * ampFourth (s i) a +
        5 * ampFourth (s i) a /
          Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) l
      (nhds (2 * Real.sqrt (2 / Real.pi) * ampFourth 0 a)) := by
    convert (hA.const_mul (2 * Real.sqrt (2 / Real.pi))).add hE using 1 <;> ring
  have hterm2 : Tendsto (fun i =>
      (2 * Real.sqrt (2 / Real.pi) * ampFourth (s i) a +
          5 * ampFourth (s i) a /
            Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) *
        (5 * ampFourth (s i) a /
          Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) * (b - a))
      l (nhds 0) := by
    convert (hB.mul hE).mul_const (b - a) using 1 <;> ring
  have hden : Tendsto (fun i => a ^ 2 - s i) l (nhds (a ^ 2)) := by
    simpa using tendsto_const_nhds.sub hs
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have hterm3 : Tendsto (fun i =>
      3 * s i * profileDensity a / (a ^ 2 - s i) * (b - a)) l (nhds 0) := by
    have hnum : Tendsto (fun i => 3 * s i * profileDensity a) l (nhds 0) := by
      have hnum' := hs.const_mul (3 * profileDensity a)
      convert hnum' using 1
      · funext i
        ring
      · ring
    have hquot : Tendsto (fun i =>
        3 * s i * profileDensity a / (a ^ 2 - s i)) l (nhds 0) := by
      convert hnum.div hden ha2 using 1
      · funext i
        change 3 * s i * profileDensity a / (a ^ 2 - s i) =
          3 * s i * profileDensity a / (a ^ 2 - s i)
        rfl
      · ring
    simpa using hquot.mul_const (b - a)
  rw [show (fun i => profileSqError (s i) (c i) a b) = fun i =>
      2 * profileWeight (s i) a / c i +
        (2 * Real.sqrt (2 / Real.pi) * ampFourth (s i) a +
            5 * ampFourth (s i) a /
              Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) *
          (5 * ampFourth (s i) a /
            Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) * (b - a) +
        3 * s i * profileDensity a / (a ^ 2 - s i) * (b - a) by
    funext i
    rw [profileSqError]]
  convert (hterm1.add hterm2).add hterm3 using 1 <;> ring

/-- Compact-interval oscillatory averaging for the literal regular Bessel density. -/
theorem tendsto_intervalIntegral_radialProlateBesselDensity
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Tendsto (fun i => ∫ x in a..b, radialProlateBesselDensity (s i) (c i) x) l
      (nhds (∫ x in a..b, profileDensity x)) := by
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcPos : ∀ᶠ i in l, 0 < c i := hc.eventually (eventually_gt_atTop 0)
  have harg := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hcxi : ∀ᶠ i in l, 1 ≤ c i * xiEndpointPhase (s i) a :=
    harg.eventually (eventually_ge_atTop 1)
  have herr := tendsto_profileSqError_zero hc hs hs0 (b := b) ha
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using squeeze_zero'
    (Filter.Eventually.of_forall fun i => abs_nonneg
      ((∫ x in a..b, radialProlateBesselDensity (s i) (c i) x) -
        ∫ x in a..b, profileDensity x))
    (by
      filter_upwards [hs0, hsHalf, hcPos, hcxi] with i hsi0 hsi1 hci hcxii
      simpa only [radialProlateBesselDensity, profileSqError] using
        abs_integral_profileSq_sub_density_le hsi0 hsi1 ha hab hci hcxii)
    herr

end GaloisForLFunctions.RHTower

end
