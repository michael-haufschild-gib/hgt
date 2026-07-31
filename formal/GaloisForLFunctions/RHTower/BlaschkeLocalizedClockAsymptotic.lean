import GaloisForLFunctions.RHTower.BlaschkeLocalizedFirstReturnSandwich

/-!
# Exact spectral-depth coefficient for the Blaschke return clock

This file normalizes the exact lower and upper first-return clocks.  The
square-root accuracy calibration and the active-coordinate cost are both
subquadratic, while the depth entropy has the exact coefficient
`1 / (4 * blaschkeSpectralSlope a)`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace RHTower

theorem tendsto_inv_natCast_atTop_zero :
    Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
  Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop

theorem tendsto_sqrt_natCast_div_natCast_atTop_zero :
    Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
  have hcongr :
      (fun S : ℝ => Real.sqrt S / S) =ᶠ[atTop]
        fun S : ℝ => 1 / Real.sqrt S := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with S hS
    have hs : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
    rw [eq_div_iff (ne_of_gt hs), div_mul_eq_mul_div,
      Real.mul_self_sqrt hS.le]
    field_simp
  have hreal :
      Tendsto (fun S : ℝ => Real.sqrt S / S) atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' hcongr.symm ?_
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      Real.tendsto_sqrt_atTop
  exact hreal.comp tendsto_natCast_atTop_atTop

theorem tendsto_blaschkeSqrtShiftedScale_div_natCast
    (K : ℝ) :
    Tendsto (fun k : ℕ =>
      blaschkeSqrtShiftedScale K k / (k : ℝ))
      atTop (𝓝 1) := by
  have hK :
      Tendsto (fun k : ℕ => K / (k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hsum :=
    (hone.add hK).add
      tendsto_sqrt_natCast_div_natCast_atTop_zero
  have ht :
      Tendsto (fun k : ℕ =>
        blaschkeSqrtShiftedScale K k / (k : ℝ))
        atTop (𝓝 ((1 + 0) + 0)) := by
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [blaschkeSqrtShiftedScale, blaschkeShiftedScale]
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using ht

theorem tendsto_blaschkeShiftedScale_div_natCast
    (K : ℝ) :
    Tendsto (fun k : ℕ =>
      blaschkeShiftedScale K k / (k : ℝ))
      atTop (𝓝 1) := by
  have hK :
      Tendsto (fun k : ℕ => K / (k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hsum := hone.add hK
  have ht :
      Tendsto (fun k : ℕ =>
        blaschkeShiftedScale K k / (k : ℝ))
        atTop (𝓝 (1 + 0)) := by
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [blaschkeShiftedScale]
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using ht

theorem tendsto_blaschkeSqrtShiftedScale_div_natCast_sq_zero
    (K : ℝ) :
    Tendsto (fun k : ℕ =>
      blaschkeSqrtShiftedScale K k / (k : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hmul :=
    (tendsto_blaschkeSqrtShiftedScale_div_natCast K).mul
      tendsto_inv_natCast_atTop_zero
  have ht :
      Tendsto (fun k : ℕ =>
        blaschkeSqrtShiftedScale K k / (k : ℝ) ^ 2)
        atTop (𝓝 (1 * 0)) := by
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using ht

theorem tendsto_const_div_natCast_sq_zero (C : ℝ) :
    Tendsto (fun k : ℕ => C / (k : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hC :
      Tendsto (fun k : ℕ => C / (k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hmul := hC.mul tendsto_inv_natCast_atTop_zero
  have ht :
      Tendsto (fun k : ℕ => C / (k : ℝ) ^ 2)
        atTop (𝓝 (0 * 0)) := by
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using ht

theorem tendsto_blaschkeSqrtShiftedQuadratic_normalized
    (a K : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun k : ℕ =>
      (blaschkeSqrtShiftedScale K k - blaschkeSpectralOffset a) ^ 2 /
          (4 * blaschkeSpectralSlope a) /
        (k : ℝ) ^ 2)
      atTop (𝓝 (1 / (4 * blaschkeSpectralSlope a))) := by
  have hc :
      Tendsto (fun k : ℕ =>
        blaschkeSpectralOffset a / (k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hlinear :=
    (tendsto_blaschkeSqrtShiftedScale_div_natCast K).sub hc
  have hsquare := hlinear.pow 2
  have hrho : blaschkeSpectralSlope a ≠ 0 :=
    (blaschkeSpectralSlope_pos a ha0 ha1).ne'
  have hscaled :=
    hsquare.div_const (4 * blaschkeSpectralSlope a)
  have ht :
      Tendsto (fun k : ℕ =>
        (blaschkeSqrtShiftedScale K k -
            blaschkeSpectralOffset a) ^ 2 /
            (4 * blaschkeSpectralSlope a) /
          (k : ℝ) ^ 2)
        atTop
        (𝓝 ((1 - 0) ^ 2 /
          (4 * blaschkeSpectralSlope a))) := by
    apply hscaled.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp [hrho]
  simpa using ht

theorem tendsto_blaschkeSqrtShiftedLinearError_normalized
    (a K : ℝ) :
    Tendsto (fun k : ℕ =>
      ((blaschkeSqrtShiftedScale K k - blaschkeSpectralSlope a) / 2 +
          (blaschkeSqrtShiftedScale K k -
            blaschkeSpectralOffset a) / 2 +
          blaschkeSpectralSlope a / 4) /
        (k : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hS :=
    tendsto_blaschkeSqrtShiftedScale_div_natCast_sq_zero K
  have hrho := tendsto_const_div_natCast_sq_zero
    (blaschkeSpectralSlope a)
  have hc := tendsto_const_div_natCast_sq_zero
    (blaschkeSpectralOffset a)
  have hfirst := (hS.sub hrho).div_const 2
  have hsecond := (hS.sub hc).div_const 2
  have hthird :=
    (tendsto_const_div_natCast_sq_zero
      (blaschkeSpectralSlope a)).div_const 4
  have hsum := (hfirst.add hsecond).add hthird
  have ht :
      Tendsto (fun k : ℕ =>
        ((blaschkeSqrtShiftedScale K k -
              blaschkeSpectralSlope a) / 2 +
            (blaschkeSqrtShiftedScale K k -
              blaschkeSpectralOffset a) / 2 +
            blaschkeSpectralSlope a / 4) /
          (k : ℝ) ^ 2)
        atTop (𝓝 ((0 - 0) / 2 + (0 - 0) / 2 + 0 / 4)) := by
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using ht

theorem tendsto_blaschkeDepthWaterEntropy_sqrtShift_normalized
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K) :
    Tendsto (fun k : ℕ =>
      blaschkeDepthWaterEntropy a
          (blaschkeSqrtShiftedScale K k) /
        (k : ℝ) ^ 2)
      atTop (𝓝 (1 / (4 * blaschkeSpectralSlope a))) := by
  have hquad :=
    tendsto_blaschkeSqrtShiftedQuadratic_normalized
      a K ha0 ha1
  have herr :=
    tendsto_blaschkeSqrtShiftedLinearError_normalized a K
  have hupper := hquad.add herr
  have hupper' :
      Tendsto (fun k : ℕ =>
        (blaschkeSqrtShiftedScale K k -
            blaschkeSpectralOffset a) ^ 2 /
            (4 * blaschkeSpectralSlope a) /
          (k : ℝ) ^ 2 +
        ((blaschkeSqrtShiftedScale K k -
              blaschkeSpectralSlope a) / 2 +
            (blaschkeSqrtShiftedScale K k -
              blaschkeSpectralOffset a) / 2 +
            blaschkeSpectralSlope a / 4) /
          (k : ℝ) ^ 2)
        atTop (𝓝 (1 / (4 * blaschkeSpectralSlope a))) := by
    simpa using hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hquad hupper'
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hStail :
        blaschkeSpectralOffset a ≤
          blaschkeSqrtShiftedScale K k := by
      rw [blaschkeSqrtShiftedScale, blaschkeShiftedScale]
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have hsqrt0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      linarith
    have hSzero :
        blaschkeSpectralSlope a ≤
          blaschkeSqrtShiftedScale K k := by
      rw [blaschkeSqrtShiftedScale, blaschkeShiftedScale]
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have hsqrt0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      linarith
    have hb :=
      blaschkeDepthWaterEntropy_shifted_quadratic_bounds
        a ha0 ha1 hStail hSzero
    exact div_le_div_of_nonneg_right hb.1 (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hStail :
        blaschkeSpectralOffset a ≤
          blaschkeSqrtShiftedScale K k := by
      rw [blaschkeSqrtShiftedScale, blaschkeShiftedScale]
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have hsqrt0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      linarith
    have hSzero :
        blaschkeSpectralSlope a ≤
          blaschkeSqrtShiftedScale K k := by
      rw [blaschkeSqrtShiftedScale, blaschkeShiftedScale]
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have hsqrt0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      linarith
    have hb :=
      blaschkeDepthWaterEntropy_shifted_quadratic_bounds
        a ha0 ha1 hStail hSzero
    have hdiv := div_le_div_of_nonneg_right hb.2 (sq_nonneg (k : ℝ))
    convert hdiv using 1 <;> ring

theorem tendsto_blaschkeActiveTailRadius_sqrtShift_normalized
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K) :
    Tendsto (fun k : ℕ =>
      ((blaschkeActiveTailRadius a
          (blaschkeSqrtShiftedScale K k) + 1 : ℕ) : ℝ) /
        (k : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hS :=
    tendsto_blaschkeSqrtShiftedScale_div_natCast_sq_zero K
  have hc :=
    tendsto_const_div_natCast_sq_zero (blaschkeSpectralOffset a)
  have hone := tendsto_const_div_natCast_sq_zero 1
  have hrho : 0 < blaschkeSpectralSlope a :=
    blaschkeSpectralSlope_pos a ha0 ha1
  have hmajor0 := (hS.sub hc).div_const (blaschkeSpectralSlope a)
  have hmajor := hmajor0.add hone
  have hmajor' :
      Tendsto (fun k : ℕ =>
        (((blaschkeSqrtShiftedScale K k -
            blaschkeSpectralOffset a) /
              blaschkeSpectralSlope a) + 1) /
          (k : ℝ) ^ 2)
        atTop (𝓝 0) := by
    have ht :
        Tendsto (fun k : ℕ =>
          (((blaschkeSqrtShiftedScale K k -
              blaschkeSpectralOffset a) /
                blaschkeSpectralSlope a) + 1) /
            (k : ℝ) ^ 2)
          atTop (𝓝 ((0 - 0) / blaschkeSpectralSlope a + 0)) := by
      apply hmajor.congr'
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      field_simp [hrho.ne']
    simpa using ht
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun k => by positivity
  · filter_upwards [eventually_ge_atTop 1] with k hk
    let S := blaschkeSqrtShiftedScale K k
    have hStail : blaschkeSpectralOffset a ≤ S := by
      dsimp only [S, blaschkeSqrtShiftedScale, blaschkeShiftedScale]
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have hsqrt0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      linarith
    have hbracket :=
      blaschkeActiveTailRadius_bracket a ha0 ha1 hStail
    have hR :
        (blaschkeActiveTailRadius a S : ℝ) ≤
          (S - blaschkeSpectralOffset a) /
            blaschkeSpectralSlope a := by
      apply (le_div_iff₀ hrho).2
      simpa only [mul_comm] using hbracket.1
    have hnum :
        ((blaschkeActiveTailRadius a S + 1 : ℕ) : ℝ) ≤
          (S - blaschkeSpectralOffset a) /
              blaschkeSpectralSlope a + 1 := by
      push_cast
      linarith
    exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
  · exact hmajor'

theorem tendsto_blaschkeActiveHeadCost_sqrtShift_normalized
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K) :
    Tendsto (fun k : ℕ =>
      (((blaschkeActiveTailRadius a
          (blaschkeSqrtShiftedScale K k) + 1 : ℕ) : ℝ) *
          Real.log projectivePhaseResolutionConstant) /
        (k : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have h :=
    (tendsto_blaschkeActiveTailRadius_sqrtShift_normalized
      a ha0 ha1 hKtail).mul_const
        (Real.log projectivePhaseResolutionConstant)
  have ht :
      Tendsto (fun k : ℕ =>
        (((blaschkeActiveTailRadius a
            (blaschkeSqrtShiftedScale K k) + 1 : ℕ) : ℝ) *
            Real.log projectivePhaseResolutionConstant) /
          (k : ℝ) ^ 2)
        atTop (𝓝 (0 * Real.log projectivePhaseResolutionConstant)) := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using ht

theorem tendsto_blaschkeConstructiveClockCarrier_normalized
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K) :
    Tendsto (fun k : ℕ =>
      (blaschkeDepthWaterEntropy a
            (blaschkeSqrtShiftedScale K k) +
          ((blaschkeActiveTailRadius a
              (blaschkeSqrtShiftedScale K k) + 1 : ℕ) : ℝ) *
            Real.log projectivePhaseResolutionConstant) /
        (k : ℝ) ^ 2)
      atTop (𝓝 (1 / (4 * blaschkeSpectralSlope a))) := by
  have hH :=
    tendsto_blaschkeDepthWaterEntropy_sqrtShift_normalized
      a ha0 ha1 hKtail hKzero
  have hC :=
    tendsto_blaschkeActiveHeadCost_sqrtShift_normalized
      a ha0 ha1 hKtail
  have hsum := hH.add hC
  have ht :
      Tendsto (fun k : ℕ =>
        (blaschkeDepthWaterEntropy a
              (blaschkeSqrtShiftedScale K k) +
            ((blaschkeActiveTailRadius a
                (blaschkeSqrtShiftedScale K k) + 1 : ℕ) : ℝ) *
              Real.log projectivePhaseResolutionConstant) /
          (k : ℝ) ^ 2)
        atTop (𝓝 (1 / (4 * blaschkeSpectralSlope a) + 0)) := by
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using ht

theorem tendsto_blaschkeShiftedScale_div_natCast_sq_zero
    (K : ℝ) :
    Tendsto (fun k : ℕ =>
      blaschkeShiftedScale K k / (k : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hmul :=
    (tendsto_blaschkeShiftedScale_div_natCast K).mul
      tendsto_inv_natCast_atTop_zero
  have ht :
      Tendsto (fun k : ℕ =>
        blaschkeShiftedScale K k / (k : ℝ) ^ 2)
        atTop (𝓝 (1 * 0)) := by
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using ht

theorem tendsto_blaschkeShiftedQuadraticClock_normalized
    (a K : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun k : ℕ =>
      blaschkeShiftedQuadraticClock a K k / (k : ℝ) ^ 2)
      atTop (𝓝 (1 / (4 * blaschkeSpectralSlope a))) := by
  have hc :
      Tendsto (fun k : ℕ =>
        blaschkeSpectralOffset a / (k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hlinear :=
    (tendsto_blaschkeShiftedScale_div_natCast K).sub hc
  have hsquare := hlinear.pow 2
  have hscaled :=
    hsquare.div_const (4 * blaschkeSpectralSlope a)
  have hrho : blaschkeSpectralSlope a ≠ 0 :=
    (blaschkeSpectralSlope_pos a ha0 ha1).ne'
  have ht :
      Tendsto (fun k : ℕ =>
        blaschkeShiftedQuadraticClock a K k / (k : ℝ) ^ 2)
        atTop
        (𝓝 ((1 - 0) ^ 2 /
          (4 * blaschkeSpectralSlope a))) := by
    apply hscaled.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    rw [blaschkeShiftedQuadraticClock]
    field_simp [hrho]
  simpa using ht

theorem tendsto_blaschkeSubentropyCarrier_normalized
    (a K delta : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun k : ℕ =>
      ((1 - delta) * blaschkeShiftedQuadraticClock a K k -
          blaschkeShiftedScale K k) /
        (k : ℝ) ^ 2)
      atTop
      (𝓝 ((1 - delta) /
        (4 * blaschkeSpectralSlope a))) := by
  have hq :=
    (tendsto_blaschkeShiftedQuadraticClock_normalized
      a K ha0 ha1).const_mul (1 - delta)
  have hL := tendsto_blaschkeShiftedScale_div_natCast_sq_zero K
  have hsub := hq.sub hL
  have ht :
      Tendsto (fun k : ℕ =>
        ((1 - delta) * blaschkeShiftedQuadraticClock a K k -
            blaschkeShiftedScale K k) /
          (k : ℝ) ^ 2)
        atTop
        (𝓝 ((1 - delta) *
            (1 / (4 * blaschkeSpectralSlope a)) - 0)) := by
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
  convert ht using 1 <;> ring

/-- Nat-valued first return along the logarithmic Blaschke target scale.
The default branch is irrelevant once the deterministic upper clock is
available; the theorem below proves eventual finiteness for every packet. -/
noncomputable def blaschkeFirstReturnClock
    (a : ℝ) (x : ℕ → UnitAddCircle) (K : ℝ) (k : ℕ) : ℕ :=
  WithTop.untopD 0
    (countableTorusWeightedFirstCoherenceTime
      (blaschkeLocalizedWeight a) x
      (Real.exp (-blaschkeShiftedScale K k)))

theorem WithTop.coe_untopD_of_ne_top
    {α : Type*} (d : α) (x : WithTop α) (hx : x ≠ ⊤) :
    ((x.untopD d : α) : WithTop α) = x := by
  obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp hx
  rw [← hy, WithTop.untopD_coe]

theorem blaschkeFirstReturnClock_log_bounds_of_sandwich
    (a K delta : ℝ) (x : ℕ → UnitAddCircle) (k T : ℕ)
    (hlower :
      (blaschkeHaarSubentropyDeadline a K delta k :
          WithTop ℕ) <
        countableTorusWeightedFirstCoherenceTime
          (blaschkeLocalizedWeight a) x
          (Real.exp (-blaschkeShiftedScale K k)))
    (hupper :
      countableTorusWeightedFirstCoherenceTime
          (blaschkeLocalizedWeight a) x
          (Real.exp (-blaschkeShiftedScale K k)) ≤ T)
    (hlog :
      Real.log (T : ℝ) ≤
        blaschkeDepthWaterEntropy a
            (blaschkeSqrtShiftedScale K k) +
          (blaschkeActiveTailRadius a
              (blaschkeSqrtShiftedScale K k) + 1 : ℕ) *
            Real.log projectivePhaseResolutionConstant) :
    (1 - delta) * blaschkeShiftedQuadraticClock a K k -
          blaschkeShiftedScale K k <
        Real.log (blaschkeFirstReturnClock a x K k : ℝ) ∧
      Real.log (blaschkeFirstReturnClock a x K k : ℝ) ≤
        blaschkeDepthWaterEntropy a
            (blaschkeSqrtShiftedScale K k) +
          (blaschkeActiveTailRadius a
              (blaschkeSqrtShiftedScale K k) + 1 : ℕ) *
            Real.log projectivePhaseResolutionConstant := by
  let τ :=
    countableTorusWeightedFirstCoherenceTime
      (blaschkeLocalizedWeight a) x
      (Real.exp (-blaschkeShiftedScale K k))
  have hτne : τ ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hupper
  have hcoe :
      ((blaschkeFirstReturnClock a x K k : ℕ) : WithTop ℕ) = τ := by
    rw [blaschkeFirstReturnClock]
    exact WithTop.coe_untopD_of_ne_top 0 τ hτne
  have hlower' := hlower
  have hupper' := hupper
  change (blaschkeHaarSubentropyDeadline a K delta k :
    WithTop ℕ) < τ at hlower'
  change τ ≤ (T : WithTop ℕ) at hupper'
  rw [← hcoe] at hlower' hupper'
  have hNatLower :
      blaschkeHaarSubentropyDeadline a K delta k <
        blaschkeFirstReturnClock a x K k := by
    exact_mod_cast hlower'
  have hNatUpper :
      blaschkeFirstReturnClock a x K k ≤ T := by
    exact_mod_cast hupper'
  let A :=
    (1 - delta) * blaschkeShiftedQuadraticClock a K k -
      blaschkeShiftedScale K k
  let N := blaschkeHaarSubentropyDeadline a K delta k
  have hexpFloor :
      Real.exp A < (N : ℝ) + 1 := by
    dsimp only [N, A, blaschkeHaarSubentropyDeadline]
    exact Nat.lt_floor_add_one _
  have hsucc :
      N + 1 ≤ blaschkeFirstReturnClock a x K k := by
    dsimp only [N] at hNatLower ⊢
    omega
  have hexpClock :
      Real.exp A <
        (blaschkeFirstReturnClock a x K k : ℝ) := by
    have hcast :
        (N : ℝ) + 1 ≤
          (blaschkeFirstReturnClock a x K k : ℝ) := by
      exact_mod_cast hsucc
    exact hexpFloor.trans_le hcast
  have hclockPos :
      0 < (blaschkeFirstReturnClock a x K k : ℝ) :=
    (Real.exp_pos A).trans hexpClock
  constructor
  · have hlogLower :=
      Real.log_lt_log (Real.exp_pos A) hexpClock
    simpa only [Real.log_exp, A] using hlogLower
  · exact
      (Real.log_le_log hclockPos
        (by exact_mod_cast hNatUpper)).trans hlog

theorem ae_eventually_blaschkeFirstReturnClock_log_bounds
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (hKnonneg : 0 ≤ K)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ =>
          (volume : Measure UnitAddCircle)),
      ∀ᶠ k in atTop,
        (1 - delta) * blaschkeShiftedQuadraticClock a K k -
              blaschkeShiftedScale K k <
            Real.log (blaschkeFirstReturnClock a x K k : ℝ) ∧
          Real.log (blaschkeFirstReturnClock a x K k : ℝ) ≤
            blaschkeDepthWaterEntropy a
                (blaschkeSqrtShiftedScale K k) +
              (blaschkeActiveTailRadius a
                  (blaschkeSqrtShiftedScale K k) + 1 : ℕ) *
                Real.log projectivePhaseResolutionConstant := by
  filter_upwards [
    ae_eventually_blaschkeFirstCoherenceTime_spectralDepthSandwich
      a ha0 ha1 hKtail hKzero hKnonneg hdelta] with x hx
  filter_upwards [hx] with k hk
  obtain ⟨hlower, T, hupper, hlog⟩ := hk
  exact blaschkeFirstReturnClock_log_bounds_of_sandwich
    a K delta x k T hlower hupper hlog

/--
Squeezing against every reciprocal subentropy gap closes the exact
quadratic coefficient for one packet.
-/
theorem tendsto_blaschkeFirstReturnClock_normalized_of_all_subentropy
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (x : ℕ → UnitAddCircle)
    (hlower : ∀ m : ℕ, ∀ᶠ k in atTop,
      (1 - (1 : ℝ) / ((m : ℝ) + 1)) *
              blaschkeShiftedQuadraticClock a K k -
            blaschkeShiftedScale K k <
          Real.log (blaschkeFirstReturnClock a x K k : ℝ))
    (hupper : ∀ᶠ k in atTop,
      Real.log (blaschkeFirstReturnClock a x K k : ℝ) ≤
        blaschkeDepthWaterEntropy a
            (blaschkeSqrtShiftedScale K k) +
          (blaschkeActiveTailRadius a
              (blaschkeSqrtShiftedScale K k) + 1 : ℕ) *
            Real.log projectivePhaseResolutionConstant) :
    Tendsto (fun k : ℕ =>
      Real.log (blaschkeFirstReturnClock a x K k : ℝ) /
        (k : ℝ) ^ 2)
      atTop (𝓝 (1 / (4 * blaschkeSpectralSlope a))) := by
  let c : ℝ := 1 / (4 * blaschkeSpectralSlope a)
  have hrho : 0 < blaschkeSpectralSlope a :=
    blaschkeSpectralSlope_pos a ha0 ha1
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hupperCarrier :=
    tendsto_blaschkeConstructiveClockCarrier_normalized
      a ha0 ha1 hKtail hKzero
  apply tendsto_order.2
  constructor
  · intro b hbc
    have hden :
        Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1))
          atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hloss :
        Tendsto (fun m : ℕ => c * ((1 : ℝ) / ((m : ℝ) + 1)))
          atTop (𝓝 0) := by
      simpa only [mul_zero] using hden.const_mul c
    have hlossSmall :
        ∀ᶠ m : ℕ in atTop,
          c * ((1 : ℝ) / ((m : ℝ) + 1)) < c - b :=
      (tendsto_order.1 hloss).2 (c - b) (sub_pos.mpr hbc)
    obtain ⟨m, hm⟩ := hlossSmall.exists
    let delta : ℝ := (1 : ℝ) / ((m : ℝ) + 1)
    have hlimit :
        b < (1 - delta) /
            (4 * blaschkeSpectralSlope a) := by
      dsimp only [delta, c] at hm ⊢
      have hrho4 : 4 * blaschkeSpectralSlope a ≠ 0 := by
        positivity
      field_simp [hrho4] at hm ⊢
      nlinarith
    have hcarrier :=
      tendsto_blaschkeSubentropyCarrier_normalized
        a K delta ha0 ha1
    have hcarrierAbove :
        ∀ᶠ k in atTop,
          b <
            ((1 - delta) *
                  blaschkeShiftedQuadraticClock a K k -
                blaschkeShiftedScale K k) /
              (k : ℝ) ^ 2 :=
      (tendsto_order.1 hcarrier).1 b hlimit
    filter_upwards [
      hcarrierAbove, hlower m, eventually_ge_atTop 1] with k hb hlow hk
    have hkpos : 0 < (k : ℝ) ^ 2 := by positivity
    have hnormalized :
        ((1 - delta) *
              blaschkeShiftedQuadraticClock a K k -
            blaschkeShiftedScale K k) /
            (k : ℝ) ^ 2 <
          Real.log (blaschkeFirstReturnClock a x K k : ℝ) /
            (k : ℝ) ^ 2 :=
      (div_lt_div_iff_of_pos_right hkpos).2 (by
        simpa only [delta] using hlow)
    exact hb.trans hnormalized
  · intro b hcb
    have hcarrierBelow :
        ∀ᶠ k in atTop,
          (blaschkeDepthWaterEntropy a
                (blaschkeSqrtShiftedScale K k) +
              ((blaschkeActiveTailRadius a
                  (blaschkeSqrtShiftedScale K k) + 1 : ℕ) : ℝ) *
                Real.log projectivePhaseResolutionConstant) /
              (k : ℝ) ^ 2 < b :=
      (tendsto_order.1 hupperCarrier).2 b hcb
    filter_upwards [
      hcarrierBelow, hupper, eventually_ge_atTop 1] with k hb hup hk
    have hkpos : 0 < (k : ℝ) ^ 2 := by positivity
    have hnormalized :
        Real.log (blaschkeFirstReturnClock a x K k : ℝ) /
              (k : ℝ) ^ 2 ≤
            (blaschkeDepthWaterEntropy a
                  (blaschkeSqrtShiftedScale K k) +
                ((blaschkeActiveTailRadius a
                    (blaschkeSqrtShiftedScale K k) + 1 : ℕ) : ℝ) *
                  Real.log projectivePhaseResolutionConstant) /
              (k : ℝ) ^ 2 :=
      (div_le_div_iff_of_pos_right hkpos).2 (by
        simpa only using hup)
    exact hnormalized.trans_lt hb

/--
Exact almost-sure first-return law for the countably infinite Blaschke
packet at logarithmic target scales.

For product-Haar phase packets, the logarithm of the actual first positive
return time to amplitude defect `exp (-(k+K))`, divided by `k²`, converges
to the reciprocal of four times the local spectral slope.
-/
theorem ae_tendsto_blaschkeFirstReturnClock_normalized
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (hKnonneg : 0 ≤ K) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ =>
          (volume : Measure UnitAddCircle)),
      Tendsto (fun k : ℕ =>
        Real.log (blaschkeFirstReturnClock a x K k : ℝ) /
          (k : ℝ) ^ 2)
        atTop (𝓝 (1 / (4 * blaschkeSpectralSlope a))) := by
  have hall :
      ∀ m : ℕ,
        ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ =>
              (volume : Measure UnitAddCircle)),
          ∀ᶠ k in atTop,
            (1 - (1 : ℝ) / ((m : ℝ) + 1)) *
                    blaschkeShiftedQuadraticClock a K k -
                  blaschkeShiftedScale K k <
                Real.log (blaschkeFirstReturnClock a x K k : ℝ) ∧
              Real.log (blaschkeFirstReturnClock a x K k : ℝ) ≤
                blaschkeDepthWaterEntropy a
                    (blaschkeSqrtShiftedScale K k) +
                  (blaschkeActiveTailRadius a
                      (blaschkeSqrtShiftedScale K k) + 1 : ℕ) *
                    Real.log projectivePhaseResolutionConstant := by
    intro m
    exact ae_eventually_blaschkeFirstReturnClock_log_bounds
      a ha0 ha1 hKtail hKzero hKnonneg (by positivity)
  have hallAe :
      ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ =>
            (volume : Measure UnitAddCircle)),
        ∀ m : ℕ,
          ∀ᶠ k in atTop,
            (1 - (1 : ℝ) / ((m : ℝ) + 1)) *
                    blaschkeShiftedQuadraticClock a K k -
                  blaschkeShiftedScale K k <
                Real.log (blaschkeFirstReturnClock a x K k : ℝ) ∧
              Real.log (blaschkeFirstReturnClock a x K k : ℝ) ≤
                blaschkeDepthWaterEntropy a
                    (blaschkeSqrtShiftedScale K k) +
                  (blaschkeActiveTailRadius a
                      (blaschkeSqrtShiftedScale K k) + 1 : ℕ) *
                    Real.log projectivePhaseResolutionConstant :=
    ae_all_iff.2 hall
  filter_upwards [hallAe] with x hx
  apply tendsto_blaschkeFirstReturnClock_normalized_of_all_subentropy
    a ha0 ha1 hKtail hKzero x
  · intro m
    exact (hx m).mono fun k hk => hk.1
  · exact (hx 0).mono fun k hk => hk.2

end RHTower
