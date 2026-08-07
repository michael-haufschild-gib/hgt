import GaloisForLFunctions.RHTower.ProlateDunsterEndpointCrossing

/-!
# Uniform bounds for the endpoint-normalized radial comparison profile

The explicit zero-free collar makes the radial profile positive and decreasing.  Dunster's
amplitude is uniformly separated from zero there, hence the transformed solution `U = R/A_s` is
bounded by two.  Companion phase bounds control both the Bessel argument and its logarithmic
endpoint envelope.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set

/-- Dunster's amplitude stays above `1/2` throughout the elementary endpoint collar. -/
theorem one_half_le_xiAmplitude_endpoint_collar {s x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx1 : 1 < x) (hx2 : x ≤ 11 / 10) :
    (1 / 2 : ℝ) ≤ xiAmplitude s x := by
  have hd : 0 < x ^ 2 - 1 := by nlinarith
  have hd1 : x ^ 2 - 1 ≤ 1 := by nlinarith
  have hn : 0 < x ^ 2 - s := by nlinarith
  have hratio : (2 / 5 : ℝ) ≤ (1 - s) / (x ^ 2 - s) := by
    rw [le_div_iff₀ hn]
    nlinarith
  have hfac : (9 / 10 : ℝ) ≤ 1 - (x ^ 2 - 1) / 6 := by nlinarith
  have hfac0 : 0 ≤ (9 / 10 : ℝ) := by norm_num
  have hfacpow : (9 / 10 : ℝ) ^ 2 ≤ (1 - (x ^ 2 - 1) / 6) ^ 2 :=
    pow_le_pow_left₀ hfac0 hfac 2
  have hproduct : (1 / 16 : ℝ) ≤
      (1 - s) / (x ^ 2 - s) * (1 - (x ^ 2 - 1) / 6) ^ 2 := by
    have hmul := mul_le_mul hratio hfacpow (by positivity)
      (div_nonneg (by linarith) hn.le)
    norm_num at hmul ⊢
    linarith
  have hamp4 := (xiAmplitude_pow_four_endpoint_bounds hs0 hs1 hx1 hd1).1
  have hlower : (1 / 16 : ℝ) ≤ xiAmplitude s x ^ 4 := hproduct.trans hamp4
  have hamp0 := (xiAmplitude_pos hs0 hs1 hx1).le
  by_contra hnot
  push Not at hnot
  have hpow : xiAmplitude s x ^ 4 < (1 / 2 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hnot hamp0 (by norm_num)
  norm_num at hpow hlower
  linarith

/-- The endpoint-normalized radial profile is positive and at most one up to the matching point. -/
theorem radialProlate_unit_bounds_to_crossing {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hx : x ∈ Icc (1 : ℝ) (dunsterEndpointCrossing c)) :
    0 < R x ∧ R x ≤ 1 := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 := (dunsterEndpointCrossing_gt_one hc0).le
  have hB2 := dunsterEndpointCrossing_le_eleven_tenths hc
  have hpos := radialProlate_pos_endpoint_collar hs0 hs1 hB1 hB2
    (dunsterEndpointCrossing_short hc0) hR1 hR hDR hode
  have hnonneg : ∀ t ∈ Icc (1 : ℝ) (dunsterEndpointCrossing c), 0 ≤ R t :=
    fun t ht => (hpos t ht).le
  have hanti := radialProlate_antitoneOn_of_nonnegative hs1 hB1 hR hDR hode hnonneg
  refine ⟨hpos x hx, ?_⟩
  simpa only [hR1] using hanti ⟨le_rfl, hB1⟩ hx hx.1

/-- The exact transformed radial solution is uniformly bounded by two in the open endpoint collar. -/
theorem abs_comparisonSol_prolateNormalForm_le_two_to_crossing
    {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hx1 : 1 < x) (hx2 : x ≤ dunsterEndpointCrossing c) :
    |comparisonSol (prolateNormalFormSol R) s x| ≤ 2 := by
  have hB2 := dunsterEndpointCrossing_le_eleven_tenths hc
  have hRx := radialProlate_unit_bounds_to_crossing hs0 hs1 hc hR1 hR hDR hode
    ⟨hx1.le, hx2⟩
  have hA := one_half_le_xiAmplitude_endpoint_collar hs0 hs1 hx1 (le_trans hx2 hB2)
  have hApos := xiAmplitude_pos hs0 hs1 hx1
  rw [comparisonSol_prolateNormalForm_eq_div_xiAmplitude hs0 hs1 hx1,
    abs_of_pos hRx.1, div_le_iff₀ hApos]
  nlinarith

/-- Uniform lower phase bracket used to integrate the inverse logarithmic envelope. -/
theorem two_thirds_mul_sqrt_le_xiEndpointPhase_endpoint_collar {s x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx1 : 1 < x) (hx2 : x ≤ 11 / 10) :
    (2 / 3 : ℝ) * Real.sqrt (x ^ 2 - 1) ≤ xiEndpointPhase s x := by
  have hd : 0 ≤ x ^ 2 - 1 := by nlinarith
  have hdsmall : x ^ 2 - 1 ≤ 2 / 7 := by nlinarith
  have hA : (7 / 10 : ℝ) ≤ Real.sqrt (1 - s) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hF : (20 / 21 : ℝ) ≤ 1 - (x ^ 2 - 1) / 6 := by nlinarith
  have hroot0 := Real.sqrt_nonneg (x ^ 2 - 1)
  have hAF : (2 / 3 : ℝ) * Real.sqrt (x ^ 2 - 1)
      ≤ Real.sqrt (1 - s) *
          (Real.sqrt (x ^ 2 - 1) * (1 - (x ^ 2 - 1) / 6)) := by
    have hmul : (7 / 10 : ℝ) * (Real.sqrt (x ^ 2 - 1) * (20 / 21))
        ≤ Real.sqrt (1 - s) *
            (Real.sqrt (x ^ 2 - 1) * (1 - (x ^ 2 - 1) / 6)) := by
      exact mul_le_mul hA (mul_le_mul_of_nonneg_left hF hroot0) (by positivity)
        (Real.sqrt_nonneg _)
    convert hmul using 1 <;> ring
  have hlog := GaloisForLFunctions.HTGeometry.sqrt_mul_one_sub_le_endpointLog hx1.le
  have hphase := sqrt_one_sub_mul_endpointLog_le_xiEndpointPhase hs0 hs1 hx1.le
  exact hAF.trans ((mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)).trans hphase)

/-- Elementary global envelope for a positive logarithm argument. -/
theorem abs_log_le_self_add_inv {u : ℝ} (hu : 0 < u) :
    |Real.log u| ≤ u + u⁻¹ := by
  rw [abs_le]
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hu
    have hinv : 0 < u⁻¹ := inv_pos.mpr hu
    linarith
  · have h := Real.log_le_sub_one_of_pos hu
    have hinv : 0 < u⁻¹ := inv_pos.mpr hu
    linarith

end GaloisForLFunctions.RHTower

end
