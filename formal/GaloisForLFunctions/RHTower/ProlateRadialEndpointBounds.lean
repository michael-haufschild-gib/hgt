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
  have hd : 0 < x ^ (2 : ℕ) - 1 := by nlinarith
  have hd1 : x ^ (2 : ℕ) - 1 ≤ 1 := by nlinarith
  have hn : 0 < x ^ (2 : ℕ) - s := by nlinarith
  have hratio : (2 / 5 : ℝ) ≤ (1 - s) / (x ^ (2 : ℕ) - s) := by
    rw [le_div_iff₀ hn]
    nlinarith
  have hfac : (9 / 10 : ℝ) ≤ 1 - (x ^ (2 : ℕ) - 1) / 6 := by nlinarith
  have hfac0 : 0 ≤ (9 / 10 : ℝ) := by norm_num
  have hfacpow : (9 / 10 : ℝ) ^ (2 : ℕ) ≤ (1 - (x ^ (2 : ℕ) - 1) / 6) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hfac0 hfac 2
  have hproduct : (1 / 16 : ℝ) ≤
      (1 - s) / (x ^ (2 : ℕ) - s) * (1 - (x ^ (2 : ℕ) - 1) / 6) ^ (2 : ℕ) := by
    have hmul := mul_le_mul hratio hfacpow (by positivity)
      (div_nonneg (by linarith) hn.le)
    norm_num at hmul ⊢
    linarith
  have hamp4 := (xiAmplitude_pow_four_endpoint_bounds hs0 hs1 hx1 hd1).1
  have hlower : (1 / 16 : ℝ) ≤ xiAmplitude s x ^ (4 : ℕ) := hproduct.trans hamp4
  have hamp0 := (xiAmplitude_pos hs0 hs1 hx1).le
  by_contra hnot
  push Not at hnot
  have hpow : xiAmplitude s x ^ (4 : ℕ) < (1 / 2 : ℝ) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ hnot hamp0 (by norm_num)
  norm_num at hpow hlower
  linarith

/-- The endpoint-normalized radial profile is positive and at most one up to the matching point. -/
theorem radialProlate_unit_bounds_to_crossing {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hx : x ∈ Icc (1 : ℝ) (dunsterEndpointCrossing c)) :
    0 < R x ∧ R x ≤ 1 := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 := (dunsterEndpointCrossing_gt_one hc0).le
  have hB2 := dunsterEndpointCrossing_le_eleven_tenths hc
  have hpos := radialProlate_pos_endpoint_collar hs0 (by linarith : s ≤ 1) hB1 hB2
    (dunsterEndpointCrossing_short hc0) hR1 hR hDR hode
  have hnonneg : ∀ t ∈ Icc (1 : ℝ) (dunsterEndpointCrossing c), 0 ≤ R t :=
    fun t ht => (hpos t ht).le
  have hanti := radialProlate_antitoneOn_of_nonnegative (by linarith : s ≤ 1)
    hB1 hR hDR hode hnonneg
  refine ⟨hpos x hx, ?_⟩
  simpa only [hR1] using hanti ⟨le_rfl, hB1⟩ hx hx.1

/-- The exact transformed radial solution is uniformly bounded by two in the open endpoint collar. -/
theorem abs_comparisonSol_prolateNormalForm_le_two_to_crossing
    {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hx1 : 1 < x) (hx2 : x ≤ dunsterEndpointCrossing c) :
    |comparisonSol (prolateNormalFormSol R) s x| ≤ 2 := by
  have hB2 := dunsterEndpointCrossing_le_eleven_tenths hc
  have hRx := radialProlate_unit_bounds_to_crossing hs0 hs1 hc hR1 hR hDR hode
    ⟨hx1.le, hx2⟩
  have hA := one_half_le_xiAmplitude_endpoint_collar hs0 hs1 hx1 (le_trans hx2 hB2)
  have hApos := xiAmplitude_pos hs0 hs1 hx1
  rw [comparisonSol_prolateNormalForm_eq_div_xiAmplitude hs0 hs1 hx1,
    abs_div, abs_of_pos hRx.1, abs_of_pos hApos, div_le_iff₀ hApos]
  nlinarith

/-- Uniform lower phase bracket used to integrate the inverse logarithmic envelope. -/
theorem two_thirds_mul_sqrt_le_xiEndpointPhase_endpoint_collar {s x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx1 : 1 < x) (hx2 : x ≤ 11 / 10) :
    (2 / 3 : ℝ) * Real.sqrt (x ^ (2 : ℕ) - 1) ≤ xiEndpointPhase s x := by
  have hd : 0 ≤ x ^ (2 : ℕ) - 1 := by nlinarith
  have hdsmall : x ^ (2 : ℕ) - 1 ≤ 2 / 7 := by nlinarith
  have hA : (7 / 10 : ℝ) ≤ Real.sqrt (1 - s) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hF : (20 / 21 : ℝ) ≤ 1 - (x ^ (2 : ℕ) - 1) / 6 := by nlinarith
  have hroot0 := Real.sqrt_nonneg (x ^ (2 : ℕ) - 1)
  have hAF : (2 / 3 : ℝ) * Real.sqrt (x ^ (2 : ℕ) - 1)
      ≤ Real.sqrt (1 - s) *
          (Real.sqrt (x ^ (2 : ℕ) - 1) * (1 - (x ^ (2 : ℕ) - 1) / 6)) := by
    have hmul : (7 / 10 : ℝ) * (Real.sqrt (x ^ (2 : ℕ) - 1) * (20 / 21))
        ≤ Real.sqrt (1 - s) *
            (Real.sqrt (x ^ (2 : ℕ) - 1) * (1 - (x ^ (2 : ℕ) - 1) / 6)) := by
      exact mul_le_mul hA (mul_le_mul_of_nonneg_left hF hroot0) (by positivity)
        (Real.sqrt_nonneg _)
    convert hmul using 1
    all_goals ring
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

/-- The Bessel argument remains at most two throughout the explicit endpoint layer. -/
theorem c_mul_xiEndpointPhase_crossing_le_two {s c : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) :
    c * xiEndpointPhase s (dunsterEndpointCrossing c) ≤ 2 := by
  let delta : ℝ := 9 / (8 * c ^ (2 : ℕ))
  let B : ℝ := 1 + delta
  let d : ℝ := B ^ (2 : ℕ) - 1
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hc2 : 25 ≤ c ^ (2 : ℕ) := by nlinarith
  have hden : 0 < 8 * c ^ (2 : ℕ) := by positivity
  have hdelta0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdeltale : delta ≤ 1 / 20 := by
    dsimp [delta]
    rw [div_le_iff₀ hden]
    nlinarith
  have hdeltasq : delta ^ (2 : ℕ) ≤ delta / 20 := by
    have := mul_nonneg hdelta0 (sub_nonneg.mpr hdeltale)
    nlinarith
  have hB : B = dunsterEndpointCrossing c := by rfl
  have hB0 : 0 ≤ B := by dsimp [B]; linarith
  have hBle : B ≤ 11 / 10 := by
    rw [hB]
    exact dunsterEndpointCrossing_le_eleven_tenths hc
  have hd0 : 0 ≤ d := by dsimp [d, B]; nlinarith
  have hcd : c ^ (2 : ℕ) * d ≤ 5 / 2 := by
    have hcne : c ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hc0.ne'
    have hcdelta : c ^ (2 : ℕ) * delta = 9 / 8 := by
      dsimp [delta]
      field_simp [hcne]
    have hdform : d = 2 * delta + delta ^ (2 : ℕ) := by
      dsimp [d, B]
      ring
    rw [hdform]
    have hstep : 2 * delta + delta ^ (2 : ℕ) ≤ (41 / 20 : ℝ) * delta := by
      nlinarith
    calc
      c ^ (2 : ℕ) * (2 * delta + delta ^ (2 : ℕ))
          ≤ c ^ (2 : ℕ) * ((41 / 20 : ℝ) * delta) :=
            mul_le_mul_of_nonneg_left hstep (sq_nonneg c)
      _ = (41 / 20 : ℝ) * (c ^ (2 : ℕ) * delta) := by ring
      _ = (41 / 20 : ℝ) * (9 / 8) := by rw [hcdelta]
      _ ≤ 5 / 2 := by norm_num
  have hBsq : B ^ (2 : ℕ) ≤ (11 / 10 : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hB0 hBle 2
  have hproduct : c ^ (2 : ℕ) * B ^ (2 : ℕ) * d ≤ 4 := by
    have hmul := mul_le_mul hBsq hcd (mul_nonneg (sq_nonneg c) hd0) (by positivity)
    norm_num at hmul ⊢
    nlinarith
  have hsqrt : Real.sqrt d ^ (2 : ℕ) = d := Real.sq_sqrt hd0
  have hgeom : c * B * Real.sqrt d ≤ 2 := by
    have hgeom0 : 0 ≤ c * B * Real.sqrt d := by positivity
    have hsq : (c * B * Real.sqrt d) ^ (2 : ℕ) = c ^ (2 : ℕ) * B ^ (2 : ℕ) * d := by
      calc
        (c * B * Real.sqrt d) ^ (2 : ℕ) = c ^ (2 : ℕ) * B ^ (2 : ℕ) * Real.sqrt d ^ (2 : ℕ) := by ring
        _ = c ^ (2 : ℕ) * B ^ (2 : ℕ) * d := by rw [hsqrt]
    nlinarith
  have hphase := xiEndpointPhase_le_sqrt_mul_endpointLog hs0 hs1
    (dunsterEndpointCrossing_gt_one hc0).le
  have hsqrtNum : Real.sqrt (B ^ (2 : ℕ) - s) ≤ B := by
    rw [Real.sqrt_le_iff]
    exact ⟨hB0, by nlinarith⟩
  have hlog := GaloisForLFunctions.HTGeometry.endpointLog_le_sqrt
    (dunsterEndpointCrossing_gt_one hc0).le
  rw [← hB] at hphase hlog ⊢
  change GaloisForLFunctions.HTGeometry.endpointLog B ≤ Real.sqrt d at hlog
  have hlog0 : 0 ≤ GaloisForLFunctions.HTGeometry.endpointLog B := by
    have hlower := GaloisForLFunctions.HTGeometry.sqrt_mul_one_sub_le_endpointLog
      (show 1 ≤ B by linarith)
    change Real.sqrt d * (1 - d / 6) ≤
      GaloisForLFunctions.HTGeometry.endpointLog B at hlower
    have hdsmall : d ≤ 3 / 20 := by
      dsimp [d]
      rw [hB]
      exact dunsterEndpointCrossing_sq_sub_one_le hc
    exact (mul_nonneg (Real.sqrt_nonneg _) (by linarith)).trans hlower
  have htoGeom : xiEndpointPhase s B ≤ B * Real.sqrt d :=
    hphase.trans (mul_le_mul hsqrtNum hlog hlog0 hB0)
  exact (mul_le_mul_of_nonneg_left htoGeom hc0.le).trans (by
    simpa only [mul_assoc] using hgeom)

/-- Integrable endpoint envelope for the logarithmic Bessel branch. -/
theorem abs_lgBesselModel2_le_endpoint_envelope {s c x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hx1 : 1 < x) (hx2 : x ≤ dunsterEndpointCrossing c) :
    |lgBesselModel2 s c x| ≤
      4 + 3 / (2 * c * Real.sqrt (x ^ (2 : ℕ) - 1)) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 := (dunsterEndpointCrossing_gt_one hc0).le
  have hB2 := dunsterEndpointCrossing_le_eleven_tenths hc
  have hphase0 := xiEndpointPhase_pos hs0 hs1 hx1
  have hu0 : 0 < c * xiEndpointPhase s x := mul_pos hc0 hphase0
  have hphaseMono := xiEndpointPhase_le_of_le hs0 hs1 hx1.le hx2
  have hu2 : c * xiEndpointPhase s x ≤ 2 :=
    (mul_le_mul_of_nonneg_left hphaseMono hc0.le).trans
      (c_mul_xiEndpointPhase_crossing_le_two hs0 hs1 hc)
  have hd0 : 0 < x ^ (2 : ℕ) - 1 := by nlinarith
  have hsqrt0 : 0 < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hd0
  have hphaseLower := two_thirds_mul_sqrt_le_xiEndpointPhase_endpoint_collar
    hs0 hs1 hx1 (le_trans hx2 hB2)
  have hinv : (c * xiEndpointPhase s x)⁻¹
      ≤ 3 / (2 * c * Real.sqrt (x ^ (2 : ℕ) - 1)) := by
    rw [show (c * xiEndpointPhase s x)⁻¹ = 1 / (c * xiEndpointPhase s x) by
      simp only [one_div]]
    rw [div_le_div_iff₀ hu0 (by positivity : 0 < 2 * c * Real.sqrt (x ^ (2 : ℕ) - 1))]
    nlinarith [mul_le_mul_of_nonneg_left hphaseLower hc0.le]
  have hmodel := (abs_lgBesselModel_le_log_envelope s c x).2
  have hlog := abs_log_le_self_add_inv hu0
  linarith

/-- Endpoint logarithm at the matching point is `O(c^-1)`, uniformly in `s`. -/
theorem endpointLog_crossing_le_twenty_div_seven_c {s c : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) :
    GaloisForLFunctions.HTGeometry.endpointLog (dunsterEndpointCrossing c)
      ≤ 20 / (7 * c) := by
  let B := dunsterEndpointCrossing c
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 : 1 < B := dunsterEndpointCrossing_gt_one hc0
  have hdsmall : B ^ (2 : ℕ) - 1 ≤ 3 / 20 := dunsterEndpointCrossing_sq_sub_one_le hc
  have hlogLower := GaloisForLFunctions.HTGeometry.sqrt_mul_one_sub_le_endpointLog hB1.le
  have hlog0 : 0 ≤ GaloisForLFunctions.HTGeometry.endpointLog B := by
    have hfac : 0 ≤ 1 - (B ^ (2 : ℕ) - 1) / 6 := by linarith
    exact (mul_nonneg (Real.sqrt_nonneg _) hfac).trans hlogLower
  have hA : (7 / 10 : ℝ) ≤ Real.sqrt (1 - s) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hphase := sqrt_one_sub_mul_endpointLog_le_xiEndpointPhase hs0 hs1 hB1.le
  have hlower : (7 / 10 : ℝ) * GaloisForLFunctions.HTGeometry.endpointLog B
      ≤ xiEndpointPhase s B :=
    (mul_le_mul_of_nonneg_right hA hlog0).trans hphase
  have hupper : c * xiEndpointPhase s B ≤ 2 :=
    c_mul_xiEndpointPhase_crossing_le_two hs0 hs1 hc
  have hscaled := mul_le_mul_of_nonneg_left hlower hc0.le
  dsimp only [B] at hscaled hupper ⊢
  have hc7 : 0 < 7 * c := by positivity
  rw [le_div_iff₀ hc7]
  nlinarith

end GaloisForLFunctions.RHTower

end
