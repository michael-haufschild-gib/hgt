import GaloisForLFunctions.HTGeometry.StrelitzMaximumSlope

/-!
# Growth of the canonical logarithmic maximum slope

Infinite coefficient support forces the canonical maximum-modulus slope to diverge.  Conversely,
subquadratic logarithmic maximum growth forces this slope to be sublinear.  Existing central-index
growth laws supply that subquadratic bound whenever `ν(r) / log r → 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Set

noncomputable section

/-- Infinite coefficient support forces the exact logarithmic maximum slope to diverge. -/
theorem tendsto_strelitzMaximumSlope_atTop
    {a : ℕ → ℂ} (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    Tendsto (strelitzMaximumSlope a) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt B
  obtain ⟨m, hnm, hm⟩ := htrans n
  have hBm : B < (m : ℝ) := hn.trans_le (by exact_mod_cast hnm)
  let C := Real.log ‖a m‖ - strelitzLogMaximum a 0
  have hlim : Tendsto (fun x : ℝ => (m : ℝ) + C / x) atTop (nhds (m : ℝ)) := by
    have hinv : Tendsto (fun x : ℝ => C / x) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul C
    simpa using tendsto_const_nhds.add hinv
  filter_upwards [hlim.eventually_const_lt hBm, eventually_gt_atTop (0 : ℝ)] with x hB hx
  have hterm := term_le_maxTerm ha (Real.exp_pos x) m
  have hM := maxTerm_le_coeffCircleMaximumNorm ha (Real.exp_pos x)
  have hlog := Real.log_le_log
    (mul_pos (norm_pos_iff.mpr hm) (pow_pos (Real.exp_pos x) m))
    (hterm.trans hM)
  have hlinear : Real.log ‖a m‖ + (m : ℝ) * x ≤ strelitzLogMaximum a x := by
    rw [Real.log_mul (norm_ne_zero_iff.mpr hm)
      (ne_of_gt (pow_pos (Real.exp_pos x) m)), Real.log_pow, Real.log_exp] at hlog
    simpa [strelitzLogMaximum] using hlog
  have hslope : (m : ℝ) + C / x ≤
      slope (strelitzLogMaximum a) x 0 := by
    rw [slope_comm]
    simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul]
    rw [show x⁻¹ * (strelitzLogMaximum a x - strelitzLogMaximum a 0) =
      (strelitzLogMaximum a x - strelitzLogMaximum a 0) / x by
        simp [div_eq_mul_inv, mul_comm]]
    rw [show (m : ℝ) + C / x = ((m : ℝ) * x + C) / x by
      field_simp [ne_of_gt hx]]
    rw [div_le_div_iff_of_pos_right hx]
    dsimp [C]
    linarith
  exact hB.le.trans (hslope.trans
    (slope_le_strelitzMaximumSlope ha hm hx))

/-- A divergent convex right slope is sublinear when the convex function is absolutely
subquadratic. -/
theorem tendsto_convexRightSlope_div_id_zero_of_abs_subquadratic
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hfsq : Tendsto (fun x : ℝ => |f x| / x ^ 2) atTop (nhds 0))
    (hK : Tendsto (convexRightSlope f) atTop atTop) :
    Tendsto (fun x : ℝ => convexRightSlope f x / x) atTop (nhds 0) := by
  have harg : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have htwoRaw := hfsq.comp harg
  have htwo : Tendsto (fun x : ℝ => |f (2 * x)| / x ^ 2) atTop (nhds 0) := by
    convert htwoRaw.const_mul 4 using 1
    · funext x
      simp only [Function.comp_apply]
      by_cases hx : x = 0
      · simp [hx]
      · rw [show (2 * x) ^ 2 = 4 * x ^ 2 by ring]
        field_simp [hx]
    · norm_num
  have hupp : Tendsto (fun x : ℝ =>
      |f (2 * x)| / x ^ 2 + |f x| / x ^ 2) atTop (nhds 0) := by
    simpa using htwo.add hfsq
  refine squeeze_zero' ?_ ?_ hupp
  · filter_upwards [hK.eventually_ge_atTop 0, eventually_gt_atTop (0 : ℝ)] with x hK0 hx
    exact div_nonneg hK0 hx.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hKs := convexRightSlope_le_slope hf (show x < 2 * x by linarith)
    have habs1 : f (2 * x) ≤ |f (2 * x)| := le_abs_self _
    have habs2 : -f x ≤ |f x| := neg_le_abs _
    simp only [slope, vsub_eq_sub, smul_eq_mul] at hKs
    rw [show 2 * x - x = x by ring,
      show x⁻¹ * (f (2 * x) - f x) = (f (2 * x) - f x) / x by
        simp [div_eq_mul_inv, mul_comm]] at hKs
    apply (div_le_iff₀ hx).2
    calc
      convexRightSlope f x ≤ (f (2 * x) - f x) / x := hKs
      _ ≤ (|f (2 * x)| + |f x|) / x :=
        (div_le_div_iff_of_pos_right hx).mpr (by linarith)
      _ = (|f (2 * x)| / x ^ 2 + |f x| / x ^ 2) * x := by
        field_simp [ne_of_gt hx]

/-- The exact circle maximum is bounded by the coefficient majorant at the same radius. -/
theorem coeffCircleMaximumNorm_le_coeffSum
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {r : ℝ} (hr : 0 < r) :
    coeffCircleMaximumNorm a r ≤ coeffSum a r := by
  obtain ⟨θ, hθ⟩ := exists_circleMap_norm_eq_coeffCircleMaximumNorm ha hr
  rw [← hθ]
  have hnorm : 0 < ‖circleMap 0 r θ‖ := by
    rw [norm_circleMap_zero, abs_of_pos hr]
    exact hr
  simpa [norm_circleMap_zero, abs_of_pos hr] using norm_coeffFun_le ha hnorm

/-- A sublogarithmic central index makes the logarithm of the doubled-scale maximum term
subquadratic in logarithmic radius. -/
theorem tendsto_log_maxTerm_exp_two_mul_div_sq_zero_of_centralIndex
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (hν : Tendsto (fun r : ℝ => (centralIndex a r : ℝ) / Real.log r)
      atTop (nhds 0)) :
    Tendsto (fun x : ℝ => Real.log (maxTerm a (Real.exp (2 * x))) / x ^ 2)
      atTop (nhds 0) := by
  have harg : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hν2 : Tendsto (fun x : ℝ =>
      (centralIndex a (Real.exp (2 * x)) : ℝ) / (2 * x)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      hν.comp (Real.tendsto_exp_atTop.comp harg)
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hinvSq : Tendsto (fun x : ℝ => x⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using hinv.pow 2
  let C0 := Real.log ‖a n₀‖
  let C1 := Real.log (maxTerm a 1)
  have hlow : Tendsto (fun x : ℝ =>
      (C0 + (2 * (n₀ : ℝ)) * x) / x ^ 2) atTop (nhds 0) := by
    have hraw := (hinvSq.const_mul C0).add (hinv.const_mul (2 * (n₀ : ℝ)))
    have heq : (fun x : ℝ => C0 * x⁻¹ ^ 2 + 2 * (n₀ : ℝ) * x⁻¹) =ᶠ[atTop]
        (fun x : ℝ => (C0 + (2 * (n₀ : ℝ)) * x) / x ^ 2) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
      field_simp [hx]
    simpa using hraw.congr' heq
  have hupp : Tendsto (fun x : ℝ =>
      (C1 + (centralIndex a (Real.exp (2 * x)) : ℝ) * (2 * x)) / x ^ 2)
      atTop (nhds 0) := by
    have hraw := (hinvSq.const_mul C1).add (hν2.const_mul 4)
    have heq : (fun x : ℝ => C1 * x⁻¹ ^ 2 +
        4 * ((centralIndex a (Real.exp (2 * x)) : ℝ) / (2 * x))) =ᶠ[atTop]
        (fun x : ℝ =>
          (C1 + (centralIndex a (Real.exp (2 * x)) : ℝ) * (2 * x)) / x ^ 2) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
      field_simp [hx]
      ring
    simpa using hraw.congr' heq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hterm := term_le_maxTerm ha (Real.exp_pos (2 * x)) n₀
    have hlog := Real.log_le_log
      (mul_pos (norm_pos_iff.mpr hn₀) (pow_pos (Real.exp_pos (2 * x)) n₀)) hterm
    rw [Real.log_mul (norm_ne_zero_iff.mpr hn₀)
      (ne_of_gt (pow_pos (Real.exp_pos (2 * x)) n₀)),
      Real.log_pow, Real.log_exp] at hlog
    rw [div_le_div_iff_of_pos_right (sq_pos_of_pos hx)]
    dsimp [C0]
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hmu := log_maxTerm_le_centralIndex_mul_log ha
      (show 1 ≤ Real.exp (2 * x) by exact Real.one_le_exp (by linarith)) hn₀
    rw [Real.log_exp] at hmu
    rw [div_le_div_iff_of_pos_right (sq_pos_of_pos hx)]
    dsimp [C1]
    exact hmu

/-- A sublogarithmic central index makes the exact logarithmic maximum absolutely subquadratic. -/
theorem tendsto_abs_strelitzLogMaximum_div_sq_zero_of_centralIndex
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (hν : Tendsto (fun r : ℝ => (centralIndex a r : ℝ) / Real.log r)
      atTop (nhds 0)) :
    Tendsto (fun x : ℝ => |strelitzLogMaximum a x| / x ^ 2) atTop (nhds 0) := by
  have hmu2 := tendsto_log_maxTerm_exp_two_mul_div_sq_zero_of_centralIndex ha hn₀ hν
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hinvSq : Tendsto (fun x : ℝ => x⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using hinv.pow 2
  let C0 := Real.log ‖a n₀‖
  have hlow : Tendsto (fun x : ℝ => (C0 + (n₀ : ℝ) * x) / x ^ 2)
      atTop (nhds 0) := by
    have hraw := (hinvSq.const_mul C0).add (hinv.const_mul (n₀ : ℝ))
    have heq : (fun x : ℝ => C0 * x⁻¹ ^ 2 + (n₀ : ℝ) * x⁻¹) =ᶠ[atTop]
        (fun x : ℝ => (C0 + (n₀ : ℝ) * x) / x ^ 2) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
      field_simp [hx]
    simpa using hraw.congr' heq
  have hupp : Tendsto (fun x : ℝ =>
      (Real.log 2 + Real.log (maxTerm a (Real.exp (2 * x)))) / x ^ 2)
      atTop (nhds 0) := by
    have hraw := (hinvSq.const_mul (Real.log 2)).add hmu2
    have heq : (fun x : ℝ => Real.log 2 * x⁻¹ ^ 2 +
        Real.log (maxTerm a (Real.exp (2 * x))) / x ^ 2) =ᶠ[atTop]
        (fun x : ℝ =>
          (Real.log 2 + Real.log (maxTerm a (Real.exp (2 * x)))) / x ^ 2) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
      field_simp [hx]
    simpa using hraw.congr' heq
  have hphi : Tendsto (fun x : ℝ => strelitzLogMaximum a x / x ^ 2)
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hterm := term_le_maxTerm ha (Real.exp_pos x) n₀
      have hM := maxTerm_le_coeffCircleMaximumNorm ha (Real.exp_pos x)
      have hlog := Real.log_le_log
        (mul_pos (norm_pos_iff.mpr hn₀) (pow_pos (Real.exp_pos x) n₀))
        (hterm.trans hM)
      rw [Real.log_mul (norm_ne_zero_iff.mpr hn₀)
        (ne_of_gt (pow_pos (Real.exp_pos x) n₀)),
        Real.log_pow, Real.log_exp] at hlog
      rw [div_le_div_iff_of_pos_right (sq_pos_of_pos hx)]
      dsimp [C0]
      simpa [strelitzLogMaximum] using hlog
    · filter_upwards [eventually_gt_atTop (Real.log 2), eventually_gt_atTop (0 : ℝ)]
        with x hx2 hx
      have hMsum := coeffCircleMaximumNorm_le_coeffSum ha (Real.exp_pos x)
      have hsum := coeffSum_le_two_mul_maxTerm ha (Real.exp_pos x)
      have hscale : 2 * Real.exp x ≤ Real.exp (2 * x) := by
        calc
          2 * Real.exp x = Real.exp (Real.log 2 + x) := by
            rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (by linarith)
      have hmono := maxTerm_mono ha (show 0 < 2 * Real.exp x by positivity) hscale
      have hle : coeffCircleMaximumNorm a (Real.exp x) ≤
          2 * maxTerm a (Real.exp (2 * x)) :=
        hMsum.trans (hsum.trans (mul_le_mul_of_nonneg_left hmono (by norm_num)))
      have hMpos := coeffCircleMaximumNorm_pos ha hn₀ (Real.exp_pos x)
      obtain ⟨_, _, hμpos⟩ := exists_maxTerm_eq ha (Real.exp_pos (2 * x)) hn₀
      have hlog := Real.log_le_log hMpos hle
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hμpos)] at hlog
      rw [div_le_div_iff_of_pos_right (sq_pos_of_pos hx)]
      simpa [strelitzLogMaximum] using hlog
  have habs := hphi.abs
  have heq : (fun x : ℝ => |strelitzLogMaximum a x / x ^ 2|) =ᶠ[atTop]
      (fun x : ℝ => |strelitzLogMaximum a x| / x ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [abs_div, abs_of_nonneg (sq_nonneg x)]
  simpa using habs.congr' heq

/-- Under infinite support and sublogarithmic central index, the exact logarithmic maximum slope is
both divergent and sublinear. -/
theorem tendsto_strelitzMaximumSlope_div_id_zero_of_centralIndex
    {a : ℕ → ℂ} (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (hν : Tendsto (fun r : ℝ => (centralIndex a r : ℝ) / Real.log r)
      atTop (nhds 0)) :
    Tendsto (fun x : ℝ => strelitzMaximumSlope a x / x) atTop (nhds 0) := by
  simpa [strelitzMaximumSlope] using
    tendsto_convexRightSlope_div_id_zero_of_abs_subquadratic
      (convexOn_strelitzLogMaximum ha hn₀)
      (tendsto_abs_strelitzLogMaximum_div_sq_zero_of_centralIndex ha hn₀ hν)
      (tendsto_strelitzMaximumSlope_atTop ha htrans)

end

end GaloisForLFunctions.HTGeometry
