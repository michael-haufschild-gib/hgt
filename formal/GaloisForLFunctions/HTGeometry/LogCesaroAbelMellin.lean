import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Logarithmic Cesàro means and Mellin–Abel means

**Theorem** (`tendsto_sq_mul_integral_of_tendsto_div_log`).  If `Q` is measurable and bounded on
compact parts of `[1, ∞)` and
`Q(x)/log x → c`, then `b² ∫_1^∞ Q(x) x^{−b−1} dx → c` as `b → 0⁺`.

This is the Abelian direction for the logarithmic scale: `∫_1^∞ log x · x^{−b−1} dx = 1/b²`, and an
`o(log x)` remainder contributes `o(1/b²)`.
-/

open Real Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.LogCesaro

/-- `∫_1^∞ log x · x^{−b−1} dx = 1/b²` for `b > 0`. -/
theorem integral_log_mul_rpow {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (1 : ℝ), Real.log x * x ^ (-b - 1) = 1 / b ^ 2 := by
  set F : ℝ → ℝ := fun x => -(Real.log x * x ^ (-b)) / b - x ^ (-b) / b ^ 2 with hF
  have hderiv : ∀ x ∈ Ici (1 : ℝ), HasDerivAt F (Real.log x * x ^ (-b - 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    have h1 : HasDerivAt (fun y : ℝ => Real.log y * y ^ (-b))
        (x⁻¹ * x ^ (-b) + Real.log x * (-b * x ^ (-b - 1))) x :=
      (Real.hasDerivAt_log hx0.ne').mul (Real.hasDerivAt_rpow_const (Or.inl hx0.ne'))
    have h2 : HasDerivAt (fun y : ℝ => y ^ (-b)) (-b * x ^ (-b - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
    have h := (h1.neg.div_const b).sub (h2.div_const (b ^ 2))
    have hxb : x ^ (-b - 1) = x ^ (-b) * x⁻¹ := by
      rw [Real.rpow_sub hx0, Real.rpow_one, div_eq_mul_inv]
    refine h.congr_deriv ?_
    rw [hxb]
    field_simp
    ring
  have hint : IntegrableOn (fun x => Real.log x * x ^ (-b - 1)) (Ioi (1 : ℝ)) := by
    have hdom : IntegrableOn (fun x : ℝ => (2 / b) * x ^ (-(b / 2) - 1)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    refine hdom.mono' ?_ ?_
    · exact (ContinuousOn.mul (Real.continuousOn_log.mono fun x hx => (ne_of_gt
        (lt_trans one_pos hx)))
        (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_trans one_pos hx))))
        |>.aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
      have hx0 : 0 < x := lt_trans one_pos hx
      have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlog (Real.rpow_nonneg hx0.le _))]
      -- `log x ≤ (2/b) x^{b/2}`
      have hle : Real.log x ≤ (2 / b) * x ^ (b / 2) := by
        have := Real.log_le_rpow_div hx0.le (by positivity : 0 < b / 2)
        calc Real.log x ≤ x ^ (b / 2) / (b / 2) := this
          _ = (2 / b) * x ^ (b / 2) := by field_simp
      calc Real.log x * x ^ (-b - 1) ≤ (2 / b) * x ^ (b / 2) * x ^ (-b - 1) :=
            mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hx0.le _)
        _ = (2 / b) * x ^ (-(b / 2) - 1) := by
            rw [mul_assoc, ← Real.rpow_add hx0]; congr 2; ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x * x ^ (-b)) atTop (𝓝 0) := by
      have h := (isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.rpow_neg hx.le, div_eq_mul_inv]
    have h2 := tendsto_rpow_neg_atTop hb
    have h := ((h1.neg.div_const b).sub (h2.div_const (b ^ 2)))
    simpa [hF] using h
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp [hF]

/-- `∫_1^∞ x^{−b−1} dx = 1/b` for `b > 0`. -/
theorem integral_rpow_neg_sub_one {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (1 : ℝ), x ^ (-b - 1) = 1 / b := by
  rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow, show -b - 1 + 1 = -b by ring,
    neg_div_neg_eq]

theorem integrableOn_log_mul_rpow {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x => Real.log x * x ^ (-b - 1)) (Ioi (1 : ℝ)) := by
  by_contra h
  have := integral_log_mul_rpow hb
  rw [integral_undef h] at this
  have : (0 : ℝ) < 1 / b ^ 2 := by positivity
  linarith

/-- **Logarithmic Abelian theorem.**  If `Q` is measurable on `(1, ∞)`, bounded on every `[1, X]`,
and `Q(x)/log x → c`, then `b² ∫_1^∞ Q(x) x^{−b−1} dx → c` as `b → 0⁺`. -/
theorem tendsto_sq_mul_integral_of_tendsto_div_log {Q : ℝ → ℂ}
    (hQm : AEStronglyMeasurable Q (volume.restrict (Ioi 1)))
    (hQb : ∀ X : ℝ, ∃ C : ℝ, ∀ x ∈ Icc (1 : ℝ) X, ‖Q x‖ ≤ C)
    {c : ℂ} (hQ : Tendsto (fun x => Q x / (Real.log x : ℂ)) atTop (𝓝 c)) :
    Tendsto (fun b : ℝ => ((b ^ 2 : ℝ) : ℂ) * ∫ x in Ioi (1 : ℝ), Q x * ((x ^ (-b - 1) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 c) := by
  set r : ℝ → ℂ := fun x => Q x - c * (Real.log x : ℂ) with hr
  have hrm : AEStronglyMeasurable r (volume.restrict (Ioi 1)) :=
    hQm.sub (aestronglyMeasurable_const.mul ((Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun x hx => ne_of_gt (lt_trans one_pos hx)))
      |>.aestronglyMeasurable measurableSet_Ioi))
  have hrb : ∀ X : ℝ, ∃ C : ℝ, ∀ x ∈ Icc (1 : ℝ) X, ‖r x‖ ≤ C := by
    intro X
    obtain ⟨C, hC⟩ := hQb X
    refine ⟨C + ‖c‖ * |Real.log X|, fun x hx => ?_⟩
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx.1
    have hlX : Real.log x ≤ |Real.log X| :=
      (Real.log_le_log (lt_of_lt_of_le one_pos hx.1) hx.2).trans (le_abs_self _)
    simp only [hr]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
    exact add_le_add (hC x hx) (mul_le_mul_of_nonneg_left hlX (norm_nonneg _))
  -- `r = o(log)`
  have hrlim : Tendsto (fun x => r x / (Real.log x : ℂ)) atTop (𝓝 0) := by
    have h := hQ.sub (tendsto_const_nhds (x := c))
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hl : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hx).ne'
    simp only [hr]
    field_simp
  -- a uniform bound `‖r x‖ ≤ C + ε log x`
  have hbound : ∀ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖r x‖ ≤ C + ε * Real.log x := by
    intro ε hε
    obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp ((hrlim.norm.eventually (gt_mem_nhds
      (by rw [norm_zero]; exact hε))).and (eventually_gt_atTop (1 : ℝ)))
    set X : ℝ := max X₀ 2 with hX
    obtain ⟨C, hC⟩ := hrb X
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    rcases le_or_gt x X with hxX | hxX
    · have := hC x ⟨hx, hxX⟩
      have hl : 0 ≤ Real.log x := Real.log_nonneg hx
      nlinarith [le_max_left C 0]
    · obtain ⟨h1, h2⟩ := hX₀ x (le_trans (le_max_left _ _) hxX.le)
      have hl : 0 < Real.log x := Real.log_pos h2
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl, div_lt_iff₀ hl] at h1
      linarith [le_max_right C 0]
  -- the main term
  have hmain : ∀ b : ℝ, 0 < b → ((b ^ 2 : ℝ) : ℂ) * ∫ x in Ioi (1 : ℝ), Q x *
      ((x ^ (-b - 1) : ℝ) : ℂ) = c + ((b ^ 2 : ℝ) : ℂ) * ∫ x in Ioi (1 : ℝ), r x *
      ((x ^ (-b - 1) : ℝ) : ℂ) := by
    intro b hb
    obtain ⟨C, hC0, hC⟩ := hbound 1 one_pos
    have hlogint : IntegrableOn (fun x => ((Real.log x * x ^ (-b - 1) : ℝ) : ℂ)) (Ioi (1 : ℝ)) :=
      (integrableOn_log_mul_rpow hb).ofReal
    have hrint : IntegrableOn (fun x => r x * ((x ^ (-b - 1) : ℝ) : ℂ)) (Ioi (1 : ℝ)) := by
      have hdom : IntegrableOn (fun x : ℝ => C * x ^ (-b - 1) + Real.log x * x ^ (-b - 1))
          (Ioi (1 : ℝ)) :=
        ((integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C).add
          (integrableOn_log_mul_rpow hb)
      refine hdom.mono' ?_ ?_
      · exact hrm.mul ((Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_trans one_pos hx))))
          |>.aestronglyMeasurable measurableSet_Ioi)
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
        have hx0 : 0 < x := lt_trans one_pos hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hx0.le _), ← add_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using hC x (le_of_lt hx))
          (Real.rpow_nonneg hx0.le _)
    have hsplit : (fun x => Q x * ((x ^ (-b - 1) : ℝ) : ℂ)) =
        fun x => c * ((Real.log x * x ^ (-b - 1) : ℝ) : ℂ) + r x * ((x ^ (-b - 1) : ℝ) : ℂ) := by
      funext x
      simp only [hr]
      push_cast
      ring
    rw [hsplit, integral_add (hlogint.const_mul c) hrint, integral_const_mul,
      integral_complex_ofReal, integral_log_mul_rpow hb, mul_add]
    congr 1
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp
  -- the remainder is `o(1)`
  have hrem : Tendsto (fun b : ℝ => ((b ^ 2 : ℝ) : ℂ) * ∫ x in Ioi (1 : ℝ), r x *
      ((x ^ (-b - 1) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := hbound (ε / 2) (by positivity)
    refine ⟨ε / (2 * (C + 1)), by positivity, fun b hb hbd => ?_⟩
    have hb0 : 0 < b := hb
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hb0] at hbd
    rw [dist_zero_right]
    have hnorm : ‖∫ x in Ioi (1 : ℝ), r x * ((x ^ (-b - 1) : ℝ) : ℂ)‖ ≤
        C * (1 / b) + ε / 2 * (1 / b ^ 2) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      have hint1 := (integrableOn_Ioi_rpow_of_lt (by linarith : -b - 1 < -1) one_pos)
      have hint2 := integrableOn_log_mul_rpow hb0
      calc ∫ x in Ioi (1 : ℝ), ‖r x * ((x ^ (-b - 1) : ℝ) : ℂ)‖
          ≤ ∫ x in Ioi (1 : ℝ), (C * x ^ (-b - 1) + ε / 2 * (Real.log x * x ^ (-b - 1))) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
              ((hint1.const_mul C).add (hint2.const_mul (ε / 2)))
              ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
            have hx0 : 0 < x := lt_trans one_pos hx
            simp only
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
            have := hC x (le_of_lt hx)
            nlinarith [Real.rpow_nonneg hx0.le (-b - 1)]
        _ = C * (1 / b) + ε / 2 * (1 / b ^ 2) := by
            rw [integral_add (hint1.const_mul C) (hint2.const_mul (ε / 2)), integral_const_mul,
              integral_const_mul, integral_rpow_neg_sub_one hb0, integral_log_mul_rpow hb0]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc b ^ 2 * ‖∫ x in Ioi (1 : ℝ), r x * ((x ^ (-b - 1) : ℝ) : ℂ)‖
        ≤ b ^ 2 * (C * (1 / b) + ε / 2 * (1 / b ^ 2)) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = C * b + ε / 2 := by field_simp
      _ < ε := by
          have : C * b < ε / 2 := by
            calc C * b ≤ (C + 1) * b := by nlinarith
              _ < (C + 1) * (ε / (2 * (C + 1))) := mul_lt_mul_of_pos_left hbd (by linarith)
              _ = ε / 2 := by field_simp
          linarith
  have hsum := (tendsto_const_nhds (x := c)).add hrem
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact (hmain b hb).symm

end GaloisForLFunctions.LogCesaro

end
