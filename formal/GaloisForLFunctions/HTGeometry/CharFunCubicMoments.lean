import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Moments from a cubic expansion of the characteristic function

If a probability measure on `ℝ` with finite second moment has characteristic function
`φ(t) = exp Ψ(t)` with `Ψ(t) = i m t - v t²/2 + O(|t|³)`, then its mean is `m` and its second
moment is `v + m²`, so its variance is `v`.  The proof compares the order-two Taylor polynomial of
`φ` at the origin, whose coefficients are the moments, with the expansion of `exp Ψ`: two quadratic
polynomials agreeing up to `o(t²)` coincide.

The cubic Taylor bound `‖e^{ix} - (1 + ix - x²/2)‖ ≤ 2|x|³`, valid for every real `x`, is proved
from the sine and cosine bounds.
-/

open MeasureTheory Complex Filter Asymptotics Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `0 ≤ cos x - 1 + x²/2 ≤ |x|³` for every real `x`. -/
theorem abs_cos_sub_quadratic_le (x : ℝ) : |Real.cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 3 := by
  have hlow : 0 ≤ Real.cos x - (1 - x ^ 2 / 2) := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  rw [abs_of_nonneg hlow]
  rcases le_or_gt |x| 1 with hx | hx
  · have hb := Real.cos_bound hx
    rw [abs_of_nonneg hlow] at hb
    have h4 : |x| ^ 4 ≤ |x| ^ 3 := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) hx
    nlinarith [abs_nonneg x]
  · have hcos := Real.cos_le_one x
    have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have h32 : |x| ^ 2 ≤ |x| ^ 3 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (by positivity) hx.le
    nlinarith

/-- **Cubic Taylor bound for the unimodular exponential.**
`‖e^{ix} - (1 + ix - x²/2)‖ ≤ 2|x|³` for every real `x`. -/
theorem norm_cexp_mul_I_sub_quadratic_le (x : ℝ) :
    ‖cexp ((x : ℂ) * I) - (1 + (x : ℂ) * I - (x : ℂ) ^ 2 / 2)‖ ≤ 2 * |x| ^ 3 := by
  have hsplit : cexp ((x : ℂ) * I) - (1 + (x : ℂ) * I - (x : ℂ) ^ 2 / 2)
      = ((Real.cos x - (1 - x ^ 2 / 2) : ℝ) : ℂ) + ((Real.sin x - x : ℝ) : ℂ) * I := by
    rw [exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [hsplit]
  calc ‖((Real.cos x - (1 - x ^ 2 / 2) : ℝ) : ℂ) + ((Real.sin x - x : ℝ) : ℂ) * I‖
      ≤ ‖((Real.cos x - (1 - x ^ 2 / 2) : ℝ) : ℂ)‖ + ‖((Real.sin x - x : ℝ) : ℂ) * I‖ :=
        norm_add_le _ _
    _ = |Real.cos x - (1 - x ^ 2 / 2)| + |Real.sin x - x| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |x| ^ 3 + |x| ^ 3 / 6 := by
        gcongr
        · exact abs_cos_sub_quadratic_le x
        · rw [abs_sub_comm]
          exact Real.abs_sub_sin_le x
    _ ≤ 2 * |x| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg x) 3]

/-- A complex polynomial `a t + b t²` which is `o(t²)` at the origin vanishes identically. -/
theorem eq_zero_of_isLittleO_linear_quadratic {a b : ℂ}
    (h : (fun t : ℝ => a * (t : ℂ) + b * (t : ℂ) ^ 2) =o[𝓝 0] fun t : ℝ => (t : ℂ) ^ 2) :
    a = 0 ∧ b = 0 := by
  have hdiv := h.tendsto_div_nhds_zero
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, (t : ℂ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact_mod_cast ht
  have hdiv' : Tendsto (fun t : ℝ => (a * (t : ℂ) + b * (t : ℂ) ^ 2) / (t : ℂ) ^ 2)
      (𝓝[≠] 0) (𝓝 0) := hdiv.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  have hmul := hid.mul hdiv'
  rw [zero_mul] at hmul
  have hlin : Tendsto (fun t : ℝ => a + b * (t : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
    refine hmul.congr' ?_
    filter_upwards [hne] with t ht
    field_simp
  have hlin' : Tendsto (fun t : ℝ => a + b * (t : ℂ)) (𝓝[≠] 0) (𝓝 (a + b * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hid)
  have ha : a = 0 := by
    have := tendsto_nhds_unique hlin' hlin
    simpa using this
  refine ⟨ha, ?_⟩
  have hb : Tendsto (fun _ : ℝ => b) (𝓝[≠] 0) (𝓝 0) := by
    refine hdiv'.congr' ?_
    filter_upwards [hne] with t ht
    rw [ha, zero_mul, zero_add]
    field_simp
  exact tendsto_nhds_unique tendsto_const_nhds hb

/-- The order-two Taylor polynomial of a characteristic function carries the first two moments. -/
theorem charFun_sub_moment_quadratic_isLittleO {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h2 : MemLp id 2 μ) :
    (fun t : ℝ => charFun μ t - (1 + ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * I
        - ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
  have htaylor := taylor_isLittleO_univ (x₀ := 0) (contDiff_charFun h2)
  simp only [sub_zero] at htaylor
  refine htaylor.congr_left fun t => ?_
  rw [taylorWithinEval_charFun_zero h2 t]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, zero_add, integral_const,
    probReal_univ, smul_eq_mul, mul_one, Nat.cast_one, inv_one, one_mul,
    Complex.ofReal_one]
  have hI : (I : ℂ) ^ 2 = -1 := I_sq
  rw [mul_pow, hI]
  push_cast
  ring

/-- **Moments from a cubic cumulant expansion.**  If `φ_μ(t) = exp Ψ(t)` and
`‖Ψ(t) - (i m t - v t²/2)‖ ≤ C|t|³`, then `E X = m` and `E X² = v + m²`. -/
theorem moments_of_charFun_cubic {μ : Measure ℝ} [IsProbabilityMeasure μ] (h2 : MemLp id 2 μ)
    {Ψ : ℝ → ℂ} (hΨ : ∀ t, charFun μ t = cexp (Ψ t)) {m v C : ℝ}
    (hC : ∀ t, ‖Ψ t - ((m : ℂ) * (t : ℂ) * I - (v : ℂ) * (t : ℂ) ^ 2 / 2)‖ ≤ C * |t| ^ 3) :
    ∫ x, x ∂μ = m ∧ ∫ x, x ^ 2 ∂μ = v + m ^ 2 := by
  set E : ℝ → ℂ := fun t => Ψ t - ((m : ℂ) * (t : ℂ) * I - (v : ℂ) * (t : ℂ) ^ 2 / 2) with hEdef
  have hE3 : E =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    refine IsBigO.of_bound C (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact hC t
  have ht : (fun t : ℝ => (t : ℂ)) =O[𝓝 0] fun t : ℝ => t :=
    IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp)
  have ht2 : (fun t : ℝ => (t : ℂ) ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 2 :=
    IsBigO.of_bound 1 (Eventually.of_forall fun t => by simp)
  have ht3 : (fun t : ℝ => t ^ 3) =O[𝓝 0] fun t : ℝ => t :=
    isBigO_iff.mpr ⟨1, by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t htb
      rw [Metric.mem_ball, dist_zero_right] at htb
      rw [one_mul, norm_pow]
      calc ‖t‖ ^ 3 = ‖t‖ * ‖t‖ ^ 2 := by ring
        _ ≤ ‖t‖ * 1 := by gcongr; nlinarith [norm_nonneg t]
        _ = ‖t‖ := mul_one _⟩
  have ht3' : (fun t : ℝ => t ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 2 :=
    isBigO_iff.mpr ⟨1, by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t htb
      rw [Metric.mem_ball, dist_zero_right] at htb
      rw [one_mul, norm_pow, norm_pow]
      calc ‖t‖ ^ 3 = ‖t‖ ^ 2 * ‖t‖ := by ring
        _ ≤ ‖t‖ ^ 2 * 1 := by gcongr
        _ = ‖t‖ ^ 2 := mul_one _⟩
  have ht2t : (fun t : ℝ => t ^ 2) =O[𝓝 0] fun t : ℝ => t :=
    isBigO_iff.mpr ⟨1, by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t htb
      rw [Metric.mem_ball, dist_zero_right] at htb
      rw [one_mul, norm_pow]
      calc ‖t‖ ^ 2 = ‖t‖ * ‖t‖ := by ring
        _ ≤ ‖t‖ * 1 := by gcongr
        _ = ‖t‖ := mul_one _⟩
  -- `Ψ - i m t = E - v t²/2 = O(t²)` and `Ψ + i m t = O(t)`.
  have hminus : (fun t : ℝ => Ψ t - (m : ℂ) * (t : ℂ) * I) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    have h1 : (fun t : ℝ => Ψ t - (m : ℂ) * (t : ℂ) * I)
        = fun t => E t + (-(v : ℂ) / 2) * (t : ℂ) ^ 2 := by
      funext t
      simp only [hEdef]
      ring
    rw [h1]
    exact (hE3.trans ht3').add (ht2.const_mul_left _)
  have hplus : (fun t : ℝ => Ψ t + (m : ℂ) * (t : ℂ) * I) =O[𝓝 0] fun t : ℝ => t := by
    have h1 : (fun t : ℝ => Ψ t + (m : ℂ) * (t : ℂ) * I)
        = fun t => (Ψ t - (m : ℂ) * (t : ℂ) * I) + (2 * (m : ℂ) * I) * (t : ℂ) := by
      funext t
      ring
    rw [h1]
    exact (hminus.trans ht2t).add (ht.const_mul_left _)
  have hΨ1 : Ψ =O[𝓝 0] fun t : ℝ => t := by
    have h1 : Ψ = fun t => (Ψ t - (m : ℂ) * (t : ℂ) * I) + ((m : ℂ) * I) * (t : ℂ) := by
      funext t
      ring
    rw [h1]
    exact (hminus.trans ht2t).add (ht.const_mul_left _)
  have hΨ0 : Tendsto Ψ (𝓝 0) (𝓝 0) := by
    have h := hΨ1.trans_tendsto (tendsto_id.mono_left le_rfl : Tendsto (fun t : ℝ => t) (𝓝 0)
      (𝓝 0))
    exact h
  -- the exponential Taylor remainder is `O(‖Ψ‖³) = O(t³)`.
  have hexp : (fun t : ℝ => cexp (Ψ t) - (1 + Ψ t + Ψ t ^ 2 / 2)) =O[𝓝 0]
      fun t : ℝ => t ^ 3 := by
    have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), ‖Ψ t‖ ≤ 1 := by
      have := hΨ0.norm
      rw [norm_zero] at this
      exact this.eventually (ge_mem_nhds one_pos)
    have hcube : (fun t : ℝ => cexp (Ψ t) - (1 + Ψ t + Ψ t ^ 2 / 2)) =O[𝓝 0]
        fun t : ℝ => Ψ t ^ 3 := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [hsmall] with t hts
      have hb := Complex.exp_bound hts (n := 3) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero,
        Nat.factorial, Nat.cast_one, div_one, zero_add, pow_one, Nat.succ_eq_add_one,
        Nat.cast_ofNat] at hb
      rw [one_mul, norm_pow]
      calc ‖cexp (Ψ t) - (1 + Ψ t + Ψ t ^ 2 / 2)‖
          = ‖cexp (Ψ t) - (1 + Ψ t + Ψ t ^ 2 / ((1 + 1) * 1 : ℕ))‖ := by norm_num
        _ ≤ ‖Ψ t‖ ^ 3 * (((3 + 1 : ℕ) : ℝ) * ((((2 + 1) * ((1 + 1) * 1) : ℕ) : ℝ) * 3)⁻¹) := by
          convert hb using 2
          norm_num
        _ ≤ ‖Ψ t‖ ^ 3 := by
          have : (((3 + 1 : ℕ) : ℝ) * ((((2 + 1) * ((1 + 1) * 1) : ℕ) : ℝ) * 3)⁻¹) ≤ 1 := by
            norm_num
          exact mul_le_of_le_one_right (by positivity) this
    have hΨ3 : (fun t : ℝ => Ψ t ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 3 := hΨ1.pow 3
    exact hcube.trans hΨ3
  -- the quadratic part of `exp Ψ` matches the Gaussian-type polynomial up to `O(t³)`.
  have hquad : (fun t : ℝ => (1 + Ψ t + Ψ t ^ 2 / 2)
      - (1 + (m : ℂ) * (t : ℂ) * I - ((v + m ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) =O[𝓝 0]
      fun t : ℝ => t ^ 3 := by
    have h1 : (fun t : ℝ => (1 + Ψ t + Ψ t ^ 2 / 2)
        - (1 + (m : ℂ) * (t : ℂ) * I - ((v + m ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))
        = fun t => E t + (1 / 2 : ℂ) * ((Ψ t - (m : ℂ) * (t : ℂ) * I)
            * (Ψ t + (m : ℂ) * (t : ℂ) * I)) := by
      funext t
      simp only [hEdef]
      push_cast
      have hI : (I : ℂ) ^ 2 = -1 := I_sq
      linear_combination ((1 / 2 : ℂ) * (m : ℂ) ^ 2 * (t : ℂ) ^ 2) * hI
    rw [h1]
    refine hE3.add (IsBigO.const_mul_left ?_ _)
    have := hminus.mul hplus
    refine this.congr_right fun t => ?_
    ring
  -- compare with Taylor.
  have hT := charFun_sub_moment_quadratic_isLittleO h2
  have hdiff : (fun t : ℝ => (((∫ x, x ∂μ : ℝ) : ℂ) - m) * I * (t : ℂ)
      + ((v + m ^ 2 - ∫ x, x ^ 2 ∂μ : ℝ) : ℂ) / 2 * (t : ℂ) ^ 2) =o[𝓝 0]
      fun t : ℝ => t ^ 2 := by
    have hA : (fun t : ℝ => charFun μ t
        - (1 + (m : ℂ) * (t : ℂ) * I - ((v + m ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) =O[𝓝 0]
        fun t : ℝ => t ^ 3 := by
      have h1 : (fun t : ℝ => charFun μ t
          - (1 + (m : ℂ) * (t : ℂ) * I - ((v + m ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))
          = fun t => (cexp (Ψ t) - (1 + Ψ t + Ψ t ^ 2 / 2)) + ((1 + Ψ t + Ψ t ^ 2 / 2)
            - (1 + (m : ℂ) * (t : ℂ) * I - ((v + m ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) := by
        funext t
        rw [hΨ t]
        ring
      rw [h1]
      exact hexp.add hquad
    have hA' := hA.trans_isLittleO (isLittleO_pow_pow (𝕜 := ℝ) (m := 2) (n := 3) (by norm_num))
    refine (hA'.sub hT).congr_left fun t => ?_
    push_cast
    ring
  have hdiff' : (fun t : ℝ => ((((∫ x, x ∂μ : ℝ) : ℂ) - m) * I) * (t : ℂ)
      + (((v + m ^ 2 - ∫ x, x ^ 2 ∂μ : ℝ) : ℂ) / 2) * (t : ℂ) ^ 2) =o[𝓝 0]
      fun t : ℝ => (t : ℂ) ^ 2 := by
    refine hdiff.trans_isBigO (IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_))
    simp
  obtain ⟨ha, hb⟩ := eq_zero_of_isLittleO_linear_quadratic hdiff'
  have ha' : ((∫ x, x ∂μ : ℝ) : ℂ) - m = 0 := by
    rcases mul_eq_zero.mp ha with h | h
    · exact h
    · exact absurd h I_ne_zero
  have hb' : ((v + m ^ 2 - ∫ x, x ^ 2 ∂μ : ℝ) : ℂ) = 0 := by
    rcases div_eq_zero_iff.mp hb with h | h
    · exact h
    · norm_num at h
  constructor
  · have := ha'
    rw [sub_eq_zero] at this
    exact_mod_cast this
  · have := hb'
    rw [Complex.ofReal_eq_zero] at this
    linarith

end GaloisForLFunctions.HTGeometry
