import GaloisForLFunctions.RHTower.HermiteWronskianDecayRate
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Tail mass of a Hermite function

Writing `φ_m = p e^{-ξ²/2}`, the quantitative polynomial-Gaussian estimate gives
`|φ_m(ξ)| ≤ C/ξ⁴` outside the unit interval, and `−1/(3ξ³)` is an antiderivative of `ξ^{-4}`.  So the
mass of a Hermite function beyond a point `a ≥ 1` is at most `C/(3a³)`, uniformly in the far
endpoint.  This is what lets the whole-line pairing be replaced by a pairing over `[−√c, √c]` at a
cost that beats every polynomial growth of the profile.
-/

noncomputable section

open MeasureTheory intervalIntegral Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **Every Hermite function decays faster than any inverse power.** -/
theorem exists_bound_abs_hermiteFun_inv_pow (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| → |hermiteFun m x| ≤ C / |x| ^ k := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun m
  have hmass : 0 ≤ polyCoeffMass p := polyCoeffMass_nonneg p
  refine ⟨polyCoeffMass p * ((p.natDegree + k).factorial : ℝ) / (1 / 2 : ℝ) ^ (p.natDegree + k),
    by positivity, fun x hx => ?_⟩
  rw [hp x, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact abs_eval_mul_exp_neg_mul_sq_le p (by norm_num : (0 : ℝ) < 1 / 2) k hx

/-- The elementary inverse-fourth-power mass. -/
theorem integral_inv_pow_four_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, 1 / x ^ 4) ≤ 1 / (3 * a ^ 3) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -(3 * t ^ 3)⁻¹) (1 / x ^ 4) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by
      rcases Set.mem_uIcc.1 hx with h | h
      · exact lt_of_lt_of_le ha0 h.1
      · exact lt_of_lt_of_le ha0 (le_trans hab h.1)
    have hpow : HasDerivAt (fun t : ℝ => 3 * t ^ 3) (9 * x ^ 2) x := by
      have h := (hasDerivAt_pow 3 x).const_mul (3 : ℝ)
      refine h.congr_deriv ?_
      push_cast
      ring
    have hne : (3 : ℝ) * x ^ 3 ≠ 0 := by positivity
    have hinv := (hpow.inv hne).neg
    refine hinv.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => 1 / x ^ 4) (Set.uIcc a b) := by
    refine ContinuousOn.div continuousOn_const ((continuous_pow 4).continuousOn) fun x hx => ?_
    have hx0 : (0 : ℝ) < x := by
      rcases Set.mem_uIcc.1 hx with h | h
      · exact lt_of_lt_of_le ha0 h.1
      · exact lt_of_lt_of_le ha0 (le_trans hab h.1)
    positivity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable)
  rw [hFTC]
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha0 hab
  have hpos : (0 : ℝ) < ((3 : ℝ) * b ^ 3)⁻¹ := by positivity
  have hid : ((3 : ℝ) * a ^ 3)⁻¹ = 1 / (3 * a ^ 3) := by
    rw [inv_eq_one_div]
  linarith [hpos, hid.le, hid.ge]

/-- **Tail mass of a Hermite function.**  Beyond `a ≥ 1` the absolute mass is at most `C/(3a³)`,
uniformly in the far endpoint. -/
theorem exists_bound_integral_abs_hermiteFun_tail (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      (∫ x in a..b, |hermiteFun m x|) ≤ C / (3 * a ^ 3) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_abs_hermiteFun_inv_pow m 4
  refine ⟨C, hC0, fun a b ha hab => ?_⟩
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hint1 : IntervalIntegrable (fun x : ℝ => |hermiteFun m x|) volume a b :=
    (continuous_hermiteFun m).abs.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x : ℝ => C * (1 / x ^ 4)) volume a b := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      ((continuous_pow 4).continuousOn) fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := by
      rcases Set.mem_uIcc.1 hx with h | h
      · exact lt_of_lt_of_le ha0 h.1
      · exact lt_of_lt_of_le ha0 (le_trans hab h.1)
    positivity
  have hmono : (∫ x in a..b, |hermiteFun m x|) ≤ ∫ x in a..b, C * (1 / x ^ 4) := by
    refine intervalIntegral.integral_mono_on hab hint1 hint2 fun x hx => ?_
    have hx1 : 1 ≤ |x| := by
      rw [abs_of_pos (lt_of_lt_of_le ha0 hx.1)]
      exact le_trans ha hx.1
    have h := hC x hx1
    rw [abs_of_pos (lt_of_lt_of_le ha0 hx.1)] at h
    calc |hermiteFun m x| ≤ C / x ^ 4 := h
      _ = C * (1 / x ^ 4) := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  have hstep : C * (∫ x in a..b, 1 / x ^ 4) ≤ C * (1 / (3 * a ^ 3)) :=
    mul_le_mul_of_nonneg_left (integral_inv_pow_four_le ha hab) hC0
  calc (∫ x in a..b, |hermiteFun m x|) ≤ C * ∫ x in a..b, 1 / x ^ 4 := hmono
    _ ≤ C * (1 / (3 * a ^ 3)) := hstep
    _ = C / (3 * a ^ 3) := by ring


/-- The inverse-fourth-power mass on the negative side. -/
theorem integral_inv_pow_four_le_neg {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ x in (-b)..(-a), 1 / x ^ 4) ≤ 1 / (3 * a ^ 3) := by
  have hcomp : (∫ x in (-b)..(-a), (1 : ℝ) / x ^ 4) = ∫ x in a..b, 1 / x ^ 4 := by
    rw [← intervalIntegral.integral_comp_neg (fun x : ℝ => 1 / x ^ 4)]
    refine intervalIntegral.integral_congr fun x _ => ?_
    norm_num
  rw [hcomp]
  exact integral_inv_pow_four_le ha hab

/-- **Tail mass of a Hermite function on the negative side.** -/
theorem exists_bound_integral_abs_hermiteFun_tail_neg (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      (∫ x in (-b)..(-a), |hermiteFun m x|) ≤ C / (3 * a ^ 3) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_abs_hermiteFun_inv_pow m 4
  refine ⟨C, hC0, fun a b ha hab => ?_⟩
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hba : (-b : ℝ) ≤ -a := by linarith
  have hint1 : IntervalIntegrable (fun x : ℝ => |hermiteFun m x|) volume (-b) (-a) :=
    (continuous_hermiteFun m).abs.intervalIntegrable _ _
  have hneg : ∀ x ∈ Set.uIcc (-b) (-a), (0 : ℝ) < -x := by
    intro x hx
    rcases Set.mem_uIcc.1 hx with h | h
    · have := h.2
      linarith
    · have := h.1
      linarith
  have hint2 : IntervalIntegrable (fun x : ℝ => C * (1 / x ^ 4)) volume (-b) (-a) := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const
      ((continuous_pow 4).continuousOn) fun x hx => ?_)
    have h := hneg x hx
    have hx4 : x ^ 4 = (-x) ^ 4 := by ring
    rw [hx4]
    positivity
  have hmono : (∫ x in (-b)..(-a), |hermiteFun m x|)
      ≤ ∫ x in (-b)..(-a), C * (1 / x ^ 4) := by
    refine intervalIntegral.integral_mono_on hba hint1 hint2 fun x hx => ?_
    have hx0 : (0 : ℝ) < -x := by
      have h1 := hx.1
      have h2 := hx.2
      linarith
    have hx1 : 1 ≤ |x| := by
      rw [abs_of_neg (by linarith : x < 0)]
      have := hx.2
      linarith
    have h := hC x hx1
    have habs : |x| ^ 4 = x ^ 4 := by
      rw [abs_of_neg (by linarith : x < 0)]
      ring
    rw [habs] at h
    calc |hermiteFun m x| ≤ C / x ^ 4 := h
      _ = C * (1 / x ^ 4) := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  have hstep : C * (∫ x in (-b)..(-a), 1 / x ^ 4) ≤ C * (1 / (3 * a ^ 3)) :=
    mul_le_mul_of_nonneg_left (integral_inv_pow_four_le_neg ha hab) hC0
  calc (∫ x in (-b)..(-a), |hermiteFun m x|) ≤ C * ∫ x in (-b)..(-a), 1 / x ^ 4 := hmono
    _ ≤ C * (1 / (3 * a ^ 3)) := hstep
    _ = C / (3 * a ^ 3) := by ring


/-- **The whole-line pairing differs from the symmetric window pairing by the tail mass.**  For a
bounded continuous factor the difference is at most the bound times twice the Hermite tail mass. -/
theorem exists_bound_abs_integral_sub_window (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : ℝ → ℝ) (B a : ℝ), 1 ≤ a → 0 ≤ B → Continuous v →
      (∀ x, |v x| ≤ B) → Integrable (fun x => v x * hermiteFun m x) →
      |(∫ x, v x * hermiteFun m x) - ∫ x in (-a)..a, v x * hermiteFun m x|
        ≤ B * (2 * C / (3 * a ^ 3)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_integral_abs_hermiteFun_tail m
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_integral_abs_hermiteFun_tail_neg m
  refine ⟨max C₁ C₂, le_trans hC₁0 (le_max_left _ _), fun v B a ha hB0 hv hB hint => ?_⟩
  set C : ℝ := max C₁ C₂ with hCdef
  have hC0 : 0 ≤ C := le_trans hC₁0 (le_max_left _ _)
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hprod : Continuous fun x : ℝ => v x * hermiteFun m x := hv.mul (continuous_hermiteFun m)
  -- the finite-window estimate, uniform in the far endpoint
  have hfin : ∀ R : ℝ, a ≤ R →
      |(∫ x in (-R)..R, v x * hermiteFun m x) - ∫ x in (-a)..a, v x * hermiteFun m x|
        ≤ B * (2 * C / (3 * a ^ 3)) := by
    intro R hR
    have hsplit1 : (∫ x in (-R)..(-a), v x * hermiteFun m x)
        + ∫ x in (-a)..a, v x * hermiteFun m x = ∫ x in (-R)..a, v x * hermiteFun m x :=
      intervalIntegral.integral_add_adjacent_intervals
        (hprod.intervalIntegrable _ _) (hprod.intervalIntegrable _ _)
    have hsplit2 : (∫ x in (-R)..a, v x * hermiteFun m x)
        + ∫ x in a..R, v x * hermiteFun m x = ∫ x in (-R)..R, v x * hermiteFun m x :=
      intervalIntegral.integral_add_adjacent_intervals
        (hprod.intervalIntegrable _ _) (hprod.intervalIntegrable _ _)
    have hdiff : (∫ x in (-R)..R, v x * hermiteFun m x) - ∫ x in (-a)..a, v x * hermiteFun m x
        = (∫ x in (-R)..(-a), v x * hermiteFun m x) + ∫ x in a..R, v x * hermiteFun m x := by
      linarith [hsplit1, hsplit2]
    rw [hdiff]
    have hright : |∫ x in a..R, v x * hermiteFun m x| ≤ B * (C / (3 * a ^ 3)) := by
      have habs := intervalIntegral.abs_integral_le_integral_abs
        (f := fun x : ℝ => v x * hermiteFun m x) (μ := volume) hR
      refine le_trans habs ?_
      have hmono : (∫ x in a..R, |v x * hermiteFun m x|)
          ≤ ∫ x in a..R, B * |hermiteFun m x| := by
        refine intervalIntegral.integral_mono_on hR (hprod.abs.intervalIntegrable _ _)
          ((continuous_const.mul (continuous_hermiteFun m).abs).intervalIntegrable _ _)
          fun x _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
      rw [intervalIntegral.integral_const_mul] at hmono
      refine le_trans hmono ?_
      refine mul_le_mul_of_nonneg_left ?_ hB0
      exact le_trans (hC₁ a R ha hR) (by gcongr; exact le_max_left _ _)
    have hleft : |∫ x in (-R)..(-a), v x * hermiteFun m x| ≤ B * (C / (3 * a ^ 3)) := by
      have hRa : (-R : ℝ) ≤ -a := by linarith
      have habs := intervalIntegral.abs_integral_le_integral_abs
        (f := fun x : ℝ => v x * hermiteFun m x) (μ := volume) hRa
      refine le_trans habs ?_
      have hmono : (∫ x in (-R)..(-a), |v x * hermiteFun m x|)
          ≤ ∫ x in (-R)..(-a), B * |hermiteFun m x| := by
        refine intervalIntegral.integral_mono_on hRa (hprod.abs.intervalIntegrable _ _)
          ((continuous_const.mul (continuous_hermiteFun m).abs).intervalIntegrable _ _)
          fun x _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
      rw [intervalIntegral.integral_const_mul] at hmono
      refine le_trans hmono ?_
      refine mul_le_mul_of_nonneg_left ?_ hB0
      exact le_trans (hC₂ a R ha hR) (by gcongr; exact le_max_right _ _)
    have habs2 := abs_add_le (∫ x in (-R)..(-a), v x * hermiteFun m x)
      (∫ x in a..R, v x * hermiteFun m x)
    have hsum : B * (C / (3 * a ^ 3)) + B * (C / (3 * a ^ 3)) = B * (2 * C / (3 * a ^ 3)) := by
      ring
    linarith [habs2, hleft, hright, hsum.le, hsum.ge]
  -- pass to the whole line
  have hlim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, v x * hermiteFun m x) atTop
      (𝓝 (∫ x, v x * hermiteFun m x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hlim2 : Tendsto (fun R : ℝ =>
      |(∫ x in (-R)..R, v x * hermiteFun m x) - ∫ x in (-a)..a, v x * hermiteFun m x|) atTop
      (𝓝 |(∫ x, v x * hermiteFun m x) - ∫ x in (-a)..a, v x * hermiteFun m x|) :=
    (hlim.sub_const _).abs
  refine le_of_tendsto hlim2 ?_
  filter_upwards [eventually_ge_atTop a] with R hR
  exact hfin R hR

end RHTower

end
