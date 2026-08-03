import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import GaloisForLFunctions.HTGeometry.ClockAnalyticWienerScale

/-!
# From coefficients back to functions: the transverse Laplacian

The iteration for the clock equation runs in the coefficient form of the analytic scale, where the
transverse Laplacian is multiplication by `-k²`. To read the result as a field on the transverse
circle one has to synthesise the series and check that the multiplication really is the second
derivative.

That is what this file does. A sequence summable against `e^{ρ|k|}` for some `ρ > 0` has
coefficients decaying faster than any power, so the cosine and sine series it generates may be
differentiated term by term, twice; and

`(∑ₖ gₖ cos kz)'' = -∑ₖ k² gₖ cos kz`.

The decay is supplied by the elementary bounds `t e^{-δt} ≤ 1/δ` and `t² e^{-δt} ≤ 4/δ²`, the second
of which already carries the derivative loss of the scale.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Powers are dominated by the exponential weight -/

/-- **One power costs `1/δ`.** -/
theorem mul_exp_neg_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    t * Real.exp (-(δ * t)) ≤ 1 / δ := by
  have hs : (0 : ℝ) ≤ δ * t := mul_nonneg hδ.le ht
  have hbase : δ * t ≤ Real.exp (δ * t) := by
    have h := Real.add_one_le_exp (δ * t)
    linarith
  have hpos : (0 : ℝ) < Real.exp (-(δ * t)) := Real.exp_pos _
  have hexp : Real.exp (-(δ * t)) * Real.exp (δ * t) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [le_div_iff₀ hδ]
  calc t * Real.exp (-(δ * t)) * δ = (δ * t) * Real.exp (-(δ * t)) := by ring
    _ ≤ Real.exp (δ * t) * Real.exp (-(δ * t)) := mul_le_mul_of_nonneg_right hbase hpos.le
    _ = 1 := by rw [mul_comm]; exact hexp

theorem abs_le_exp_weight {ρ : ℝ} (hρ : 0 < ρ) (k : ℤ) :
    |(k : ℝ)| ≤ 1 / ρ * Real.exp (ρ * |(k : ℝ)|) := by
  have h := mul_exp_neg_le (δ := ρ) (t := |(k : ℝ)|) hρ (abs_nonneg _)
  have hpos : (0 : ℝ) < Real.exp (ρ * |(k : ℝ)|) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right h hpos.le
  have hcancel : |(k : ℝ)| * Real.exp (-(ρ * |(k : ℝ)|)) * Real.exp (ρ * |(k : ℝ)|)
      = |(k : ℝ)| := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  rwa [hcancel] at hmul

theorem sq_le_exp_weight {ρ : ℝ} (hρ : 0 < ρ) (k : ℤ) :
    (k : ℝ) ^ 2 ≤ 4 / ρ ^ 2 * Real.exp (ρ * |(k : ℝ)|) := by
  have h := sq_mul_exp_neg_le (δ := ρ) (t := |(k : ℝ)|) hρ (abs_nonneg _)
  have hpos : (0 : ℝ) < Real.exp (ρ * |(k : ℝ)|) := Real.exp_pos _
  have habs : |(k : ℝ)| ^ 2 = (k : ℝ) ^ 2 := sq_abs _
  rw [habs] at h
  have hmul := mul_le_mul_of_nonneg_right h hpos.le
  have hcancel : (k : ℝ) ^ 2 * Real.exp (-(ρ * |(k : ℝ)|)) * Real.exp (ρ * |(k : ℝ)|)
      = (k : ℝ) ^ 2 := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  rwa [hcancel] at hmul

/-! ## Summability of the weighted coefficients -/

theorem summable_abs_of_wienerSummable {ρ : ℝ} (hρ : 0 ≤ ρ) {g : ℤ → ℝ}
    (hg : WienerSummable ρ g) : Summable fun k : ℤ => |g k| := by
  refine hg.of_nonneg_of_le (fun _ => abs_nonneg _) fun k => ?_
  have h1 : (1 : ℝ) ≤ Real.exp (ρ * |(k : ℝ)|) :=
    Real.one_le_exp (mul_nonneg hρ (abs_nonneg _))
  nlinarith [abs_nonneg (g k)]

theorem summable_of_wienerSummable {ρ : ℝ} (hρ : 0 ≤ ρ) {g : ℤ → ℝ}
    (hg : WienerSummable ρ g) : Summable g :=
  (summable_abs_of_wienerSummable hρ hg).of_abs

theorem summable_absMul {ρ : ℝ} (hρ : 0 < ρ) {g : ℤ → ℝ} (hg : WienerSummable ρ g) :
    Summable fun k : ℤ => |g k| * |(k : ℝ)| := by
  refine (hg.mul_left (1 / ρ)).of_nonneg_of_le (fun _ => by positivity) fun k => ?_
  calc |g k| * |(k : ℝ)| ≤ |g k| * (1 / ρ * Real.exp (ρ * |(k : ℝ)|)) :=
        mul_le_mul_of_nonneg_left (abs_le_exp_weight hρ k) (abs_nonneg _)
    _ = 1 / ρ * (|g k| * Real.exp (ρ * |(k : ℝ)|)) := by ring

theorem summable_absSq {ρ : ℝ} (hρ : 0 < ρ) {g : ℤ → ℝ} (hg : WienerSummable ρ g) :
    Summable fun k : ℤ => |g k| * (k : ℝ) ^ 2 := by
  refine (hg.mul_left (4 / ρ ^ 2)).of_nonneg_of_le (fun _ => by positivity) fun k => ?_
  calc |g k| * (k : ℝ) ^ 2 ≤ |g k| * (4 / ρ ^ 2 * Real.exp (ρ * |(k : ℝ)|)) :=
        mul_le_mul_of_nonneg_left (sq_le_exp_weight hρ k) (abs_nonneg _)
    _ = 4 / ρ ^ 2 * (|g k| * Real.exp (ρ * |(k : ℝ)|)) := by ring

/-! ## The synthesised field -/

/-- The cosine series of a coefficient sequence. -/
noncomputable def cosSeries (g : ℤ → ℝ) : ℝ → ℝ :=
  fun z => ∑' k : ℤ, g k * Real.cos ((k : ℝ) * z)

/-- The sine series of a coefficient sequence. -/
noncomputable def sinSeries (g : ℤ → ℝ) : ℝ → ℝ :=
  fun z => ∑' k : ℤ, g k * Real.sin ((k : ℝ) * z)

theorem hasDerivAt_cos_term (a : ℝ) (c : ℝ) (z : ℝ) :
    HasDerivAt (fun y => c * Real.cos (a * y)) (-(c * a) * Real.sin (a * z)) z := by
  have hlin : HasDerivAt (fun y : ℝ => a * y) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  have hcos : HasDerivAt (fun y => Real.cos (a * y)) (-Real.sin (a * z) * a) z :=
    HasDerivAt.cos hlin
  have hres : HasDerivAt (fun y => c * Real.cos (a * y)) (c * (-Real.sin (a * z) * a)) z :=
    HasDerivAt.const_mul c hcos
  convert hres using 1
  ring

theorem hasDerivAt_sin_term (a : ℝ) (c : ℝ) (z : ℝ) :
    HasDerivAt (fun y => c * Real.sin (a * y)) (c * a * Real.cos (a * z)) z := by
  have hlin : HasDerivAt (fun y : ℝ => a * y) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  have hsin : HasDerivAt (fun y => Real.sin (a * y)) (Real.cos (a * z) * a) z :=
    HasDerivAt.sin hlin
  have hres : HasDerivAt (fun y => c * Real.sin (a * y)) (c * (Real.cos (a * z) * a)) z :=
    HasDerivAt.const_mul c hsin
  convert hres using 1
  ring

/-- **The cosine series may be differentiated term by term.** -/
theorem hasDerivAt_cosSeries {ρ : ℝ} (hρ : 0 < ρ) {g : ℤ → ℝ} (hg : WienerSummable ρ g)
    (z : ℝ) :
    HasDerivAt (cosSeries g) (sinSeries (fun k => -(g k * (k : ℝ))) z) z := by
  refine hasDerivAt_tsum (u := fun k : ℤ => |g k| * |(k : ℝ)|)
    (g := fun (k : ℤ) (y : ℝ) => g k * Real.cos ((k : ℝ) * y))
    (g' := fun (k : ℤ) (y : ℝ) => -(g k * (k : ℝ)) * Real.sin ((k : ℝ) * y))
    (y₀ := 0) (summable_absMul hρ hg) (fun k y => hasDerivAt_cos_term _ _ _) ?_ ?_ z
  · intro k y
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul]
    have hsin : |Real.sin ((k : ℝ) * y)| ≤ 1 := Real.abs_sin_le_one _
    have hnn : (0 : ℝ) ≤ |g k| * |(k : ℝ)| := by positivity
    calc |g k| * |(k : ℝ)| * |Real.sin ((k : ℝ) * y)| ≤ |g k| * |(k : ℝ)| * 1 :=
          mul_le_mul_of_nonneg_left hsin hnn
      _ = |g k| * |(k : ℝ)| := mul_one _
  · simpa using summable_of_wienerSummable hρ.le hg

/-- **The sine series may be differentiated term by term.** -/
theorem hasDerivAt_sinSeries {ρ : ℝ} (hρ : 0 < ρ) {g : ℤ → ℝ} (hg : WienerSummable ρ g)
    (z : ℝ) :
    HasDerivAt (sinSeries g) (cosSeries (fun k => g k * (k : ℝ)) z) z := by
  refine hasDerivAt_tsum (u := fun k : ℤ => |g k| * |(k : ℝ)|)
    (g := fun (k : ℤ) (y : ℝ) => g k * Real.sin ((k : ℝ) * y))
    (g' := fun (k : ℤ) (y : ℝ) => g k * (k : ℝ) * Real.cos ((k : ℝ) * y))
    (y₀ := 0) (summable_absMul hρ hg) (fun k y => hasDerivAt_sin_term _ _ _) ?_ ?_ z
  · intro k y
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hcos : |Real.cos ((k : ℝ) * y)| ≤ 1 := Real.abs_cos_le_one _
    have hnn : (0 : ℝ) ≤ |g k| * |(k : ℝ)| := by positivity
    calc |g k| * |(k : ℝ)| * |Real.cos ((k : ℝ) * y)| ≤ |g k| * |(k : ℝ)| * 1 :=
          mul_le_mul_of_nonneg_left hcos hnn
      _ = |g k| * |(k : ℝ)| := mul_one _
  · simp

/-- An integer is dominated by its square. -/
theorem abs_int_le_sq (k : ℤ) : |(k : ℝ)| ≤ (k : ℝ) ^ 2 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp
  · have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have hz : (1 : ℤ) ≤ |k| := Int.one_le_abs (by exact_mod_cast hk)
      have hcast : ((|k| : ℤ) : ℝ) = |(k : ℝ)| := Int.cast_abs
      calc (1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast hz
        _ = |(k : ℝ)| := hcast
    nlinarith [sq_abs ((k : ℝ)), h1]

/-- **Multiplication by `-k²` is the second derivative of the synthesised field.** -/
theorem deriv_deriv_cosSeries {ρ ρ' : ℝ} (hρ' : 0 < ρ') (hρ : ρ' < ρ) {g : ℤ → ℝ}
    (hg : WienerSummable ρ g) (z : ℝ) :
    deriv (deriv (cosSeries g)) z = -cosSeries (sqMul g) z := by
  have hd1 : WienerSummable ρ' (fun k => -(g k * (k : ℝ))) := by
    refine (wienerSummable_sqMul hρ hg).of_nonneg_of_le (fun _ => by positivity) fun k => ?_
    have habs : |-(g k * (k : ℝ))| = |g k| * |(k : ℝ)| := by
      rw [abs_neg, abs_mul]
    have hsq : |sqMul g k| = (k : ℝ) ^ 2 * |g k| := abs_sqMul g k
    have hkk : |g k| * |(k : ℝ)| ≤ (k : ℝ) ^ 2 * |g k| := by
      have := mul_le_mul_of_nonneg_left (abs_int_le_sq k) (abs_nonneg (g k))
      linarith [this]
    rw [habs, hsq]
    exact mul_le_mul_of_nonneg_right hkk (Real.exp_pos _).le
  have hderiv1 : deriv (cosSeries g) = sinSeries (fun k => -(g k * (k : ℝ))) := by
    funext y
    exact (hasDerivAt_cosSeries (hρ'.trans hρ) hg y).deriv
  rw [hderiv1, (hasDerivAt_sinSeries hρ' hd1 z).deriv]
  simp only [cosSeries]
  rw [← tsum_neg]
  refine tsum_congr fun k => ?_
  rw [sqMul]
  ring

end GaloisForLFunctions.HTGeometry
