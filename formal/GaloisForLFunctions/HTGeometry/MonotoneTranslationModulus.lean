import Mathlib

/-!
# The `L¹` modulus of continuity of a monotone function

For a monotone function the translation difference telescopes exactly:

`∫_a^b (g(x+h) − g(x)) dx = ∫_b^{b+h} g − ∫_a^{a+h} g`,

because translating the variable moves the window rather than the function.  Monotonicity bounds
the two short windows by their endpoint values, giving

`∫_a^b |g(x+h) − g(x)| dx ≤ h · (g(b+h) − g(a))`.

The right-hand side is the variation of `g` across the enlarged window, so this is the `L¹`
modulus of continuity of a bounded-variation function in the monotone case.  No differentiability
is used anywhere — which is the point, since a monotone profile may have infinite one-sided
derivative.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- A translate of a monotone function is monotone. -/
theorem monotone_comp_add_right {g : ℝ → ℝ} (hg : Monotone g) (h : ℝ) :
    Monotone fun x => g (x + h) := fun _ _ hpq => hg (by linarith)

/-- **The translation difference telescopes.**  Shifting the variable of a monotone function moves
the integration window, so the difference of the two integrals is the difference of the two short
end windows. -/
theorem integral_translate_sub_eq_end_windows {g : ℝ → ℝ} (hg : Monotone g) (a b h : ℝ) :
    (∫ x in a..b, (g (x + h) - g x)) = (∫ x in b..(b + h), g x) - ∫ x in a..(a + h), g x := by
  have hgi : ∀ p q : ℝ, IntervalIntegrable g volume p q := fun _ _ => hg.intervalIntegrable
  have hti : ∀ p q : ℝ, IntervalIntegrable (fun x => g (x + h)) volume p q := fun _ _ =>
    (monotone_comp_add_right hg h).intervalIntegrable
  rw [intervalIntegral.integral_sub (hti a b) (hgi a b),
    intervalIntegral.integral_comp_add_right g h]
  have h1 : (∫ x in a..(a + h), g x) + ∫ x in (a + h)..(b + h), g x = ∫ x in a..(b + h), g x :=
    intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _)
  have h2 : (∫ x in a..b, g x) + ∫ x in b..(b + h), g x = ∫ x in a..(b + h), g x :=
    intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _)
  linarith

/-- A short window of a monotone function is bounded above by its length times the right endpoint
value. -/
theorem integral_le_length_mul_right {g : ℝ → ℝ} (hg : Monotone g) {c h : ℝ} (hh : 0 ≤ h) :
    (∫ x in c..(c + h), g x) ≤ h * g (c + h) := by
  have hle : c ≤ c + h := by linarith
  have hmono : (∫ x in c..(c + h), g x) ≤ ∫ _x in c..(c + h), g (c + h) :=
    intervalIntegral.integral_mono_on hle hg.intervalIntegrable
      intervalIntegrable_const fun x hx => hg hx.2
  rwa [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hmono

/-- A short window of a monotone function is bounded below by its length times the left endpoint
value. -/
theorem length_mul_left_le_integral {g : ℝ → ℝ} (hg : Monotone g) {c h : ℝ} (hh : 0 ≤ h) :
    h * g c ≤ ∫ x in c..(c + h), g x := by
  have hle : c ≤ c + h := by linarith
  have hmono : (∫ _x in c..(c + h), g c) ≤ ∫ x in c..(c + h), g x :=
    intervalIntegral.integral_mono_on hle intervalIntegrable_const
      hg.intervalIntegrable fun x hx => hg hx.1
  rwa [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hmono

/-- **The `L¹` modulus of continuity of a monotone function.**  The translation difference over a
window is bounded by the shift times the variation of `g` across the enlarged window. -/
theorem integral_translate_sub_le {g : ℝ → ℝ} (hg : Monotone g) {a b h : ℝ} (hh : 0 ≤ h) :
    (∫ x in a..b, (g (x + h) - g x)) ≤ h * (g (b + h) - g a) := by
  rw [integral_translate_sub_eq_end_windows hg a b h]
  have hup := integral_le_length_mul_right hg (c := b) hh
  have hlow := length_mul_left_le_integral hg (c := a) hh
  nlinarith [hup, hlow]

/-- **The `L¹` modulus of continuity in absolute value.**  For a monotone function and a
nonnegative shift the integrand is already nonnegative, so the absolute value costs nothing. -/
theorem integral_abs_translate_sub_le {g : ℝ → ℝ} (hg : Monotone g) {a b h : ℝ} (hh : 0 ≤ h) :
    (∫ x in a..b, |g (x + h) - g x|) ≤ h * (g (b + h) - g a) := by
  have hcongr : (∫ x in a..b, |g (x + h) - g x|) = ∫ x in a..b, (g (x + h) - g x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact abs_of_nonneg (sub_nonneg.mpr (hg (by linarith)))
  rw [hcongr]
  exact integral_translate_sub_le hg hh

/-- **The bound in terms of the total rise.**  If a monotone function rises by at most `V` across
the whole enlarged window, its `L¹` translation modulus is at most `V · h`.  This is the estimate
that feeds the fractional Sobolev criterion. -/
theorem integral_abs_translate_sub_le_variation {g : ℝ → ℝ} (hg : Monotone g) {a b h V : ℝ}
    (hh : 0 ≤ h) (hV : g (b + h) - g a ≤ V) :
    (∫ x in a..b, |g (x + h) - g x|) ≤ V * h := by
  have hmain := integral_abs_translate_sub_le hg (a := a) (b := b) hh
  nlinarith [hmain, hV, hh]


/-! ## Interpolation: the `L²` translation modulus

Squaring costs a sup norm.  Combining the `L¹` bound above with the uniform bound gives the
`L²` modulus of continuity, which is the quantity the fractional Sobolev criterion integrates
against `|h|^{-(1+2s)}`.
-/

namespace MonotoneTranslation

open Set

/-- The translation difference of a monotone function is interval integrable. -/
theorem intervalIntegrable_translate_sub {g : ℝ → ℝ} (hg : Monotone g) (h a b : ℝ) :
    IntervalIntegrable (fun x => g (x + h) - g x) volume a b :=
  (monotone_comp_add_right hg h).intervalIntegrable.sub hg.intervalIntegrable

/-- The squared translation difference of a bounded monotone function is interval integrable:
it is measurable and dominated by a constant multiple of the difference itself. -/
theorem intervalIntegrable_translate_sub_sq {g : ℝ → ℝ} (hg : Monotone g) {h M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ x, |g (x + h) - g x| ≤ M) (a b : ℝ) :
    IntervalIntegrable (fun x => (g (x + h) - g x) ^ 2) volume a b := by
  refine IntervalIntegrable.mono_fun
    (((intervalIntegrable_translate_sub hg h a b).norm).const_mul M) ?_ ?_
  · exact (((monotone_comp_add_right hg h).measurable.sub hg.measurable).pow_const
      2).aestronglyMeasurable
  · filter_upwards with x
    have hsq : |(g (x + h) - g x) ^ 2| = |g (x + h) - g x| * |g (x + h) - g x| := by
      rw [sq, abs_mul]
    simp only [Real.norm_eq_abs, hsq, abs_mul, abs_abs, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hbd x) (abs_nonneg _)

/-- **The `L²` modulus of continuity of a bounded monotone function.**  Interpolating the `L¹`
bound against the uniform bound gives a modulus linear in the shift.  Linearity in `|h|` is
exactly the borderline that puts the profile in every `H^s` with `s < 1/2`. -/
theorem integral_sq_translate_sub_le {g : ℝ → ℝ} (hg : Monotone g) {a b h M V : ℝ}
    (hh : 0 ≤ h) (hM : 0 ≤ M) (hbd : ∀ x, |g (x + h) - g x| ≤ M)
    (hV : g (b + h) - g a ≤ V) (hab : a ≤ b) :
    (∫ x in a..b, (g (x + h) - g x) ^ 2) ≤ M * (V * h) := by
  have hstep : (∫ x in a..b, (g (x + h) - g x) ^ 2) ≤ ∫ x in a..b, M * |g (x + h) - g x| := by
    refine intervalIntegral.integral_mono_on hab
      (intervalIntegrable_translate_sub_sq hg hM hbd a b)
      (((intervalIntegrable_translate_sub hg h a b).abs).const_mul M) fun x _ => ?_
    have hsq : (g (x + h) - g x) ^ 2 = |g (x + h) - g x| * |g (x + h) - g x| := by
      rw [sq, abs_mul_abs_self]
    rw [hsq]
    exact mul_le_mul_of_nonneg_right (hbd x) (abs_nonneg _)
  rw [intervalIntegral.integral_const_mul] at hstep
  have hL1 := integral_abs_translate_sub_le_variation hg (a := a) (b := b) hh hV
  nlinarith [hstep, hL1, hM, hh]


/-! ## The Gagliardo integral converges exactly below one half

A modulus linear in the shift makes the Gagliardo integrand `‖Δ_h u‖₂² / |h|^{1+2s}` dominated by
`C |h|^{-2s}`, which is integrable near the origin precisely when `s < 1/2`.  This is the
threshold: the estimate is sharp, and a bounded-variation profile sits in every `H^s` below one
half and in none at or above it.
-/

/-- The Gagliardo dominating power is integrable near the origin exactly below the threshold. -/
theorem integrableOn_rpow_neg_two_mul {s : ℝ} (hs : s < 1 / 2) :
    IntegrableOn (fun h : ℝ => h ^ (-(2 * s))) (Ioo 0 1) := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  linarith

/-- Conversely, at or above the threshold the dominating power is not integrable — the exponent
`1/2` is not an artefact of the estimate. -/
theorem not_integrableOn_rpow_neg_two_mul {s : ℝ} (hs : 1 / 2 ≤ s) :
    ¬ IntegrableOn (fun h : ℝ => h ^ (-(2 * s))) (Ioo 0 1) := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  intro hcon
  linarith

/-- The Gagliardo quotient of a linear modulus is the dominating power. -/
theorem div_rpow_eq_rpow_neg_two_mul {s h : ℝ} (hpos : 0 < h) :
    h / h ^ (1 + 2 * s) = h ^ (-(2 * s)) := by
  have hsub : h ^ (1 : ℝ) / h ^ (1 + 2 * s) = h ^ ((1 : ℝ) - (1 + 2 * s)) :=
    (Real.rpow_sub hpos _ _).symm
  rw [Real.rpow_one] at hsub
  rw [hsub]
  congr 1
  ring

/-- **The Gagliardo seminorm is finite below one half.**  Any nonnegative modulus that is linear
in the shift makes the Gagliardo integrand integrable on the unit window for every `s < 1/2`. -/
theorem integrableOn_gagliardo_quotient {s C : ℝ} (hs : s < 1 / 2) {F : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable F (volume.restrict (Ioo (0 : ℝ) 1)))
    (hnn : ∀ h ∈ Ioo (0 : ℝ) 1, 0 ≤ F h) (hbd : ∀ h ∈ Ioo (0 : ℝ) 1, F h ≤ C * h) :
    IntegrableOn (fun h => F h / h ^ (1 + 2 * s)) (Ioo (0 : ℝ) 1) := by
  have hdom : IntegrableOn (fun h : ℝ => C * h ^ (-(2 * s))) (Ioo (0 : ℝ) 1) :=
    (integrableOn_rpow_neg_two_mul hs).const_mul C
  have hm : Measurable fun h : ℝ => h ^ (1 + 2 * s) := by fun_prop
  have hq : AEStronglyMeasurable (fun h => F h / h ^ (1 + 2 * s))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    simp only [div_eq_mul_inv]
    exact hmeas.mul (hm.inv).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hdom hq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  have hpos : (0 : ℝ) < h := hh.1
  have hden : (0 : ℝ) < h ^ (1 + 2 * s) := Real.rpow_pos_of_pos hpos _
  have hsplit := div_rpow_eq_rpow_neg_two_mul (s := s) hpos
  have hquot : F h / h ^ (1 + 2 * s) ≤ C * h ^ (-(2 * s)) := by
    rw [← hsplit, ← mul_div_assoc, div_le_div_iff_of_pos_right hden]
    exact hbd h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hnn h hh) hden.le)]
  exact hquot

/-! ## The logarithmic weight is dominated by every positive power

The Sobolev criterion is applied to `log⟨ξ⟩`, not to a power of `ξ`.  The two are compatible
because the logarithm grows slower than every positive power: `log⟨ξ⟩ ≤ C_s (1 + |ξ|^s)` for every
`s > 0`, with the explicit constant `C_s = 2^{s/2}/s`.  So membership in one Sobolev weight below
one half already puts `log⟨D⟩u` in `L²`.
-/

/-- A power of the larger of `1` and `|ξ|` is bounded by `1 + |ξ|^s`. -/
theorem max_one_abs_rpow_le (s : ℝ) (ξ : ℝ) :
    (max 1 |ξ|) ^ s ≤ 1 + |ξ| ^ s := by
  rcases le_total |ξ| 1 with h | h
  · rw [max_eq_left h, Real.one_rpow]
    have := Real.rpow_nonneg (abs_nonneg ξ) s
    linarith
  · rw [max_eq_right h]
    linarith [zero_le_one (α := ℝ)]

/-- The squared bracket is bounded by twice the square of the larger of `1` and `|ξ|`. -/
theorem one_add_sq_le_two_mul_max_sq (ξ : ℝ) : 1 + ξ ^ 2 ≤ 2 * (max 1 |ξ|) ^ 2 := by
  have h1 : (1 : ℝ) ≤ max 1 |ξ| := le_max_left _ _
  have h2 : |ξ| ≤ max 1 |ξ| := le_max_right _ _
  have h3 : ξ ^ 2 = |ξ| ^ 2 := (sq_abs ξ).symm
  nlinarith [abs_nonneg ξ]

/-- **The logarithmic weight is dominated by every positive power**, with explicit constant.
This is the compatibility that lets a fractional Sobolev bound feed a logarithmic multiplier. -/
theorem log_sqrt_one_add_sq_le {s : ℝ} (hs : 0 < s) (ξ : ℝ) :
    Real.log (Real.sqrt (1 + ξ ^ 2)) ≤ 2 ^ (s / 2) / s * (1 + |ξ| ^ s) := by
  have hbase : (0 : ℝ) < 1 + ξ ^ 2 := by positivity
  have hstep : Real.log (Real.sqrt (1 + ξ ^ 2)) ≤ Real.sqrt (1 + ξ ^ 2) ^ s / s :=
    Real.log_le_rpow_div (Real.sqrt_nonneg _) hs
  have hrw : Real.sqrt (1 + ξ ^ 2) ^ s = (1 + ξ ^ 2) ^ (s / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    ring_nf
  have hmax : (0 : ℝ) ≤ max 1 |ξ| := le_trans zero_le_one (le_max_left _ _)
  have hbound : (1 + ξ ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * (max 1 |ξ|) ^ s := by
    have h1 : (1 + ξ ^ 2) ^ (s / 2) ≤ (2 * (max 1 |ξ|) ^ 2) ^ (s / 2) :=
      Real.rpow_le_rpow hbase.le (one_add_sq_le_two_mul_max_sq ξ) (by positivity)
    have h2 : (2 * (max 1 |ξ|) ^ 2 : ℝ) ^ (s / 2) = 2 ^ (s / 2) * (max 1 |ξ|) ^ s := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast (max 1 |ξ|) 2, ← Real.rpow_mul hmax]
      congr 1
      push_cast
      ring
    rw [h2] at h1
    exact h1
  have hpow : (max 1 |ξ|) ^ s ≤ 1 + |ξ| ^ s := max_one_abs_rpow_le s ξ
  have htwo : (0 : ℝ) < 2 ^ (s / 2) := Real.rpow_pos_of_pos (by norm_num) _
  rw [hrw] at hstep
  have hchain : (1 + ξ ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * (1 + |ξ| ^ s) := by
    refine hbound.trans ?_
    exact mul_le_mul_of_nonneg_left hpow htwo.le
  calc Real.log (Real.sqrt (1 + ξ ^ 2)) ≤ (1 + ξ ^ 2) ^ (s / 2) / s := hstep
    _ ≤ 2 ^ (s / 2) * (1 + |ξ| ^ s) / s := by
        gcongr
    _ = 2 ^ (s / 2) / s * (1 + |ξ| ^ s) := by ring

end MonotoneTranslation

end GaloisForLFunctions.HTGeometry
