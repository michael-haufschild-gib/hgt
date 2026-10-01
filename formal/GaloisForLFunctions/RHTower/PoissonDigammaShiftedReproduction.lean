import GaloisForLFunctions.RHTower.PoissonDigammaReproduction
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel

/-!
# The Poisson kernel reproduces the digamma line at every centre

For `a, c > 0` and every real `t`,

`∫ P_a(x − t) · Re ψ(c + i x/2) dx = Re ψ(c + a/2 + i t/2)`,  `P_a(x) = a/(π(a² + x²))`

(`integral_poissonWeight_shift_mul_re_digamma_half`).  This is the shifted form of
`integral_poissonWeight_mul_re_digamma_half`: the harmonic function `Re ψ(w/2)` on `Re w > 0` is
the Poisson integral of its values on every vertical line.

Each Gauss summand `1/(n+1) − 2B/(B² + x²)`, `B = 2(c+n)`, is a constant minus a Poisson kernel of
height `B`, and the Poisson semigroup `P_a ∗ P_B = P_{a+B}` evaluates it at the interior point
`c + a/2 + it/2`.  The Poisson masses of the absolute summands are `O(n⁻²)`, so the Gauss series may
be integrated termwise.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem poissonWeight_eq_halfPlanePoisson (a x : ℝ) :
    poissonWeight a x = halfPlanePoisson a x := rfl

theorem poissonWeight_sub_comm (a x t : ℝ) : poissonWeight a (x - t) = poissonWeight a (t - x) := by
  unfold poissonWeight
  rw [show (x - t) ^ 2 = (t - x) ^ 2 by ring]

theorem integrable_poissonWeight_shift {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Integrable fun x : ℝ => poissonWeight a (x - t) :=
  (integrable_poissonWeight ha).comp_sub_right t

theorem integral_poissonWeight_shift {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∫ x : ℝ, poissonWeight a (x - t)) = 1 := by
  rw [integral_sub_right_eq_self (fun x => poissonWeight a x) t]
  exact integral_poissonWeight ha

theorem inv_sq_add_sq_eq_halfPlanePoisson {B : ℝ} (hB : 0 < B) (x : ℝ) :
    (B ^ 2 + x ^ 2)⁻¹ = (Real.pi / B) * halfPlanePoisson B x := by
  unfold halfPlanePoisson
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hB0 : B ≠ 0 := hB.ne'
  have hd : B ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp

theorem poissonWeight_shift_mul_inv_eq {B : ℝ} (hB : 0 < B) (a t x : ℝ) :
    poissonWeight a (x - t) * (B ^ 2 + x ^ 2)⁻¹
      = (Real.pi / B) * (halfPlanePoisson a (t - x) * halfPlanePoisson B (x - 0)) := by
  rw [inv_sq_add_sq_eq_halfPlanePoisson hB, poissonWeight_sub_comm,
    poissonWeight_eq_halfPlanePoisson, sub_zero]
  ring

theorem integrable_poissonWeight_shift_mul_inv {a B : ℝ} (ha : 0 < a) (hB : 0 < B) (t : ℝ) :
    Integrable fun x : ℝ => poissonWeight a (x - t) * (B ^ 2 + x ^ 2)⁻¹ := by
  refine ((integrable_poisson_shift_product ha hB t 0).const_mul (Real.pi / B)).congr ?_
  filter_upwards with x
  rw [poissonWeight_shift_mul_inv_eq hB]

/-- The Poisson mass, centred at `t`, of a second Poisson kernel of height `B`. -/
theorem integral_poissonWeight_shift_mul_inv {a B : ℝ} (ha : 0 < a) (hB : 0 < B) (t : ℝ) :
    (∫ x : ℝ, poissonWeight a (x - t) * (B ^ 2 + x ^ 2)⁻¹)
      = (a + B) / (B * ((a + B) ^ 2 + t ^ 2)) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (poissonWeight_shift_mul_inv_eq hB a t)),
    integral_const_mul, integral_poisson_shift_product ha hB t 0, sub_zero]
  unfold halfPlanePoisson
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hB0 : B ≠ 0 := hB.ne'
  have hd : (a + B) ^ 2 + t ^ 2 ≠ 0 := by positivity
  field_simp

/-- The Poisson mass, centred at `t`, of the complementary weight `x²/(B² + x²)`. -/
theorem integral_poissonWeight_shift_mul_sq_div {a B : ℝ} (ha : 0 < a) (hB : 0 < B) (t : ℝ) :
    (∫ x : ℝ, poissonWeight a (x - t) * (x ^ 2 * (B ^ 2 + x ^ 2)⁻¹))
      = (a * (a + B) + t ^ 2) / ((a + B) ^ 2 + t ^ 2) := by
  have hcongr : ∀ x : ℝ, poissonWeight a (x - t) * (x ^ 2 * (B ^ 2 + x ^ 2)⁻¹)
      = poissonWeight a (x - t) - B ^ 2 * (poissonWeight a (x - t) * (B ^ 2 + x ^ 2)⁻¹) := by
    intro x
    have hne : B ^ 2 + x ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
    integral_sub (integrable_poissonWeight_shift ha t)
      ((integrable_poissonWeight_shift_mul_inv ha hB t).const_mul _),
    integral_const_mul, integral_poissonWeight_shift ha t,
    integral_poissonWeight_shift_mul_inv ha hB t]
  have hB0 : B ≠ 0 := hB.ne'
  have hd : (a + B) ^ 2 + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ## The Gauss summands -/

theorem integrable_poissonWeight_shift_mul_digammaHalfTerm {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (t : ℝ) (n : ℕ) :
    Integrable fun x : ℝ => poissonWeight a (x - t) * digammaHalfTerm c n x := by
  have hcn : (0 : ℝ) < 2 * (c + n) := by positivity
  refine (((integrable_poissonWeight_shift ha t).const_mul (1 / ((n : ℝ) + 1))).sub
    ((integrable_poissonWeight_shift_mul_inv ha hcn t).const_mul (2 * (2 * (c + n))))).congr ?_
  filter_upwards with x
  rw [digammaHalfTerm_eq hc n x]
  ring

/-- **The shifted Poisson mass of one Gauss summand** is the Gauss summand at the interior point
`c + a/2 + it/2`. -/
theorem integral_poissonWeight_shift_mul_digammaHalfTerm {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (t : ℝ) (n : ℕ) :
    (∫ x : ℝ, poissonWeight a (x - t) * digammaHalfTerm c n x)
      = (gaussDigammaSeriesTerm (((c + a / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I) n).re := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcn : (0 : ℝ) < 2 * (c + n) := by positivity
  have hcongr : ∀ x : ℝ, poissonWeight a (x - t) * digammaHalfTerm c n x
      = (1 / ((n : ℝ) + 1)) * poissonWeight a (x - t)
        - (2 * (2 * (c + n))) * (poissonWeight a (x - t) * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) := by
    intro x
    rw [digammaHalfTerm_eq hc n x]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
    integral_sub ((integrable_poissonWeight_shift ha t).const_mul _)
      ((integrable_poissonWeight_shift_mul_inv ha hcn t).const_mul _),
    integral_const_mul, integral_const_mul, integral_poissonWeight_shift ha t,
    integral_poissonWeight_shift_mul_inv ha hcn t, re_gaussDigammaSeriesTerm_vertical]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hd1 : (a + 2 * (c + n)) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have hd2 : (c + a / 2 + n) ^ (2 : ℕ) + (t / 2) ^ (2 : ℕ) ≠ 0 := by positivity
  have hcn0 : c + (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The shifted Poisson mass of one absolute Gauss summand. -/
theorem integral_norm_poissonWeight_shift_mul_digammaHalfTerm_le {a c : ℝ} (ha : 0 < a)
    (hc : 0 < c) (t : ℝ) (n : ℕ) :
    (∫ x : ℝ, ‖poissonWeight a (x - t) * digammaHalfTerm c n x‖)
      ≤ |digammaHalfDefect c n| + (2 / (2 * (c + n)))
          * ((a * (a + 2 * (c + n)) + t ^ 2) / ((a + 2 * (c + n)) ^ 2 + t ^ 2)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcn : (0 : ℝ) < 2 * (c + n) := by positivity
  have hq : Integrable fun x : ℝ =>
      poissonWeight a (x - t) * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) := by
    refine ((integrable_poissonWeight_shift ha t).sub
      ((integrable_poissonWeight_shift_mul_inv ha hcn t).const_mul ((2 * (c + n)) ^ 2))).congr ?_
    filter_upwards with x
    have hne : (2 * (c + n)) ^ 2 + x ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hmaj : Integrable fun x : ℝ =>
      |digammaHalfDefect c n| * poissonWeight a (x - t)
        + (2 / (2 * (c + n))) * (poissonWeight a (x - t)
            * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹)) :=
    ((integrable_poissonWeight_shift ha t).const_mul _).add (hq.const_mul _)
  have hptwise : ∀ x : ℝ, ‖poissonWeight a (x - t) * digammaHalfTerm c n x‖
      ≤ |digammaHalfDefect c n| * poissonWeight a (x - t)
        + (2 / (2 * (c + n))) * (poissonWeight a (x - t)
            * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹)) := by
    intro x
    have hP : 0 ≤ poissonWeight a (x - t) := poissonWeight_nonneg ha _
    have hw : 0 ≤ (2 / (2 * (c + n))) * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) := by
      positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP, digammaHalfTerm_split hc n x]
    have habs := abs_add_le (digammaHalfDefect c n)
      ((2 / (2 * (c + n))) * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹))
    rw [abs_of_nonneg hw] at habs
    nlinarith [habs, hP]
  refine (integral_mono (integrable_poissonWeight_shift_mul_digammaHalfTerm ha hc t n).norm
    hmaj hptwise).trans (le_of_eq ?_)
  rw [integral_add ((integrable_poissonWeight_shift ha t).const_mul _) (hq.const_mul _),
    integral_const_mul, integral_const_mul, integral_poissonWeight_shift ha t,
    integral_poissonWeight_shift_mul_sq_div ha hcn t, mul_one]

theorem digammaHalfShiftBound_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (t : ℝ) (n : ℕ) :
    |digammaHalfDefect c n| + (2 / (2 * (c + n)))
        * ((a * (a + 2 * (c + n)) + t ^ 2) / ((a + 2 * (c + n)) ^ 2 + t ^ 2))
      ≤ (|c - 1| / min c 1 + a / (2 * min c 1 ^ 2) + t ^ 2 / (4 * min c 1 ^ 3))
          * (1 / (((n : ℝ) + 1) ^ 2)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : (0 : ℝ) < min c 1 := lt_min hc one_pos
  have hm1 : min c 1 ≤ c := min_le_left _ _
  have hM : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hD : (0 : ℝ) < c + n := by linarith
  have hlow : min c 1 * ((n : ℝ) + 1) ≤ c + n := by
    rcases le_total c 1 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have heq : digammaHalfDefect c n = (c - 1) / (((n : ℝ) + 1) * (c + n)) := by
    rw [digammaHalfDefect]
    field_simp
    ring
  have h1 : |digammaHalfDefect c n| ≤ |c - 1| / (min c 1 * ((n : ℝ) + 1) ^ 2) := by
    rw [heq, abs_div, abs_of_pos (mul_pos hM hD)]
    refine div_le_div_of_nonneg_left (abs_nonneg (c - 1)) (mul_pos hm (by positivity)) ?_
    nlinarith [hlow, mul_pos hm hM]
  -- the Poisson part: `(2/B)·(a(a+B) + t²)/((a+B)² + t²) ≤ 2a/B² + 2t²/B³`
  set B : ℝ := 2 * (c + n) with hB
  have hBpos : 0 < B := by positivity
  have hBlow : 2 * min c 1 * ((n : ℝ) + 1) ≤ B := by rw [hB]; linarith
  have hBm : 2 * min c 1 ≤ B := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    nlinarith
  have hstep : (2 / B) * ((a * (a + B) + t ^ 2) / ((a + B) ^ 2 + t ^ 2))
      ≤ 2 * a / B ^ 2 + 2 * t ^ 2 / B ^ 3 := by
    have hden : (a + B) ^ 2 ≤ (a + B) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
    have hAB : 0 < a + B := by linarith
    have hfrac : (a * (a + B) + t ^ 2) / ((a + B) ^ 2 + t ^ 2)
        ≤ a / B + t ^ 2 / B ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have e1 : a / B * ((a + B) ^ 2 + t ^ 2) ≥ a * (a + B) := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hBpos]
        nlinarith [mul_pos ha hAB, sq_nonneg t, mul_pos ha hBpos]
      have e2 : t ^ 2 / B ^ 2 * ((a + B) ^ 2 + t ^ 2) ≥ t ^ 2 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : B ^ 2 ≤ (a + B) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
        nlinarith [sq_nonneg t]
      nlinarith
    calc (2 / B) * ((a * (a + B) + t ^ 2) / ((a + B) ^ 2 + t ^ 2))
        ≤ (2 / B) * (a / B + t ^ 2 / B ^ 2) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 2 * a / B ^ 2 + 2 * t ^ 2 / B ^ 3 := by field_simp; ring
  have hsq : 4 * min c 1 ^ 2 * ((n : ℝ) + 1) ^ 2 ≤ B ^ 2 := by
    have h0 : 0 ≤ 2 * min c 1 * ((n : ℝ) + 1) := by positivity
    nlinarith [hBlow]
  have hcube : 8 * min c 1 ^ 3 * ((n : ℝ) + 1) ^ 2 ≤ B ^ 3 := by
    have h0 : 0 ≤ 4 * min c 1 ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
    have : B ^ 3 = B ^ 2 * B := by ring
    rw [this]
    nlinarith [mul_le_mul hsq hBm (by positivity) (by positivity)]
  have h2 : 2 * a / B ^ 2 ≤ a / (2 * min c 1 ^ 2 * ((n : ℝ) + 1) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, ha]
  have h3 : 2 * t ^ 2 / B ^ 3 ≤ t ^ 2 / (4 * min c 1 ^ 3 * ((n : ℝ) + 1) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcube, sq_nonneg t]
  have hcomb : |c - 1| / (min c 1 * ((n : ℝ) + 1) ^ 2)
      + a / (2 * min c 1 ^ 2 * ((n : ℝ) + 1) ^ 2)
      + t ^ 2 / (4 * min c 1 ^ 3 * ((n : ℝ) + 1) ^ 2)
      = (|c - 1| / min c 1 + a / (2 * min c 1 ^ 2) + t ^ 2 / (4 * min c 1 ^ 3))
          * (1 / (((n : ℝ) + 1) ^ 2)) := by
    field_simp
  linarith [h1, hstep, h2, h3, hcomb.le, hcomb.ge]

theorem summable_integral_norm_poissonWeight_shift_digammaHalf {a c : ℝ} (ha : 0 < a)
    (hc : 0 < c) (t : ℝ) :
    Summable fun n : ℕ => ∫ x : ℝ, ‖poissonWeight a (x - t) * digammaHalfTerm c n x‖ :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => (integral_norm_poissonWeight_shift_mul_digammaHalfTerm_le ha hc t n).trans
      (digammaHalfShiftBound_le ha hc t n))
    (summable_one_div_natSucc_sq.mul_left _)

/-! ## The reproducing identity -/

theorem log_two_add_abs_le_add (x t : ℝ) :
    Real.log (2 + |x|) ≤ Real.log (2 + |x - t|) + Real.log (2 + |t|) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by positivity) ?_
  have h1 : |x| ≤ |x - t| + |t| := by
    calc |x| = |(x - t) + t| := by ring_nf
      _ ≤ |x - t| + |t| := abs_add_le _ _
  nlinarith [abs_nonneg (x - t), abs_nonneg t, mul_nonneg (abs_nonneg (x - t)) (abs_nonneg t)]

theorem integrable_poissonWeight_shift_mul_re_digamma_half {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (t : ℝ) :
    Integrable fun x : ℝ => poissonWeight a (x - t)
      * (Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re := by
  set K : ℝ := digammaVerticalGrowthConst c + Real.log (2 + |t|) with hKdef
  have hK : 0 ≤ K := by
    have := digammaVerticalGrowthConst_nonneg hc
    have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hmaj0 : Integrable fun y : ℝ =>
      (a / Real.pi) * (K * (a ^ 2 + y ^ 2)⁻¹ + Real.log (2 + |y|) * (a ^ 2 + y ^ 2)⁻¹) :=
    (((integrable_inv_sq_add_sq ha).const_mul K).add
      (integrable_log_mul_inv_sq_add_sq ha)).const_mul _
  refine (hmaj0.comp_sub_right t).mono' ?_ ?_
  · exact (integrable_poissonWeight_shift ha t).aestronglyMeasurable.mul
      (continuous_re_digamma_half hc).aestronglyMeasurable
  filter_upwards with x
  have hP : 0 ≤ poissonWeight a (x - t) := poissonWeight_nonneg ha _
  have hbound := abs_re_digamma_vertical_le hc (x / 2)
  have hhalf : |x / 2| ≤ |x| := by
    rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
    linarith [abs_nonneg x]
  have hmono : Real.log (2 + |x / 2|) ≤ Real.log (2 + |x|) :=
    Real.log_le_log (by positivity) (by linarith)
  have hshift := log_two_add_abs_le_add x t
  have hstep : |(Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re|
      ≤ K + Real.log (2 + |x - t|) := by
    rw [hKdef]
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP, poissonWeight_eq]
  have hapi : 0 ≤ (a / Real.pi) * (a ^ 2 + (x - t) ^ 2)⁻¹ := by
    have := Real.pi_pos
    positivity
  calc (a / Real.pi) * (a ^ 2 + (x - t) ^ 2)⁻¹
        * |(Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re|
      ≤ (a / Real.pi) * (a ^ 2 + (x - t) ^ 2)⁻¹ * (K + Real.log (2 + |x - t|)) :=
        mul_le_mul_of_nonneg_left hstep hapi
    _ = (a / Real.pi) * (K * (a ^ 2 + (x - t) ^ 2)⁻¹
          + Real.log (2 + |x - t|) * (a ^ 2 + (x - t) ^ 2)⁻¹) := by ring


/-- **The Poisson kernel reproduces the digamma line at every centre.** -/
theorem integral_poissonWeight_shift_mul_re_digamma_half {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (t : ℝ) :
    (∫ x : ℝ, poissonWeight a (x - t)
        * (Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re)
      = (Complex.digamma (((c + a / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)).re := by
  have hc2 : (0 : ℝ) < c + a / 2 := by linarith
  have hkey := integral_tsum_of_summable_integral_norm
    (F := fun n : ℕ => fun x : ℝ => poissonWeight a (x - t) * digammaHalfTerm c n x)
    (fun n => integrable_poissonWeight_shift_mul_digammaHalfTerm ha hc t n)
    (summable_integral_norm_poissonWeight_shift_digammaHalf ha hc t)
  have hL : (∑' n : ℕ, ∫ x : ℝ, poissonWeight a (x - t) * digammaHalfTerm c n x)
      = (Complex.digamma (((c + a / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)).re
        + Real.eulerMascheroniConstant := by
    rw [tsum_congr (integral_poissonWeight_shift_mul_digammaHalfTerm ha hc t)]
    have h := re_digamma_vertical_eq hc2 (t / 2)
    linarith [h]
  have hR : (∫ x : ℝ, ∑' n : ℕ, poissonWeight a (x - t) * digammaHalfTerm c n x)
      = ∫ x : ℝ, (poissonWeight a (x - t)
          * (Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re
          + Real.eulerMascheroniConstant * poissonWeight a (x - t)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (∑' n : ℕ, poissonWeight a (x - t) * digammaHalfTerm c n x) = _
    rw [tsum_mul_left, tsum_digammaHalfTerm hc x]
    ring
  have hint := integrable_poissonWeight_shift_mul_re_digamma_half ha hc t
  have htot := hkey.symm.trans hR
  rw [hL, integral_add hint ((integrable_poissonWeight_shift ha t).const_mul _),
    integral_const_mul, integral_poissonWeight_shift ha t, mul_one] at htot
  linarith

end

end RHTower
