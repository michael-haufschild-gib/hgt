import GaloisForLFunctions.RHTower.ZetaCentredSawtoothContinuation

/-!
# The third-order Euler–Maclaurin representation of `ζ`

The corpus's centred representation (`zeta_eq_centredTruncated_of_re_pos`) stops at the second
Bernoulli kernel:

`ζ(s) = Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - N^{-s}/2 - s(s+1) ∫_N^∞ B₂({u}) u^{-s-2} du`.

Its remainder is `O(|s|² N^{-σ-1})`.  At height `T` that forces a truncation length `N ≥ T^{4/3}`
before the remainder is below `T^{-1/2}`, which is too long for zero detection.  One more
integration by parts removes the mean `-1/12` of `B₂` and moves to the third local kernel
`P₃(u) = u(u-1)(2u-1)/12`.  It vanishes at both endpoints of every cell and is bounded by `1/48`:

`ζ(s) = Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - N^{-s}/2 + (s/12) N^{-s-1}
          - s(s+1)(s+2) ∫_N^∞ P₃({u}) u^{-s-3} du`,

with `|∫_N^∞ P₃({u}) u^{-s-3} du| ≤ N^{-σ-2}/(48(σ+2))`.  The remainder is now `O(|s|³N^{-σ-2})`,
below `T^{-1/2}` as soon as `N ≥ T^{6/5+ε}`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Complex intervalIntegral

/-! ## The third Bernoulli kernel -/

/-- The third local Bernoulli kernel `u(u-1)(2u-1)/12`. -/
def bernoulliThirdLocal (u : ℝ) : ℝ := u * (u - 1) * (2 * u - 1) / 12

/-- The periodic third Bernoulli kernel `P₃({x})`. -/
def bernoulliThirdPeriodic (x : ℝ) : ℝ := bernoulliThirdLocal (Int.fract x)

theorem bernoulliThirdLocal_zero : bernoulliThirdLocal 0 = 0 := by
  simp [bernoulliThirdLocal]

theorem bernoulliThirdLocal_one : bernoulliThirdLocal 1 = 0 := by
  simp [bernoulliThirdLocal]

theorem continuous_bernoulliThirdLocal : Continuous bernoulliThirdLocal := by
  unfold bernoulliThirdLocal
  fun_prop

theorem abs_bernoulliThirdLocal_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |bernoulliThirdLocal u| ≤ 1 / 48 := by
  have ha : |u * (u - 1)| ≤ 1 / 4 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (u - 1 / 2)]
  have hb : |2 * u - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hprod : |u * (u - 1)| * |2 * u - 1| ≤ 1 / 4 := by
    calc |u * (u - 1)| * |2 * u - 1| ≤ 1 / 4 * 1 :=
          mul_le_mul ha hb (abs_nonneg _) (by norm_num)
      _ = 1 / 4 := by norm_num
  unfold bernoulliThirdLocal
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  linarith

theorem abs_bernoulliThirdPeriodic_le (x : ℝ) : |bernoulliThirdPeriodic x| ≤ 1 / 48 :=
  abs_bernoulliThirdLocal_le (Int.fract_nonneg x) (Int.fract_lt_one x).le

theorem measurable_bernoulliThirdPeriodic : Measurable bernoulliThirdPeriodic :=
  continuous_bernoulliThirdLocal.measurable.comp measurable_fract

/-- The derivative of the shifted third kernel is the centred second kernel
`((x-m)² - (x-m))/2 + 1/12`. -/
theorem hasDerivAt_bernoulliThirdLocal_sub (m x : ℝ) :
    HasDerivAt (fun y : ℝ => bernoulliThirdLocal (y - m))
      (((x - m) ^ 2 - (x - m)) / 2 + 1 / 12) x := by
  have h1 : HasDerivAt (fun y : ℝ => y - m) 1 x := (hasDerivAt_id x).sub_const m
  have h2 : HasDerivAt (fun y : ℝ => (y - m) * (y - m - 1) * (2 * (y - m) - 1) / 12)
      (((1 * (x - m - 1) + (x - m) * 1) * (2 * (x - m) - 1)
        + (x - m) * (x - m - 1) * (2 * 1)) / 12) x :=
    ((h1.mul (h1.sub_const 1)).mul ((h1.const_mul 2).sub_const 1)).div_const 12
  have hfun : (fun y : ℝ => bernoulliThirdLocal (y - m))
      = fun y : ℝ => (y - m) * (y - m - 1) * (2 * (y - m) - 1) / 12 := by
    funext y
    simp only [bernoulliThirdLocal]
  rw [hfun]
  exact h2.congr_deriv (by ring)

private theorem hasDerivAt_ofReal_cpow_pos {c : ℂ} {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ c) (c * (x : ℂ) ^ (c - 1)) x := by
  have hb : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have hmem : (x : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hx)
  have hout : HasDerivAt (fun z : ℂ => z ^ c) (c * (x : ℂ) ^ (c - 1) * 1) (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).cpow_const hmem
  have hcomp := hout.comp x hb
  have hfun : (fun y : ℝ => (y : ℂ) ^ c) = (fun z : ℂ => z ^ c) ∘ Complex.ofReal := by
    funext y
    rfl
  rw [hfun]
  exact hcomp.congr_deriv (by ring)

private theorem continuousOn_ofReal_cpow_cell {m : ℕ} (hm : 1 ≤ m) (c : ℂ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ c) (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
  have hmb : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  refine ContinuousOn.cpow_const (by fun_prop) (fun y hy => Or.inl ?_)
  rw [Set.uIcc_of_le hmb] at hy
  have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simpa using (by linarith [hy.1] : (0 : ℝ) < y)

/-! ## One cell -/

/-- **Per-cell integration by parts.**  The third kernel vanishes at both endpoints, so
`∫_m^{m+1} (B₂(x-m) + 1/12) x^{-s-2} = (s+2) ∫_m^{m+1} P₃(x-m) x^{-s-3}`. -/
theorem bernoulliThird_ibp_unit {m : ℕ} (hm : 1 ≤ m) (s : ℂ) :
    (∫ x in (m : ℝ)..((m : ℝ) + 1),
        ((((x - m) ^ 2 - (x - m)) / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2))
      = (s + 2) * ∫ x in (m : ℝ)..((m : ℝ) + 1),
          ((bernoulliThirdLocal (x - m) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3) := by
  have hmb : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hpos : ∀ y ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1), 0 < y := by
    intro y hy
    rw [Set.uIcc_of_le hmb] at hy
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith [hy.1]
  have hderiv : ∀ y ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1),
      HasDerivAt (fun y : ℝ => ((bernoulliThirdLocal (y - m) : ℝ) : ℂ) * (y : ℂ) ^ (-s - 2))
        (((((y - m) ^ 2 - (y - m)) / 2 + 1 / 12 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 2)
          + (-s - 2) * (((bernoulliThirdLocal (y - m) : ℝ) : ℂ) * (y : ℂ) ^ (-s - 3))) y := by
    intro y hy
    have hP := (hasDerivAt_bernoulliThirdLocal_sub (m : ℝ) y).ofReal_comp
    have hC := hasDerivAt_ofReal_cpow_pos (c := -s - 2) (hpos y hy)
    have hmul := hP.mul hC
    refine hmul.congr_deriv ?_
    rw [show (-s - 2 - 1 : ℂ) = -s - 3 by ring]
    ring
  have hAint : IntervalIntegrable
      (fun y : ℝ => ((((y - m) ^ 2 - (y - m)) / 2 + 1 / 12 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 2))
      volume (m : ℝ) ((m : ℝ) + 1) :=
    (ContinuousOn.mul (by fun_prop) (continuousOn_ofReal_cpow_cell hm _)).intervalIntegrable
  have hBint : IntervalIntegrable
      (fun y : ℝ => ((bernoulliThirdLocal (y - m) : ℝ) : ℂ) * (y : ℂ) ^ (-s - 3))
      volume (m : ℝ) ((m : ℝ) + 1) :=
    (ContinuousOn.mul
      ((Complex.continuous_ofReal.comp
        (continuous_bernoulliThirdLocal.comp (continuous_id.sub continuous_const))).continuousOn)
      (continuousOn_ofReal_cpow_cell hm _)).intervalIntegrable
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv (hAint.add (hBint.const_mul (-s - 2)))
  simp only [add_sub_cancel_left, sub_self, bernoulliThirdLocal_one, bernoulliThirdLocal_zero,
    Complex.ofReal_zero, zero_mul] at hFTC
  rw [intervalIntegral.integral_add hAint (hBint.const_mul _),
    intervalIntegral.integral_const_mul] at hFTC
  linear_combination hFTC

/-! ## Summing the cells -/

/-- **The cells from `N` to `M`.**  `∫_N^M (B₂({x}) + 1/12) x^{-s-2} = (s+2) ∫_N^M P₃({x}) x^{-s-3}`. -/
theorem bernoulliThird_ibp_sum_from {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) (s : ℂ) :
    (∫ x in (N : ℝ)..(M : ℝ), ((bernoulliPeriodic x + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2))
      = (s + 2) * ∫ x in (N : ℝ)..(M : ℝ),
          ((bernoulliThirdPeriodic x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3) := by
  have hcellL : ∀ m : ℕ, 1 ≤ m →
      (∫ x in (m : ℝ)..((m : ℝ) + 1),
          ((bernoulliPeriodic x + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2))
        = ∫ x in (m : ℝ)..((m : ℝ) + 1),
            ((((x - m) ^ 2 - (x - m)) / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2) := by
    intro m _
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    apply intervalIntegral.integral_congr_ae
    filter_upwards [fract_ae_sub m] with x hx
    intro hxu
    rw [Set.uIoc_of_le hle] at hxu
    simp only [bernoulliPeriodic, hx hxu]
  have hcellR : ∀ m : ℕ, 1 ≤ m →
      (∫ x in (m : ℝ)..((m : ℝ) + 1),
          ((bernoulliThirdPeriodic x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3))
        = ∫ x in (m : ℝ)..((m : ℝ) + 1),
            ((bernoulliThirdLocal (x - m) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3) := by
    intro m _
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    apply intervalIntegral.integral_congr_ae
    filter_upwards [fract_ae_sub m] with x hx
    intro hxu
    rw [Set.uIoc_of_le hle] at hxu
    simp only [bernoulliThirdPeriodic, hx hxu]
  have hintL : ∀ m : ℕ, 1 ≤ m → IntervalIntegrable
      (fun x : ℝ => ((bernoulliPeriodic x + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2))
      volume (m : ℝ) ((m : ℝ) + 1) := by
    intro m hm
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hG : IntervalIntegrable
        (fun x : ℝ => ((((x - m) ^ 2 - (x - m)) / 2 + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2))
        volume (m : ℝ) ((m : ℝ) + 1) :=
      (ContinuousOn.mul (by fun_prop) (continuousOn_ofReal_cpow_cell hm _)).intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hG ⊢
    refine hG.congr ?_
    have hae := (ae_restrict_iff' measurableSet_Ioc).mpr (fract_ae_sub m)
    filter_upwards [hae] with x hx
    simp only [bernoulliPeriodic, hx]
  have hintR : ∀ m : ℕ, 1 ≤ m → IntervalIntegrable
      (fun x : ℝ => ((bernoulliThirdPeriodic x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3))
      volume (m : ℝ) ((m : ℝ) + 1) := by
    intro m hm
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hG : IntervalIntegrable
        (fun x : ℝ => ((bernoulliThirdLocal (x - m) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3))
        volume (m : ℝ) ((m : ℝ) + 1) :=
      (ContinuousOn.mul
        ((Complex.continuous_ofReal.comp
          (continuous_bernoulliThirdLocal.comp (continuous_id.sub continuous_const))).continuousOn)
        (continuousOn_ofReal_cpow_cell hm _)).intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hG ⊢
    refine hG.congr ?_
    have hae := (ae_restrict_iff' measurableSet_Ioc).mpr (fract_ae_sub m)
    filter_upwards [hae] with x hx
    simp only [bernoulliThirdPeriodic, hx]
  set a : ℕ → ℝ := fun k => (N : ℝ) + k with ha
  have hak : ∀ k : ℕ, a k = ((N + k : ℕ) : ℝ) := fun k => by simp [ha]
  have hak1 : ∀ k : ℕ, a (k + 1) = ((N + k : ℕ) : ℝ) + 1 := fun k => by
    simp only [ha]
    push_cast
    ring
  have hsL := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : ℝ => ((bernoulliPeriodic x + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2))
    (a := a) (n := M - N)
    (fun k _ => by
      rw [hak k, hak1 k]
      exact hintL (N + k) (le_add_right hN))
  have hsR := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : ℝ => ((bernoulliThirdPeriodic x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3))
    (a := a) (n := M - N)
    (fun k _ => by
      rw [hak k, hak1 k]
      exact hintR (N + k) (le_add_right hN))
  have hstart : a 0 = (N : ℝ) := by simp only [ha]; simp
  have hend : a (M - N) = (M : ℝ) := by
    simp only [ha]
    rw [Nat.cast_sub hNM]
    ring
  rw [hstart, hend] at hsL hsR
  rw [← hsL, ← hsR, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hm1 : 1 ≤ N + k := le_add_right hN
  rw [hak k, hak1 k, hcellL (N + k) hm1, hcellR (N + k) hm1]
  exact bernoulliThird_ibp_unit hm1 s

/-! ## The tail -/

/-- The third-order tail `∫_N^∞ P₃({u}) u^{-s-3} du`. -/
def zetaBernoulliThirdTail (N : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi (N : ℝ), ((bernoulliThirdPeriodic u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 3)

variable {N : ℕ}

/-- Absolute integrability of the third-order integrand on `(N, ∞)` for `Re s > -2`. -/
theorem integrableOn_bernoulliThird_cpow {s : ℂ} (hs : -2 < s.re) (hN : 1 ≤ N) :
    IntegrableOn (fun u : ℝ => ((bernoulliThirdPeriodic u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 3))
      (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcomp : IntegrableOn (fun u : ℝ => u ^ (-s.re - 3)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => ((bernoulliThirdPeriodic u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 3))
      (volume.restrict (Set.Ioi (N : ℝ))) := by
    apply AEStronglyMeasurable.mul
    · exact (Complex.measurable_ofReal.comp measurable_bernoulliThirdPeriodic).aestronglyMeasurable
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
      exact (continuousAt_ofReal_cpow_const u (-s - 3) (Or.inr (ne_of_gt hu0))).continuousWithinAt
  refine Integrable.mono hcomp hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
  have hre : (-s - 3).re = -s.re - 3 := by
    simp only [Complex.sub_re, Complex.neg_re]
    norm_num
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
  have hb : |bernoulliThirdPeriodic u| ≤ 1 :=
    le_trans (abs_bernoulliThirdPeriodic_le u) (by norm_num)
  exact mul_le_of_le_one_left (Real.rpow_nonneg hu0.le _) hb

/-- **The third-order tail bound.**  `|∫_N^∞ P₃({u}) u^{-s-3} du| ≤ N^{-σ-2}/(48(σ+2))`. -/
theorem norm_zetaBernoulliThirdTail_le (hN : 1 ≤ N) {s : ℂ} (hs : -2 < s.re) :
    ‖zetaBernoulliThirdTail N s‖ ≤ (N : ℝ) ^ (-s.re - 2) / (48 * (s.re + 2)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcomp : IntegrableOn (fun u : ℝ => u ^ (-s.re - 3)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi (N : ℝ))),
      ‖((bernoulliThirdPeriodic u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 3)‖ ≤ (1 / 48) * u ^ (-s.re - 3) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
    have hre : (-s - 3).re = -s.re - 3 := by
      simp only [Complex.sub_re, Complex.neg_re]
      norm_num
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_bernoulliThirdPeriodic_le u)
      (Real.rpow_nonneg hu0.le _)
  have hle := norm_integral_le_of_norm_le (hcomp.const_mul (1 / 48)) hbound
  have hval : ∫ u in Set.Ioi (N : ℝ), (1 / 48 : ℝ) * u ^ (-s.re - 3)
      = (N : ℝ) ^ (-s.re - 2) / (48 * (s.re + 2)) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN0,
      show (-s.re - 3 + 1 : ℝ) = -s.re - 2 by ring]
    have h2 : s.re + 2 ≠ 0 := by linarith
    have h3 : -s.re - 2 ≠ 0 := by linarith
    field_simp
    ring
  unfold zetaBernoulliThirdTail
  linarith [hle, hval.le, hval.ge]

/-- **Removing the mean of `B₂`.**  On `Re s > -1`,
`∫_N^∞ B₂({u}) u^{-s-2} du = -N^{-s-1}/(12(s+1)) + (s+2) ∫_N^∞ P₃({u}) u^{-s-3} du`. -/
theorem zetaBernoulliTail_eq_third (hN : 1 ≤ N) {s : ℂ} (hs : -1 < s.re) :
    zetaBernoulliTail N s =
      -(N : ℂ) ^ (-s - 1) / (12 * (s + 1)) + (s + 2) * zetaBernoulliThirdTail N s := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  have hre : (-s - 2).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re]
    norm_num
    linarith
  have hexp : (-s - 1 - 1 : ℂ) = -s - 2 := by ring
  have hcpow : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hre hN0
  have hc : IntegrableOn (fun u : ℝ => (-1 / 12 : ℂ) * (u : ℂ) ^ (-s - 2)) (Set.Ioi (N : ℝ)) :=
    hcpow.const_mul _
  have hbint := integrableOn_bernoulli_cpow (s := s) hs hN
  rw [hexp] at hbint
  have hgint : IntegrableOn
      (fun u : ℝ => ((bernoulliPeriodic u + 1 / 12 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
      (Set.Ioi (N : ℝ)) := by
    refine (hbint.sub hc).congr_fun ?_ measurableSet_Ioi
    intro u _
    simp only [Pi.sub_apply]
    push_cast
    ring
  have hsplit : zetaBernoulliTail N s
      = (∫ u in Set.Ioi (N : ℝ), (-1 / 12 : ℂ) * (u : ℂ) ^ (-s - 2))
        + ∫ u in Set.Ioi (N : ℝ),
            ((bernoulliPeriodic u + 1 / 12 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2) := by
    unfold zetaBernoulliTail
    rw [← integral_add hc hgint]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro u _
    rw [hexp]
    push_cast
    ring
  have hconst : (∫ u in Set.Ioi (N : ℝ), (-1 / 12 : ℂ) * (u : ℂ) ^ (-s - 2))
      = -(N : ℂ) ^ (-s - 1) / (12 * (s + 1)) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_cpow_of_lt hre hN0,
      show (-s - 2 + 1 : ℂ) = -s - 1 by ring]
    have h2 : (-s - 1 : ℂ) ≠ 0 := by
      intro h
      exact hs1 (by linear_combination -h)
    field_simp
    push_cast
    ring
  have hthird := integrableOn_bernoulliThird_cpow (s := s) (by linarith) hN
  have hlim : (∫ u in Set.Ioi (N : ℝ),
        ((bernoulliPeriodic u + 1 / 12 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2))
      = (s + 2) * zetaBernoulliThirdTail N s := by
    have hL := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hgint tendsto_natCast_atTop_atTop
    have hR := (intervalIntegral_tendsto_integral_Ioi (N : ℝ) hthird
      tendsto_natCast_atTop_atTop).const_mul (s + 2)
    have heq : ∀ᶠ M : ℕ in atTop,
        (s + 2) * (∫ x in (N : ℝ)..(M : ℝ),
          ((bernoulliThirdPeriodic x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 3))
        = ∫ x in (N : ℝ)..(M : ℝ),
            ((bernoulliPeriodic x + 1 / 12 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2) := by
      filter_upwards [Filter.eventually_ge_atTop N] with M hM
      rw [bernoulliThird_ibp_sum_from hN hM s]
    exact tendsto_nhds_unique hL (hR.congr' heq)
  rw [hsplit, hconst, hlim]

/-! ## The representation -/

/-- **The third-order Euler–Maclaurin representation** on `Re s > 0`, `s ≠ 1`. -/
theorem riemannZeta_eq_eulerMaclaurinThird (hN : 1 ≤ N) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1)
        - (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
        - s * (s + 1) * (s + 2) * zetaBernoulliThirdTail N s := by
  have hsp1 : s + 1 ≠ 0 := by
    intro h
    have : (s + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  rw [zeta_eq_centredTruncated_of_re_pos hN hs0 hs1, zetaCentredTruncated,
    zetaBernoulliTail_eq_third hN (by linarith)]
  field_simp
  ring

/-- The explicit third-order Euler–Maclaurin main term. -/
def zetaEulerMaclaurinThirdMain (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1)
    - (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)

/-- **The third-order remainder bound.**  On `Re s > 0`, `s ≠ 1`,
`|ζ(s) - main_N(s)| ≤ |s(s+1)(s+2)| N^{-σ-2}/(48(σ+2))`. -/
theorem norm_riemannZeta_sub_eulerMaclaurinThirdMain_le (hN : 1 ≤ N) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - zetaEulerMaclaurinThirdMain N s‖
      ≤ ‖s * (s + 1) * (s + 2)‖ * ((N : ℝ) ^ (-s.re - 2) / (48 * (s.re + 2))) := by
  rw [riemannZeta_eq_eulerMaclaurinThird hN hs0 hs1, zetaEulerMaclaurinThirdMain,
    show ∀ a b : ℂ, a - b - a = -b from fun a b => by ring, norm_neg, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_zetaBernoulliThirdTail_le hN (by linarith))
    (norm_nonneg _)

end RHTower
