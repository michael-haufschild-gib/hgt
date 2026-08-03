import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The integer-dilated sawtooth has an exact rational mean

The sawtooth `S(x) = ∑_{k ≥ 1} sin(kx)/k` equals `(π - x)/2` on `(0, 2π)`, so it is the `2π`-periodic
extension of a linear ramp.  Writing it as `π · (1/2 - {x/2π})` makes that closed form the definition
and the Fourier series a consequence, which is what lets the whole layer be computed without any
`L²` Fourier interface.

* `sawUnit` — the unit-period sawtooth `1/2 - {u}`, with its period, its closed form on `[0, 1)`, and
  the uniform bound `1/2`.
* `sawWave`, `sawWave_eq_of_mem_Ioo`, `abs_sawWave_le` — equation `(1)`.
* `integral_quadratic` — the fundamental theorem of calculus for a quadratic, which is all the
  integration the mean needs.
* `integral_sawUnit_dilate_piece`, `integral_sawUnit_dilate` — equation `(2)`, the exact
  integer-dilation mean `1/(12 n)` in unit normalization.  The `j`-th period of the fast factor
  contributes `1/(12 n²)`, uniformly in `j`, and there are `n` of them.
* `integral_sawWave_dilate` — equation `(2)` itself: the mean of `S(x) S(nx)` over a period is
  `π²/(12 n)`.
* `periodic_sawUnitDilate`, `sawDilatePrimitive`, `sawDilatePrimitive_periodic`,
  `abs_sawDilatePrimitive_le` — equations `(3)`--`(4)`: the centered product has period one and mean
  zero, so its primitive is periodic, and `1/3` bounds it uniformly in the dilation.
* `integral_sawUnit_comp_mul`, `abs_integral_sawUnit_le` — equation `(24)`: dilating divides the
  primitive by the dilation, and the undilated primitive is bounded by `1/8`.
* `endpointProfile`, `endpointProfile_mul_shift` — equations `(10)` and `(15)`.
* `sum_one_div_Icc_le_log`, `sum_vonMangoldt_div_le_log_sq` — equation `(16)`, with no error term:
  the harmonic bound is proved from `log(N/(N+1)) ≤ -1/(N+1)`, so the visible weight is at most
  `log² N`.
* `lseriesSummable_vonMangoldt_two`, `lseries_vonMangoldt_two` — equation `(17)`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set ArithmeticFunction

/-! ## The unit-period sawtooth -/

/-- The unit-period sawtooth `1/2 - {u}`. -/
def sawUnit (u : ℝ) : ℝ := 1 / 2 - Int.fract u

theorem sawUnit_eq_of_mem_Ico {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) : sawUnit u = 1 / 2 - u := by
  rw [sawUnit, Int.fract_eq_self.mpr ⟨hu.1, hu.2⟩]

theorem sawUnit_add_intCast (u : ℝ) (m : ℤ) : sawUnit (u + m) = sawUnit u := by
  rw [sawUnit, sawUnit, Int.fract_add_intCast]

theorem sawUnit_add_natCast (u : ℝ) (m : ℕ) : sawUnit (u + m) = sawUnit u := by
  have hcast : ((m : ℤ) : ℝ) = (m : ℝ) := by push_cast; ring
  rw [← hcast, sawUnit_add_intCast]

theorem abs_sawUnit_le (u : ℝ) : |sawUnit u| ≤ 1 / 2 := by
  rw [sawUnit, abs_le]
  exact ⟨by linarith [Int.fract_lt_one u], by linarith [Int.fract_nonneg u]⟩

theorem measurable_sawUnit : Measurable sawUnit :=
  measurable_const.sub measurable_fract

/-! ## The `2π`-periodic sawtooth -/

/-- **Equation (1).**  The `2π`-periodic sawtooth in closed form. -/
def sawWave (x : ℝ) : ℝ := Real.pi * sawUnit (x / (2 * Real.pi))

theorem sawWave_eq_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 (2 * Real.pi)) :
    sawWave x = (Real.pi - x) / 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : x / (2 * Real.pi) ∈ Ico (0 : ℝ) 1 :=
    ⟨div_nonneg hx.1.le hpi.le, by rw [div_lt_one hpi]; exact hx.2⟩
  rw [sawWave, sawUnit_eq_of_mem_Ico h1]
  have hne : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
  field_simp

theorem abs_sawWave_le (x : ℝ) : |sawWave x| ≤ Real.pi / 2 := by
  rw [sawWave, abs_mul, abs_of_pos Real.pi_pos]
  calc Real.pi * |sawUnit (x / (2 * Real.pi))| ≤ Real.pi * (1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_sawUnit_le _) Real.pi_pos.le
    _ = Real.pi / 2 := by ring

theorem sawWave_add_two_pi (x : ℝ) : sawWave (x + 2 * Real.pi) = sawWave x := by
  have hne : (2 * Real.pi) ≠ 0 := by positivity
  rw [sawWave, sawWave]
  congr 1
  rw [show (x + 2 * Real.pi) / (2 * Real.pi) = x / (2 * Real.pi) + ((1 : ℤ) : ℝ) by
    push_cast; field_simp]
  rw [sawUnit_add_intCast]

/-! ## The integration used -/

/-- The fundamental theorem of calculus for a quadratic. -/
theorem integral_quadratic (A B C a b : ℝ) :
    (∫ u in a..b, (A + B * u + C * u ^ 2))
      = (A * b + B * b ^ 2 / 2 + C * b ^ 3 / 3)
        - (A * a + B * a ^ 2 / 2 + C * a ^ 3 / 3) := by
  have hd : ∀ u ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => A * t + B * t ^ 2 / 2 + C * t ^ 3 / 3)
        (A + B * u + C * u ^ 2) u := by
    intro u _
    have h1 : HasDerivAt (fun t : ℝ => A * t) (A * 1) u := (hasDerivAt_id u).const_mul A
    have h2 : HasDerivAt (fun t : ℝ => B * t ^ 2 / 2) (B * ((2 : ℕ) * u ^ (2 - 1)) / 2) u :=
      ((hasDerivAt_pow 2 u).const_mul B).div_const 2
    have h3 : HasDerivAt (fun t : ℝ => C * t ^ 3 / 3) (C * ((3 : ℕ) * u ^ (3 - 1)) / 3) u :=
      ((hasDerivAt_pow 3 u).const_mul C).div_const 3
    have h := (h1.add h2).add h3
    have heq : A * 1 + B * ((2 : ℕ) * u ^ (2 - 1)) / 2 + C * ((3 : ℕ) * u ^ (3 - 1)) / 3
        = A + B * u + C * u ^ 2 := by push_cast; ring
    rw [← heq]
    exact h
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt hd ?_
  refine Continuous.intervalIntegrable ?_ _ _
  fun_prop

/-- An interval integral only sees the open interval. -/
theorem integral_congr_of_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ t ∈ Ioo a b, f t = g t) : (∫ t in a..b, f t) = ∫ t in a..b, g t := by
  refine intervalIntegral.integral_congr_ae ?_
  have h1 : ({b}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton b)
  filter_upwards [h1] with t ht hmem
  rw [Set.uIoc_of_le hab] at hmem
  exact h t ⟨hmem.1, lt_of_le_of_ne hmem.2 (by simpa using ht)⟩

theorem intervalIntegrable_sawUnit_dilate (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u => sawUnit u * sawUnit ((n : ℝ) * u)) volume a b := by
  have hmeas : Measurable fun u : ℝ => sawUnit u * sawUnit ((n : ℝ) * u) :=
    measurable_sawUnit.mul (measurable_sawUnit.comp (measurable_const_mul _))
  have hb : ∀ u : ℝ, ‖sawUnit u * sawUnit ((n : ℝ) * u)‖ ≤ 1 / 4 := by
    intro u
    rw [Real.norm_eq_abs, abs_mul]
    calc |sawUnit u| * |sawUnit ((n : ℝ) * u)| ≤ (1 / 2) * (1 / 2) :=
          mul_le_mul (abs_sawUnit_le u) (abs_sawUnit_le _) (abs_nonneg _) (by norm_num)
      _ = 1 / 4 := by norm_num
  constructor <;>
  · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1 / 4) (by simp)
      hmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hb

/-! ## The exact integer-dilation mean -/

/-- One period of the fast factor contributes `1/(12 n²)`, whatever the period index. -/
theorem integral_sawUnit_dilate_piece {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    (∫ u in ((j : ℝ) / n)..(((j : ℝ) + 1) / n), sawUnit u * sawUnit ((n : ℝ) * u))
      = 1 / (12 * (n : ℝ) ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hcongr : (∫ u in ((j : ℝ) / n)..(((j : ℝ) + 1) / n), sawUnit u * sawUnit ((n : ℝ) * u))
      = ∫ u in ((j : ℝ) / n)..(((j : ℝ) + 1) / n),
          sawUnit ((n : ℝ) * u / (n : ℝ)) * sawUnit ((n : ℝ) * u) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [mul_div_cancel_left₀ u hn0]
  have hmul := intervalIntegral.integral_comp_mul_left
    (a := (j : ℝ) / n) (b := ((j : ℝ) + 1) / n)
    (fun t : ℝ => sawUnit (t / (n : ℝ)) * sawUnit t) hn0
  have he1 : (n : ℝ) * ((j : ℝ) / n) = (j : ℝ) := by field_simp
  have he2 : (n : ℝ) * (((j : ℝ) + 1) / n) = (j : ℝ) + 1 := by field_simp
  have hshift := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (1 : ℝ))
    (fun t : ℝ => sawUnit (t / (n : ℝ)) * sawUnit t) (j : ℝ)
  rw [zero_add, add_comm (1 : ℝ) (j : ℝ)] at hshift
  have hlin : ∀ t ∈ Ioo (0 : ℝ) 1,
      sawUnit ((t + (j : ℝ)) / (n : ℝ)) * sawUnit (t + (j : ℝ))
        = (1 / 4 - (j : ℝ) / (2 * n))
          + (-(1 / 2) + (j : ℝ) / n - 1 / (2 * n)) * t + (1 / n) * t ^ 2 := by
    intro t ht
    have hmem : (t + (j : ℝ)) / (n : ℝ) ∈ Ico (0 : ℝ) 1 := by
      refine ⟨div_nonneg (by linarith [ht.1]) hnpos.le, ?_⟩
      rw [div_lt_one hnpos]
      have hjn : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
      linarith [ht.2]
    rw [sawUnit_eq_of_mem_Ico hmem, sawUnit_add_natCast t j,
      sawUnit_eq_of_mem_Ico ⟨ht.1.le, ht.2⟩]
    field_simp
    ring
  calc (∫ u in ((j : ℝ) / n)..(((j : ℝ) + 1) / n), sawUnit u * sawUnit ((n : ℝ) * u))
      = ∫ u in ((j : ℝ) / n)..(((j : ℝ) + 1) / n),
          sawUnit ((n : ℝ) * u / (n : ℝ)) * sawUnit ((n : ℝ) * u) := hcongr
    _ = (n : ℝ)⁻¹ • ∫ t in ((n : ℝ) * ((j : ℝ) / n))..((n : ℝ) * (((j : ℝ) + 1) / n)),
          sawUnit (t / (n : ℝ)) * sawUnit t := hmul
    _ = (n : ℝ)⁻¹ • ∫ t in ((j : ℝ))..((j : ℝ) + 1), sawUnit (t / (n : ℝ)) * sawUnit t := by
        rw [he1, he2]
    _ = (n : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
          sawUnit ((t + (j : ℝ)) / (n : ℝ)) * sawUnit (t + (j : ℝ)) := by
        rw [hshift]
    _ = (n : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1, ((1 / 4 - (j : ℝ) / (2 * n))
          + (-(1 / 2) + (j : ℝ) / n - 1 / (2 * n)) * t + (1 / n) * t ^ 2) := by
        rw [integral_congr_of_Ioo (by norm_num : (0:ℝ) ≤ 1) hlin]
    _ = 1 / (12 * (n : ℝ) ^ 2) := by
        rw [integral_quadratic, smul_eq_mul]
        field_simp
        ring

/-- **Equation (2), unit normalization.**  The exact integer-dilation mean. -/
theorem integral_sawUnit_dilate {n : ℕ} (hn : 0 < n) :
    (∫ u in (0 : ℝ)..1, sawUnit u * sawUnit ((n : ℝ) * u)) = 1 / (12 * (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) / n) (f := fun u => sawUnit u * sawUnit ((n : ℝ) * u))
    (n := n) (fun k _ => intervalIntegrable_sawUnit_dilate n _ _)
  have hpiece : ∀ k ∈ Finset.range n,
      (∫ u in ((k : ℝ) / n)..(((k : ℝ) + 1) / n), sawUnit u * sawUnit ((n : ℝ) * u))
        = 1 / (12 * (n : ℝ) ^ 2) := by
    intro k hk
    exact integral_sawUnit_dilate_piece hn (Finset.mem_range.mp hk)
  have hcast : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) / n = ((k : ℝ) + 1) / n := by
    intro k; push_cast; ring
  simp only [hcast] at hsum
  rw [Finset.sum_congr rfl hpiece, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hends : ((0 : ℕ) : ℝ) / n = 0 ∧ ((n : ℕ) : ℝ) / n = 1 := by
    refine ⟨by norm_num, div_self hn0⟩
  rw [hends.1, hends.2] at hsum
  rw [← hsum]
  field_simp

/-! ## Periodicity and the bounded zero-mean primitive -/

theorem periodic_sawUnit : Function.Periodic sawUnit 1 := by
  intro u
  simpa using sawUnit_add_natCast u 1

theorem periodic_sawUnitDilate (n : ℕ) :
    Function.Periodic (fun u => sawUnit u * sawUnit ((n : ℝ) * u)) 1 := by
  intro u
  have h1 : sawUnit (u + 1) = sawUnit u := periodic_sawUnit u
  have h2 : sawUnit ((n : ℝ) * (u + 1)) = sawUnit ((n : ℝ) * u) := by
    rw [mul_add, mul_one]
    simpa using sawUnit_add_natCast ((n : ℝ) * u) n
  simp only [h1, h2]

theorem intervalIntegrable_sawUnit (a b : ℝ) :
    IntervalIntegrable sawUnit volume a b := by
  have hb : ∀ u : ℝ, ‖sawUnit u‖ ≤ 1 / 2 := fun u => by
    rw [Real.norm_eq_abs]; exact abs_sawUnit_le u
  constructor <;>
  · refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1 / 2) (by simp)
      measurable_sawUnit.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hb

/-- The sawtooth has mean zero over a period. -/
theorem integral_sawUnit_unit : (∫ t in (0 : ℝ)..1, sawUnit t) = 0 := by
  have hlin : ∀ t ∈ Ioo (0 : ℝ) 1, sawUnit t = (1 / 2 : ℝ) + (-1) * t + 0 * t ^ 2 := by
    intro t ht
    rw [sawUnit_eq_of_mem_Ico ⟨ht.1.le, ht.2⟩]
    ring
  rw [integral_congr_of_Ioo (by norm_num : (0 : ℝ) ≤ 1) hlin, integral_quadratic]
  norm_num

/-- **Equation (3).**  The zero-mean primitive of the dilated sawtooth product. -/
def sawDilatePrimitive (n : ℕ) (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ)))

theorem intervalIntegrable_sawDilateCentered (n : ℕ) (a b : ℝ) :
    IntervalIntegrable
      (fun t => sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ))) volume a b :=
  (intervalIntegrable_sawUnit_dilate n a b).sub (intervalIntegrable_const)

/-- The centered integrand has period one and mean zero, so its primitive is periodic. -/
theorem sawDilatePrimitive_periodic {n : ℕ} (hn : 0 < n) :
    Function.Periodic (sawDilatePrimitive n) 1 := by
  have hper : Function.Periodic
      (fun t => sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ))) 1 := by
    intro t
    simp only [periodic_sawUnitDilate n t]
  have hmean : (∫ t in (0 : ℝ)..1,
      (sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ)))) = 0 := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_sawUnit_dilate n 0 1)
      intervalIntegrable_const, integral_sawUnit_dilate hn]
    simp
  intro u
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := u) (c := u + 1)
    (intervalIntegrable_sawDilateCentered n 0 u)
    (intervalIntegrable_sawDilateCentered n u (u + 1))
  have htrans := Function.Periodic.intervalIntegral_add_eq hper u 0
  rw [zero_add] at htrans
  show sawDilatePrimitive n (u + 1) = sawDilatePrimitive n u
  rw [sawDilatePrimitive, sawDilatePrimitive, ← hadj, htrans, hmean, add_zero]

/-- The primitive is bounded on one period by the sup norm of its integrand. -/
theorem abs_sawDilatePrimitive_le_of_mem {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |sawDilatePrimitive n u| ≤ 1 / 3 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) u,
      ‖sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ))‖ ≤ 1 / 3 := by
    intro t _
    have h1 : |sawUnit t * sawUnit ((n : ℝ) * t)| ≤ 1 / 4 := by
      rw [abs_mul]
      calc |sawUnit t| * |sawUnit ((n : ℝ) * t)| ≤ (1 / 2) * (1 / 2) :=
            mul_le_mul (abs_sawUnit_le t) (abs_sawUnit_le _) (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    have h2 : |1 / (12 * (n : ℝ))| ≤ 1 / 12 := by
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    rw [Real.norm_eq_abs]
    calc |sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ))|
        ≤ |sawUnit t * sawUnit ((n : ℝ) * t)| + |1 / (12 * (n : ℝ))| := abs_sub _ _
      _ ≤ 1 / 4 + 1 / 12 := add_le_add h1 h2
      _ = 1 / 3 := by norm_num
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at h
  calc |sawDilatePrimitive n u| ≤ 1 / 3 * |u - 0| := h
    _ ≤ 1 / 3 := by
        rw [sub_zero, abs_of_nonneg hu.1]
        nlinarith [hu.1, hu.2]

/-- **Equation (4).**  The zero-mean primitives are bounded uniformly in the dilation.  The card's
`C₀` is one admissible constant; in unit normalization `1/3` works. -/
theorem abs_sawDilatePrimitive_le {n : ℕ} (hn : 0 < n) (u : ℝ) :
    |sawDilatePrimitive n u| ≤ 1 / 3 := by
  have hper := sawDilatePrimitive_periodic hn
  have hshift : sawDilatePrimitive n (u - (⌊u⌋ : ℤ) * 1) = sawDilatePrimitive n u :=
    Function.Periodic.sub_int_mul_eq hper ⌊u⌋
  have hfr : u - ((⌊u⌋ : ℤ) : ℝ) * 1 = Int.fract u := by
    rw [mul_one]
    rfl
  rw [hfr] at hshift
  rw [← hshift]
  exact abs_sawDilatePrimitive_le_of_mem hn
    ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩

/-! ## The dilated sawtooth primitive -/

/-- **Equation (24).**  Dilating the sawtooth divides its primitive by the dilation. -/
theorem integral_sawUnit_comp_mul {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, sawUnit ((n : ℝ) * t))
      = (n : ℝ)⁻¹ * ∫ t in (0 : ℝ)..((n : ℝ) * x), sawUnit t := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := x) sawUnit hn0
  rw [mul_zero] at h
  rw [h, smul_eq_mul]

theorem periodic_integral_sawUnit :
    Function.Periodic (fun x => ∫ t in (0 : ℝ)..x, sawUnit t) 1 := by
  intro u
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := u) (c := u + 1)
    (intervalIntegrable_sawUnit 0 u) (intervalIntegrable_sawUnit u (u + 1))
  have htrans := Function.Periodic.intervalIntegral_add_eq periodic_sawUnit u 0
  rw [zero_add] at htrans
  show (∫ t in (0 : ℝ)..(u + 1), sawUnit t) = ∫ t in (0 : ℝ)..u, sawUnit t
  rw [← hadj, htrans, integral_sawUnit_unit, add_zero]

theorem integral_sawUnit_eq_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..x, sawUnit t) = x / 2 - x ^ 2 / 2 := by
  have hlin : ∀ t ∈ Ioo (0 : ℝ) x, sawUnit t = (1 / 2 : ℝ) + (-1) * t + 0 * t ^ 2 := by
    intro t ht
    rw [sawUnit_eq_of_mem_Ico ⟨ht.1.le, lt_of_lt_of_le ht.2 hx.2⟩]
    ring
  rw [integral_congr_of_Ioo hx.1 hlin, integral_quadratic]
  ring

/-- `1/8` bounds the sawtooth primitive, uniformly on the line. -/
theorem abs_integral_sawUnit_le (x : ℝ) : |∫ t in (0 : ℝ)..x, sawUnit t| ≤ 1 / 8 := by
  have hshift : (∫ t in (0 : ℝ)..(x - ((⌊x⌋ : ℤ) : ℝ) * 1), sawUnit t)
      = ∫ t in (0 : ℝ)..x, sawUnit t :=
    Function.Periodic.sub_int_mul_eq periodic_integral_sawUnit ⌊x⌋
  have hfr : x - ((⌊x⌋ : ℤ) : ℝ) * 1 = Int.fract x := by
    rw [mul_one]
    rfl
  rw [hfr] at hshift
  rw [← hshift, integral_sawUnit_eq_of_mem_Icc
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩]
  have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have h1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract x - 1 / 2), sq_nonneg (Int.fract x)]

/-! ## Distributional integration by parts against a bounded primitive -/

theorem intervalIntegrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ t, |f t| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  constructor <;>
  · refine MeasureTheory.Measure.integrableOn_of_bounded (M := C) (by simp)
      hf.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hb t

/-- The primitive of a bounded measurable function, read as an integral of a cut-off over the whole
window. -/
theorem integral_eq_integral_indicator {a b : ℝ} {g : ℝ → ℝ} (hg : Measurable g) {Cg : ℝ}
    (hgb : ∀ t, |g t| ≤ Cg) {u : ℝ} (hau : a ≤ u) (hub : u ≤ b) :
    (∫ t in a..u, g t) = ∫ t in a..b, (if t ≤ u then g t else 0) := by
  have hind : Measurable fun t : ℝ => if t ≤ u then g t else 0 :=
    Measurable.ite (measurableSet_le measurable_id measurable_const) hg measurable_const
  have hindb : ∀ t : ℝ, |if t ≤ u then g t else 0| ≤ |Cg| := by
    intro t
    by_cases h : t ≤ u
    · rw [if_pos h]
      exact (hgb t).trans (le_abs_self Cg)
    · rw [if_neg h, abs_zero]
      exact abs_nonneg Cg
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := a) (b := u) (c := b) (intervalIntegrable_of_bound hind hindb a u)
    (intervalIntegrable_of_bound hind hindb u b)
  have h1 : (∫ t in a..u, (if t ≤ u then g t else 0)) = ∫ t in a..u, g t := by
    refine integral_congr_of_Ioo hau fun t ht => ?_
    rw [if_pos ht.2.le]
  have h2 : (∫ t in u..b, (if t ≤ u then g t else 0)) = 0 := by
    have hz : (∫ t in u..b, (if t ≤ u then g t else 0)) = ∫ _ in u..b, (0 : ℝ) :=
      integral_congr_of_Ioo hub fun t ht => by rw [if_neg (by linarith [ht.1])]
    rw [hz, intervalIntegral.integral_zero]
  rw [h1, h2, add_zero] at hadj
  exact hadj.symm

/-- Integration by parts in which only the smooth factor is differentiated.  The primitive of `g`
need not be differentiable anywhere: the identity comes from Fubini on the triangle
`{a ≤ t ≤ u ≤ b}`, so a bounded measurable `g` — in particular a discontinuous periodic sawtooth
product — is admissible. -/
theorem integral_deriv_mul_primitive {a b : ℝ} (hab : a ≤ b) {g φ φ' : ℝ → ℝ}
    (hg : Measurable g) {Cg : ℝ} (hgb : ∀ t, |g t| ≤ Cg)
    (hφ : ∀ u, HasDerivAt φ (φ' u) u) (hφ'c : Continuous φ') {Cd : ℝ}
    (hφ'b : ∀ u, |φ' u| ≤ Cd) :
    (∫ u in a..b, φ' u * (∫ t in a..u, g t))
      = φ b * (∫ t in a..b, g t) - ∫ t in a..b, φ t * g t := by
  classical
  have hCg : (0 : ℝ) ≤ |Cg| := abs_nonneg Cg
  have hCd : (0 : ℝ) ≤ |Cd| := abs_nonneg Cd
  have hFmeas : Measurable
      (Function.uncurry fun u t : ℝ => φ' u * (if t ≤ u then g t else 0)) := by
    have h1 : Measurable fun p : ℝ × ℝ => φ' p.1 := hφ'c.measurable.comp measurable_fst
    have h2 : Measurable fun p : ℝ × ℝ => if p.2 ≤ p.1 then g p.2 else 0 :=
      Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hg.comp measurable_snd) measurable_const
    exact h1.mul h2
  have hFb : ∀ p : ℝ × ℝ,
      ‖Function.uncurry (fun u t : ℝ => φ' u * (if t ≤ u then g t else 0)) p‖
        ≤ |Cd| * |Cg| := by
    intro p
    have h1 : |φ' p.1| ≤ |Cd| := (hφ'b p.1).trans (le_abs_self Cd)
    have h2 : |if p.2 ≤ p.1 then g p.2 else 0| ≤ |Cg| := by
      by_cases h : p.2 ≤ p.1
      · rw [if_pos h]; exact (hgb p.2).trans (le_abs_self Cg)
      · rw [if_neg h, abs_zero]; exact hCg
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hCd
  -- Fubini on the window
  set μ : Measure ℝ := volume.restrict (Ioc a b) with hμ
  haveI hfin : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  have hFint : Integrable
      (Function.uncurry fun u t : ℝ => φ' u * (if t ≤ u then g t else 0)) (μ.prod μ) := by
    have h := MeasureTheory.Measure.integrableOn_of_bounded (s := Set.univ)
      (μ := μ.prod μ) (f := Function.uncurry fun u t : ℝ => φ' u * (if t ≤ u then g t else 0))
      (measure_ne_top _ _) hFmeas.aestronglyMeasurable (M := |Cd| * |Cg|)
      (Filter.Eventually.of_forall hFb)
    rwa [MeasureTheory.integrableOn_univ] at h
  have hswap := MeasureTheory.integral_integral_swap hFint
  -- the left side is the double integral
  have hleft : (∫ u in a..b, φ' u * (∫ t in a..u, g t))
      = ∫ u, (∫ t, φ' u * (if t ≤ u then g t else 0) ∂μ) ∂μ := by
    rw [intervalIntegral.integral_of_le hab, ← hμ]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [integral_eq_integral_indicator hg hgb hu.1.le hu.2,
      intervalIntegral.integral_of_le hab, ← hμ, MeasureTheory.integral_const_mul]
  -- the inner integral of the swapped side
  have hinner : ∀ t ∈ Ioc a b,
      (∫ u in a..b, φ' u * (if t ≤ u then g t else 0)) = g t * (φ b - φ t) := by
    intro t ht
    have hat : a ≤ t := ht.1.le
    have htb : t ≤ b := ht.2
    have hind : Measurable fun u : ℝ => φ' u * (if t ≤ u then g t else 0) :=
      hφ'c.measurable.mul
        (Measurable.ite (measurableSet_le measurable_const measurable_id)
          measurable_const measurable_const)
    have hindb : ∀ u : ℝ, |φ' u * (if t ≤ u then g t else 0)| ≤ |Cd| * |Cg| := by
      intro u
      have h1 : |φ' u| ≤ |Cd| := (hφ'b u).trans (le_abs_self Cd)
      have h2 : |if t ≤ u then g t else 0| ≤ |Cg| := by
        by_cases h : t ≤ u
        · rw [if_pos h]; exact (hgb t).trans (le_abs_self Cg)
        · rw [if_neg h, abs_zero]; exact hCg
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hCd
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (a := a) (b := t) (c := b) (intervalIntegrable_of_bound hind hindb a t)
      (intervalIntegrable_of_bound hind hindb t b)
    have h1 : (∫ u in a..t, φ' u * (if t ≤ u then g t else 0)) = 0 := by
      have hz : (∫ u in a..t, φ' u * (if t ≤ u then g t else 0)) = ∫ _ in a..t, (0 : ℝ) :=
        integral_congr_of_Ioo hat fun u hu => by
          rw [if_neg (by linarith [hu.2]), mul_zero]
      rw [hz, intervalIntegral.integral_zero]
    have h2 : (∫ u in t..b, φ' u * (if t ≤ u then g t else 0))
        = (∫ u in t..b, φ' u) * g t := by
      have hz : (∫ u in t..b, φ' u * (if t ≤ u then g t else 0))
          = ∫ u in t..b, φ' u * g t :=
        integral_congr_of_Ioo htb fun u hu => by rw [if_pos hu.1.le]
      rw [hz, intervalIntegral.integral_mul_const]
    have hftc : (∫ u in t..b, φ' u) = φ b - φ t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hφ u)
        (hφ'c.intervalIntegrable _ _)
    rw [h1, h2, hftc, zero_add] at hadj
    rw [← hadj]
    ring
  -- assemble
  have hright : (∫ t, (∫ u, φ' u * (if t ≤ u then g t else 0) ∂μ) ∂μ)
      = ∫ t in a..b, g t * (φ b - φ t) := by
    rw [intervalIntegral.integral_of_le hab, ← hμ]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [← hinner t ht, intervalIntegral.integral_of_le hab, ← hμ]
  have hsplit : (∫ t in a..b, g t * (φ b - φ t))
      = φ b * (∫ t in a..b, g t) - ∫ t in a..b, φ t * g t := by
    have hgi : IntervalIntegrable g volume a b := intervalIntegrable_of_bound hg hgb a b
    obtain ⟨Cφ, hCφ⟩ : ∃ C : ℝ, ∀ t ∈ Icc a b, |φ t| ≤ C :=
      (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
        (fun u _ => (hφ u).continuousAt.continuousWithinAt)
    have hφc : Continuous φ := by
      refine continuous_iff_continuousAt.mpr fun u => ?_
      exact (hφ u).continuousAt
    have h1 : IntervalIntegrable (fun t => φ b * g t) volume a b := hgi.const_mul _
    have h2 : IntervalIntegrable (fun t => φ t * g t) volume a b := by
      obtain ⟨C, hC⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
        hφc.continuousOn
      refine intervalIntegrable_of_bound (hφc.measurable.mul hg) (C := |C| * |Cg| + 1) ?_ a b
      intro t
      by_cases hmem : t ∈ uIcc a b
      · rw [abs_mul]
        have hb1 : |φ t| ≤ |C| := (hC t hmem).trans (le_abs_self C)
        have hb2 : |g t| ≤ |Cg| := (hgb t).trans (le_abs_self Cg)
        nlinarith [abs_nonneg (φ t), abs_nonneg (g t), abs_nonneg C, abs_nonneg Cg]
      · exact le_trans (le_of_eq rfl) (by nlinarith [abs_nonneg (φ t * g t),
          abs_nonneg C, abs_nonneg Cg, mul_nonneg hCd hCg])
    have hpt : ∀ t : ℝ, g t * (φ b - φ t) = φ b * g t - φ t * g t := fun t => by ring
    calc (∫ t in a..b, g t * (φ b - φ t))
        = ∫ t in a..b, (φ b * g t - φ t * g t) := by simp_rw [hpt]
      _ = (∫ t in a..b, φ b * g t) - ∫ t in a..b, φ t * g t :=
          intervalIntegral.integral_sub h1 h2
      _ = φ b * (∫ t in a..b, g t) - ∫ t in a..b, φ t * g t := by
          rw [intervalIntegral.integral_const_mul]
  rw [hleft, hswap, hright, hsplit]

/-! ## The endpoint profile and the shift identity -/

/-- **Equation (10).**  The normalized leading endpoint profile. -/
def endpointProfile (L s : ℝ) : ℝ := Real.exp (-s / 2) * sawWave (L * Real.exp s)

/-- **Equation (15).**  A logarithmic shift by `log n` turns the profile correlation into the
integer-dilated sawtooth product, with the exact Euler weight `n^{-1/2}` and the exponential
density `e^{-s}`. -/
theorem endpointProfile_mul_shift {n : ℕ} (hn : 0 < n) (L s : ℝ) :
    endpointProfile L s * endpointProfile L (s + Real.log n)
      = (Real.sqrt n)⁻¹ * (Real.exp (-s) *
          (sawWave (L * Real.exp s) * sawWave ((n : ℝ) * (L * Real.exp s)))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hexp : Real.exp (s + Real.log n) = Real.exp s * (n : ℝ) := by
    rw [Real.exp_add, Real.exp_log hnpos]
  have hsq : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have hinv : (Real.sqrt (n : ℝ))⁻¹ = Real.exp (-(Real.log n / 2)) := by
    rw [hsq, Real.exp_neg]
  have harg : L * Real.exp (s + Real.log n) = (n : ℝ) * (L * Real.exp s) := by
    rw [hexp]; ring
  have hcoef : Real.exp (-s / 2) * Real.exp (-(s + Real.log n) / 2)
      = Real.exp (-(Real.log n / 2)) * Real.exp (-s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [endpointProfile, endpointProfile, harg, hinv,
    show Real.exp (-s / 2) * sawWave (L * Real.exp s) *
        (Real.exp (-(s + Real.log n) / 2) * sawWave ((n : ℝ) * (L * Real.exp s)))
      = (Real.exp (-s / 2) * Real.exp (-(s + Real.log n) / 2)) *
        (sawWave (L * Real.exp s) * sawWave ((n : ℝ) * (L * Real.exp s))) from by ring,
    hcoef]
  ring

/-! ## The arithmetic weight -/

/-- A harmonic bound with no error term: `∑_{2 ≤ n ≤ N} 1/n ≤ log N`, from
`log(N/(N+1)) ≤ -1/(N+1)`. -/
theorem sum_one_div_Icc_le_log : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n ≤ Real.log N
  | 0, h => absurd h (by norm_num)
  | 1, _ => by norm_num
  | (N + 2), _ => by
    have hind := sum_one_div_Icc_le_log (N + 1) (by omega)
    have hpos : (0 : ℝ) < ((N : ℝ) + 1) := by positivity
    have hpos2 : (0 : ℝ) < ((N : ℝ) + 2) := by positivity
    have hkey : (1 : ℝ) / ((N : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) - Real.log ((N : ℝ) + 1) := by
      have hratio : ((N : ℝ) + 1) / ((N : ℝ) + 2) > 0 := by positivity
      have h1 := Real.log_le_sub_one_of_pos hratio
      rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hpos2)] at h1
      have h2 : ((N : ℝ) + 1) / ((N : ℝ) + 2) - 1 = -(1 / ((N : ℝ) + 2)) := by
        field_simp
        ring
      rw [h2] at h1
      linarith
    have htop := Finset.sum_Icc_succ_top (a := 2) (b := N + 1)
      (by omega : 2 ≤ N + 1 + 1) (fun n => (1 : ℝ) / n)
    rw [htop]
    have hcast1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((N + 1 + 1 : ℕ) : ℝ) = (N : ℝ) + 2 := by push_cast; ring
    rw [hcast2]
    rw [hcast1] at hind
    linarith

/-- **Equation (16).**  The visible von Mangoldt weight, divided by the radial index, is bounded by
the square of the logarithm of the cutoff. -/
theorem sum_vonMangoldt_div_le_log_sq {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) ≤ Real.log N ^ 2 := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hterm : ∀ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ) ≤ Real.log N * ((1 : ℝ) / n) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have h1 : Λ n ≤ Real.log n := vonMangoldt_le_log
    have h2 : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hn.2)
    rw [mul_one_div]
    gcongr
    linarith
  calc ∑ n ∈ Finset.Icc 2 N, Λ n / (n : ℝ)
      ≤ ∑ n ∈ Finset.Icc 2 N, Real.log N * ((1 : ℝ) / n) := Finset.sum_le_sum hterm
    _ = Real.log N * ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / n := by rw [Finset.mul_sum]
    _ ≤ Real.log N * Real.log N :=
        mul_le_mul_of_nonneg_left (sum_one_div_Icc_le_log N hN) hlogN
    _ = Real.log N ^ 2 := by ring

/-- **Equation (17).**  The Euler logarithmic-derivative moment.  The full weight `Λ(n) n^{-2}` is
absolutely summable and sums to `-ζ'(2)/ζ(2)`. -/
theorem lseriesSummable_vonMangoldt_two :
    LSeriesSummable (fun n => (Λ n : ℂ)) 2 :=
  LSeriesSummable_vonMangoldt (by norm_num)

theorem lseries_vonMangoldt_two :
    LSeries (fun n => (Λ n : ℂ)) 2 = -deriv riemannZeta 2 / riemannZeta 2 :=
  LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by norm_num)

/-- **Equation (2).**  The mean of `S(x) S(nx)` over a period is `π²/(12 n)`. -/
theorem integral_sawWave_dilate {n : ℕ} (hn : 0 < n) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), sawWave x * sawWave ((n : ℝ) * x))
      = 2 * Real.pi * (Real.pi ^ 2 / (12 * (n : ℝ))) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpine : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
  have hG : ∀ x : ℝ, sawWave x * sawWave ((n : ℝ) * x)
      = Real.pi ^ 2 * ((fun u : ℝ => sawUnit u * sawUnit ((n : ℝ) * u)) (x / (2 * Real.pi))) := by
    intro x
    rw [sawWave, sawWave]
    have hd : (n : ℝ) * x / (2 * Real.pi) = (n : ℝ) * (x / (2 * Real.pi)) := by ring
    rw [hd]
    ring
  simp_rw [hG]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun u : ℝ => sawUnit u * sawUnit ((n : ℝ) * u)) hpine,
    zero_div, div_self hpine, smul_eq_mul, integral_sawUnit_dilate hn]
  ring

end GaloisForLFunctions.RHTower

end
