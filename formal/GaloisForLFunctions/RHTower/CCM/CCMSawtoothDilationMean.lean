import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.JacobianOneDim
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
* `sawWave`, `sawWave_eq_of_mem_Ioo`, `abs_sawWave_le` — the closed form of `S` and its sup bound.
* `integral_quadratic` — the fundamental theorem of calculus for a quadratic, which is all the
  integration the mean needs.
* `integral_sawUnit_dilate_piece`, `integral_sawUnit_dilate` — the exact integer-dilation mean
  `1/(12 n)` in unit normalization.  The `j`-th period of the fast factor contributes `1/(12 n²)`,
  uniformly in `j`, and there are `n` of them.
* `periodic_sawUnitDilate`, `sawDilatePrimitive`, `sawDilatePrimitive_periodic`,
  `abs_sawDilatePrimitive_le` — the centered product has period one and mean zero, so its primitive is
  periodic, and `1/3` bounds it uniformly in the dilation.
* `integral_sawUnit_comp_mul`, `abs_integral_sawUnit_le` — dilation divides the sawtooth primitive by
  the dilation, and the undilated primitive is bounded by `1/8`.
* `integral_deriv_mul_primitive` — integration by parts in which only the smooth factor is
  differentiated, proved by Fubini on the triangle `{a ≤ t ≤ u ≤ b}`.  A bounded measurable factor is
  admissible, so the discontinuity of the sawtooth costs nothing.
* `abs_integral_weight_mul_sawDilateCentered_le` — the averaging estimate: against a `C¹` weight
  vanishing at both ends of the window, the dilated product agrees with its own mean up to one third of
  the total variation of the weight, uniformly in the dilation.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set ArithmeticFunction Filter Topology

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
    (∫ u in a..b, (A + B * u + C * u ^ (2 : ℕ)))
      = (A * b + B * b ^ (2 : ℕ) / 2 + C * b ^ (3 : ℕ) / 3)
        - (A * a + B * a ^ (2 : ℕ) / 2 + C * a ^ (3 : ℕ) / 3) := by
  have hd : ∀ u ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => A * t + B * t ^ (2 : ℕ) / 2 + C * t ^ (3 : ℕ) / 3)
        (A + B * u + C * u ^ (2 : ℕ)) u := by
    intro u _
    have h1 : HasDerivAt (fun t : ℝ => A * t) (A * 1) u := (hasDerivAt_id u).const_mul A
    have h2 : HasDerivAt (fun t : ℝ => B * t ^ (2 : ℕ) / 2) (B * ((2 : ℕ) * u ^ (2 - 1)) / 2) u :=
      ((hasDerivAt_pow 2 u).const_mul B).div_const 2
    have h3 : HasDerivAt (fun t : ℝ => C * t ^ (3 : ℕ) / 3) (C * ((3 : ℕ) * u ^ (3 - 1)) / 3) u :=
      ((hasDerivAt_pow 3 u).const_mul C).div_const 3
    have h := (h1.add h2).add h3
    have heq : A * 1 + B * ((2 : ℕ) * u ^ (2 - 1)) / 2 + C * ((3 : ℕ) * u ^ (3 - 1)) / 3
        = A + B * u + C * u ^ (2 : ℕ) := by push_cast; ring
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
      = 1 / (12 * (n : ℝ) ^ (2 : ℕ)) := by
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
          + (-(1 / 2) + (j : ℝ) / n - 1 / (2 * n)) * t + (1 / n) * t ^ (2 : ℕ) := by
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
          + (-(1 / 2) + (j : ℝ) / n - 1 / (2 * n)) * t + (1 / n) * t ^ (2 : ℕ)) := by
        rw [integral_congr_of_Ioo (by norm_num : (0:ℝ) ≤ 1) hlin]
    _ = 1 / (12 * (n : ℝ) ^ (2 : ℕ)) := by
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
        = 1 / (12 * (n : ℝ) ^ (2 : ℕ)) := by
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
  have hlin : ∀ t ∈ Ioo (0 : ℝ) 1, sawUnit t = (1 / 2 : ℝ) + (-1) * t + 0 * t ^ (2 : ℕ) := by
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

/-- The centered integrand is bounded by `1/3`, uniformly in the dilation. -/
theorem abs_sawDilateCentered_le {n : ℕ} (hn : 0 < n) (t : ℝ) :
    |sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ))| ≤ 1 / 3 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : |sawUnit t * sawUnit ((n : ℝ) * t)| ≤ 1 / 4 := by
    rw [abs_mul]
    calc |sawUnit t| * |sawUnit ((n : ℝ) * t)| ≤ (1 / 2) * (1 / 2) :=
          mul_le_mul (abs_sawUnit_le t) (abs_sawUnit_le _) (abs_nonneg _) (by norm_num)
      _ = 1 / 4 := by norm_num
  have h2 : |1 / (12 * (n : ℝ))| ≤ 1 / 12 := by
    rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  calc |sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ))|
      ≤ |sawUnit t * sawUnit ((n : ℝ) * t)| + |1 / (12 * (n : ℝ))| := abs_sub _ _
    _ ≤ 1 / 4 + 1 / 12 := add_le_add h1 h2
    _ = 1 / 3 := by norm_num

theorem measurable_sawDilateCentered (n : ℕ) :
    Measurable fun t : ℝ => sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ)) :=
  (measurable_sawUnit.mul (measurable_sawUnit.comp (measurable_const_mul _))).sub measurable_const

/-- The primitive is bounded on one period by the sup norm of its integrand. -/
theorem abs_sawDilatePrimitive_le_of_mem {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |sawDilatePrimitive n u| ≤ 1 / 3 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) u,
      ‖sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ))‖ ≤ 1 / 3 := by
    intro t _
    rw [Real.norm_eq_abs]
    exact abs_sawDilateCentered_le hn t
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
    (∫ t in (0 : ℝ)..x, sawUnit t) = x / 2 - x ^ (2 : ℕ) / 2 := by
  have hlin : ∀ t ∈ Ioo (0 : ℝ) x, sawUnit t = (1 / 2 : ℝ) + (-1) * t + 0 * t ^ (2 : ℕ) := by
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
  exact hadj

theorem intervalIntegrable_of_bound_on {f : ℝ → ℝ} (hf : Measurable f) {C a b : ℝ} (hab : a ≤ b)
    (hb : ∀ t ∈ Icc a b, |f t| ≤ C) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := |C|) (by simp)
    hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact (hb t (Ioc_subset_Icc_self ht)).trans (le_abs_self C)

/-- Integration by parts in which only the smooth factor is differentiated.  The primitive of `g`
need not be differentiable anywhere: the identity comes from Fubini on the triangle
`{a ≤ t ≤ u ≤ b}`, so a bounded measurable `g` — in particular a discontinuous periodic sawtooth
product — is admissible.  All hypotheses on the smooth factor are local to the window, apart from
measurability of its derivative. -/
theorem integral_deriv_mul_primitive {a b : ℝ} (hab : a ≤ b) {g φ φ' : ℝ → ℝ}
    (hg : Measurable g) {Cg : ℝ} (hgb : ∀ t, |g t| ≤ Cg) (hφ'meas : Measurable φ')
    (hφ : ∀ u ∈ Icc a b, HasDerivAt φ (φ' u) u) {Cd : ℝ}
    (hφ'b : ∀ u ∈ Icc a b, |φ' u| ≤ Cd) :
    (∫ u in a..b, φ' u * (∫ t in a..u, g t))
      = φ b * (∫ t in a..b, g t) - ∫ t in a..b, φ t * g t := by
  classical
  have hCg : (0 : ℝ) ≤ |Cg| := abs_nonneg Cg
  have hCd : (0 : ℝ) ≤ |Cd| := abs_nonneg Cd
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hFmeas : Measurable
      (Function.uncurry fun u t : ℝ => φ' u * (if t ≤ u then g t else 0)) := by
    have h1 : Measurable fun p : ℝ × ℝ => φ' p.1 := hφ'meas.comp measurable_fst
    have h2 : Measurable fun p : ℝ × ℝ => if p.2 ≤ p.1 then g p.2 else 0 :=
      Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hg.comp measurable_snd) measurable_const
    exact h1.mul h2
  have habs : ∀ t u : ℝ, |if t ≤ u then g t else 0| ≤ |Cg| := by
    intro t u
    by_cases h : t ≤ u
    · rw [if_pos h]; exact (hgb t).trans (le_abs_self Cg)
    · rw [if_neg h, abs_zero]; exact hCg
  set μ : Measure ℝ := volume.restrict (Ioc a b) with hμ
  haveI hfin : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  have hFint : Integrable
      (Function.uncurry fun u t : ℝ => φ' u * (if t ≤ u then g t else 0)) (μ.prod μ) := by
    have hae : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ), p ∈ Ioc a b ×ˢ Ioc a b := by
      rw [hμ, Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    have hbound : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ),
        ‖Function.uncurry (fun u t : ℝ => φ' u * (if t ≤ u then g t else 0)) p‖
          ≤ |Cd| * |Cg| := by
      filter_upwards [hae] with p hp
      have h1 : |φ' p.1| ≤ |Cd| :=
        (hφ'b p.1 (Ioc_subset_Icc_self hp.1)).trans (le_abs_self Cd)
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 (habs p.2 p.1) (abs_nonneg _) hCd
    have h := MeasureTheory.Measure.integrableOn_of_bounded (s := Set.univ)
      (μ := μ.prod μ) (f := Function.uncurry fun u t : ℝ => φ' u * (if t ≤ u then g t else 0))
      (measure_ne_top _ _) hFmeas.aestronglyMeasurable (M := |Cd| * |Cg|)
      (by rwa [Measure.restrict_univ])
    rwa [MeasureTheory.integrableOn_univ] at h
  have hswap := MeasureTheory.integral_integral_swap hFint
  have hleft : (∫ u in a..b, φ' u * (∫ t in a..u, g t))
      = ∫ u, (∫ t, φ' u * (if t ≤ u then g t else 0) ∂μ) ∂μ := by
    rw [intervalIntegral.integral_of_le hab, ← hμ]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [integral_eq_integral_indicator hg hgb hu.1.le hu.2,
      intervalIntegral.integral_of_le hab, ← hμ, MeasureTheory.integral_const_mul]
  have hinner : ∀ t ∈ Ioc a b,
      (∫ u in a..b, φ' u * (if t ≤ u then g t else 0)) = g t * (φ b - φ t) := by
    intro t ht
    have hat : a ≤ t := ht.1.le
    have htb : t ≤ b := ht.2
    have hind : Measurable fun u : ℝ => φ' u * (if t ≤ u then g t else 0) :=
      hφ'meas.mul (Measurable.ite (measurableSet_le measurable_const measurable_id)
        measurable_const measurable_const)
    have hindb : ∀ u ∈ Icc a b, |φ' u * (if t ≤ u then g t else 0)| ≤ |Cd| * |Cg| := by
      intro u hu
      have h1 : |φ' u| ≤ |Cd| := (hφ'b u hu).trans (le_abs_self Cd)
      rw [abs_mul]
      exact mul_le_mul h1 (habs t u) (abs_nonneg _) hCd
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (a := a) (b := t) (c := b)
      (intervalIntegrable_of_bound_on hind hat
        (fun u hu => hindb u ⟨hu.1, le_trans hu.2 htb⟩))
      (intervalIntegrable_of_bound_on hind htb
        (fun u hu => hindb u ⟨le_trans hat hu.1, hu.2⟩))
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
    have hftc : (∫ u in t..b, φ' u) = φ b - φ t := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => ?_)
        (intervalIntegrable_of_bound_on hφ'meas htb
          (fun u hu => hφ'b u ⟨le_trans hat hu.1, hu.2⟩))
      rw [uIcc_of_le htb] at hu
      exact hφ u ⟨le_trans hat hu.1, hu.2⟩
    rw [h1, h2, hftc, zero_add] at hadj
    rw [← hadj]
    ring
  have hright : (∫ t, (∫ u, φ' u * (if t ≤ u then g t else 0) ∂μ) ∂μ)
      = ∫ t in a..b, g t * (φ b - φ t) := by
    rw [intervalIntegral.integral_of_le hab, ← hμ]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [← hinner t ht, intervalIntegral.integral_of_le hab, ← hμ]
  have hsplit : (∫ t in a..b, g t * (φ b - φ t))
      = φ b * (∫ t in a..b, g t) - ∫ t in a..b, φ t * g t := by
    have hgi : IntervalIntegrable g volume a b := intervalIntegrable_of_bound hg hgb a b
    have hφcont : ContinuousOn φ (uIcc a b) := by
      rw [huIcc]
      exact fun u hu => (hφ u hu).continuousAt.continuousWithinAt
    have h1 : IntervalIntegrable (fun t => φ b * g t) volume a b := hgi.const_mul _
    have h2 : IntervalIntegrable (fun t => φ t * g t) volume a b :=
      hgi.continuousOn_mul hφcont
    have hpt : ∀ t : ℝ, g t * (φ b - φ t) = φ b * g t - φ t * g t := fun t => by ring
    calc (∫ t in a..b, g t * (φ b - φ t))
        = ∫ t in a..b, (φ b * g t - φ t * g t) := by simp_rw [hpt]
      _ = (∫ t in a..b, φ b * g t) - ∫ t in a..b, φ t * g t :=
          intervalIntegral.integral_sub h1 h2
      _ = φ b * (∫ t in a..b, g t) - ∫ t in a..b, φ t * g t := by
          rw [intervalIntegral.integral_const_mul]
  rw [hleft, hswap, hright, hsplit]

theorem continuous_sawDilatePrimitive (n : ℕ) : Continuous (sawDilatePrimitive n) :=
  intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_sawDilateCentered n a b) 0

theorem integral_sawDilateCentered_eq (n : ℕ) (α x : ℝ) :
    (∫ t in α..x, (sawUnit t * sawUnit ((n : ℝ) * t) - 1 / (12 * (n : ℝ))))
      = sawDilatePrimitive n x - sawDilatePrimitive n α := by
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := α) (c := x)
    (intervalIntegrable_sawDilateCentered n 0 α) (intervalIntegrable_sawDilateCentered n α x)
  rw [sawDilatePrimitive, sawDilatePrimitive]
  linarith [hadj]

/-- **Equations (5)--(6), the averaging estimate.**  Against a `C¹` weight vanishing at both ends of
the window, the dilated sawtooth product agrees with its own mean up to one third of the total
variation of the weight — uniformly in the dilation.  This is the card's `(5)`--`(6)` with the
integration by parts performed in the multiplicative variable, so no almost-everywhere derivative of
the discontinuous primitive is ever used. -/
theorem abs_integral_weight_mul_sawDilateCentered_le {n : ℕ} (hn : 0 < n) {α β : ℝ} (hαβ : α ≤ β)
    {G G' : ℝ → ℝ} (hG : ∀ x, HasDerivAt G (G' x) x) (hG'c : Continuous G')
    {CG : ℝ} (hG'b : ∀ x, |G' x| ≤ CG) (hGα : G α = 0) (hGβ : G β = 0) :
    |∫ x in α..β, G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ)))|
      ≤ (1 / 3) * ∫ x in α..β, |G' x| := by
  have hgm := measurable_sawDilateCentered n
  have hgb := abs_sawDilateCentered_le hn
  have hibp := integral_deriv_mul_primitive hαβ hgm hgb hG'c.measurable
    (fun x _ => hG x) (fun x _ => hG'b x)
  rw [hGβ, zero_mul, zero_sub] at hibp
  simp only [integral_sawDilateCentered_eq n α] at hibp
  have hG'i : IntervalIntegrable G' volume α β := hG'c.intervalIntegrable _ _
  have hAi : IntervalIntegrable (fun x => G' x * sawDilatePrimitive n x) volume α β :=
    hG'i.mul_continuousOn (continuous_sawDilatePrimitive n).continuousOn
  have hconst : IntervalIntegrable (fun x => G' x * sawDilatePrimitive n α) volume α β :=
    hG'i.mul_continuousOn continuousOn_const
  have hstep : (∫ x in α..β, G' x * (sawDilatePrimitive n x - sawDilatePrimitive n α))
      = (∫ x in α..β, G' x * sawDilatePrimitive n x)
        - ∫ x in α..β, G' x * sawDilatePrimitive n α := by
    have hpt : ∀ x : ℝ, G' x * (sawDilatePrimitive n x - sawDilatePrimitive n α)
        = G' x * sawDilatePrimitive n x - G' x * sawDilatePrimitive n α := fun x => by ring
    simp_rw [hpt]
    exact intervalIntegral.integral_sub hAi hconst
  have hzero : (∫ x in α..β, G' x * sawDilatePrimitive n α) = 0 := by
    rw [intervalIntegral.integral_mul_const]
    have hftc : (∫ x in α..β, G' x) = G β - G α :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x) hG'i
    rw [hftc, hGα, hGβ, sub_zero, zero_mul]
  rw [hstep, hzero, sub_zero] at hibp
  have hkey : (∫ x in α..β, G x * (sawUnit x * sawUnit ((n : ℝ) * x) - 1 / (12 * (n : ℝ))))
      = -∫ x in α..β, G' x * sawDilatePrimitive n x := by
    linarith [hibp]
  rw [hkey, abs_neg]
  calc |∫ x in α..β, G' x * sawDilatePrimitive n x|
      ≤ ∫ x in α..β, |G' x * sawDilatePrimitive n x| :=
        intervalIntegral.abs_integral_le_integral_abs hαβ
    _ ≤ ∫ x in α..β, (1 / 3) * |G' x| := by
        refine intervalIntegral.integral_mono_on hαβ hAi.abs (hG'i.abs.const_mul _) ?_
        intro x _
        rw [abs_mul]
        have hA := abs_sawDilatePrimitive_le hn x
        nlinarith [abs_nonneg (G' x), abs_nonneg (sawDilatePrimitive n x)]
    _ = (1 / 3) * ∫ x in α..β, |G' x| := intervalIntegral.integral_const_mul _ _

/-! ## The sawtooth on one period, and its dilated primitive -/

/-- On the period starting at an integer the sawtooth is affine. -/
theorem sawUnit_eq_of_mem_Ico_int (k : ℤ) {x : ℝ} (hx : x ∈ Ico ((k : ℝ)) ((k : ℝ) + 1)) :
    sawUnit x = (k : ℝ) + 1 / 2 - x := by
  have hfl : ⌊x⌋ = k := by
    rw [Int.floor_eq_iff]
    exact ⟨hx.1, hx.2⟩
  have hfr : Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) := rfl
  rw [hfl] at hfr
  rw [sawUnit, hfr]
  ring

theorem intervalIntegrable_sawUnit_comp_mul (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => sawUnit ((n : ℝ) * t)) volume a b :=
  intervalIntegrable_of_bound (measurable_sawUnit.comp (measurable_const_mul _))
    (fun _ => abs_sawUnit_le _) a b

/-- **Equation (24), as a bound.**  The primitive of the dilated sawtooth is `O(1/n)`, uniformly on the
line and over base points. -/
theorem abs_integral_sawUnit_comp_mul_le {n : ℕ} (hn : 0 < n) (a x : ℝ) :
    |∫ t in a..x, sawUnit ((n : ℝ) * t)| ≤ 1 / (4 * (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := a) (c := x)
    (intervalIntegrable_sawUnit_comp_mul n 0 a) (intervalIntegrable_sawUnit_comp_mul n a x)
  have hsplit : (∫ t in a..x, sawUnit ((n : ℝ) * t))
      = (∫ t in (0 : ℝ)..x, sawUnit ((n : ℝ) * t))
        - ∫ t in (0 : ℝ)..a, sawUnit ((n : ℝ) * t) := by linarith [hadj]
  rw [hsplit, integral_sawUnit_comp_mul hn x, integral_sawUnit_comp_mul hn a, ← mul_sub, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)⁻¹)]
  have h1 := abs_integral_sawUnit_le ((n : ℝ) * x)
  have h2 := abs_integral_sawUnit_le ((n : ℝ) * a)
  have h3 := abs_sub (∫ t in (0 : ℝ)..((n : ℝ) * x), sawUnit t)
    (∫ t in (0 : ℝ)..((n : ℝ) * a), sawUnit t)
  have hle : |(∫ t in (0 : ℝ)..((n : ℝ) * x), sawUnit t)
      - ∫ t in (0 : ℝ)..((n : ℝ) * a), sawUnit t| ≤ 1 / 4 := by linarith
  calc (n : ℝ)⁻¹ * |(∫ t in (0 : ℝ)..((n : ℝ) * x), sawUnit t)
        - ∫ t in (0 : ℝ)..((n : ℝ) * a), sawUnit t|
      ≤ (n : ℝ)⁻¹ * (1 / 4) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 / (4 * (n : ℝ)) := by field_simp

end GaloisForLFunctions.RHTower

end
