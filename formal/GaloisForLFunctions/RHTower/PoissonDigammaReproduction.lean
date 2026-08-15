import GaloisForLFunctions.HTGeometry.LogWeightedPoisson
import GaloisForLFunctions.HTGeometry.GammaShiftExpIntegral
import GaloisForLFunctions.RHTower.DigammaVerticalGrowthBound

/-!
# The Poisson kernel reproduces the digamma line

Pairing the unit-mass Poisson kernel of height `a` with the Gauss series of `psi` on the vertical
line `c + i x / 2` evaluates every summand in closed form:

`(1/pi) int a/(a²+x²) · [1/(n+1) - 2 b_n/(b_n²+x²)] dx = 1/(n+1) - 1/(c + a/2 + n)`,  `b_n = 2(c+n)`,

which is the Gauss summand of `psi` at the *interior* point `c + a/2`.  Termwise summation — legal
because each summand splits as a summable constant plus a kernel whose Poisson mass is `O(n^{-2})`
— gives the reproducing identity

`(1/pi) int a/(a²+x²) · Re psi(c + i x/2) dx = psi(c + a/2)`.

This is the harmonic mean-value property of the archimedean rate, made elementary.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The unit-mass Poisson kernel -/

/-- The Poisson kernel of height `a` on the line, normalised to unit mass. -/
def poissonWeight (a x : ℝ) : ℝ := a / (Real.pi * (a ^ 2 + x ^ 2))

theorem poissonWeight_eq (a x : ℝ) :
    poissonWeight a x = (a / Real.pi) * (a ^ 2 + x ^ 2)⁻¹ := by
  unfold poissonWeight
  rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv, mul_assoc]

theorem poissonWeight_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 ≤ poissonWeight a x := by
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  unfold poissonWeight
  positivity

theorem integrable_poissonWeight {a : ℝ} (ha : 0 < a) : Integrable (poissonWeight a) := by
  refine ((integrable_inv_sq_add_sq ha).const_mul (a / Real.pi)).congr ?_
  filter_upwards with x
  exact (poissonWeight_eq a x).symm

theorem integral_poissonWeight {a : ℝ} (ha : 0 < a) : (∫ x : ℝ, poissonWeight a x) = 1 := by
  have hane : a ≠ 0 := ne_of_gt ha
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (poissonWeight_eq a)),
    MeasureTheory.integral_const_mul, integral_inv_sq_add_sq ha]
  field_simp

theorem integrable_poissonWeight_mul_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable fun x : ℝ => poissonWeight a x * (b ^ 2 + x ^ 2)⁻¹ := by
  refine ((integrable_inv_sq_add_sq_mul ha hb).const_mul (a / Real.pi)).congr ?_
  filter_upwards with x
  rw [poissonWeight_eq, mul_inv]
  ring

/-- The Poisson mass of a second Poisson kernel. -/
theorem integral_poissonWeight_mul_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ, poissonWeight a x * (b ^ 2 + x ^ 2)⁻¹) = 1 / (b * (a + b)) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  have habne : a + b ≠ 0 := by positivity
  have hcongr : ∀ x : ℝ, poissonWeight a x * (b ^ 2 + x ^ 2)⁻¹
      = (a / Real.pi) * (((a ^ 2 + x ^ 2) * (b ^ 2 + x ^ 2))⁻¹) := by
    intro x
    rw [poissonWeight_eq, mul_inv]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_const_mul, integral_inv_sq_add_sq_mul' ha hb]
  field_simp

/-- The Poisson mass of the complementary weight `x²/(b²+x²)`. -/
theorem integral_poissonWeight_mul_sq_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ, poissonWeight a x * (x ^ 2 * (b ^ 2 + x ^ 2)⁻¹)) = a / (a + b) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  have habne : a + b ≠ 0 := by positivity
  have hcongr : ∀ x : ℝ, poissonWeight a x * (x ^ 2 * (b ^ 2 + x ^ 2)⁻¹)
      = poissonWeight a x - b ^ 2 * (poissonWeight a x * (b ^ 2 + x ^ 2)⁻¹) := by
    intro x
    have hpos : (0 : ℝ) < b ^ 2 + x ^ 2 := by positivity
    have hne : (b ^ 2 + x ^ 2) ≠ 0 := ne_of_gt hpos
    field_simp
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_sub (integrable_poissonWeight ha)
      ((integrable_poissonWeight_mul_inv ha hb).const_mul (b ^ 2)),
    MeasureTheory.integral_const_mul, integral_poissonWeight ha,
    integral_poissonWeight_mul_inv ha hb]
  field_simp
  ring


/-! ## The Gauss series of the digamma line, paired with the Poisson kernel -/

/-- The Gauss summand of the digamma line at half height, as a real function of the line
variable. -/
def digammaHalfTerm (c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (gaussDigammaSeriesTerm ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I) n).re

/-- The constant part of a Gauss summand: its value at infinite height. -/
def digammaHalfDefect (c : ℝ) (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) - 1 / (c + n)

theorem digammaHalfTerm_eq {c : ℝ} (hc : 0 < c) (n : ℕ) (x : ℝ) :
    digammaHalfTerm c n x
      = 1 / ((n : ℝ) + 1) - 2 * (2 * (c + n)) * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹ := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcn : (0 : ℝ) < c + n := by linarith
  have hd1 : (0 : ℝ) < (c + n) ^ 2 + (x / 2) ^ 2 := by positivity
  have hd2 : (0 : ℝ) < (2 * (c + n)) ^ 2 + x ^ 2 := by positivity
  unfold digammaHalfTerm
  rw [re_gaussDigammaSeriesTerm_vertical c (x / 2) n]
  rw [div_eq_mul_inv]
  field_simp

theorem digammaHalfTerm_split {c : ℝ} (hc : 0 < c) (n : ℕ) (x : ℝ) :
    digammaHalfTerm c n x
      = digammaHalfDefect c n
        + (2 / (2 * (c + n))) * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcn : (0 : ℝ) < c + n := by linarith
  have hd2 : (0 : ℝ) < (2 * (c + n)) ^ 2 + x ^ 2 := by positivity
  rw [digammaHalfTerm_eq hc n x, digammaHalfDefect]
  field_simp
  ring

theorem integrable_poissonWeight_mul_digammaHalfTerm {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (n : ℕ) :
    Integrable fun x : ℝ => poissonWeight a x * digammaHalfTerm c n x := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcn : (0 : ℝ) < 2 * (c + n) := by linarith
  have hbase : Integrable fun x : ℝ =>
      (1 / ((n : ℝ) + 1)) * poissonWeight a x
        - (2 * (2 * (c + n))) * (poissonWeight a x * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) :=
    ((integrable_poissonWeight ha).const_mul _).sub
      ((integrable_poissonWeight_mul_inv ha hcn).const_mul _)
  refine hbase.congr ?_
  filter_upwards with x
  rw [digammaHalfTerm_eq hc n x]
  ring

/-- **The Poisson mass of one Gauss summand** is the Gauss summand at the interior point. -/
theorem integral_poissonWeight_mul_digammaHalfTerm {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (n : ℕ) :
    (∫ x : ℝ, poissonWeight a x * digammaHalfTerm c n x)
      = 1 / ((n : ℝ) + 1) - 1 / (c + a / 2 + n) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcn : (0 : ℝ) < 2 * (c + n) := by linarith
  have hcongr : ∀ x : ℝ, poissonWeight a x * digammaHalfTerm c n x
      = (1 / ((n : ℝ) + 1)) * poissonWeight a x
        - (2 * (2 * (c + n))) * (poissonWeight a x * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) := by
    intro x
    rw [digammaHalfTerm_eq hc n x]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_sub ((integrable_poissonWeight ha).const_mul _)
      ((integrable_poissonWeight_mul_inv ha hcn).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_poissonWeight ha, integral_poissonWeight_mul_inv ha hcn]
  have hane : a ≠ 0 := ne_of_gt ha
  have hsum : (0 : ℝ) < a + 2 * (c + n) := by linarith
  have hkey : (2 * (2 * (c + n))) * (1 / (2 * (c + n) * (a + 2 * (c + n))))
      = 1 / (c + a / 2 + n) := by
    rw [eq_div_iff (by intro h0; nlinarith)]
    field_simp
    ring
  rw [mul_one, hkey]

/-- The Poisson mass of the absolute value of one Gauss summand. -/
theorem integral_norm_poissonWeight_mul_digammaHalfTerm_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) :
    (∫ x : ℝ, ‖poissonWeight a x * digammaHalfTerm c n x‖)
      ≤ |digammaHalfDefect c n| + (2 / (2 * (c + n))) * (a / (a + 2 * (c + n))) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcn : (0 : ℝ) < 2 * (c + n) := by linarith
  have hmaj : Integrable fun x : ℝ =>
      |digammaHalfDefect c n| * poissonWeight a x
        + (2 / (2 * (c + n))) * (poissonWeight a x * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹)) := by
    refine ((integrable_poissonWeight ha).const_mul _).add ?_
    refine Integrable.const_mul ?_ _
    have hsub : Integrable fun x : ℝ =>
        poissonWeight a x - (2 * (c + n)) ^ 2 * (poissonWeight a x
          * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) :=
      (integrable_poissonWeight ha).sub
        ((integrable_poissonWeight_mul_inv ha hcn).const_mul _)
    refine hsub.congr ?_
    filter_upwards with x
    have hpos : (0 : ℝ) < (2 * (c + n)) ^ 2 + x ^ 2 := by positivity
    have hne : ((2 * (c + n)) ^ 2 + x ^ 2) ≠ 0 := ne_of_gt hpos
    field_simp
    ring
  have hptwise : ∀ x : ℝ, ‖poissonWeight a x * digammaHalfTerm c n x‖
      ≤ |digammaHalfDefect c n| * poissonWeight a x
        + (2 / (2 * (c + n))) * (poissonWeight a x
            * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹)) := by
    intro x
    have hP : 0 ≤ poissonWeight a x := poissonWeight_nonneg ha x
    have hpos : (0 : ℝ) < (2 * (c + n)) ^ 2 + x ^ 2 := by positivity
    have hq : 0 ≤ x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP, digammaHalfTerm_split hc n x]
    have habs : |digammaHalfDefect c n
        + (2 / (2 * (c + n))) * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹)|
        ≤ |digammaHalfDefect c n|
          + (2 / (2 * (c + n))) * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) := by
      refine le_trans (abs_add_le _ _) ?_
      have : |(2 / (2 * (c + n))) * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹)|
          = (2 / (2 * (c + n))) * (x ^ 2 * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) := by
        rw [abs_of_nonneg (by positivity)]
      linarith [this.le, this.ge]
    nlinarith [habs, hP]
  have hle := MeasureTheory.integral_mono
    (integrable_poissonWeight_mul_digammaHalfTerm ha hc n).norm hmaj hptwise
  refine le_trans hle ?_
  rw [MeasureTheory.integral_add ((integrable_poissonWeight ha).const_mul _)
      (Integrable.const_mul (by
        have hsub : Integrable fun x : ℝ =>
            poissonWeight a x - (2 * (c + n)) ^ 2 * (poissonWeight a x
              * ((2 * (c + n)) ^ 2 + x ^ 2)⁻¹) :=
          (integrable_poissonWeight ha).sub
            ((integrable_poissonWeight_mul_inv ha hcn).const_mul _)
        refine hsub.congr ?_
        filter_upwards with x
        have hpos : (0 : ℝ) < (2 * (c + n)) ^ 2 + x ^ 2 := by positivity
        have hne : ((2 * (c + n)) ^ 2 + x ^ 2) ≠ 0 := ne_of_gt hpos
        field_simp
        ring) _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_poissonWeight ha, integral_poissonWeight_mul_sq_div ha hcn, mul_one]


/-! ## Termwise summation -/

theorem summable_one_div_natSucc_sq : Summable fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  apply h.congr
  intro n
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  simp only [Real.rpow_two]

theorem digammaHalfBound_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (n : ℕ) :
    |digammaHalfDefect c n| + (2 / (2 * (c + n))) * (a / (a + 2 * (c + n)))
      ≤ (|c - 1| / min c 1 + a / (2 * min c 1 ^ 2)) * (1 / (((n : ℝ) + 1) ^ 2)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : (0 : ℝ) < min c 1 := lt_min hc one_pos
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
  have h2 : (2 / (2 * (c + n))) * (a / (a + 2 * (c + n)))
      ≤ a / (2 * min c 1 ^ 2 * ((n : ℝ) + 1) ^ 2) := by
    have hstep : (2 / (2 * (c + n))) * (a / (a + 2 * (c + n))) ≤ a / (2 * (c + n) ^ 2) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos ha hD, sq_nonneg a, mul_nonneg (mul_nonneg ha.le ha.le) hD.le]
    refine le_trans hstep ?_
    refine div_le_div_of_nonneg_left ha.le (by positivity) ?_
    nlinarith [hlow, mul_pos hm hM]
  have hcomb : |c - 1| / (min c 1 * ((n : ℝ) + 1) ^ 2)
      + a / (2 * min c 1 ^ 2 * ((n : ℝ) + 1) ^ 2)
      = (|c - 1| / min c 1 + a / (2 * min c 1 ^ 2)) * (1 / (((n : ℝ) + 1) ^ 2)) := by
    field_simp
  linarith [h1, h2, hcomb.le, hcomb.ge]

theorem summable_digammaHalfBound {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Summable fun n : ℕ =>
      |digammaHalfDefect c n| + (2 / (2 * (c + n))) * (a / (a + 2 * (c + n))) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => digammaHalfBound_le ha hc n)
    (summable_one_div_natSucc_sq.mul_left _)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hD : (0 : ℝ) < c + n := by linarith
  have : (0 : ℝ) ≤ (2 / (2 * (c + n))) * (a / (a + 2 * (c + n))) := by positivity
  linarith [abs_nonneg (digammaHalfDefect c n)]

theorem summable_integral_norm_poissonWeight_digammaHalf {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Summable fun n : ℕ => ∫ x : ℝ, ‖poissonWeight a x * digammaHalfTerm c n x‖ :=
  Summable.of_nonneg_of_le (fun _ => MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
    (fun n => integral_norm_poissonWeight_mul_digammaHalfTerm_le ha hc n)
    (summable_digammaHalfBound ha hc)

theorem tsum_digammaHalfTerm {c : ℝ} (hc : 0 < c) (x : ℝ) :
    (∑' n : ℕ, digammaHalfTerm c n x)
      = (Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re
        + Real.eulerMascheroniConstant := by
  have h := re_digamma_vertical_eq hc (x / 2)
  unfold digammaHalfTerm
  linarith [h]

theorem re_gaussDigammaSeriesTerm_realPoint {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (gaussDigammaSeriesTerm ((s : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) n).re
      = 1 / ((n : ℝ) + 1) - 1 / (s + n) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsn : (0 : ℝ) < s + n := by linarith
  have hne : s + (n : ℝ) ≠ 0 := ne_of_gt hsn
  have hz : (s + (n : ℝ)) / ((s + (n : ℝ)) ^ 2 + (0 : ℝ) ^ 2) = 1 / (s + (n : ℝ)) := by
    rw [show ((s + (n : ℝ)) ^ 2 + (0 : ℝ) ^ 2) = (s + (n : ℝ)) * (s + (n : ℝ)) by ring]
    field_simp
  rw [re_gaussDigammaSeriesTerm_vertical s 0 n, hz]

/-- **The Poisson kernel reproduces the digamma line.**  Pairing the unit-mass Poisson kernel of
height `a` with the archimedean rate on the line `c + i x / 2` returns the rate at the interior
point `c + a / 2`. -/
theorem integral_poissonWeight_mul_re_digamma_add_euler {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (∫ x : ℝ, poissonWeight a x
        * ((Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re
            + Real.eulerMascheroniConstant))
      = (Complex.digamma (((c + a / 2 : ℝ)) : ℂ)).re + Real.eulerMascheroniConstant := by
  have hc2 : (0 : ℝ) < c + a / 2 := by linarith
  have hkey := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun n : ℕ => fun x : ℝ => poissonWeight a x * digammaHalfTerm c n x)
    (fun n => integrable_poissonWeight_mul_digammaHalfTerm ha hc n)
    (summable_integral_norm_poissonWeight_digammaHalf ha hc)
  have hshift : ((c + a / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = ((c + a / 2 : ℝ) : ℂ) := by
    simp
  have hterm : ∀ n : ℕ, (∫ x : ℝ, poissonWeight a x * digammaHalfTerm c n x)
      = (gaussDigammaSeriesTerm (((c + a / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) n).re := by
    intro n
    rw [integral_poissonWeight_mul_digammaHalfTerm ha hc n,
      re_gaussDigammaSeriesTerm_realPoint hc2 n]
  have hL : (∑' n : ℕ, ∫ x : ℝ, poissonWeight a x * digammaHalfTerm c n x)
      = (Complex.digamma (((c + a / 2 : ℝ)) : ℂ)).re + Real.eulerMascheroniConstant := by
    rw [tsum_congr hterm]
    have h := re_digamma_vertical_eq hc2 0
    simp only [hshift] at h ⊢
    linarith [h]
  have hR : (∫ x : ℝ, ∑' n : ℕ, poissonWeight a x * digammaHalfTerm c n x)
      = ∫ x : ℝ, poissonWeight a x
          * ((Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re
              + Real.eulerMascheroniConstant) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (∑' n : ℕ, poissonWeight a x * digammaHalfTerm c n x)
        = poissonWeight a x * ((Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re
            + Real.eulerMascheroniConstant)
    rw [tsum_mul_left, tsum_digammaHalfTerm hc x]
  rw [← hR, ← hkey, hL]


/-! ## The reproducing identity without the Euler shift -/

theorem continuous_re_digamma_half {c : ℝ} (hc : 0 < c) :
    Continuous fun x : ℝ => (Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re := by
  have hmem : ∀ x : ℝ, ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I) ∈ {z : ℂ | 0 < z.re} := by
    intro x
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact hc
  have hcomp : Continuous fun x : ℝ => Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I) :=
    continuousOn_digamma_rePos.comp_continuous (by fun_prop) hmem
  exact Complex.continuous_re.comp hcomp

theorem integrable_poissonWeight_mul_re_digamma_half {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Integrable fun x : ℝ =>
      poissonWeight a x * (Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re := by
  have hK : 0 ≤ digammaVerticalGrowthConst c := digammaVerticalGrowthConst_nonneg hc
  have hmaj : Integrable fun x : ℝ =>
      (a / Real.pi) * (digammaVerticalGrowthConst c * (a ^ 2 + x ^ 2)⁻¹
        + Real.log (2 + |x|) * (a ^ 2 + x ^ 2)⁻¹) :=
    (((integrable_inv_sq_add_sq ha).const_mul (digammaVerticalGrowthConst c)).add
      (integrable_log_mul_inv_sq_add_sq ha)).const_mul _
  refine hmaj.mono' ?_ ?_
  · exact ((integrable_poissonWeight ha).aestronglyMeasurable).mul
      (continuous_re_digamma_half hc).aestronglyMeasurable
  filter_upwards with x
  have hP : 0 ≤ poissonWeight a x := poissonWeight_nonneg ha x
  have hbound := abs_re_digamma_vertical_le hc (x / 2)
  have hhalf : |x / 2| ≤ |x| := by
    rw [abs_div]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    have h0 : 0 ≤ |x| := abs_nonneg x
    linarith
  have hmono : Real.log (2 + |x / 2|) ≤ Real.log (2 + |x|) := by
    refine Real.log_le_log (by positivity) ?_
    linarith
  have hstep : |(Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re|
      ≤ digammaVerticalGrowthConst c + Real.log (2 + |x|) := by
    have : |(Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re|
        ≤ digammaVerticalGrowthConst c + Real.log (2 + |x / 2|) := hbound
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP, poissonWeight_eq]
  have hinvpos : (0 : ℝ) < (a ^ 2 + x ^ 2)⁻¹ := by positivity
  have hapi : (0 : ℝ) < a / Real.pi := by
    have := Real.pi_pos
    positivity
  calc (a / Real.pi) * (a ^ 2 + x ^ 2)⁻¹
        * |(Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re|
      ≤ (a / Real.pi) * (a ^ 2 + x ^ 2)⁻¹
          * (digammaVerticalGrowthConst c + Real.log (2 + |x|)) := by
        refine mul_le_mul_of_nonneg_left hstep ?_
        positivity
    _ = (a / Real.pi) * (digammaVerticalGrowthConst c * (a ^ 2 + x ^ 2)⁻¹
          + Real.log (2 + |x|) * (a ^ 2 + x ^ 2)⁻¹) := by ring

/-- **The Poisson reproducing identity for the archimedean rate.** -/
theorem integral_poissonWeight_mul_re_digamma_half {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (∫ x : ℝ, poissonWeight a x
        * (Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re)
      = (Complex.digamma (((c + a / 2 : ℝ)) : ℂ)).re := by
  have hkey := integral_poissonWeight_mul_re_digamma_add_euler ha hc
  have hsplit : ∀ x : ℝ, poissonWeight a x
      * ((Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re
          + Real.eulerMascheroniConstant)
      = poissonWeight a x * (Complex.digamma ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I)).re
        + Real.eulerMascheroniConstant * poissonWeight a x := by
    intro x
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
    MeasureTheory.integral_add (integrable_poissonWeight_mul_re_digamma_half ha hc)
      ((integrable_poissonWeight ha).const_mul _),
    MeasureTheory.integral_const_mul, integral_poissonWeight ha, mul_one] at hkey
  linarith [hkey]

end RHTower

end
