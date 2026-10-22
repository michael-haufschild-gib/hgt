import GaloisForLFunctions.RHTower.XiResolventMassBudget
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Heat traces centered at an arbitrary zero ordinate

The translated Gaussian is summable without a spectral separation assumption. Reciprocal-square
mass bounds its value at time one and its exterior tail at every later time. The translation
cost is polynomial in the center, which permits quantitative compact detection.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- One translated heat atom of the multiplicity-exact Xi divisor. -/
def xiCenteredHeatTerm (c t : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp (-(t : ℂ) * (xiSpectralPoint q - c) ^ 2)

/-- The heat trace centered at height `c`. -/
def xiCenteredHeatTrace (c t : ℝ) : ℂ := ∑' q, xiCenteredHeatTerm c t q

/-- The real part of the centered heat trace. -/
def xiCenteredHeatTraceReal (c t : ℝ) : ℝ := (xiCenteredHeatTrace c t).re

/-- A bound for the trace at time one and for the exterior tail at later times. -/
def xiCenteredHeatBaseBound (c : ℝ) : ℝ := 6 * (1 + c ^ 2)

theorem xiCenteredHeatBaseBound_pos (c : ℝ) : 0 < xiCenteredHeatBaseBound c := by
  unfold xiCenteredHeatBaseBound
  positivity

theorem norm_xiCenteredHeatTerm (c t : ℝ) (q : XiZeroCopy) :
    ‖xiCenteredHeatTerm c t q‖ =
      Real.exp (t * ((xiSpectralPoint q).im ^ 2 - ((xiSpectralPoint q).re - c) ^ 2)) := by
  rw [xiCenteredHeatTerm, Complex.norm_exp]
  congr 1
  simp [pow_two]
  ring

theorem re_xiCenteredHeatTerm (c t : ℝ) (q : XiZeroCopy) :
    (xiCenteredHeatTerm c t q).re =
      Real.exp (t * ((xiSpectralPoint q).im ^ 2 - ((xiSpectralPoint q).re - c) ^ 2)) *
        Real.cos (-2 * t * ((xiSpectralPoint q).re - c) * (xiSpectralPoint q).im) := by
  rw [xiCenteredHeatTerm, Complex.exp_re]
  congr 1 <;> congr 1 <;> simp [pow_two] <;> ring

theorem xiCenteredHeat_reciprocal_mass_lt_one :
    (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) < 1 := by
  have h := tsum_norm_xiResolventPoint_le_budget (X := 0) (by positivity)
  simp only [xiResolventPoint, Complex.ofReal_zero, add_zero, norm_inv, norm_pow] at h
  simp only [one_div]
  linarith

private theorem mul_exp_neg_le_one (x : ℝ) :
    x * Real.exp (-x) ≤ 1 := by
  have h : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  exact hm

private theorem exp_quarter_le_two : Real.exp (1 / 4 : ℝ) ≤ 2 := by
  by_contra h
  have htwo : 2 ≤ Real.exp (1 / 4 : ℝ) := (lt_of_not_ge h).le
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 4
  have he : Real.exp (1 / 4 : ℝ) ^ 4 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he] at hp
  have hbound := Real.exp_one_lt_d9
  norm_num at hp
  linarith

/-- A centered Gaussian still pays for reciprocal-square mass at polynomial cost. -/
theorem xiCenteredHeat_weighted_gaussian_le (c : ℝ) (q : XiZeroCopy) :
    ‖xiSpectralPoint q‖ ^ 2 * Real.exp (-((xiSpectralPoint q).re - c) ^ 2) ≤
      3 * (1 + c ^ 2) := by
  set r : ℝ := (xiSpectralPoint q).re - c with hr
  have hz : ‖xiSpectralPoint q‖ ^ 2 ≤ 2 * r ^ 2 + 2 * c ^ 2 + 1 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hr]
    nlinarith [xiSpectralPoint_im_sq_lt_quarter q,
      sq_nonneg ((xiSpectralPoint q).re - 2 * c)]
  have hsmall : Real.exp (-r ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hmoment : r ^ 2 * Real.exp (-r ^ 2) ≤ 1 := mul_exp_neg_le_one (r ^ 2)
  calc
    ‖xiSpectralPoint q‖ ^ 2 * Real.exp (-r ^ 2)
        ≤ (2 * r ^ 2 + 2 * c ^ 2 + 1 / 4) * Real.exp (-r ^ 2) := by gcongr
    _ = 2 * (r ^ 2 * Real.exp (-r ^ 2)) +
        (2 * c ^ 2 + 1 / 4) * Real.exp (-r ^ 2) := by ring
    _ ≤ 2 * 1 + (2 * c ^ 2 + 1 / 4) * 1 := by gcongr
    _ ≤ 3 * (1 + c ^ 2) := by nlinarith [sq_nonneg c]

/-- The half-strip controls the growth, while height distance gives Gaussian decay. -/
theorem norm_xiCenteredHeatTerm_le_gaussian {t : ℝ} (ht : 1 ≤ t) (c : ℝ) (q : XiZeroCopy) :
    ‖xiCenteredHeatTerm c t q‖ ≤
      Real.exp (t / 4) * Real.exp (-((xiSpectralPoint q).re - c) ^ 2) := by
  set r : ℝ := (xiSpectralPoint q).re - c with hr
  have ht0 : 0 ≤ t := by linarith
  have hstrip := mul_le_mul_of_nonneg_left (xiSpectralPoint_im_sq_lt_quarter q).le ht0
  rw [norm_xiCenteredHeatTerm, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change t * ((xiSpectralPoint q).im ^ 2 - r ^ 2) ≤ t / 4 + -r ^ 2
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg r)]

/-- Summable domination for every time at least one. -/
theorem norm_xiCenteredHeatTerm_le {t : ℝ} (ht : 1 ≤ t) (c : ℝ) (q : XiZeroCopy) :
    ‖xiCenteredHeatTerm c t q‖ ≤
      (3 * (1 + c ^ 2) * Real.exp (t / 4)) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  set r : ℝ := (xiSpectralPoint q).re - c with hr
  have hgauss := norm_xiCenteredHeatTerm_le_gaussian ht c q
  have hweighted := xiCenteredHeat_weighted_gaussian_le c q
  have hprod : ‖xiSpectralPoint q‖ ^ 2 * ‖xiCenteredHeatTerm c t q‖ ≤
      3 * (1 + c ^ 2) * Real.exp (t / 4) := by
    calc
      ‖xiSpectralPoint q‖ ^ 2 * ‖xiCenteredHeatTerm c t q‖
          ≤ ‖xiSpectralPoint q‖ ^ 2 * (Real.exp (t / 4) * Real.exp (-r ^ 2)) := by gcongr
      _ = (‖xiSpectralPoint q‖ ^ 2 * Real.exp (-r ^ 2)) * Real.exp (t / 4) := by ring
      _ ≤ 3 * (1 + c ^ 2) * Real.exp (t / 4) := by gcongr
  have hz : 0 < ‖xiSpectralPoint q‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))
  rw [mul_one_div, le_div_iff₀ hz]
  simpa only [mul_comm] using hprod

theorem summable_xiCenteredHeatTerm {t : ℝ} (ht : 1 ≤ t) (c : ℝ) :
    Summable (xiCenteredHeatTerm c t) :=
  Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left _)
    (norm_xiCenteredHeatTerm_le ht c)

theorem norm_xiCenteredHeatTerm_one_le (c : ℝ) (q : XiZeroCopy) :
    ‖xiCenteredHeatTerm c 1 q‖ ≤
      xiCenteredHeatBaseBound c * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  refine (norm_xiCenteredHeatTerm_le (t := 1) le_rfl c q).trans ?_
  unfold xiCenteredHeatBaseBound
  have h := exp_quarter_le_two
  calc
    3 * (1 + c ^ 2) * Real.exp (1 / 4) * (1 / ‖xiSpectralPoint q‖ ^ 2)
        ≤ 3 * (1 + c ^ 2) * 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by gcongr
    _ = _ := by ring

theorem tsum_norm_xiCenteredHeatTerm_one_le (c : ℝ) :
    (∑' q, ‖xiCenteredHeatTerm c 1 q‖) ≤ xiCenteredHeatBaseBound c := by
  have hsum := (summable_xiCenteredHeatTerm (t := 1) le_rfl c).norm.tsum_le_tsum
    (norm_xiCenteredHeatTerm_one_le c)
    (xiSpectralPoint_inv_sq_summable.mul_left (xiCenteredHeatBaseBound c))
  rw [tsum_mul_left] at hsum
  have hB := xiCenteredHeatBaseBound_pos c
  nlinarith [xiCenteredHeat_reciprocal_mass_lt_one]

theorem norm_xiCenteredHeatTrace_one_le (c : ℝ) :
    ‖xiCenteredHeatTrace c 1‖ ≤ xiCenteredHeatBaseBound c :=
  (norm_tsum_le_tsum_norm (summable_xiCenteredHeatTerm (t := 1) le_rfl c).norm).trans
    (tsum_norm_xiCenteredHeatTerm_one_le c)

private theorem one_add_sq_mul_exp_neg_le_five {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ 2 * Real.exp (-x) ≤ 5 := by
  have h1 := mul_exp_neg_le_one x
  have h2raw := Real.pow_div_factorial_le_exp x hx 2
  norm_num at h2raw
  have hm := mul_le_mul_of_nonneg_right h2raw (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

/-- The first heat derivative has a summable reciprocal-square majorant. -/
theorem norm_xiCenteredHeatMomentTerm_le {t : ℝ} (ht : 1 ≤ t) (c : ℝ) (q : XiZeroCopy) :
    ‖(xiSpectralPoint q - c) ^ 2 * xiCenteredHeatTerm c t q‖ ≤
      (15 * (1 + c ^ 2) * Real.exp (t / 4)) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  set r : ℝ := (xiSpectralPoint q).re - c with hr
  have hz : ‖xiSpectralPoint q‖ ^ 2 ≤ 3 * (1 + c ^ 2) * (1 + r ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hr]
    nlinarith [xiSpectralPoint_im_sq_lt_quarter q,
      sq_nonneg ((xiSpectralPoint q).re - 2 * c),
      mul_nonneg (sq_nonneg c) (sq_nonneg ((xiSpectralPoint q).re - c))]
  have hw : ‖xiSpectralPoint q - c‖ ^ 2 ≤ 1 + r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    change r * r + (xiSpectralPoint q).im * (xiSpectralPoint q).im ≤ 1 + r ^ 2
    nlinarith [xiSpectralPoint_im_sq_lt_quarter q]
  have hprod : ‖xiSpectralPoint q‖ ^ 2 * ‖xiSpectralPoint q - c‖ ^ 2 ≤
      3 * (1 + c ^ 2) * (1 + r ^ 2) ^ 2 := by
    calc
      ‖xiSpectralPoint q‖ ^ 2 * ‖xiSpectralPoint q - c‖ ^ 2
          ≤ (3 * (1 + c ^ 2) * (1 + r ^ 2)) * (1 + r ^ 2) := by gcongr
      _ = _ := by ring
  have hg := norm_xiCenteredHeatTerm_le_gaussian ht c q
  have hm := one_add_sq_mul_exp_neg_le_five (sq_nonneg r)
  have hweighted : ‖xiSpectralPoint q‖ ^ 2 *
      ‖(xiSpectralPoint q - c) ^ 2 * xiCenteredHeatTerm c t q‖ ≤
        15 * (1 + c ^ 2) * Real.exp (t / 4) := by
    rw [norm_mul, norm_pow]
    calc
      ‖xiSpectralPoint q‖ ^ 2 * (‖xiSpectralPoint q - c‖ ^ 2 * ‖xiCenteredHeatTerm c t q‖)
          ≤ (‖xiSpectralPoint q‖ ^ 2 * ‖xiSpectralPoint q - c‖ ^ 2) *
            (Real.exp (t / 4) * Real.exp (-r ^ 2)) := by
              rw [mul_assoc]
              gcongr
      _ ≤ (3 * (1 + c ^ 2) * (1 + r ^ 2) ^ 2) *
            (Real.exp (t / 4) * Real.exp (-r ^ 2)) := by gcongr
      _ = 3 * (1 + c ^ 2) * ((1 + r ^ 2) ^ 2 * Real.exp (-r ^ 2)) * Real.exp (t / 4) := by ring
      _ ≤ 3 * (1 + c ^ 2) * 5 * Real.exp (t / 4) := by gcongr
      _ = _ := by ring
  have hpos : 0 < ‖xiSpectralPoint q‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))
  rw [mul_one_div, le_div_iff₀ hpos]
  simpa only [mul_comm] using hweighted

theorem summable_xiCenteredHeatMomentTerm {t : ℝ} (ht : 1 ≤ t) (c : ℝ) :
    Summable (fun q => (xiSpectralPoint q - c) ^ 2 * xiCenteredHeatTerm c t q) :=
  Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left _)
    (norm_xiCenteredHeatMomentTerm_le ht c)

/-- Outside the unit height window the heat atoms only decrease in modulus. -/
theorem norm_xiCenteredHeatTerm_le_one_of_far {t c : ℝ} (ht : 1 ≤ t)
    (q : XiZeroCopy) (hfar : 1 ≤ |(xiSpectralPoint q).re - c|) :
    ‖xiCenteredHeatTerm c t q‖ ≤ ‖xiCenteredHeatTerm c 1 q‖ := by
  rw [norm_xiCenteredHeatTerm, norm_xiCenteredHeatTerm]
  apply Real.exp_le_exp.mpr
  have hr : 1 ≤ ((xiSpectralPoint q).re - c) ^ 2 := by
    nlinarith [sq_abs ((xiSpectralPoint q).re - c)]
  have hs := xiSpectralPoint_im_sq_lt_quarter q
  have hd : 0 ≤ ((xiSpectralPoint q).re - c) ^ 2 - (xiSpectralPoint q).im ^ 2 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) hd]

end

end RHTower
