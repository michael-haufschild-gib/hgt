import GaloisForLFunctions.RHTower.CCM.CCMFirstClockLandauTransform

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- A strip-uniform bound for the removable compact first-clock kernel. -/
theorem norm_ccmFirstClockFixedCompactKernel_le
    {x : ℂ} (him : |x.im| ≤ Real.pi / 4) :
    ‖ccmFirstClockFixedCompactKernel x‖ ≤
      ‖-(1 / (2 * (Real.pi : ℂ)))‖ * Real.exp (Real.pi / 4) := by
  by_cases hden : x ^ (2 : ℕ) = (2 * (Real.pi : ℂ)) ^ (2 : ℕ)
  · unfold ccmFirstClockFixedCompactKernel
    rw [hden, sub_self, div_zero, norm_zero]
    positivity
  · rw [ccmFirstClockFixedCompactKernel_eq_cosineIntegral hden]
    rw [norm_mul]
    gcongr
    have hpoint (u : ℝ) (hu : u ∈ Set.uIoc (0 : ℝ) 1) :
        ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
            Complex.cos (x * (u : ℂ))‖ ≤
          Real.exp (Real.pi / 4) := by
      have huIoc : u ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hu
      have hu' : u ∈ Set.Icc (0 : ℝ) 1 := ⟨huIoc.1.le, huIoc.2⟩
      have hsin :
          ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ))‖ ≤ 1 := by
        rw [show (2 * (Real.pi : ℂ)) * (u : ℂ) =
            ((2 * Real.pi * u : ℝ) : ℂ) by
          push_cast
          ring]
        rw [← Complex.ofReal_sin, norm_real, Real.norm_eq_abs]
        exact Real.abs_sin_le_one _
      have hcos :
          ‖Complex.cos (x * (u : ℂ))‖ ≤ Real.exp (|x.im|) := by
        simpa using norm_cos_real_mul_le_exp_abs_im x
          (L := (1 : ℝ)) (u := u) (by norm_num) hu'
      rw [norm_mul]
      calc
        ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ))‖ *
            ‖Complex.cos (x * (u : ℂ))‖ ≤
          1 * Real.exp (|x.im|) := by gcongr
        _ ≤ Real.exp (Real.pi / 4) := by
          simpa using Real.exp_le_exp.mpr him
    simpa using
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint

/-- Away from its two removable points, the fixed kernel has exact reciprocal-square decay. -/
theorem norm_ccmFirstClockFixedCompactKernel_le_div_sq
    {x : ℂ} (him : |x.im| ≤ Real.pi / 4)
    (hfar : 2 * ‖2 * (Real.pi : ℂ)‖ ≤ ‖x‖) :
    ‖ccmFirstClockFixedCompactKernel x‖ ≤
      ((4 : ℝ) / 3) * (1 + Real.exp (Real.pi / 4)) / ‖x‖ ^ (2 : ℕ) := by
  let a : ℂ := 2 * (Real.pi : ℂ)
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha : 0 < ‖a‖ := by
    apply norm_pos_iff.mpr
    dsimp only [a]
    exact mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hpi))
  have hx : 0 < ‖x‖ :=
    lt_of_lt_of_le (mul_pos (by norm_num) ha) hfar
  have hquarter : ‖a‖ ^ (2 : ℕ) ≤ (1 / 4 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (‖x‖ - 2 * ‖a‖)]
  have hdenLower :
      (3 / 4 : ℝ) * ‖x‖ ^ (2 : ℕ) ≤ ‖x ^ (2 : ℕ) - a ^ (2 : ℕ)‖ := by
    have htri := norm_sub_norm_le (x ^ (2 : ℕ)) (a ^ (2 : ℕ))
    rw [norm_pow, norm_pow] at htri
    nlinarith
  have hcos :
      ‖Complex.cos x‖ ≤ Real.exp (Real.pi / 4) := by
    have h := norm_cos_real_mul_le_exp_abs_im x
      (L := (1 : ℝ)) (u := (1 : ℝ)) (by norm_num)
      (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
    have him' : |x.im| * 1 ≤ Real.pi / 4 := by simpa using him
    simpa using h.trans (Real.exp_le_exp.mpr him')
  have hnum :
      ‖1 - Complex.cos x‖ ≤ 1 + Real.exp (Real.pi / 4) := by
    calc
      ‖1 - Complex.cos x‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.cos x‖ :=
        norm_sub_le _ _
      _ ≤ 1 + Real.exp (Real.pi / 4) := by
        simpa using add_le_add_left hcos 1
  unfold ccmFirstClockFixedCompactKernel
  dsimp only [a] at hdenLower ⊢
  rw [norm_div]
  apply (div_le_div_iff₀ (by
    exact lt_of_lt_of_le (mul_pos (by norm_num) (sq_pos_of_pos hx))
      hdenLower) (sq_pos_of_pos hx)).2
  calc
    ‖1 - Complex.cos x‖ * ‖x‖ ^ (2 : ℕ) ≤
        (1 + Real.exp (Real.pi / 4)) * ‖x‖ ^ (2 : ℕ) := by
      gcongr
    _ ≤ (((4 : ℝ) / 3) * (1 + Real.exp (Real.pi / 4))) *
        ‖x ^ (2 : ℕ) - (2 * (Real.pi : ℂ)) ^ (2 : ℕ)‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hdenLower
        (show 0 ≤ (4 / 3 : ℝ) * (1 + Real.exp (Real.pi / 4)) by positivity)]

/-- Universal constant controlling every first-clock atom on the compact physical head. -/
def ccmFirstClockHeadReciprocalSquareConstant : ℝ :=
  (2 * ‖2 * (Real.pi : ℂ)‖) ^ (2 : ℕ) *
      (‖-(1 / (2 * (Real.pi : ℂ)))‖ *
        Real.exp (Real.pi / 4)) +
    ((4 : ℝ) / 3) * (1 + Real.exp (Real.pi / 4))

theorem ccmFirstClockHeadReciprocalSquareConstant_nonneg :
    0 ≤ ccmFirstClockHeadReciprocalSquareConstant := by
  unfold ccmFirstClockHeadReciprocalSquareConstant
  positivity

/-- **Compact-head reciprocal-square law.**  Endpoint cancellation controls every aperture
from zero through the physical first-clock threshold, including the two removable resonance
points.  This is the missing uniform estimate needed to sum the literal infinite divisor. -/
theorem norm_ccmFirstClockRationalKernel_xiSpectralPoint_le_head
    {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ Real.pi / 2)
    (q : XiZeroCopy) :
    ‖ccmFirstClockRationalKernel L (xiSpectralPoint q)‖ ≤
      ccmFirstClockHeadReciprocalSquareConstant /
        ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  by_cases hLzero : L = 0
  · subst L
    rw [show ccmFirstClockRationalKernel 0 (xiSpectralPoint q) = 0 by
      simp [ccmFirstClockRationalKernel]]
    rw [norm_zero]
    exact div_nonneg ccmFirstClockHeadReciprocalSquareConstant_nonneg
      (sq_nonneg ‖xiSpectralPoint q‖)
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hLzero)
  let z : ℂ := xiSpectralPoint q
  let x : ℂ := (L : ℂ) * z
  let B : ℝ := 2 * ‖2 * (Real.pi : ℂ)‖
  let C₀ : ℝ :=
    ‖-(1 / (2 * (Real.pi : ℂ)))‖ * Real.exp (Real.pi / 4)
  let Cfar : ℝ := ((4 : ℝ) / 3) * (1 + Real.exp (Real.pi / 4))
  have hz : z ≠ 0 := xiSpectralPoint_ne_zero q
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hCfar : 0 ≤ Cfar := by dsimp only [Cfar]; positivity
  have hstrip : |z.im| < 1 / 2 := by
    dsimp only [z]
    rw [abs_lt]
    constructor <;> linarith [xiSpectralPoint_im_mem_openHalf q]
  have hxim : |x.im| ≤ Real.pi / 4 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have him : x.im = L * z.im := by
      dsimp only [x]
      simp [mul_im]
    rw [him, abs_mul, abs_of_nonneg hL0]
    nlinarith [abs_nonneg z.im]
  have hxNorm : ‖x‖ = L * ‖z‖ := by
    dsimp only [x]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  rw [ccmFirstClockRationalKernel_eq_dilation hLzero z]
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  by_cases hfar : B ≤ ‖x‖
  · have hdecay :
        ‖ccmFirstClockFixedCompactKernel x‖ ≤ Cfar / ‖x‖ ^ (2 : ℕ) := by
      apply norm_ccmFirstClockFixedCompactKernel_le_div_sq hxim
      simpa only [B] using hfar
    calc
      L ^ (2 : ℕ) * ‖ccmFirstClockFixedCompactKernel x‖ ≤
          L ^ (2 : ℕ) * (Cfar / ‖x‖ ^ (2 : ℕ)) := by
        gcongr
      _ = Cfar / ‖z‖ ^ (2 : ℕ) := by
        rw [hxNorm]
        field_simp [hLzero, ne_of_gt hzNorm]
      _ ≤ ccmFirstClockHeadReciprocalSquareConstant / ‖z‖ ^ (2 : ℕ) := by
        change Cfar / ‖z‖ ^ (2 : ℕ) ≤
          (B ^ (2 : ℕ) * C₀ + Cfar) / ‖z‖ ^ (2 : ℕ)
        apply div_le_div_of_nonneg_right _ (sq_nonneg ‖z‖)
        exact le_add_of_nonneg_left (mul_nonneg (sq_nonneg B) (by
          dsimp only [C₀]
          positivity))
  · have hnear : ‖x‖ < B := lt_of_not_ge hfar
    have hfixed :
        ‖ccmFirstClockFixedCompactKernel x‖ ≤ C₀ := by
      simpa only [C₀] using norm_ccmFirstClockFixedCompactKernel_le hxim
    have hB0 : 0 ≤ B := by dsimp only [B]; positivity
    have hC0 : 0 ≤ C₀ := by dsimp only [C₀]; positivity
    apply (le_div_iff₀ (sq_pos_of_pos hzNorm)).2
    calc
      L ^ (2 : ℕ) * ‖ccmFirstClockFixedCompactKernel x‖ * ‖z‖ ^ (2 : ℕ) ≤
          L ^ (2 : ℕ) * C₀ * ‖z‖ ^ (2 : ℕ) := by
        gcongr
      _ = (L * ‖z‖) ^ (2 : ℕ) * C₀ := by ring
      _ ≤ B ^ (2 : ℕ) * C₀ := by
        gcongr
        rw [← hxNorm]
        exact hnear.le
      _ ≤ ccmFirstClockHeadReciprocalSquareConstant := by
        change B ^ (2 : ℕ) * C₀ ≤ B ^ (2 : ℕ) * C₀ + Cfar
        exact le_add_of_nonneg_right hCfar

end

end RHTower
