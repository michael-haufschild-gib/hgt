import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureWardGreenPlancherelFracture
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureHolomorphicSectorCoercivity
import GaloisForLFunctions.RHTower.LegStripSteepness

/-!
# Removable Ward--Green extension and critical-line kernel projection

The inverse-square Ward scalar is not genuinely singular.  Every reflection-pair defect has a
canonical continuous extension through transverse displacement zero.  Lean's totalized inverse
sets precisely that missing quadratic jet to zero.  This module identifies the resulting defect as
one explicit critical-line projection.

This is an exact source/diagonal separation theorem.  It does not supply the still-open arithmetic
upper budget required for a zero-density conclusion.
-/

open Complex MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-! ## Canonical removable exponential-pair quotient -/

/-- Real hyperbolic sinc with its canonical removable value at zero. -/
def wardRemovableSinhc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / x

@[simp] theorem wardRemovableSinhc_zero : wardRemovableSinhc 0 = 1 := by
  simp [wardRemovableSinhc]

theorem wardRemovableSinhc_eq (hx : x ≠ 0) :
    wardRemovableSinhc x = Real.sinh x / x := by
  simp [wardRemovableSinhc, hx]

/-- The definition above is a genuine removable extension, continuous at the puncture. -/
theorem continuousAt_wardRemovableSinhc_zero :
    ContinuousAt wardRemovableSinhc 0 := by
  have htend : Tendsto wardRemovableSinhc (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    apply tendsto_sinh_div.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (wardRemovableSinhc_eq (by simpa using hx)).symm
  have hdecomp : (𝓝 (0 : ℝ)) = 𝓝[≠] (0 : ℝ) ⊔ pure (0 : ℝ) := by
    rw [← nhdsWithin_singleton (0 : ℝ), ← nhdsWithin_union,
      Set.compl_union_self, nhdsWithin_univ]
  rw [ContinuousAt, wardRemovableSinhc_zero, hdecomp, tendsto_sup]
  exact ⟨htend, by simpa using tendsto_pure_nhds wardRemovableSinhc 0⟩

/-- Continuous extension of `a⁻² (exp(2ka)+exp(-2ka)-2)`. -/
def wardRemovableExpPairQuotient (k a : ℝ) : ℝ :=
  4 * k ^ 2 * wardRemovableSinhc (k * a) ^ 2

@[simp] theorem wardRemovableExpPairQuotient_zero (k : ℝ) :
    wardRemovableExpPairQuotient k 0 = 4 * k ^ 2 := by
  simp [wardRemovableExpPairQuotient]

theorem continuousAt_wardRemovableExpPairQuotient_zero (k : ℝ) :
    ContinuousAt (wardRemovableExpPairQuotient k) 0 := by
  have harg : ContinuousAt (fun a : ℝ => k * a) 0 :=
    continuousAt_const.mul continuousAt_id
  have hsinc : ContinuousAt (fun a : ℝ => wardRemovableSinhc (k * a)) 0 := by
    have hcomp := continuousAt_wardRemovableSinhc_zero.comp_of_eq harg (by simp)
    simpa [Function.comp_def] using hcomp
  exact (hsinc.pow 2).const_mul (4 * k ^ 2)

/-- Off the puncture, the removable quotient is exactly the totalized inverse-square defect. -/
theorem invSq_expPairDefect_eq_wardRemovable
    {k a : ℝ} (ha : a ≠ 0) :
    a⁻¹ ^ 2 *
        (Real.exp (2 * k * a) + Real.exp (-2 * k * a) - 2) =
      wardRemovableExpPairQuotient k a := by
  by_cases hk : k = 0
  · subst k
    norm_num [wardRemovableExpPairQuotient]
  · rw [show 2 * k * a = 2 * (k * a) by ring,
      show -2 * k * a = -2 * (k * a) by ring,
      fiveShift_exp_pair_defect_eq_four_sinh_sq]
    rw [wardRemovableExpPairQuotient, wardRemovableSinhc_eq (mul_ne_zero hk ha)]
    field_simp [ha, hk]

/-! ## Five-shift removable scalar -/

def fiveShiftWardCoefficientOne : ℝ :=
  Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) * Real.exp (-(21 / 10 : ℝ))

def fiveShiftWardCoefficientTwo : ℝ :=
  Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) +
    Real.exp (-(6 / 5 : ℝ)) * Real.exp (-(21 / 10 : ℝ)) +
    Real.exp (-2) * Real.exp (-(21 / 10 : ℝ)) +
    Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) * Real.exp (-(21 / 10 : ℝ))

def fiveShiftWardCoefficientThree : ℝ :=
  Real.exp (-(6 / 5 : ℝ)) + Real.exp (-2) + Real.exp (-(21 / 10 : ℝ)) +
    Real.exp (-(6 / 5 : ℝ)) * Real.exp (-2) +
    Real.exp (-(6 / 5 : ℝ)) * Real.exp (-(21 / 10 : ℝ)) +
    Real.exp (-2) * Real.exp (-(21 / 10 : ℝ))

def fiveShiftWardCoefficientFour : ℝ :=
  1 + Real.exp (-(6 / 5 : ℝ)) + Real.exp (-2) + Real.exp (-(21 / 10 : ℝ))

/-- Continuous source-side extension of the inverse-square five-shift scalar at scale one. -/
def fiveShiftWardRemovableSourceScalar (a : ℝ) : ℝ :=
  fiveShiftWardCoefficientOne * wardRemovableExpPairQuotient 1 a -
    fiveShiftWardCoefficientTwo * wardRemovableExpPairQuotient 2 a +
    fiveShiftWardCoefficientThree * wardRemovableExpPairQuotient 3 a -
    fiveShiftWardCoefficientFour * wardRemovableExpPairQuotient 4 a +
    wardRemovableExpPairQuotient 5 a

/-- Missing quadratic jet at the Ward kernel. -/
def fiveShiftWardKernelJump : ℝ :=
  4 * (fiveShiftWardCoefficientOne * 1 ^ 2 -
    fiveShiftWardCoefficientTwo * 2 ^ 2 +
    fiveShiftWardCoefficientThree * 3 ^ 2 -
    fiveShiftWardCoefficientFour * 4 ^ 2 + 5 ^ 2)

@[simp] theorem fiveShiftWardRemovableSourceScalar_zero :
    fiveShiftWardRemovableSourceScalar 0 = fiveShiftWardKernelJump := by
  simp [fiveShiftWardRemovableSourceScalar, fiveShiftWardKernelJump]
  ring

theorem continuousAt_fiveShiftWardRemovableSourceScalar_zero :
    ContinuousAt fiveShiftWardRemovableSourceScalar 0 := by
  unfold fiveShiftWardRemovableSourceScalar
  exact
    ((((continuousAt_wardRemovableExpPairQuotient_zero 1).const_mul
          fiveShiftWardCoefficientOne).sub
        ((continuousAt_wardRemovableExpPairQuotient_zero 2).const_mul
          fiveShiftWardCoefficientTwo)).add
      ((continuousAt_wardRemovableExpPairQuotient_zero 3).const_mul
        fiveShiftWardCoefficientThree)).sub
    ((continuousAt_wardRemovableExpPairQuotient_zero 4).const_mul
      fiveShiftWardCoefficientFour) |>.add
        (continuousAt_wardRemovableExpPairQuotient_zero 5)

/-- Unnormalized five-shift combination written entirely as reflection-pair exponential defects. -/
def fiveShiftWardExpPairDefectCombination (a : ℝ) : ℝ :=
  let D (k : ℝ) := Real.exp (2 * k * a) + Real.exp (-2 * k * a) - 2
  fiveShiftWardCoefficientOne * D 1 - fiveShiftWardCoefficientTwo * D 2 +
    fiveShiftWardCoefficientThree * D 3 - fiveShiftWardCoefficientFour * D 4 + D 5

/-- The exponential-defect presentation is exactly the functional-equation-paired feature. -/
theorem fiveShiftWardExpPairDefectCombination_eq_pairedFeature (a : ℝ) :
    fiveShiftWardExpPairDefectCombination a =
      fiveShiftEulerGammaPairedFeature 1 a := by
  unfold fiveShiftWardExpPairDefectCombination
  dsimp only
  rw [fiveShiftEulerGammaPairedFeature,
    fiveShiftEulerGammaFeature, fiveShiftEulerGammaFeature,
    fiveShiftEulerGammaPolynomial_eq_coefficients,
    fiveShiftEulerGammaPolynomial_eq_coefficients]
  norm_num only [one_mul, mul_one]
  unfold fiveShiftWardCoefficientOne fiveShiftWardCoefficientTwo
    fiveShiftWardCoefficientThree fiveShiftWardCoefficientFour
  have hp2 : Real.exp (a * 4) = Real.exp (a * 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1 <;> ring
  have hp3 : Real.exp (a * 6) = Real.exp (a * 2) ^ 3 := by
    rw [← Real.exp_nat_mul]
    congr 1 <;> ring
  have hp4 : Real.exp (a * 8) = Real.exp (a * 2) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1 <;> ring
  have hp5 : Real.exp (a * 10) = Real.exp (a * 2) ^ 5 := by
    rw [← Real.exp_nat_mul]
    congr 1 <;> ring
  have hn2 : Real.exp (-(a * 4)) = Real.exp (-(a * 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1 <;> ring
  have hn3 : Real.exp (-(a * 6)) = Real.exp (-(a * 2)) ^ 3 := by
    rw [← Real.exp_nat_mul]
    congr 1 <;> ring
  have hn4 : Real.exp (-(a * 8)) = Real.exp (-(a * 2)) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1 <;> ring
  have hn5 : Real.exp (-(a * 10)) = Real.exp (-(a * 2)) ^ 5 := by
    rw [← Real.exp_nat_mul]
    congr 1 <;> ring
  ring_nf
  rw [hp2, hp3, hp4, hp5, hn2, hn3, hn4, hn5]
  ring

/-- Away from the line, the removable scalar is the inverse-square normalized raw defect. -/
theorem fiveShiftWardRemovableSourceScalar_eq_invSq_defect
    {a : ℝ} (ha : a ≠ 0) :
    fiveShiftWardRemovableSourceScalar a =
      a⁻¹ ^ 2 * fiveShiftWardExpPairDefectCombination a := by
  rw [fiveShiftWardRemovableSourceScalar, fiveShiftWardExpPairDefectCombination]
  dsimp only
  rw [← invSq_expPairDefect_eq_wardRemovable (k := 1) ha,
    ← invSq_expPairDefect_eq_wardRemovable (k := 2) ha,
    ← invSq_expPairDefect_eq_wardRemovable (k := 3) ha,
    ← invSq_expPairDefect_eq_wardRemovable (k := 4) ha,
    ← invSq_expPairDefect_eq_wardRemovable (k := 5) ha]
  ring

/-- Punctured agreement with the totalized Ward--Green scalar. -/
theorem fiveShiftWardRemovableSourceScalar_eq_renormalizedFeature
    {a : ℝ} (ha : a ≠ 0) :
    fiveShiftWardRemovableSourceScalar a =
      fiveShiftEulerGammaPairedRenormalizedFeature 1 a := by
  rw [fiveShiftWardRemovableSourceScalar_eq_invSq_defect ha,
    fiveShiftWardExpPairDefectCombination_eq_pairedFeature,
    fiveShiftEulerGammaPairedRenormalizedFeature]

/-- The missing critical-line jet retains the same universal `1/81` quantum as every punctured
right-half displacement.  This follows by continuity, not by a numerical evaluation of the
exponential coefficient expression. -/
theorem fiveShiftWardKernelJump_ge :
    1 / 81 ≤ fiveShiftWardKernelJump := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    linarith
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa [one_div, Pi.inv_def] using hden.inv_tendsto_atTop
  have hlim : Tendsto
      (fun n : ℕ => fiveShiftWardRemovableSourceScalar (1 / ((n : ℝ) + 2)))
      atTop (𝓝 fiveShiftWardKernelJump) := by
    simpa [Function.comp_def, one_div] using
      continuousAt_fiveShiftWardRemovableSourceScalar_zero.tendsto.comp hzero
  apply ge_of_tendsto' hlim
  intro n
  rw [fiveShiftWardRemovableSourceScalar_eq_renormalizedFeature (by positivity)]
  apply fiveShiftEulerGammaPairedRenormalizedFeature_one_ge
  · positivity
  · apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith

open HedenmalmThetaSource

def wardGreenSinhc (x : ℝ) : ℝ :=
  Function.update (fun y : ℝ => Real.sinh y / y) 0 1 x

@[simp] theorem wardGreenSinhc_zero : wardGreenSinhc 0 = 1 := by
  rw [wardGreenSinhc, Function.update_self]

theorem wardGreenSinhc_mul (x : ℝ) :
    wardGreenSinhc x * x = Real.sinh x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [wardGreenSinhc, Function.update_of_ne hx, div_mul_cancel₀ _ hx]

theorem continuous_wardGreenSinhc : Continuous wardGreenSinhc := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_update_same.mpr tendsto_sinh_div
  · have hbase : ContinuousAt (fun y : ℝ => Real.sinh y / y) x :=
      Real.continuous_sinh.continuousAt.div continuousAt_id hx
    apply hbase.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [wardGreenSinhc, Function.update_of_ne hy]

def fiveShiftWardPairCoefficientOne (r : ℝ) : ℝ :=
  Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) *
    Real.exp (-(21 / 10 : ℝ) * r)

def fiveShiftWardPairCoefficientTwo (r : ℝ) : ℝ :=
  Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) +
    Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-(21 / 10 : ℝ) * r) +
    Real.exp (-2 * r) * Real.exp (-(21 / 10 : ℝ) * r) +
    Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) *
      Real.exp (-(21 / 10 : ℝ) * r)

def fiveShiftWardPairCoefficientThree (r : ℝ) : ℝ :=
  Real.exp (-(6 / 5 : ℝ) * r) + Real.exp (-2 * r) +
    Real.exp (-(21 / 10 : ℝ) * r) +
    Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) +
    Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-(21 / 10 : ℝ) * r) +
    Real.exp (-2 * r) * Real.exp (-(21 / 10 : ℝ) * r)

def fiveShiftWardPairCoefficientFour (r : ℝ) : ℝ :=
  1 + Real.exp (-(6 / 5 : ℝ) * r) + Real.exp (-2 * r) +
    Real.exp (-(21 / 10 : ℝ) * r)

def fiveShiftWardExponentialPairDefect (k : ℕ) (r a : ℝ) : ℝ :=
  Real.exp (-2 * a * r) ^ k + Real.exp (2 * a * r) ^ k - 2

theorem fiveShiftEulerGammaPairedFeature_eq_pairDefects (r a : ℝ) :
    fiveShiftEulerGammaPairedFeature r a =
      fiveShiftWardPairCoefficientOne r *
          fiveShiftWardExponentialPairDefect 1 r a -
        fiveShiftWardPairCoefficientTwo r *
          fiveShiftWardExponentialPairDefect 2 r a +
        fiveShiftWardPairCoefficientThree r *
          fiveShiftWardExponentialPairDefect 3 r a -
        fiveShiftWardPairCoefficientFour r *
          fiveShiftWardExponentialPairDefect 4 r a +
        fiveShiftWardExponentialPairDefect 5 r a := by
  rw [fiveShiftEulerGammaPairedFeature, fiveShiftEulerGammaFeature,
    fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial_eq_coefficients,
    fiveShiftEulerGammaPolynomial_eq_coefficients]
  have hneg : Real.exp (-2 * -a * r) = Real.exp (2 * a * r) := by
    congr 1
    ring
  rw [hneg]
  simp only [fiveShiftWardPairCoefficientOne, fiveShiftWardPairCoefficientTwo,
    fiveShiftWardPairCoefficientThree, fiveShiftWardPairCoefficientFour,
    fiveShiftWardExponentialPairDefect]
  ring

theorem fiveShiftWardExponentialPairDefect_eq_four_sinh_sq
    (k : ℕ) (r a : ℝ) :
    fiveShiftWardExponentialPairDefect k r a =
      4 * Real.sinh ((k : ℝ) * r * a) ^ 2 := by
  rw [fiveShiftWardExponentialPairDefect, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul]
  rw [show (k : ℝ) * (-2 * a * r) = -2 * ((k : ℝ) * r * a) by ring,
    show (k : ℝ) * (2 * a * r) = 2 * ((k : ℝ) * r * a) by ring]
  simpa [add_comm] using
    fiveShift_exp_pair_defect_eq_four_sinh_sq ((k : ℝ) * r * a)

def fiveShiftWardGreenRemovableExtension (r a : ℝ) : ℝ :=
  fiveShiftWardPairCoefficientOne r *
      (4 * ((1 : ℝ) * r) ^ 2 * wardGreenSinhc ((1 : ℝ) * r * a) ^ 2) -
    fiveShiftWardPairCoefficientTwo r *
      (4 * ((2 : ℝ) * r) ^ 2 * wardGreenSinhc ((2 : ℝ) * r * a) ^ 2) +
    fiveShiftWardPairCoefficientThree r *
      (4 * ((3 : ℝ) * r) ^ 2 * wardGreenSinhc ((3 : ℝ) * r * a) ^ 2) -
    fiveShiftWardPairCoefficientFour r *
      (4 * ((4 : ℝ) * r) ^ 2 * wardGreenSinhc ((4 : ℝ) * r * a) ^ 2) +
    4 * ((5 : ℝ) * r) ^ 2 * wardGreenSinhc ((5 : ℝ) * r * a) ^ 2

theorem continuous_fiveShiftWardGreenRemovableExtension (r : ℝ) :
    Continuous (fiveShiftWardGreenRemovableExtension r) := by
  have hterm (k : ℕ) : Continuous (fun a : ℝ =>
      4 * ((k : ℝ) * r) ^ 2 * wardGreenSinhc ((k : ℝ) * r * a) ^ 2) := by
    exact continuous_const.mul
      ((continuous_wardGreenSinhc.comp
        (continuous_const.mul continuous_id)).pow 2)
  have hscaled (c : ℝ) (k : ℕ) : Continuous (fun a : ℝ =>
      c * (4 * ((k : ℝ) * r) ^ 2 * wardGreenSinhc ((k : ℝ) * r * a) ^ 2)) :=
    continuous_const.mul (hterm k)
  unfold fiveShiftWardGreenRemovableExtension
  have hcombined := ((((hscaled (fiveShiftWardPairCoefficientOne r) 1).sub
      (hscaled (fiveShiftWardPairCoefficientTwo r) 2)).add
      (hscaled (fiveShiftWardPairCoefficientThree r) 3)).sub
      (hscaled (fiveShiftWardPairCoefficientFour r) 4)).add (hterm 5)
  convert hcombined using 1
  funext a
  norm_num

theorem fiveShiftWardExponentialPairDefect_div_sq_eq_removable
    (k : ℕ) (r : ℝ) {a : ℝ} (ha : a ≠ 0) :
    a⁻¹ ^ 2 * fiveShiftWardExponentialPairDefect k r a =
      4 * ((k : ℝ) * r) ^ 2 * wardGreenSinhc ((k : ℝ) * r * a) ^ 2 := by
  rw [fiveShiftWardExponentialPairDefect_eq_four_sinh_sq]
  have hs := wardGreenSinhc_mul ((k : ℝ) * r * a)
  rw [← hs]
  field_simp [ha]

theorem fiveShiftEulerGammaPairedRenormalizedFeature_eq_removableExtension
    (r : ℝ) {a : ℝ} (ha : a ≠ 0) :
    fiveShiftEulerGammaPairedRenormalizedFeature r a =
      fiveShiftWardGreenRemovableExtension r a := by
  rw [fiveShiftEulerGammaPairedRenormalizedFeature,
    fiveShiftEulerGammaPairedFeature_eq_pairDefects]
  rw [show a⁻¹ ^ 2 *
      (fiveShiftWardPairCoefficientOne r * fiveShiftWardExponentialPairDefect 1 r a -
              fiveShiftWardPairCoefficientTwo r * fiveShiftWardExponentialPairDefect 2 r a +
            fiveShiftWardPairCoefficientThree r * fiveShiftWardExponentialPairDefect 3 r a -
          fiveShiftWardPairCoefficientFour r * fiveShiftWardExponentialPairDefect 4 r a +
        fiveShiftWardExponentialPairDefect 5 r a) =
      fiveShiftWardPairCoefficientOne r *
          (a⁻¹ ^ 2 * fiveShiftWardExponentialPairDefect 1 r a) -
        fiveShiftWardPairCoefficientTwo r *
          (a⁻¹ ^ 2 * fiveShiftWardExponentialPairDefect 2 r a) +
        fiveShiftWardPairCoefficientThree r *
          (a⁻¹ ^ 2 * fiveShiftWardExponentialPairDefect 3 r a) -
        fiveShiftWardPairCoefficientFour r *
          (a⁻¹ ^ 2 * fiveShiftWardExponentialPairDefect 4 r a) +
        a⁻¹ ^ 2 * fiveShiftWardExponentialPairDefect 5 r a by ring]
  rw [fiveShiftWardExponentialPairDefect_div_sq_eq_removable 1 r ha,
    fiveShiftWardExponentialPairDefect_div_sq_eq_removable 2 r ha,
    fiveShiftWardExponentialPairDefect_div_sq_eq_removable 3 r ha,
    fiveShiftWardExponentialPairDefect_div_sq_eq_removable 4 r ha,
    fiveShiftWardExponentialPairDefect_div_sq_eq_removable 5 r ha]
  simp [fiveShiftWardGreenRemovableExtension]

/-- Positive removable value discarded by totalized Ward inversion at scale one. -/
def fiveShiftWardGreenKernelJump : ℝ :=
  fiveShiftWardGreenRemovableExtension 1 0

theorem fiveShiftWardGreenKernelJump_ge :
    1 / 81 ≤ fiveShiftWardGreenKernelJump := by
  have harg : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto
      (fun n : ℕ => fiveShiftWardGreenRemovableExtension 1 (1 / (n + 1 : ℝ)))
      atTop (nhds fiveShiftWardGreenKernelJump) := by
    exact (continuous_fiveShiftWardGreenRemovableExtension 1).continuousAt.tendsto.comp harg
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have ha0 : (1 / (n + 1 : ℝ)) ≠ 0 := by positivity
  rw [← fiveShiftEulerGammaPairedRenormalizedFeature_eq_removableExtension 1 ha0]
  apply fiveShiftEulerGammaPairedRenormalizedFeature_one_ge
  · positivity
  · have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : 0 < (n + 1 : ℝ) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith

def fiveShiftWardGreenKernelAtom (r a : ℝ) : ℝ :=
  if a = 0 then fiveShiftWardGreenRemovableExtension r 0 else 0

/-- Exact scalar fracture: totalized Green value is the removable source value minus one kernel
atom. -/
theorem fiveShiftEulerGammaPairedRenormalizedFeature_eq_extension_sub_kernelAtom
    (r a : ℝ) :
    fiveShiftEulerGammaPairedRenormalizedFeature r a =
      fiveShiftWardGreenRemovableExtension r a -
        fiveShiftWardGreenKernelAtom r a := by
  by_cases ha : a = 0
  · subst a
    simp [fiveShiftEulerGammaPairedRenormalizedFeature_zero,
      fiveShiftWardGreenKernelAtom]
  · rw [fiveShiftEulerGammaPairedRenormalizedFeature_eq_removableExtension r ha,
      fiveShiftWardGreenKernelAtom, if_neg ha, sub_zero]

theorem fiveShiftWardGreenKernelAtom_one_eq (a : ℝ) :
    fiveShiftWardGreenKernelAtom 1 a =
      if a = 0 then fiveShiftWardGreenKernelJump else 0 := by
  rfl

theorem fiveShiftEulerGammaRenormalizedKreinDefectCombination_eq_extension_sub_kernelAtom
    (q : XiZeroCopy) :
    fiveShiftEulerGammaRenormalizedKreinDefectCombination 1 q =
      fiveShiftWardGreenRemovableExtension 1 ((q.1 : ℂ).re - 1 / 2) -
        fiveShiftWardGreenKernelAtom 1 ((q.1 : ℂ).re - 1 / 2) := by
  rw [fiveShiftEulerGammaRenormalizedKreinDefectCombination_eq_pairedFeature
    (r := 1) (by norm_num)]
  exact fiveShiftEulerGammaPairedRenormalizedFeature_eq_extension_sub_kernelAtom
    1 ((q.1 : ℂ).re - 1 / 2)

def fiveShiftWardGreenRemovableCriticalFeatureCurrent (t : ℝ) (q : XiZeroCopy) : ℝ :=
  fiveShiftWardGreenRemovableExtension 1 ((q.1 : ℂ).re - 1 / 2) *
    Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))

def fiveShiftWardGreenKernelProjectionCurrent (t : ℝ) (q : XiZeroCopy) : ℝ :=
  fiveShiftWardGreenKernelAtom 1 ((q.1 : ℂ).re - 1 / 2) *
    Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))

/-- Per-copy current is exactly removable source current minus critical-line projection current. -/
theorem fiveShiftCriticalFeatureWardGreenCurrent_eq_removable_sub_kernelProjection
    (t : ℝ) (q : XiZeroCopy) :
    fiveShiftCriticalFeatureWardGreenCurrent t q =
      fiveShiftWardGreenRemovableCriticalFeatureCurrent t q -
        fiveShiftWardGreenKernelProjectionCurrent t q := by
  rw [fiveShiftCriticalFeatureWardGreenCurrent_eq_renormalizedKrein_mul,
    fiveShiftEulerGammaRenormalizedKreinDefectCombination_eq_extension_sub_kernelAtom]
  have heval :
      criticalEvaluation (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
          (criticalFeature (t : ℂ) (by norm_num)) =
        criticalFeatureCauchyKernelTest t (xiSpectralPoint q) := by
    rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
    rfl
  rw [heval]
  unfold fiveShiftWardGreenRemovableCriticalFeatureCurrent
    fiveShiftWardGreenKernelProjectionCurrent
  ring

theorem fiveShiftWardGreenKernelProjectionCurrent_nonneg
    (t : ℝ) (q : XiZeroCopy) :
    0 ≤ fiveShiftWardGreenKernelProjectionCurrent t q := by
  rw [fiveShiftWardGreenKernelProjectionCurrent,
    fiveShiftWardGreenKernelAtom_one_eq]
  split_ifs
  · exact mul_nonneg (fiveShiftWardGreenKernelJump_ge.trans' (by norm_num))
      (Complex.normSq_nonneg _)
  · simp

theorem fiveShiftWardGreenKernelProjectionCurrent_le
    (t : ℝ) (q : XiZeroCopy) :
    fiveShiftWardGreenKernelProjectionCurrent t q ≤
      fiveShiftWardGreenKernelJump *
        Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) := by
  rw [fiveShiftWardGreenKernelProjectionCurrent,
    fiveShiftWardGreenKernelAtom_one_eq]
  split_ifs <;> simp
  exact mul_nonneg (fiveShiftWardGreenKernelJump_ge.trans' (by norm_num))
    (Complex.normSq_nonneg _)

theorem fiveShiftWardGreenKernelProjectionCurrent_summable (t : ℝ) :
    Summable (fiveShiftWardGreenKernelProjectionCurrent t) := by
  have hmajor : Summable (fun q : XiZeroCopy =>
      fiveShiftWardGreenKernelJump *
        Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))) :=
    (criticalFeatureHermitianEnergy_summable t).mul_left fiveShiftWardGreenKernelJump
  exact Summable.of_nonneg_of_le
    (fiveShiftWardGreenKernelProjectionCurrent_nonneg t)
    (fiveShiftWardGreenKernelProjectionCurrent_le t) hmajor

theorem fiveShiftWardGreenRemovableCriticalFeatureCurrent_eq_add
    (t : ℝ) (q : XiZeroCopy) :
    fiveShiftWardGreenRemovableCriticalFeatureCurrent t q =
      fiveShiftCriticalFeatureWardGreenCurrent t q +
        fiveShiftWardGreenKernelProjectionCurrent t q := by
  rw [fiveShiftCriticalFeatureWardGreenCurrent_eq_removable_sub_kernelProjection]
  ring

theorem fiveShiftWardGreenRemovableCriticalFeatureCurrent_summable (t : ℝ) :
    Summable (fiveShiftWardGreenRemovableCriticalFeatureCurrent t) := by
  exact ((fiveShiftCriticalFeatureWardGreenCurrent_summable t).add
    (fiveShiftWardGreenKernelProjectionCurrent_summable t)).congr
      (fun q => (fiveShiftWardGreenRemovableCriticalFeatureCurrent_eq_add t q).symm)

def fiveShiftWardGreenRemovableCriticalFeatureTrace (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, fiveShiftWardGreenRemovableCriticalFeatureCurrent t q

def fiveShiftWardGreenKernelProjectionTrace (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, fiveShiftWardGreenKernelProjectionCurrent t q

def criticalLineCriticalFeatureEnergy (t : ℝ) (q : XiZeroCopy) : ℝ :=
  if (q.1 : ℂ).re = 1 / 2 then
    Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))
  else 0

def criticalLineCriticalFeatureEnergyTrace (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, criticalLineCriticalFeatureEnergy t q

theorem criticalLineCriticalFeatureEnergy_summable (t : ℝ) :
    Summable (criticalLineCriticalFeatureEnergy t) := by
  exact Summable.of_nonneg_of_le
    (fun q => by
      rw [criticalLineCriticalFeatureEnergy]
      by_cases hq : (q.1 : ℂ).re = (1 / 2 : ℝ)
      · rw [if_pos hq]
        exact Complex.normSq_nonneg _
      · rw [if_neg hq])
    (fun q => by
      rw [criticalLineCriticalFeatureEnergy]
      by_cases hq : (q.1 : ℂ).re = (1 / 2 : ℝ)
      · rw [if_pos hq]
      · rw [if_neg hq]
        exact Complex.normSq_nonneg _)
    (criticalFeatureHermitianEnergy_summable t)

def offLineCriticalFeatureEnergy (t : ℝ) (q : XiZeroCopy) : ℝ :=
  if (q.1 : ℂ).re = 1 / 2 then 0
  else Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))

def offLineCriticalFeatureEnergyTrace (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, offLineCriticalFeatureEnergy t q

theorem offLineCriticalFeatureEnergy_summable (t : ℝ) :
    Summable (offLineCriticalFeatureEnergy t) := by
  exact Summable.of_nonneg_of_le
    (fun q => by
      rw [offLineCriticalFeatureEnergy]
      by_cases hq : (q.1 : ℂ).re = (1 / 2 : ℝ)
      · rw [if_pos hq]
      · rw [if_neg hq]
        exact Complex.normSq_nonneg _)
    (fun q => by
      rw [offLineCriticalFeatureEnergy]
      by_cases hq : (q.1 : ℂ).re = (1 / 2 : ℝ)
      · rw [if_pos hq]
        exact Complex.normSq_nonneg _
      · rw [if_neg hq])
    (criticalFeatureHermitianEnergy_summable t)

theorem offLineCriticalFeatureEnergy_nonneg (t : ℝ) (q : XiZeroCopy) :
    0 ≤ offLineCriticalFeatureEnergy t q := by
  rw [offLineCriticalFeatureEnergy]
  split_ifs
  · simp
  · exact Complex.normSq_nonneg _

theorem criticalFeatureHermitianEnergyTrace_eq_line_add_offLine (t : ℝ) :
    criticalFeatureHermitianEnergyTrace t =
      criticalLineCriticalFeatureEnergyTrace t +
        offLineCriticalFeatureEnergyTrace t := by
  rw [criticalFeatureHermitianEnergyTrace,
    criticalLineCriticalFeatureEnergyTrace,
    offLineCriticalFeatureEnergyTrace,
    ← (criticalLineCriticalFeatureEnergy_summable t).tsum_add
      (offLineCriticalFeatureEnergy_summable t)]
  apply tsum_congr
  intro q
  by_cases hq : (q.1 : ℂ).re = (2 : ℝ)⁻¹
  · simp [criticalLineCriticalFeatureEnergy, offLineCriticalFeatureEnergy,
      show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, hq]
  · simp [criticalLineCriticalFeatureEnergy, offLineCriticalFeatureEnergy,
      show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, hq]

theorem offLineCriticalFeatureEnergyTrace_eq_zero_iff_rh (t : ℝ) :
    offLineCriticalFeatureEnergyTrace t = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline : (q.1 : ℂ).re = 1 / 2 := by
      by_contra hq
      have htermPos : 0 < offLineCriticalFeatureEnergy t q := by
        rw [offLineCriticalFeatureEnergy, if_neg hq]
        apply Complex.normSq_pos.mpr
        have heval := criticalEvaluation_realCriticalFeature_ne_zero t
          (abs_xiSpectralPoint_im_lt_half q)
        rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum] at heval
        exact heval
      have htracePos : 0 < offLineCriticalFeatureEnergyTrace t :=
        (offLineCriticalFeatureEnergy_summable t).tsum_pos
          (offLineCriticalFeatureEnergy_nonneg t)
          q htermPos
      rw [hzero] at htracePos
      exact lt_irrefl 0 htracePos
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · rw [Complex.ofReal_im, xiSpectralPoint_im_eq]
      linarith
  · intro hRH
    rw [offLineCriticalFeatureEnergyTrace]
    have hfun : offLineCriticalFeatureEnergy t = fun _ : XiZeroCopy => 0 := by
      funext q
      obtain ⟨u, hu⟩ := xiSpectralPoint_real_of_rh hRH q
      have hline : (q.1 : ℂ).re = 1 / 2 := by
        have him := congrArg Complex.im hu
        rw [xiSpectralPoint_im_eq] at him
        simp only [Complex.ofReal_im] at him
        linarith
      simp [offLineCriticalFeatureEnergy, hline]
    rw [hfun, tsum_zero]

/-- The critical-line projection exhausts full feature energy exactly under RH. -/
theorem criticalLineCriticalFeatureEnergyTrace_eq_full_iff_rh (t : ℝ) :
    criticalLineCriticalFeatureEnergyTrace t =
        criticalFeatureHermitianEnergyTrace t ↔
      RiemannHypothesis := by
  have hsplit := criticalFeatureHermitianEnergyTrace_eq_line_add_offLine t
  constructor
  · intro h
    apply (offLineCriticalFeatureEnergyTrace_eq_zero_iff_rh t).mp
    linarith
  · intro hRH
    have hoff := (offLineCriticalFeatureEnergyTrace_eq_zero_iff_rh t).mpr hRH
    linarith

/-- Kernel projection trace is exactly the positive jump times critical-line feature energy. -/
theorem fiveShiftWardGreenKernelProjectionTrace_eq_jump_mul_lineEnergy
    (t : ℝ) :
    fiveShiftWardGreenKernelProjectionTrace t =
      fiveShiftWardGreenKernelJump * criticalLineCriticalFeatureEnergyTrace t := by
  rw [fiveShiftWardGreenKernelProjectionTrace,
    criticalLineCriticalFeatureEnergyTrace, ← tsum_mul_left]
  apply tsum_congr
  intro q
  simp [fiveShiftWardGreenKernelProjectionCurrent,
    fiveShiftWardGreenKernelAtom_one_eq, criticalLineCriticalFeatureEnergy,
    sub_eq_zero]

/-- Exact trace fracture. No remainder remains beyond one critical-line projection trace. -/
theorem fiveShiftCriticalFeatureWardGreenTrace_eq_removable_sub_kernelProjection
    (t : ℝ) :
    fiveShiftCriticalFeatureWardGreenTrace t =
      fiveShiftWardGreenRemovableCriticalFeatureTrace t -
        fiveShiftWardGreenKernelProjectionTrace t := by
  rw [fiveShiftCriticalFeatureWardGreenTrace,
    fiveShiftWardGreenRemovableCriticalFeatureTrace,
    fiveShiftWardGreenKernelProjectionTrace,
    ← (fiveShiftWardGreenRemovableCriticalFeatureCurrent_summable t).tsum_sub
      (fiveShiftWardGreenKernelProjectionCurrent_summable t)]
  apply tsum_congr
  exact fiveShiftCriticalFeatureWardGreenCurrent_eq_removable_sub_kernelProjection t

/-- Final exact normal form: regular removable trace minus one positive critical-line projector. -/
theorem fiveShiftCriticalFeatureWardGreenTrace_eq_removable_sub_jump_mul_lineEnergy
    (t : ℝ) :
    fiveShiftCriticalFeatureWardGreenTrace t =
      fiveShiftWardGreenRemovableCriticalFeatureTrace t -
        fiveShiftWardGreenKernelJump * criticalLineCriticalFeatureEnergyTrace t := by
  rw [fiveShiftCriticalFeatureWardGreenTrace_eq_removable_sub_kernelProjection,
    fiveShiftWardGreenKernelProjectionTrace_eq_jump_mul_lineEnergy]


end

end RHTower
