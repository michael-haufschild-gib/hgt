import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometric phase-orbit light coercivity

For `0 ≤ R < 1`, the geometric phase orbit has negative-light energy

`E₋(R, θ) = ∑ e, R^e (1 - sin ((e + 1)θ))`.

This file evaluates the sum exactly and proves the sharp phase-independent lower bound

`R / (1 - R²) ≤ E₋(R, θ)`.

The bound is attained.  Thus a single phase coordinate can be null, but its complete contractive
geometric orbit is uniformly nonzero in the same light direction.
-/

open Complex

namespace HTGeometry

noncomputable section

/-- Complex ratio of a contractive geometric orbit with phase increment `θ`. -/
def geometricPhaseRatio (R θ : ℝ) : ℂ :=
  (R : ℂ) * Complex.exp ((θ : ℂ) * I)

/-- Complex phase term whose imaginary part is `R^e sin((e+1)θ)`. -/
def geometricPhaseTerm (R θ : ℝ) (e : ℕ) : ℂ :=
  Complex.exp ((θ : ℂ) * I) * geometricPhaseRatio R θ ^ e

/-- Normalized negative-light energy at depth `e`. -/
def geometricNegativeLightTerm (R θ : ℝ) (e : ℕ) : ℝ :=
  R ^ e - (geometricPhaseTerm R θ e).im

theorem geometricPhaseTerm_eq
    (R θ : ℝ) (e : ℕ) :
    geometricPhaseTerm R θ e =
      (R ^ e : ℂ) *
        Complex.exp (((((e : ℝ) + 1) * θ : ℝ) : ℂ) * I) := by
  rw [geometricPhaseTerm, geometricPhaseRatio, mul_pow]
  push_cast
  rw [← Complex.exp_nat_mul]
  calc
    Complex.exp ((θ : ℂ) * I) *
        ((R : ℂ) ^ e * Complex.exp ((e : ℂ) * ((θ : ℂ) * I))) =
      (R : ℂ) ^ e *
        (Complex.exp ((θ : ℂ) * I) *
          Complex.exp ((e : ℂ) * ((θ : ℂ) * I))) := by ring
    _ = (R : ℂ) ^ e *
        Complex.exp ((θ : ℂ) * I + (e : ℂ) * ((θ : ℂ) * I)) := by
          rw [Complex.exp_add]
    _ = _ := by
      congr 2
      ring

theorem geometricNegativeLightTerm_eq
    (R θ : ℝ) (e : ℕ) :
    geometricNegativeLightTerm R θ e =
      R ^ e * (1 - Real.sin (((e : ℝ) + 1) * θ)) := by
  rw [geometricNegativeLightTerm, geometricPhaseTerm_eq]
  rw [← Complex.ofReal_pow R e]
  rw [Complex.mul_im]
  rw [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [Complex.exp_im]
  simp
  ring

theorem norm_geometricPhaseRatio
    {R θ : ℝ} (hR : 0 ≤ R) :
    ‖geometricPhaseRatio R θ‖ = R := by
  rw [geometricPhaseRatio, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hR, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem summable_geometricPhaseTerm
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    Summable (geometricPhaseTerm R θ) := by
  have hq : ‖geometricPhaseRatio R θ‖ < 1 := by
    rw [norm_geometricPhaseRatio hR0]
    exact hR1
  exact (summable_geometric_of_norm_lt_one hq).mul_left _

theorem tsum_geometricPhaseTerm
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    (∑' e : ℕ, geometricPhaseTerm R θ e) =
      Complex.exp ((θ : ℂ) * I) * (1 - geometricPhaseRatio R θ)⁻¹ := by
  change (∑' e : ℕ,
    Complex.exp ((θ : ℂ) * I) * geometricPhaseRatio R θ ^ e) = _
  rw [tsum_mul_left,
    tsum_geometric_of_norm_lt_one
      (by rw [norm_geometricPhaseRatio hR0]; exact hR1)]

theorem tsum_im_geometricPhaseTerm
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    (∑' e : ℕ, (geometricPhaseTerm R θ e).im) =
      (Complex.exp ((θ : ℂ) * I) *
        (1 - geometricPhaseRatio R θ)⁻¹).im := by
  have hmap := Complex.imCLM.map_tsum
    (f := geometricPhaseTerm R θ) (summable_geometricPhaseTerm hR0 hR1)
  rw [tsum_geometricPhaseTerm hR0 hR1] at hmap
  simpa only [Complex.imCLM_apply] using hmap.symm

theorem summable_geometricNegativeLightTerm
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    Summable (geometricNegativeLightTerm R θ) := by
  have him : Summable (fun e : ℕ => (geometricPhaseTerm R θ e).im) :=
    Complex.imCLM.summable (summable_geometricPhaseTerm hR0 hR1)
  exact (summable_geometric_of_lt_one hR0 hR1).sub him

/-- Resolvent denominator of the contractive phase orbit. -/
def geometricPhaseDenominator (R θ : ℝ) : ℝ :=
  1 - 2 * R * Real.cos θ + R ^ 2

theorem normSq_one_sub_geometricPhaseRatio
    (R θ : ℝ) :
    Complex.normSq (1 - geometricPhaseRatio R θ) =
      geometricPhaseDenominator R θ := by
  have hre : (Complex.exp ((θ : ℂ) * I)).re = Real.cos θ := by
    simp [Complex.exp_re]
  have him : (Complex.exp ((θ : ℂ) * I)).im = Real.sin θ := by
    simp [Complex.exp_im]
  rw [Complex.normSq_apply]
  simp [geometricPhaseRatio, geometricPhaseDenominator,
    Complex.mul_re, Complex.mul_im, hre, him]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem im_geometricPhaseResolvent
    {R θ : ℝ} :
    (Complex.exp ((θ : ℂ) * I) *
        (1 - geometricPhaseRatio R θ)⁻¹).im =
      Real.sin θ / geometricPhaseDenominator R θ := by
  have hre : (Complex.exp ((θ : ℂ) * I)).re = Real.cos θ := by
    simp [Complex.exp_re]
  have him : (Complex.exp ((θ : ℂ) * I)).im = Real.sin θ := by
    simp [Complex.exp_im]
  rw [Complex.mul_im, Complex.inv_re, Complex.inv_im,
    normSq_one_sub_geometricPhaseRatio]
  simp [geometricPhaseRatio, Complex.mul_re, Complex.mul_im, hre, him]
  ring

/-- Closed form of the complete negative-light energy. -/
def geometricNegativeLightEnergy (R θ : ℝ) : ℝ :=
  (1 - R)⁻¹ -
    Real.sin θ / geometricPhaseDenominator R θ

theorem tsum_geometricNegativeLightTerm_eq
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    (∑' e : ℕ, geometricNegativeLightTerm R θ e) =
      geometricNegativeLightEnergy R θ := by
  have him : Summable (fun e : ℕ => (geometricPhaseTerm R θ e).im) :=
    Complex.imCLM.summable (summable_geometricPhaseTerm hR0 hR1)
  change (∑' e : ℕ,
      (fun k : ℕ => R ^ k - (geometricPhaseTerm R θ k).im) e) = _
  rw [(summable_geometric_of_lt_one hR0 hR1).tsum_sub him,
    tsum_geometric_of_lt_one hR0 hR1,
    tsum_im_geometricPhaseTerm hR0 hR1,
    im_geometricPhaseResolvent]
  rfl

theorem geometricPhaseDenominator_pos
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    0 < geometricPhaseDenominator R θ := by
  have hcos := Real.cos_le_one θ
  have hsq : 0 < (1 - R) ^ 2 := sq_pos_of_pos (sub_pos.mpr hR1)
  rw [geometricPhaseDenominator]
  nlinarith

private theorem phaseFloorNumerator_nonneg (R θ : ℝ) :
    0 ≤ 1 + R ^ 2 - 2 * R * Real.cos θ -
      (1 - R ^ 2) * Real.sin θ := by
  let N := 1 + R ^ 2 - 2 * R * Real.cos θ -
    (1 - R ^ 2) * Real.sin θ
  have hsq : 0 ≤
      (2 * R - (1 + R ^ 2) * Real.cos θ) ^ 2 +
        ((1 - R ^ 2) - (1 + R ^ 2) * Real.sin θ) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have htrig := Real.sin_sq_add_cos_sq θ
  have hid :
      (2 * R - (1 + R ^ 2) * Real.cos θ) ^ 2 +
          ((1 - R ^ 2) - (1 + R ^ 2) * Real.sin θ) ^ 2 =
        2 * (1 + R ^ 2) * N := by
    calc
      _ = 2 * (1 + R ^ 2) *
            (1 + R ^ 2 - 2 * R * Real.cos θ -
            (1 - R ^ 2) * Real.sin θ) +
          (1 + R ^ 2) ^ 2 *
            (Real.sin θ ^ 2 + Real.cos θ ^ 2 - 1) := by
              ring
      _ = _ := by rw [htrig]; ring
  rw [hid] at hsq
  have hC : 0 < 2 * (1 + R ^ 2) := by positivity
  dsimp [N] at hsq ⊢
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hsq) hC

private theorem phaseFloorSquares_eq (R θ : ℝ) :
    (2 * R - (1 + R ^ 2) * Real.cos θ) ^ 2 +
        ((1 - R ^ 2) - (1 + R ^ 2) * Real.sin θ) ^ 2 =
      2 * (1 + R ^ 2) *
        (1 + R ^ 2 - 2 * R * Real.cos θ -
          (1 - R ^ 2) * Real.sin θ) := by
  have htrig := Real.sin_sq_add_cos_sq θ
  calc
    _ = 2 * (1 + R ^ 2) *
          (1 + R ^ 2 - 2 * R * Real.cos θ -
            (1 - R ^ 2) * Real.sin θ) +
        (1 + R ^ 2) ^ 2 *
          (Real.sin θ ^ 2 + Real.cos θ ^ 2 - 1) := by ring
    _ = _ := by rw [htrig]; ring

theorem geometricNegativeLightEnergy_sub_floor
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    geometricNegativeLightEnergy R θ - R / (1 - R ^ 2) =
      (1 + R ^ 2 - 2 * R * Real.cos θ -
          (1 - R ^ 2) * Real.sin θ) /
        ((1 - R ^ 2) * geometricPhaseDenominator R θ) := by
  have h1 : 1 - R ≠ 0 := ne_of_gt (sub_pos.mpr hR1)
  have hsq : 1 - R ^ 2 ≠ 0 := by nlinarith
  have hD : geometricPhaseDenominator R θ ≠ 0 :=
    ne_of_gt (geometricPhaseDenominator_pos hR0 hR1)
  rw [geometricNegativeLightEnergy, inv_eq_one_div]
  field_simp [h1, hsq, hD]
  unfold geometricPhaseDenominator
  ring

/-- **Sharp universal light-coercivity law.**  Complete valuation depth removes every phase hole. -/
theorem geometricNegativeLightEnergy_ge_sharpFloor
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    R / (1 - R ^ 2) ≤ geometricNegativeLightEnergy R θ := by
  rw [← sub_nonneg]
  rw [geometricNegativeLightEnergy_sub_floor hR0 hR1]
  exact div_nonneg (phaseFloorNumerator_nonneg R θ)
    (mul_nonneg (by nlinarith) (geometricPhaseDenominator_pos hR0 hR1).le)

theorem tsum_geometricNegativeLightTerm_ge_sharpFloor
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    R / (1 - R ^ 2) ≤
      ∑' e : ℕ, geometricNegativeLightTerm R θ e := by
  rw [tsum_geometricNegativeLightTerm_eq hR0 hR1]
  exact geometricNegativeLightEnergy_ge_sharpFloor hR0 hR1

/-- Equality classification for the sharp lower frame bound. -/
theorem geometricNegativeLightEnergy_eq_sharpFloor_iff
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    geometricNegativeLightEnergy R θ = R / (1 - R ^ 2) ↔
      (1 + R ^ 2) * Real.cos θ = 2 * R ∧
        (1 + R ^ 2) * Real.sin θ = 1 - R ^ 2 := by
  have hden : (1 - R ^ 2) * geometricPhaseDenominator R θ ≠ 0 := by
    apply mul_ne_zero
    · nlinarith
    · exact ne_of_gt (geometricPhaseDenominator_pos hR0 hR1)
  constructor
  · intro h
    have hzero :
        geometricNegativeLightEnergy R θ - R / (1 - R ^ 2) = 0 := by
      linarith
    rw [geometricNegativeLightEnergy_sub_floor hR0 hR1] at hzero
    have hN :
        1 + R ^ 2 - 2 * R * Real.cos θ -
            (1 - R ^ 2) * Real.sin θ = 0 :=
      (div_eq_zero_iff.mp hzero).resolve_right hden
    have hsquares :
        (2 * R - (1 + R ^ 2) * Real.cos θ) ^ 2 +
          ((1 - R ^ 2) - (1 + R ^ 2) * Real.sin θ) ^ 2 = 0 := by
      rw [phaseFloorSquares_eq, hN, mul_zero]
    have hfirst :
        (2 * R - (1 + R ^ 2) * Real.cos θ) ^ 2 = 0 := by
      nlinarith [sq_nonneg
        ((1 - R ^ 2) - (1 + R ^ 2) * Real.sin θ)]
    have hsecond :
        ((1 - R ^ 2) - (1 + R ^ 2) * Real.sin θ) ^ 2 = 0 := by
      nlinarith [sq_nonneg
        (2 * R - (1 + R ^ 2) * Real.cos θ)]
    constructor
    · nlinarith [sq_eq_zero_iff.mp hfirst]
    · nlinarith [sq_eq_zero_iff.mp hsecond]
  · rintro ⟨hcos, hsin⟩
    have hN :
        1 + R ^ 2 - 2 * R * Real.cos θ -
            (1 - R ^ 2) * Real.sin θ = 0 := by
      have hcircle := Real.sin_sq_add_cos_sq θ
      nlinarith
    have hsub := geometricNegativeLightEnergy_sub_floor (θ := θ) hR0 hR1
    rw [hN, zero_div] at hsub
    linarith

/-- The universal floor is optimal for every contractive radius. -/
theorem exists_geometricNegativeLightEnergy_eq_sharpFloor
    {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    ∃ θ : ℝ,
      geometricNegativeLightEnergy R θ = R / (1 - R ^ 2) := by
  let x := 2 * R / (1 + R ^ 2)
  have hden : 0 < 1 + R ^ 2 := by positivity
  have hx0 : 0 ≤ x :=
    div_nonneg (mul_nonneg (by norm_num) hR0) hden.le
  have hx1 : x ≤ 1 := by
    rw [div_le_one hden]
    nlinarith [sq_nonneg (1 - R)]
  have hcos : Real.cos (Real.arccos x) = x :=
    Real.cos_arccos (by linarith) hx1
  have hsin :
      Real.sin (Real.arccos x) = (1 - R ^ 2) / (1 + R ^ 2) := by
    rw [Real.sin_arccos]
    apply (Real.sqrt_eq_iff_eq_sq
      (by nlinarith [sq_nonneg x])
      (div_nonneg (by nlinarith) hden.le)).2
    dsimp [x]
    field_simp [ne_of_gt hden]
    ring
  refine ⟨Real.arccos x,
    (geometricNegativeLightEnergy_eq_sharpFloor_iff hR0 hR1).2 ?_⟩
  rw [hcos, hsin]
  dsimp [x]
  constructor <;> field_simp [ne_of_gt hden]

/-- Normalized positive-light energy at depth `e`. -/
def geometricPositiveLightTerm (R θ : ℝ) (e : ℕ) : ℝ :=
  R ^ e * (1 + Real.sin (((e : ℝ) + 1) * θ))

/-- Complete positive-light energy. -/
def geometricPositiveLightEnergy (R θ : ℝ) : ℝ :=
  geometricNegativeLightEnergy R (-θ)

theorem geometricPositiveLightTerm_eq_negative_neg
    (R θ : ℝ) (e : ℕ) :
    geometricPositiveLightTerm R θ e =
      geometricNegativeLightTerm R (-θ) e := by
  rw [geometricPositiveLightTerm, geometricNegativeLightTerm_eq]
  simp only [mul_neg, Real.sin_neg]
  ring

theorem tsum_geometricPositiveLightTerm_eq
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    (∑' e : ℕ, geometricPositiveLightTerm R θ e) =
      geometricPositiveLightEnergy R θ := by
  rw [show (∑' e : ℕ, geometricPositiveLightTerm R θ e) =
      ∑' e : ℕ, geometricNegativeLightTerm R (-θ) e by
        apply tsum_congr
        exact geometricPositiveLightTerm_eq_negative_neg R θ]
  exact tsum_geometricNegativeLightTerm_eq hR0 hR1

theorem geometricPositiveLightEnergy_ge_sharpFloor
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    R / (1 - R ^ 2) ≤ geometricPositiveLightEnergy R θ :=
  geometricNegativeLightEnergy_ge_sharpFloor hR0 hR1

/-- The two completed light energies exactly partition twice the geometric mass. -/
theorem geometricLightEnergies_add
    {R θ : ℝ} (hR1 : R < 1) :
    geometricNegativeLightEnergy R θ +
        geometricPositiveLightEnergy R θ =
      2 / (1 - R) := by
  have hne : 1 - R ≠ 0 := ne_of_gt (sub_pos.mpr hR1)
  simp only [geometricPositiveLightEnergy, geometricNegativeLightEnergy,
    geometricPhaseDenominator, Real.sin_neg, Real.cos_neg]
  field_simp [hne]
  ring

/-- Sharp upper companion to the light-coercivity floor. -/
theorem geometricNegativeLightEnergy_le_sharpCeiling
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    geometricNegativeLightEnergy R θ ≤ (R + 2) / (1 - R ^ 2) := by
  have hplus := geometricPositiveLightEnergy_ge_sharpFloor
    (θ := θ) hR0 hR1
  have hsum := geometricLightEnergies_add (θ := θ) hR1
  have hne1 : 1 - R ≠ 0 := ne_of_gt (sub_pos.mpr hR1)
  have hne2 : 1 - R ^ 2 ≠ 0 := by nlinarith
  calc
    geometricNegativeLightEnergy R θ
        ≤ 2 / (1 - R) - R / (1 - R ^ 2) := by linarith
    _ = (R + 2) / (1 - R ^ 2) := by
      field_simp [hne1, hne2]
      ring

theorem geometricPositiveLightEnergy_le_sharpCeiling
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    geometricPositiveLightEnergy R θ ≤ (R + 2) / (1 - R ^ 2) :=
  geometricNegativeLightEnergy_le_sharpCeiling (θ := -θ) hR0 hR1

/-- **Two-sided universal light-frame law.**  Both Lorentz light channels are uniformly coercive. -/
theorem geometricLightEnergy_mem_sharpInterval
    {R θ : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    (R / (1 - R ^ 2) ≤ geometricNegativeLightEnergy R θ ∧
      geometricNegativeLightEnergy R θ ≤ (R + 2) / (1 - R ^ 2)) ∧
    (R / (1 - R ^ 2) ≤ geometricPositiveLightEnergy R θ ∧
      geometricPositiveLightEnergy R θ ≤ (R + 2) / (1 - R ^ 2)) :=
  ⟨⟨geometricNegativeLightEnergy_ge_sharpFloor hR0 hR1,
      geometricNegativeLightEnergy_le_sharpCeiling hR0 hR1⟩,
    ⟨geometricPositiveLightEnergy_ge_sharpFloor hR0 hR1,
      geometricPositiveLightEnergy_le_sharpCeiling hR0 hR1⟩⟩

end

end HTGeometry
