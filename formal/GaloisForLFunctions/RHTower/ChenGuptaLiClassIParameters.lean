/-
# Chen--Gupta--Li class-I exponent parameters

Closed real-algebra layer of Chen--Gupta--Li §12.3.  The source ranges are
stored in certified parameter data, and every displayed parameter inequality is
proved from those fields.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterLargeValues

namespace RHTower

noncomputable section

/-- The range `0.7 ≤ σ ≤ 0.8` used in the class-I analysis. -/
structure CGLSigmaWindow where
  value : ℝ
  lower : (7 : ℝ) / 10 ≤ value
  upper : value ≤ (4 : ℝ) / 5

/-- Lower endpoint `v` for the source's auxiliary exponent `a`. -/
def cglClassIV (σ : CGLSigmaWindow) : ℝ := 5 / (3 + 5 * σ.value)

/-- Upper endpoint `w_max` for the source's auxiliary exponent `a`. -/
def cglClassIWMax (σ : CGLSigmaWindow) : ℝ := 4 / (3 * (1 + σ.value))

/-- A certified choice of the class-I auxiliary exponent. -/
structure CGLClassIExponentParameter (σ : CGLSigmaWindow) where
  value : ℝ
  lower : cglClassIV σ ≤ value
  upper : value ≤ cglClassIWMax σ

/-- The source's clamped exponent `b`. -/
def cglClassIB (σ : CGLSigmaWindow) (a : CGLClassIExponentParameter σ) : ℝ :=
  min (15 * a.value * (1 - σ.value) / (18 - 20 * σ.value)) 1

theorem cglSigma_denomV_pos (σ : CGLSigmaWindow) : 0 < 3 + 5 * σ.value := by
  nlinarith [σ.lower]

theorem cglSigma_denomW_pos (σ : CGLSigmaWindow) : 0 < 3 * (1 + σ.value) := by
  nlinarith [σ.lower]

theorem cglSigma_denomB_pos (σ : CGLSigmaWindow) : 0 < 18 - 20 * σ.value := by
  nlinarith [σ.upper]

theorem cglClassIV_gt_twoThirds (σ : CGLSigmaWindow) : (2 : ℝ) / 3 < cglClassIV σ := by
  unfold cglClassIV
  rw [lt_div_iff₀ (cglSigma_denomV_pos σ)]
  nlinarith [σ.upper]

theorem cglClassIWMax_lt_fiveSixths (σ : CGLSigmaWindow) :
    cglClassIWMax σ < (5 : ℝ) / 6 := by
  unfold cglClassIWMax
  rw [div_lt_iff₀ (cglSigma_denomW_pos σ)]
  nlinarith [σ.lower]

theorem cglClassIExponent_gt_twoThirds (σ : CGLSigmaWindow)
    (a : CGLClassIExponentParameter σ) : (2 : ℝ) / 3 < a.value :=
  (cglClassIV_gt_twoThirds σ).trans_le a.lower

theorem cglClassIExponent_lt_fiveSixths (σ : CGLSigmaWindow)
    (a : CGLClassIExponentParameter σ) : a.value < (5 : ℝ) / 6 :=
  a.upper.trans_lt (cglClassIWMax_lt_fiveSixths σ)

theorem cglClassIB_unclamped_gt_fiveSixths (σ : CGLSigmaWindow)
    (a : CGLClassIExponentParameter σ) :
    (5 : ℝ) / 6 < 15 * a.value * (1 - σ.value) / (18 - 20 * σ.value) := by
  have hfactor_pos : 0 < 15 * (1 - σ.value) := by
    nlinarith [σ.upper]
  have hmono :
      15 * cglClassIV σ * (1 - σ.value) ≤ 15 * a.value * (1 - σ.value) := by
    have h := mul_le_mul_of_nonneg_left a.lower hfactor_pos.le
    calc
      15 * cglClassIV σ * (1 - σ.value) =
          (15 * (1 - σ.value)) * cglClassIV σ := by ring
      _ ≤ (15 * (1 - σ.value)) * a.value := h
      _ = 15 * a.value * (1 - σ.value) := by ring
  calc
    (5 : ℝ) / 6 < 15 * cglClassIV σ * (1 - σ.value) / (18 - 20 * σ.value) := by
      unfold cglClassIV
      rw [lt_div_iff₀ (cglSigma_denomB_pos σ)]
      have hrewrite : 15 * (5 / (3 + 5 * σ.value)) * (1 - σ.value) =
          (15 * 5 * (1 - σ.value)) / (3 + 5 * σ.value) := by
        field_simp [ne_of_gt (cglSigma_denomV_pos σ)]
      rw [hrewrite, lt_div_iff₀ (cglSigma_denomV_pos σ)]
      have hs : 0 < 10 * σ.value - 6 := by
        nlinarith [σ.lower]
      have hquad : 0 < 500 * σ.value ^ (2 : ℕ) - 600 * σ.value + 180 := by
        nlinarith [sq_pos_of_pos hs]
      by_contra h
      have hle : 15 * 5 * (1 - σ.value) ≤
          (5 : ℝ) / 6 * (18 - 20 * σ.value) * (3 + 5 * σ.value) :=
        le_of_not_gt h
      ring_nf at hle
      nlinarith [hquad]
    _ ≤ 15 * a.value * (1 - σ.value) / (18 - 20 * σ.value) := by
      exact (div_le_div_iff_of_pos_right (cglSigma_denomB_pos σ)).mpr hmono

theorem cglClassIB_gt_fiveSixths (σ : CGLSigmaWindow)
    (a : CGLClassIExponentParameter σ) : (5 : ℝ) / 6 < cglClassIB σ a := by
  unfold cglClassIB
  rw [lt_min_iff]
  exact ⟨cglClassIB_unclamped_gt_fiveSixths σ a, by norm_num⟩

theorem cglClassIB_le_one (σ : CGLSigmaWindow)
    (a : CGLClassIExponentParameter σ) : cglClassIB σ a ≤ 1 := by
  unfold cglClassIB
  exact min_le_right _ _

theorem cglClassI_lower_power_exponent_le_middle (σ : CGLSigmaWindow)
    (a : CGLClassIExponentParameter σ) :
    2 - 2 * σ.value ≤ 1 + cglClassIB σ a * (1 - 2 * σ.value) := by
  have hneg : 1 - 2 * σ.value ≤ 0 := by
    nlinarith [σ.lower]
  have hmul := mul_le_mul_of_nonpos_right (cglClassIB_le_one σ a) hneg
  nlinarith

theorem cglClassIV_unclamped_middle_le (σ : CGLSigmaWindow) :
    1 + (15 * cglClassIV σ * (1 - σ.value) / (18 - 20 * σ.value)) *
        (1 - 2 * σ.value) ≤ 3 * cglClassIV σ * (1 - σ.value) := by
  have hD : 0 < 18 - 20 * σ.value := cglSigma_denomB_pos σ
  have hV : 0 < 3 + 5 * σ.value := cglSigma_denomV_pos σ
  have hDV : 0 < (18 - 20 * σ.value) * (3 + 5 * σ.value) := mul_pos hD hV
  have hD' : 18 - σ.value * 20 ≠ 0 := by nlinarith [hD]
  have hDV' : 54 + σ.value * 30 - σ.value ^ (2 : ℕ) * 100 ≠ 0 := by
    intro hzero
    apply hDV.ne'
    calc
      (18 - 20 * σ.value) * (3 + 5 * σ.value) =
          54 + σ.value * 30 - σ.value ^ (2 : ℕ) * 100 := by ring
      _ = 0 := hzero
  have hquad : 0 < 250 * σ.value ^ (2 : ℕ) - 375 * σ.value + 141 := by
    nlinarith [sq_nonneg (σ.value - (3 : ℝ) / 4)]
  have hnumerator :
      (18 - 20 * σ.value) * (3 + 5 * σ.value) +
        15 * 5 * (1 - σ.value) * (1 - 2 * σ.value) ≤
      15 * (1 - σ.value) * (18 - 20 * σ.value) := by
    have hid :
        15 * (1 - σ.value) * (18 - 20 * σ.value) -
          ((18 - 20 * σ.value) * (3 + 5 * σ.value) +
            15 * 5 * (1 - σ.value) * (1 - 2 * σ.value)) =
          250 * σ.value ^ (2 : ℕ) - 375 * σ.value + 141 := by ring
    apply sub_nonneg.mp
    rw [hid]
    exact hquad.le
  unfold cglClassIV
  calc
    1 + (15 * (5 / (3 + 5 * σ.value)) * (1 - σ.value) /
        (18 - 20 * σ.value)) * (1 - 2 * σ.value) =
        ((18 - 20 * σ.value) * (3 + 5 * σ.value) +
          15 * 5 * (1 - σ.value) * (1 - 2 * σ.value)) /
          ((18 - 20 * σ.value) * (3 + 5 * σ.value)) := by
          field_simp [ne_of_gt hD, ne_of_gt hV, hD']
    _ ≤ (15 * (1 - σ.value) * (18 - 20 * σ.value)) /
          ((18 - 20 * σ.value) * (3 + 5 * σ.value)) :=
      (div_le_div_iff_of_pos_right hDV).mpr hnumerator
    _ = 3 * (5 / (3 + 5 * σ.value)) * (1 - σ.value) := by
      field_simp [ne_of_gt hD, ne_of_gt hV, hD', hDV']
      ring_nf

theorem cglClassIV_unclamped_le (σ : CGLSigmaWindow)
    (a : CGLClassIExponentParameter σ) :
    15 * cglClassIV σ * (1 - σ.value) / (18 - 20 * σ.value) ≤
      15 * a.value * (1 - σ.value) / (18 - 20 * σ.value) := by
  have hfactor_pos : 0 < 15 * (1 - σ.value) := by
    nlinarith [σ.upper]
  have hmono :
      15 * cglClassIV σ * (1 - σ.value) ≤ 15 * a.value * (1 - σ.value) := by
    have h := mul_le_mul_of_nonneg_left a.lower hfactor_pos.le
    calc
      15 * cglClassIV σ * (1 - σ.value) =
          (15 * (1 - σ.value)) * cglClassIV σ := by ring
      _ ≤ (15 * (1 - σ.value)) * a.value := h
      _ = 15 * a.value * (1 - σ.value) := by ring
  exact (div_le_div_iff_of_pos_right (cglSigma_denomB_pos σ)).mpr hmono

theorem cglClassIV_twice_le (σ : CGLSigmaWindow) :
    2 - 2 * σ.value ≤ 3 * cglClassIV σ * (1 - σ.value) := by
  have hV : 0 < 3 + 5 * σ.value := cglSigma_denomV_pos σ
  have hleft : 10 * σ.value - 9 ≤ 0 := by nlinarith [σ.upper]
  have hright : σ.value - 1 ≤ 0 := by nlinarith [σ.upper]
  have hproduct : 0 ≤ (10 * σ.value - 9) * (σ.value - 1) :=
    mul_nonneg_of_nonpos_of_nonpos hleft hright
  unfold cglClassIV
  have hrewrite : 3 * (5 / (3 + 5 * σ.value)) * (1 - σ.value) =
      (15 * (1 - σ.value)) / (3 + 5 * σ.value) := by
    field_simp [ne_of_gt hV]
    ring
  rw [hrewrite, le_div_iff₀ hV]
  have hid :
      15 * (1 - σ.value) - (2 - 2 * σ.value) * (3 + 5 * σ.value) =
        (10 * σ.value - 9) * (σ.value - 1) := by ring
  apply sub_nonneg.mp
  rw [hid]
  exact hproduct

/-- The source exponent chain
`2-2σ ≤ 1+b(1-2σ) ≤ 3a(1-σ)`. -/
theorem cglClassI_middle_power_exponent_le (σ : CGLSigmaWindow)
    (a : CGLClassIExponentParameter σ) :
    1 + cglClassIB σ a * (1 - 2 * σ.value) ≤ 3 * a.value * (1 - σ.value) := by
  have hneg : 1 - 2 * σ.value ≤ 0 := by
    nlinarith [σ.lower]
  have hrightfactor : 0 ≤ 3 * (1 - σ.value) := by
    nlinarith [σ.upper]
  have hrightmono :
      3 * cglClassIV σ * (1 - σ.value) ≤ 3 * a.value * (1 - σ.value) := by
    have h := mul_le_mul_of_nonneg_left a.lower hrightfactor
    calc
      3 * cglClassIV σ * (1 - σ.value) =
          (3 * (1 - σ.value)) * cglClassIV σ := by ring
      _ ≤ (3 * (1 - σ.value)) * a.value := h
      _ = 3 * a.value * (1 - σ.value) := by ring
  unfold cglClassIB
  rcases le_total (15 * a.value * (1 - σ.value) / (18 - 20 * σ.value)) 1 with hle | hge
  · rw [min_eq_left hle]
    have hmul := mul_le_mul_of_nonpos_right (cglClassIV_unclamped_le σ a) hneg
    calc
      1 + (15 * a.value * (1 - σ.value) / (18 - 20 * σ.value)) *
          (1 - 2 * σ.value) ≤
        1 + (15 * cglClassIV σ * (1 - σ.value) / (18 - 20 * σ.value)) *
          (1 - 2 * σ.value) := by linarith
      _ ≤ 3 * cglClassIV σ * (1 - σ.value) := cglClassIV_unclamped_middle_le σ
      _ ≤ 3 * a.value * (1 - σ.value) := hrightmono
  · rw [min_eq_right hge]
    calc
      1 + 1 * (1 - 2 * σ.value) = 2 - 2 * σ.value := by ring
      _ ≤ 3 * cglClassIV σ * (1 - σ.value) := cglClassIV_twice_le σ
      _ ≤ 3 * a.value * (1 - σ.value) := hrightmono

end

end RHTower
