import GaloisForLFunctions.RHTower.SoninCouplingShellProduct

/-!
# The shell–dilation–shell product lies in the relative ideal

Expanding the shell product gives eight terms.  The four like-polarization ones vanish exactly: the
dilation intertwining turns the second shell into an annulus that the crossing chamber places
either entirely below the first or entirely above it, so the disjoint-shell laws apply.  The four
mixed-polarization ones are finite time-band blocks, hence generators of the ideal.

Consequently the whole product is in the ideal, and with the shell product form of the coupling so
is the coupling itself.
-/

noncomputable section


namespace RHTower

open ContinuousLinearMap

section Vanishing

variable {a b c r : ℝ}

theorem indicatorShell_forward_vanishing (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) (hcr : c ≤ r * a) :
    (evenIndicatorCutoff b - evenIndicatorCutoff a) *
        evenDilationCLM r (zero_lt_one.trans hr) *
        (evenIndicatorCutoff c - evenIndicatorCutoff b) = 0 := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hmc := evenDilationCLM_mul_evenIndicatorCutoff c r hr0
  have hmb := evenDilationCLM_mul_evenIndicatorCutoff b r hr0
  have hmove : evenDilationCLM r hr0 *
      (evenIndicatorCutoff c - evenIndicatorCutoff b) =
      (evenIndicatorCutoff (r⁻¹ * c) - evenIndicatorCutoff (r⁻¹ * b)) *
        evenDilationCLM r hr0 := by
    rw [mul_sub, hmc, hmb, sub_mul]
  have hle : r⁻¹ * c ≤ a := by
    rw [inv_mul_le_iff₀ hr0]; linarith
  have hmono : r⁻¹ * b ≤ r⁻¹ * c :=
    mul_le_mul_of_nonneg_left hbc (inv_pos.mpr hr0).le
  have hzero := evenIndicatorShell_mul_eq_zero_of_right_ceiling_le_left_floor
    a b (r⁻¹ * b) (r⁻¹ * c) hab hmono hle
  calc
    (evenIndicatorCutoff b - evenIndicatorCutoff a) *
        evenDilationCLM r hr0 *
        (evenIndicatorCutoff c - evenIndicatorCutoff b)
        = (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            (evenDilationCLM r hr0 *
              (evenIndicatorCutoff c - evenIndicatorCutoff b)) := by
          rw [mul_assoc]
    _ = ((evenIndicatorCutoff b - evenIndicatorCutoff a) *
          (evenIndicatorCutoff (r⁻¹ * c) - evenIndicatorCutoff (r⁻¹ * b))) *
            evenDilationCLM r hr0 := by rw [hmove, mul_assoc]
    _ = 0 := by rw [hzero, zero_mul]

theorem indicatorShell_inverse_vanishing (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) :
    (evenIndicatorCutoff b - evenIndicatorCutoff a) *
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
        (evenIndicatorCutoff c - evenIndicatorCutoff b) = 0 := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have hmc := evenDilationCLM_mul_evenIndicatorCutoff c r⁻¹ hrinv
  have hmb := evenDilationCLM_mul_evenIndicatorCutoff b r⁻¹ hrinv
  rw [inv_inv] at hmc hmb
  have hmove : evenDilationCLM r⁻¹ hrinv *
      (evenIndicatorCutoff c - evenIndicatorCutoff b) =
      (evenIndicatorCutoff (r * c) - evenIndicatorCutoff (r * b)) *
        evenDilationCLM r⁻¹ hrinv := by
    rw [mul_sub, hmc, hmb, sub_mul]
  have hbrb : b ≤ r * b := le_mul_of_one_le_left hb0.le hr.le
  have hmono : r * b ≤ r * c := mul_le_mul_of_nonneg_left hbc hr0.le
  have hzero := evenIndicatorShell_mul_eq_zero_of_left_ceiling_le_right_floor
    a b (r * b) (r * c) hab hmono hbrb
  calc
    (evenIndicatorCutoff b - evenIndicatorCutoff a) *
        evenDilationCLM r⁻¹ hrinv *
        (evenIndicatorCutoff c - evenIndicatorCutoff b)
        = (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            (evenDilationCLM r⁻¹ hrinv *
              (evenIndicatorCutoff c - evenIndicatorCutoff b)) := by
          rw [mul_assoc]
    _ = ((evenIndicatorCutoff b - evenIndicatorCutoff a) *
          (evenIndicatorCutoff (r * c) - evenIndicatorCutoff (r * b))) *
            evenDilationCLM r⁻¹ hrinv := by rw [hmove, mul_assoc]
    _ = 0 := by rw [hzero, zero_mul]

theorem fourierShell_forward_vanishing (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) :
    (evenFourierCutoff b - evenFourierCutoff a) *
        evenDilationCLM r (zero_lt_one.trans hr) *
        (evenFourierCutoff c - evenFourierCutoff b) = 0 := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have hmc := evenDilationCLM_mul_evenFourierCutoff c r hr0
  have hmb := evenDilationCLM_mul_evenFourierCutoff b r hr0
  have hmove : evenDilationCLM r hr0 *
      (evenFourierCutoff c - evenFourierCutoff b) =
      (evenFourierCutoff (r * c) - evenFourierCutoff (r * b)) *
        evenDilationCLM r hr0 := by
    rw [mul_sub, hmc, hmb, sub_mul]
  have hbrb : b ≤ r * b := le_mul_of_one_le_left hb0.le hr.le
  have hmono : r * b ≤ r * c := mul_le_mul_of_nonneg_left hbc hr0.le
  have hzero := evenFourierShell_mul_eq_zero_of_left_ceiling_le_right_floor
    a b (r * b) (r * c) hab hmono hbrb
  calc
    (evenFourierCutoff b - evenFourierCutoff a) *
        evenDilationCLM r hr0 *
        (evenFourierCutoff c - evenFourierCutoff b)
        = (evenFourierCutoff b - evenFourierCutoff a) *
            (evenDilationCLM r hr0 *
              (evenFourierCutoff c - evenFourierCutoff b)) := by rw [mul_assoc]
    _ = ((evenFourierCutoff b - evenFourierCutoff a) *
          (evenFourierCutoff (r * c) - evenFourierCutoff (r * b))) *
            evenDilationCLM r hr0 := by rw [hmove, mul_assoc]
    _ = 0 := by rw [hzero, zero_mul]

theorem fourierShell_inverse_vanishing (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) (hcr : c ≤ r * a) :
    (evenFourierCutoff b - evenFourierCutoff a) *
        evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) *
        (evenFourierCutoff c - evenFourierCutoff b) = 0 := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have hmc := evenDilationCLM_mul_evenFourierCutoff c r⁻¹ hrinv
  have hmb := evenDilationCLM_mul_evenFourierCutoff b r⁻¹ hrinv
  have hmove : evenDilationCLM r⁻¹ hrinv *
      (evenFourierCutoff c - evenFourierCutoff b) =
      (evenFourierCutoff (r⁻¹ * c) - evenFourierCutoff (r⁻¹ * b)) *
        evenDilationCLM r⁻¹ hrinv := by
    rw [mul_sub, hmc, hmb, sub_mul]
  have hle : r⁻¹ * c ≤ a := by
    rw [inv_mul_le_iff₀ hr0]; linarith
  have hmono : r⁻¹ * b ≤ r⁻¹ * c :=
    mul_le_mul_of_nonneg_left hbc hrinv.le
  have hzero := evenFourierShell_mul_eq_zero_of_right_ceiling_le_left_floor
    a b (r⁻¹ * b) (r⁻¹ * c) hab hmono hle
  calc
    (evenFourierCutoff b - evenFourierCutoff a) *
        evenDilationCLM r⁻¹ hrinv *
        (evenFourierCutoff c - evenFourierCutoff b)
        = (evenFourierCutoff b - evenFourierCutoff a) *
            (evenDilationCLM r⁻¹ hrinv *
              (evenFourierCutoff c - evenFourierCutoff b)) := by rw [mul_assoc]
    _ = ((evenFourierCutoff b - evenFourierCutoff a) *
          (evenFourierCutoff (r⁻¹ * c) - evenFourierCutoff (r⁻¹ * b))) *
            evenDilationCLM r⁻¹ hrinv := by rw [hmove, mul_assoc]
    _ = 0 := by rw [hzero, zero_mul]

end Vanishing

end RHTower

namespace RHTower

open ContinuousLinearMap

section Assembly

variable {a b c r : ℝ}

private theorem mixed_indicator_fourier_mem (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x) :
    IsSoninPrincipalRelativeIdeal
      ((evenIndicatorCutoff b - evenIndicatorCutoff a) *
        evenDilationCLM x hx * (evenFourierCutoff c - evenFourierCutoff b)) := by
  have hmc := evenDilationCLM_mul_evenFourierCutoff c x hx
  have hmb := evenDilationCLM_mul_evenFourierCutoff b x hx
  have hmove : evenDilationCLM x hx *
      (evenFourierCutoff c - evenFourierCutoff b) =
      (evenFourierCutoff (x * c) - evenFourierCutoff (x * b)) *
        evenDilationCLM x hx := by
    rw [mul_sub, hmc, hmb, sub_mul]
  have hblock := evenIndicatorDiff_mul_evenFourierDiff_mem_principalRelativeIdeal
    b a (x * c) (x * b) hb ha
  apply (hblock.rightMul (evenDilationCLM x hx)).of_eq
  calc
    (evenIndicatorCutoff b - evenIndicatorCutoff a) *
        (evenFourierCutoff (x * c) - evenFourierCutoff (x * b)) *
        evenDilationCLM x hx
        = (evenIndicatorCutoff b - evenIndicatorCutoff a) *
            ((evenFourierCutoff (x * c) - evenFourierCutoff (x * b)) *
              evenDilationCLM x hx) := by rw [mul_assoc]
    _ = (evenIndicatorCutoff b - evenIndicatorCutoff a) *
          (evenDilationCLM x hx *
            (evenFourierCutoff c - evenFourierCutoff b)) := by rw [hmove]
    _ = (evenIndicatorCutoff b - evenIndicatorCutoff a) *
          evenDilationCLM x hx *
          (evenFourierCutoff c - evenFourierCutoff b) := by rw [mul_assoc]

private theorem mixed_fourier_indicator_mem (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 < x) :
    IsSoninPrincipalRelativeIdeal
      ((evenFourierCutoff b - evenFourierCutoff a) *
        evenDilationCLM x hx *
        (evenIndicatorCutoff c - evenIndicatorCutoff b)) := by
  have hmc := evenDilationCLM_mul_evenIndicatorCutoff c x hx
  have hmb := evenDilationCLM_mul_evenIndicatorCutoff b x hx
  have hmove : evenDilationCLM x hx *
      (evenIndicatorCutoff c - evenIndicatorCutoff b) =
      (evenIndicatorCutoff (x⁻¹ * c) - evenIndicatorCutoff (x⁻¹ * b)) *
        evenDilationCLM x hx := by
    rw [mul_sub, hmc, hmb, sub_mul]
  have hblock := evenFourierDiff_mul_evenIndicatorDiff_mem_principalRelativeIdeal
    b a (x⁻¹ * c) (x⁻¹ * b) hb ha
  apply (hblock.rightMul (evenDilationCLM x hx)).of_eq
  calc
    (evenFourierCutoff b - evenFourierCutoff a) *
        (evenIndicatorCutoff (x⁻¹ * c) - evenIndicatorCutoff (x⁻¹ * b)) *
        evenDilationCLM x hx
        = (evenFourierCutoff b - evenFourierCutoff a) *
            ((evenIndicatorCutoff (x⁻¹ * c) - evenIndicatorCutoff (x⁻¹ * b)) *
              evenDilationCLM x hx) := by rw [mul_assoc]
    _ = (evenFourierCutoff b - evenFourierCutoff a) *
          (evenDilationCLM x hx *
            (evenIndicatorCutoff c - evenIndicatorCutoff b)) := by rw [hmove]
    _ = (evenFourierCutoff b - evenFourierCutoff a) *
          evenDilationCLM x hx *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) := by rw [mul_assoc]

/-- **The shell product lies in the relative ideal.**  Four of the eight terms vanish exactly by
disjointness in the crossing chamber, and the other four are finite time-band blocks. -/
theorem evenTwoPolarizationShell_mul_evenDilationSum_mul_shell_mem_ideal
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hbc : b ≤ c)
    (hr : 1 < r) (hcr : c ≤ r * a) :
    IsSoninPrincipalRelativeIdeal
      (evenTwoPolarizationShell a b * evenDilationSum r hr *
        evenTwoPolarizationShell b c) := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have v1 := indicatorShell_forward_vanishing hab hbc hr hcr
  have v2 := indicatorShell_inverse_vanishing ha hab hbc hr
  have v3 := fourierShell_forward_vanishing ha hab hbc hr
  have v4 := fourierShell_inverse_vanishing hab hbc hr hcr
  have m1 := mixed_indicator_fourier_mem (c := c) ha hb hr0
  have m2 := mixed_indicator_fourier_mem (c := c) ha hb hrinv
  have m3 := mixed_fourier_indicator_mem (c := c) ha hb hr0
  have m4 := mixed_fourier_indicator_mem (c := c) ha hb hrinv
  apply (((m1.add m2).add m3).add m4).of_eq
  rw [evenDilationSum_eq]
  unfold evenTwoPolarizationShell
  have hexpand :
      ((evenIndicatorCutoff b - evenIndicatorCutoff a) +
          (evenFourierCutoff b - evenFourierCutoff a)) *
        (evenDilationCLM r hr0 + evenDilationCLM r⁻¹ hrinv) *
        ((evenIndicatorCutoff c - evenIndicatorCutoff b) +
          (evenFourierCutoff c - evenFourierCutoff b)) =
      ((evenIndicatorCutoff b - evenIndicatorCutoff a) * evenDilationCLM r hr0 *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenIndicatorCutoff b - evenIndicatorCutoff a) *
          evenDilationCLM r⁻¹ hrinv *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) * evenDilationCLM r hr0 *
          (evenFourierCutoff c - evenFourierCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) *
          evenDilationCLM r⁻¹ hrinv *
          (evenFourierCutoff c - evenFourierCutoff b)) +
      ((evenIndicatorCutoff b - evenIndicatorCutoff a) * evenDilationCLM r hr0 *
          (evenFourierCutoff c - evenFourierCutoff b) +
        (evenIndicatorCutoff b - evenIndicatorCutoff a) *
          evenDilationCLM r⁻¹ hrinv *
          (evenFourierCutoff c - evenFourierCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) * evenDilationCLM r hr0 *
          (evenIndicatorCutoff c - evenIndicatorCutoff b) +
        (evenFourierCutoff b - evenFourierCutoff a) *
          evenDilationCLM r⁻¹ hrinv *
          (evenIndicatorCutoff c - evenIndicatorCutoff b)) := by
    -- Keep each shell intact while distributing the two dilation branches.
    simp only [mul_add, add_mul]
    abel
  rw [hexpand, v1, v2, v3, v4]
  abel

end Assembly

end RHTower

namespace RHTower

open ContinuousLinearMap

/-- **The layer coupling lies in the relative ideal.**  Combining the shell product form with the
disjointness expansion: the coupling is congruent to the shell product, which is itself in the
ideal.  This strengthens the coupling's Hilbert--Schmidt property to membership in the concrete
Schatten-1 ideal of the construction. -/
theorem evenSoninApertureSuccessiveLayerTransition_mem_principalRelativeIdeal
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (hcr : c ≤ r * a) :
    IsSoninPrincipalRelativeIdeal
      (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  have hcong := isSoninPrincipalRelativeIdeal_coupling_sub_shellProduct
    ha hb hc hab hbc hr
  have hprod := evenTwoPolarizationShell_mul_evenDilationSum_mul_shell_mem_ideal
    ha hb hab hbc hr hcr
  apply (hcong.add hprod).of_eq
  abel

end RHTower
