import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.XiContourBounds
import GaloisForLFunctions.RHTower.XiMassHeightTransfer

/-!
# Explicit relative error for the symmetric ξ-zero mass

The quarter-contour remainder is `10T + 100 log T`. A closed-form height
absorbs it into any prescribed relative error. Monotonicity transfers the bound
from admissible contours to every height, including zero ordinates.
-/

open Complex Filter Topology intervalIntegral MeasureTheory Set Metric

noncomputable section
namespace RHTower

/-- A numerical remainder for the symmetric ξ-divisor mass on admissible contours. -/
theorem abs_xiSymmetricMass_sub_main_le_ten_mul_add_hundred_log {T : ℝ} (hT : 4 ≤ T)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    |(xiSymmetricMass T : ℝ) - (1 / Real.pi) * (T * Real.log T)|
      ≤ 10 * T + 100 * Real.log T := by
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  let V : ℝ := ∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re
  let H : ℝ := ∫ x in (1 / 2 : ℝ)..2, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im
  have hv : |V - (1 / 2) * (T * Real.log T)| ≤ 10 * T :=
    abs_vertical_xi_sub_half_mul_log_le hT
  have hh : |H| ≤ 100 * Real.log T := abs_horizontal_xi_le_hundred_log hT hne
  have hmass := two_pi_mul_xiSymmetricMass hT0.le hne
  change 2 * Real.pi * (xiSymmetricMass T : ℝ) = 4 * V - 4 * H at hmass
  have heq : (xiSymmetricMass T : ℝ) - (1 / Real.pi) * (T * Real.log T) =
      (2 / Real.pi) * (V - (1 / 2) * (T * Real.log T) - H) := by
    field_simp
    linarith [hmass]
  have hscale0 : 0 < 2 / Real.pi := by positivity
  have hscale : 2 / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  rw [heq, abs_mul, abs_of_pos hscale0]
  calc
    _ ≤ (2 / Real.pi) * (|V - (1 / 2) * (T * Real.log T)| + |H|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hscale0.le
    _ ≤ (2 / Real.pi) * (10 * T + 100 * Real.log T) := by gcongr
    _ ≤ 10 * T + 100 * Real.log T := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hscale (by positivity : 0 ≤ 10 * T + 100 * Real.log T)

/-- An explicit height for relative zero-mass error on admissible contours. -/
def xiAdmissibleMassHeight (ε : ℝ) : ℝ :=
  max (max 4 (Real.exp (20 / ε))) (200 / ε)

theorem four_le_xiAdmissibleMassHeight (ε : ℝ) : 4 ≤ xiAdmissibleMassHeight ε :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem xiSymmetricMass_admissible_close_explicit {ε T : ℝ} (hε : 0 < ε)
    (hT : xiAdmissibleMassHeight ε ≤ T)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    |(xiSymmetricMass T : ℝ) - (1 / Real.pi) * (T * Real.log T)|
      ≤ ε * (T * Real.log T) := by
  have hT4 : 4 ≤ T := (four_le_xiAdmissibleMassHeight ε).trans hT
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hexp : Real.exp (20 / ε) ≤ T :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hlarge : 200 / ε ≤ T := (le_max_right _ _).trans hT
  have hlog : 20 / ε ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr hexp
  rw [div_le_iff₀ hε] at hlog hlarge
  have hv : 10 * T ≤ ε / 2 * (T * Real.log T) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hT0.le]
  have hh : 100 * Real.log T ≤ ε / 2 * (T * Real.log T) := by
    nlinarith [mul_le_mul_of_nonneg_right hlarge hlog0]
  exact (abs_xiSymmetricMass_sub_main_le_ten_mul_add_hundred_log hT4 hne).trans (by linarith)

/-- An explicit height for relative symmetric zero-mass error, including zero ordinates. -/
def xiMassHeight (ε : ℝ) : ℝ :=
  max (max (xiAdmissibleMassHeight (ε / 2) + 1)
    (3 / (Real.pi * (ε / 2)) + 3)) 8

theorem four_le_xiMassHeight (ε : ℝ) : 4 ≤ xiMassHeight ε :=
  (by norm_num : (4 : ℝ) ≤ 8).trans (le_max_right _ _)

/-- The relative symmetric zero-mass error is explicit at every height. -/
theorem xiSymmetricMass_close_explicit {ε T : ℝ} (hε : 0 < ε)
    (hT : xiMassHeight ε ≤ T) :
    |(xiSymmetricMass T : ℝ) - (1 / Real.pi) * (T * Real.log T)|
      ≤ ε * (T * Real.log T) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set P : ℝ := 1 / Real.pi with hPdef
  have hP : (0 : ℝ) < P := by rw [hPdef]; positivity
  have hPpi : P * Real.pi = 1 := by rw [hPdef]; field_simp
  set ε₁ : ℝ := ε / 2 with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  let Ta := xiAdmissibleMassHeight ε₁
  have hTa4 : 4 ≤ Ta := four_le_xiAdmissibleMassHeight ε₁
  have hadm : ∀ U : ℝ, Ta ≤ U →
      (∀ x : ℝ, xi ((x : ℂ) + (U : ℂ) * I) ≠ 0) →
      |(xiSymmetricMass U : ℝ) - (1 / Real.pi) * (U * Real.log U)|
        ≤ ε₁ * (U * Real.log U) :=
    fun _ hU hne => xiSymmetricMass_admissible_close_explicit hε₁ hU hne
  change max (max (Ta + 1) (3 / (Real.pi * ε₁) + 3)) 8 ≤ T at hT
  have hT8 : (8 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTa1 : Ta + 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTthr : 3 / (Real.pi * ε₁) + 3 ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hTlog : (0 : ℝ) < T * Real.log T := by positivity
  have hεrel : ε₁ * (T * Real.log T) + ε₁ * (T * Real.log T) = ε * (T * Real.log T) := by
    rw [hε₁def]; ring
  -- the threshold inequality
  have hkey : (P + ε₁) * (Real.log T + 2) ≤ ε₁ * (T * Real.log T) := by
    have h3 : Real.log T + 2 ≤ 3 * Real.log T := by linarith
    have hthr : 3 * (P + ε₁) ≤ ε₁ * T := by
      have hb : 3 / (Real.pi * ε₁) ≤ T - 3 := by linarith
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi * ε₁)] at hb
      have h3pi : 3 * P ≤ (T - 3) * ε₁ := by
        have hmul : (3 * P) * Real.pi ≤ ((T - 3) * ε₁) * Real.pi := by
          rw [show (3 * P) * Real.pi = 3 * (P * Real.pi) by ring, hPpi, mul_one,
            show ((T - 3) * ε₁) * Real.pi = (T - 3) * (Real.pi * ε₁) by ring]
          exact hb
        exact le_of_mul_le_mul_right hmul hπ
      linarith
    calc (P + ε₁) * (Real.log T + 2)
        ≤ (P + ε₁) * (3 * Real.log T) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (3 * (P + ε₁)) * Real.log T := by ring
      _ ≤ (ε₁ * T) * Real.log T := mul_le_mul_of_nonneg_right hthr (by linarith)
      _ = ε₁ * (T * Real.log T) := by ring
  -- upper bound via an admissible height just above T
  obtain ⟨T₂, hT₂mem, hT₂adm⟩ := exists_admissible_height (a := T) (b := T + 1) (by linarith)
  obtain ⟨T₃, hT₃mem, hT₃adm⟩ := exists_admissible_height (a := T - 1) (b := T) (by linarith)
  have hupper : (xiSymmetricMass T : ℝ) ≤ P * (T * Real.log T)
      + ε * (T * Real.log T) := by
    have hmono : xiSymmetricMass T ≤ xiSymmetricMass T₂ :=
      xiSymmetricMass_mono hT0.le hT₂mem.1.le
    have hmono' : (xiSymmetricMass T : ℝ) ≤ (xiSymmetricMass T₂ : ℝ) := by exact_mod_cast hmono
    have hb := hadm T₂ (by linarith [hT₂mem.1]) hT₂adm
    rw [abs_le, ← hPdef] at hb
    have hT₂log : T₂ * Real.log T₂ ≤ (T + 1) * Real.log (T + 1) :=
      mul_log_mono (by linarith [hT₂mem.1]) hT₂mem.2.le
    have hT₂log' : (T + 1) * Real.log (T + 1) ≤ T * Real.log T + Real.log T + 2 :=
      succ_mul_log_le (by linarith)
    have hcoef : (P + ε₁) * (T₂ * Real.log T₂)
        ≤ (P + ε₁) * (T * Real.log T + Real.log T + 2) :=
      mul_le_mul_of_nonneg_left (le_trans hT₂log hT₂log') (by positivity)
    linarith [hmono', hb.2, hcoef, hkey, hεrel]
  have hlower : P * (T * Real.log T) - ε * (T * Real.log T)
      ≤ (xiSymmetricMass T : ℝ) := by
    have hmono : xiSymmetricMass T₃ ≤ xiSymmetricMass T :=
      xiSymmetricMass_mono (by linarith [hT₃mem.1]) hT₃mem.2.le
    have hmono' : (xiSymmetricMass T₃ : ℝ) ≤ (xiSymmetricMass T : ℝ) := by exact_mod_cast hmono
    have hb := hadm T₃ (by linarith [hT₃mem.1]) hT₃adm
    rw [abs_le, ← hPdef] at hb
    have hT₃low : T * Real.log T - Real.log T - 2 ≤ T₃ * Real.log T₃ := by
      refine le_trans (pred_mul_log_ge (by linarith)) ?_
      exact mul_log_mono (by linarith [hT₃mem.1]) hT₃mem.1.le
    have hT₃high : T₃ * Real.log T₃ ≤ T * Real.log T :=
      mul_log_mono (by linarith [hT₃mem.1]) hT₃mem.2.le
    have hcoef : P * (T * Real.log T - Real.log T - 2)
        ≤ P * (T₃ * Real.log T₃) :=
      mul_le_mul_of_nonneg_left hT₃low (by positivity)
    have hcoef2 : ε₁ * (T₃ * Real.log T₃) ≤ ε₁ * (T * Real.log T) :=
      mul_le_mul_of_nonneg_left hT₃high hε₁.le
    have hslack : (0 : ℝ) ≤ ε₁ * Real.log T := by positivity
    linarith [hmono', hb.1, hcoef, hcoef2, hkey, hslack, hεrel]
  rw [abs_le]
  constructor <;> linarith

#print axioms xiSymmetricMass_admissible_close_explicit
#print axioms xiSymmetricMass_close_explicit

end RHTower
