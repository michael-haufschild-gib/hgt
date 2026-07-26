/-
# Exact interval localization for the double large sieve

This file replaces a one-dimensional additive character by its exact
average over a short normalized interval.  The reciprocal multiplier is
well-defined and has an explicit norm bound whenever the frequency lies
in the prescribed range.  These lemmas are the coordinatewise input to
the Bombieri--Iwaniec double large sieve.
-/
import GaloisForLFunctions.RHTower.BourgainFejerSpacing
import GaloisForLFunctions.RHTower.BourgainGaussianFourier
import GaloisForLFunctions.RHTower.BourgainSquareRootQuadraticModel

open MeasureTheory

namespace RHTower

noncomputable section

/-- Half-width used for interval localization at frequency scale `Y`. -/
def bourgainLocalizationEpsilon (Y : ℝ) : ℝ :=
  1 / (8 * Y)

/-- Exact normalized interval formula for an additive character. -/
theorem bourgain_normalizedIntervalCharacterIntegral
    (x ε L y : ℝ) (hL : 0 < L) :
    (∫ z in ((x - ε) / L)..((x + ε) / L),
        bourgainUnitCharacter ((L * y) * z)) =
      ((L : ℂ)⁻¹ *
        (bourgainUnitCharacter (x * y) *
          bourgainIntervalCharacterIntegral (2 * ε) y)) := by
  have hfun :
      (fun z : ℝ => bourgainUnitCharacter ((L * y) * z)) =
        fun z : ℝ => bourgainUnitCharacter (y * (L * z)) := by
    funext z
    congr 1
    ring
  rw [hfun]
  rw [intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => bourgainUnitCharacter (y * t)) hL.ne']
  have hlower : L * ((x - ε) / L) = x - ε := by
    field_simp [hL.ne']
  have hupper : L * ((x + ε) / L) = x + ε := by
    field_simp [hL.ne']
  rw [hlower, hupper]
  have htranslate :=
    intervalIntegral.integral_comp_add_right
      (fun t : ℝ => bourgainUnitCharacter (y * t)) x
      (a := -ε) (b := ε)
  rw [show -ε + x = x - ε by ring,
    show ε + x = x + ε by ring] at htranslate
  rw [← htranslate]
  have hadd (t : ℝ) :
      bourgainUnitCharacter (y * (t + x)) =
        bourgainUnitCharacter (x * y) *
          bourgainUnitCharacter (y * t) := by
    rw [show y * (t + x) = x * y + y * t by ring,
      bourgainUnitCharacter_add]
  simp_rw [hadd]
  rw [intervalIntegral.integral_const_mul]
  unfold bourgainIntervalCharacterIntegral
  rw [Complex.real_smul]
  push_cast
  ring_nf

/-- The centered character integral stays uniformly away from zero on
the prescribed frequency interval. -/
theorem bourgain_intervalCharacter_norm_lower
    {Y y : ℝ} (hY : 0 < Y) (hy : |y| ≤ Y) :
    1 / (2 * Real.pi * Y) ≤
      ‖bourgainIntervalCharacterIntegral
        (2 * bourgainLocalizationEpsilon Y) y‖ := by
  have harg :
      |Real.pi * (2 * bourgainLocalizationEpsilon Y) * y| ≤
        Real.pi / 2 := by
    unfold bourgainLocalizationEpsilon
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    have hscale : |2 * (1 / (8 * Y))| = 1 / (4 * Y) := by
      rw [abs_of_pos]
      · field_simp [hY.ne']
        ring
      · positivity
    rw [hscale]
    have hmul :=
      mul_le_mul_of_nonneg_left hy
        (by positivity : 0 ≤ 1 / (4 * Y))
    have hcalc : (1 / (4 * Y)) * Y = (1 / 4 : ℝ) := by
      field_simp [hY.ne']
    rw [hcalc] at hmul
    nlinarith [Real.pi_pos]
  have hsinc :
      2 / Real.pi ≤
        |Real.sinc
          (Real.pi * (2 * bourgainLocalizationEpsilon Y) * y)| := by
    let u : ℝ :=
      Real.pi * (2 * bourgainLocalizationEpsilon Y) * y
    by_cases hu : u = 0
    · rw [show
          Real.pi * (2 * bourgainLocalizationEpsilon Y) * y = 0
          from hu,
        Real.sinc_zero, abs_one]
      exact (div_le_one Real.pi_pos).2 Real.two_le_pi
    · rw [Real.sinc_of_ne_zero hu, abs_div]
      have hu0 : 0 < |u| := abs_pos.mpr hu
      have hjordan :=
        Real.mul_abs_le_abs_sin
          (show |u| ≤ Real.pi / 2 by exact harg)
      exact (le_div_iff₀ hu0).2 (by
        simpa [u, mul_assoc] using hjordan)
  rw [bourgainIntervalCharacterIntegral_eq]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have heps :
      2 * bourgainLocalizationEpsilon Y = 1 / (4 * Y) := by
    unfold bourgainLocalizationEpsilon
    field_simp [hY.ne']
    ring
  rw [abs_of_pos (show
    0 < 2 * bourgainLocalizationEpsilon Y by
      unfold bourgainLocalizationEpsilon
      positivity)]
  calc
    1 / (2 * Real.pi * Y) =
        (2 * bourgainLocalizationEpsilon Y) *
          (2 / Real.pi) := by
      rw [heps]
      field_simp [Real.pi_ne_zero, hY.ne']
      ring
    _ ≤ (2 * bourgainLocalizationEpsilon Y) *
        |Real.sinc
          (Real.pi * (2 * bourgainLocalizationEpsilon Y) * y)| :=
      mul_le_mul_of_nonneg_left hsinc (by
        unfold bourgainLocalizationEpsilon
        positivity)

/-- Reciprocal multiplier which recovers the central character from its
normalized short-interval average. -/
def bourgainLocalizationMultiplier
    (Y L y : ℝ) : ℂ :=
  (L : ℂ) *
    (bourgainIntervalCharacterIntegral
      (2 * bourgainLocalizationEpsilon Y) y)⁻¹

theorem norm_bourgainLocalizationMultiplier_le
    {Y L y : ℝ} (hY : 0 < Y) (hL : 0 < L)
    (hy : |y| ≤ Y) :
    ‖bourgainLocalizationMultiplier Y L y‖ ≤
      2 * Real.pi * Y * L := by
  have hlower :=
    bourgain_intervalCharacter_norm_lower hY hy
  unfold bourgainLocalizationMultiplier
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hL]
  have hden : 0 < 1 / (2 * Real.pi * Y) := by positivity
  have hnormpos :
      0 < ‖bourgainIntervalCharacterIntegral
        (2 * bourgainLocalizationEpsilon Y) y‖ :=
    lt_of_lt_of_le hden hlower
  have hinv := (inv_le_inv₀ hnormpos hden).2 hlower
  have hcalc :
      (1 / (2 * Real.pi * Y))⁻¹ =
        2 * Real.pi * Y := by
    field_simp [Real.pi_ne_zero, hY.ne']
  rw [hcalc] at hinv
  nlinarith

/-- Exact one-dimensional recovery identity. -/
theorem bourgain_recover_character_from_interval
    {Y L x y : ℝ} (hY : 0 < Y) (hL : 0 < L)
    (hy : |y| ≤ Y) :
    bourgainLocalizationMultiplier Y L y *
        (∫ z in
          ((x - bourgainLocalizationEpsilon Y) / L)..
          ((x + bourgainLocalizationEpsilon Y) / L),
          bourgainUnitCharacter ((L * y) * z)) =
      bourgainUnitCharacter (x * y) := by
  rw [bourgain_normalizedIntervalCharacterIntegral x
    (bourgainLocalizationEpsilon Y) L y hL]
  have hlower :=
    bourgain_intervalCharacter_norm_lower hY hy
  have hpos : 0 <
      ‖bourgainIntervalCharacterIntegral
        (2 * bourgainLocalizationEpsilon Y) y‖ := by
    have hbase : 0 < 1 / (2 * Real.pi * Y) := by
      positivity
    exact lt_of_lt_of_le hbase hlower
  have hI :
      bourgainIntervalCharacterIntegral
        (2 * bourgainLocalizationEpsilon Y) y ≠ 0 :=
    norm_ne_zero_iff.mp hpos.ne'
  have hLc : (L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hL.ne'
  unfold bourgainLocalizationMultiplier
  field_simp

end

end RHTower
