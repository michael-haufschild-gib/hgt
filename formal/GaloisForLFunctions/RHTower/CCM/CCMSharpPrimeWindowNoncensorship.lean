import GaloisForLFunctions.RHTower.CCM.CCMRectangularTwoEdge
import Mathlib.NumberTheory.Real.Irrational

/-!
# Sharp prime-window Mellin noncensorship

This file formalizes the unconditional Mellin geometry behind sharp moving-prime windows.
The Mellin factor of the multiplicative rectangle `[1, exp L]` is
`A_L(s - 1)`, where `A_L` is `rectangularWindowAmplitude`.  Its zeros are exactly the
nonzero integral exponential periods.  Consequently one positive width is nonvanishing
on `Re s > 1`, while two widths with irrational ratio have no common zero anywhere.

These are concrete function theorems.  No meromorphic-continuation predicate, RH
hypothesis, or target-divisor interface is used.
-/

noncomputable section

namespace RHTower

open Complex

/-- Mellin factor of the sharp multiplicative window `1_[1, exp L]`. -/
def sharpPrimeWindowMellin (L : ℝ) (s : ℂ) : ℂ :=
  rectangularWindowAmplitude L (s - 1)

@[simp] theorem sharpPrimeWindowMellin_one (L : ℝ) :
    sharpPrimeWindowMellin L 1 = L := by
  simp [sharpPrimeWindowMellin]

/-- The sharp-window Mellin factor at the shifted zeta pole.  Twice this value is
the scalar square-root counterterm coefficient. -/
theorem sharpPrimeWindowMellin_three_halves {L : ℝ} :
    sharpPrimeWindowMellin L (3 / 2 : ℂ) =
      2 * (1 - Complex.exp (-(L : ℂ) / 2)) := by
  have hw : (3 / 2 : ℂ) - 1 ≠ 0 := by norm_num
  have harg : -(L : ℂ) * ((3 / 2 : ℂ) - 1) = -(L : ℂ) / 2 := by ring
  rw [sharpPrimeWindowMellin, rectangularWindowAmplitude_eq_div hw, harg]
  norm_num [div_eq_mul_inv]
  ring

/-- Exact zero classification for the rectangular amplitude: a positive-width
amplitude vanishes precisely at a nonzero integral exponential period. -/
theorem rectangularWindowAmplitude_eq_zero_iff_period
    {L : ℝ} (hL : 0 < L) (w : ℂ) :
    rectangularWindowAmplitude L w = 0 ↔
      ∃ n : ℤ, n ≠ 0 ∧ (L : ℂ) * w = (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  constructor
  · intro hA
    have hw : w ≠ 0 := by
      intro hw
      subst w
      simp only [rectangularWindowAmplitude_zero] at hA
      exact (ne_of_gt hL) (ofReal_inj.mp hA)
    rw [rectangularWindowAmplitude_eq_div hw] at hA
    have hnum : 1 - Complex.exp (-(L : ℂ) * w) = 0 :=
      (div_eq_zero_iff.mp hA).resolve_right hw
    have hexp : Complex.exp (-(L : ℂ) * w) = 1 := (sub_eq_zero.mp hnum).symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    refine ⟨-n, ?_, ?_⟩
    · intro hneg
      have hn0 : n = 0 := by omega
      subst n
      simp only [Int.cast_zero, zero_mul] at hn
      have hL0 : (-(L : ℂ)) ≠ 0 :=
        neg_ne_zero.mpr (ofReal_ne_zero.mpr (ne_of_gt hL))
      exact hw ((mul_eq_zero.mp hn).resolve_left hL0)
    · calc
        (L : ℂ) * w = -(-(L : ℂ) * w) := by ring
        _ = -((n : ℂ) * (2 * (Real.pi : ℂ) * I)) := by rw [hn]
        _ = ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by simp
  · rintro ⟨n, hn0, hn⟩
    have hw : w ≠ 0 := by
      intro hw
      subst w
      simp only [mul_zero] at hn
      have hperiod : ((n : ℂ) * (2 * (Real.pi : ℂ) * I)) ≠ 0 :=
        mul_ne_zero (Int.cast_ne_zero.mpr hn0) Complex.two_pi_I_ne_zero
      exact hperiod hn.symm
    rw [rectangularWindowAmplitude_eq_div hw]
    apply div_eq_zero_iff.mpr
    left
    apply sub_eq_zero.mpr
    have harg : -(L : ℂ) * w = ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      calc
        -(L : ℂ) * w = -((L : ℂ) * w) := by ring
        _ = -((n : ℂ) * (2 * (Real.pi : ℂ) * I)) := by rw [hn]
        _ = ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by simp
    have hexp : Complex.exp (-(L : ℂ) * w) = 1 := by
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I (-n)
    exact hexp.symm

/-- Shifted zero classification for the sharp-window Mellin factor. -/
theorem sharpPrimeWindowMellin_eq_zero_iff_period
    {L : ℝ} (hL : 0 < L) (s : ℂ) :
    sharpPrimeWindowMellin L s = 0 ↔
      ∃ n : ℤ, n ≠ 0 ∧
        (L : ℂ) * (s - 1) = (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  exact rectangularWindowAmplitude_eq_zero_iff_period hL (s - 1)

/-- One positive-width sharp window cannot censor any coordinate strictly to the
right of the shifted critical boundary. -/
theorem sharpPrimeWindowMellin_ne_zero_of_one_lt_re
    {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 1 < s.re) :
    sharpPrimeWindowMellin L s ≠ 0 := by
  apply rectangularWindowAmplitude_ne_zero hL
  simp only [sub_re, one_re]
  linarith

/-- Positive rectangular amplitudes of irrationally related widths have no common
zero.  This is the exact two-window noncensorship mechanism. -/
theorem rectangularWindowAmplitude_pair_nonzero_of_irrational_ratio
    {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hirr : Irrational (L₁ / L₂)) (w : ℂ) :
    rectangularWindowAmplitude L₁ w ≠ 0 ∨
      rectangularWindowAmplitude L₂ w ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨n₁, hn₁, hper₁⟩ :=
    (rectangularWindowAmplitude_eq_zero_iff_period hL₁ w).mp h.1
  obtain ⟨n₂, hn₂, hper₂⟩ :=
    (rectangularWindowAmplitude_eq_zero_iff_period hL₂ w).mp h.2
  have hw : w ≠ 0 := by
    intro hw
    subst w
    simp only [mul_zero] at hper₁
    exact (mul_ne_zero (Int.cast_ne_zero.mpr hn₁) Complex.two_pi_I_ne_zero) hper₁.symm
  have hL₂c : (L₂ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hL₂)
  have hn₂c : (n₂ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn₂
  have hperiod : (2 * (Real.pi : ℂ) * I) ≠ 0 := Complex.two_pi_I_ne_zero
  have hratioC : (L₁ : ℂ) / (L₂ : ℂ) = (n₁ : ℂ) / (n₂ : ℂ) := by
    calc
      (L₁ : ℂ) / (L₂ : ℂ) = ((L₁ : ℂ) * w) / ((L₂ : ℂ) * w) := by
        field_simp
      _ = ((n₁ : ℂ) * (2 * (Real.pi : ℂ) * I)) /
          ((n₂ : ℂ) * (2 * (Real.pi : ℂ) * I)) := by rw [hper₁, hper₂]
      _ = (n₁ : ℂ) / (n₂ : ℂ) := by
        field_simp
  have hratioR : L₁ / L₂ = (n₁ : ℝ) / (n₂ : ℝ) := by
    apply Complex.ofReal_inj.mp
    rw [Complex.ofReal_div, Complex.ofReal_div]
    norm_cast at hratioC ⊢
  apply hirr.ne_rat ((n₁ : ℚ) / (n₂ : ℚ))
  rw [hratioR]
  norm_num

/-- Shifted form: two sharp-window Mellin factors of irrationally related widths
jointly see every complex coordinate. -/
theorem sharpPrimeWindowMellin_pair_nonzero_of_irrational_ratio
    {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hirr : Irrational (L₁ / L₂)) (s : ℂ) :
    sharpPrimeWindowMellin L₁ s ≠ 0 ∨ sharpPrimeWindowMellin L₂ s ≠ 0 := by
  exact rectangularWindowAmplitude_pair_nonzero_of_irrational_ratio hL₁ hL₂ hirr (s - 1)

end RHTower
