import GaloisForLFunctions.HTGeometry.BohrUniqueness

/-!
# Cauchy–Schwarz for the Bohr mean

Expanding `0 ≤ M(|h - z k|²)` in `z` and optimizing gives

`‖M(h · conj k)‖² ≤ M(|h|²) · M(|k|²)`.

The degenerate case `M(|k|²) = 0` is handled by the positivity lemma: it forces `k = 0`.
-/

open MeasureTheory ComplexConjugate

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

variable {h k : ℝ → ℂ} (hhc : Continuous h) (hha : IsBohrAlmostPeriodic h)
  (hkc : Continuous k) (hka : IsBohrAlmostPeriodic k)

include hhc hha hkc hka in
/-- The expansion of the mean square of `h - z k`. -/
theorem bohrMean_sub_smul_mul_conj (z : ℂ) :
    bohrMean (fun t => (h t - z * k t) * conj (h t - z * k t))
      = bohrMean (fun t => h t * conj (h t)) - conj z * bohrMean (fun t => h t * conj (k t))
        - z * bohrMean (fun t => k t * conj (h t))
        + z * conj z * bohrMean (fun t => k t * conj (k t)) := by
  have hch : Continuous fun t : ℝ => conj (h t) := Complex.continuous_conj.comp hhc
  have hah : IsBohrAlmostPeriodic fun t : ℝ => conj (h t) := isBohrAlmostPeriodic_conj hha
  have hck : Continuous fun t : ℝ => conj (k t) := Complex.continuous_conj.comp hkc
  have hak : IsBohrAlmostPeriodic fun t : ℝ => conj (k t) := isBohrAlmostPeriodic_conj hka
  have hhh : Continuous fun t : ℝ => h t * conj (h t) := hhc.mul hch
  have hhha : IsBohrAlmostPeriodic fun t : ℝ => h t * conj (h t) :=
    isBohrAlmostPeriodic_mul hhc hha hch hah
  have hhk : Continuous fun t : ℝ => h t * conj (k t) := hhc.mul hck
  have hhka : IsBohrAlmostPeriodic fun t : ℝ => h t * conj (k t) :=
    isBohrAlmostPeriodic_mul hhc hha hck hak
  have hkh : Continuous fun t : ℝ => k t * conj (h t) := hkc.mul hch
  have hkha : IsBohrAlmostPeriodic fun t : ℝ => k t * conj (h t) :=
    isBohrAlmostPeriodic_mul hkc hka hch hah
  have hkk : Continuous fun t : ℝ => k t * conj (k t) := hkc.mul hck
  have hkka : IsBohrAlmostPeriodic fun t : ℝ => k t * conj (k t) :=
    isBohrAlmostPeriodic_mul hkc hka hck hak
  have hexpand : (fun t : ℝ => (h t - z * k t) * conj (h t - z * k t))
      = fun t : ℝ => (h t * conj (h t) - conj z * (h t * conj (k t)))
        - (z * (k t * conj (h t)) - z * conj z * (k t * conj (k t))) := by
    funext t
    rw [map_sub, map_mul]
    ring
  rw [hexpand,
    bohrMean_sub (f := fun t : ℝ => h t * conj (h t) - conj z * (h t * conj (k t)))
      (g := fun t : ℝ => z * (k t * conj (h t)) - z * conj z * (k t * conj (k t)))
      (hhh.sub (continuous_const.mul hhk))
      (isBohrAlmostPeriodic_sub hhh hhha (continuous_const.mul hhk)
        (isBohrAlmostPeriodic_const_mul _ hhka))
      ((continuous_const.mul hkh).sub (continuous_const.mul hkk))
      (isBohrAlmostPeriodic_sub (continuous_const.mul hkh)
        (isBohrAlmostPeriodic_const_mul _ hkha) (continuous_const.mul hkk)
        (isBohrAlmostPeriodic_const_mul _ hkka)),
    bohrMean_sub (f := fun t : ℝ => h t * conj (h t)) (g := fun t : ℝ => conj z * (h t * conj (k t)))
      hhh hhha (continuous_const.mul hhk) (isBohrAlmostPeriodic_const_mul _ hhka),
    bohrMean_sub (f := fun t : ℝ => z * (k t * conj (h t)))
      (g := fun t : ℝ => z * conj z * (k t * conj (k t)))
      (continuous_const.mul hkh) (isBohrAlmostPeriodic_const_mul _ hkha)
      (continuous_const.mul hkk) (isBohrAlmostPeriodic_const_mul _ hkka),
    bohrMean_const_mul (f := fun t : ℝ => h t * conj (k t)) _ hhk hhka,
    bohrMean_const_mul (f := fun t : ℝ => k t * conj (h t)) _ hkh hkha,
    bohrMean_const_mul (f := fun t : ℝ => k t * conj (k t)) _ hkk hkka]
  ring

include hhc hha hkc hka in
/-- **Cauchy–Schwarz for the Bohr mean.** -/
theorem norm_bohrMean_mul_conj_sq_le :
    ‖bohrMean (fun t => h t * conj (k t))‖ ^ (2 : ℕ)
      ≤ (bohrMean (fun t => h t * conj (h t))).re * (bohrMean (fun t => k t * conj (k t))).re := by
  set A : ℝ := (bohrMean (fun t => h t * conj (h t))).re with hA
  set B : ℝ := (bohrMean (fun t => k t * conj (k t))).re with hB
  set C : ℂ := bohrMean (fun t => h t * conj (k t)) with hC
  have hAnonneg : 0 ≤ A := bohrMean_mul_conj_re_nonneg hhc hha
  have hBnonneg : 0 ≤ B := bohrMean_mul_conj_re_nonneg hkc hka
  have hCconj : bohrMean (fun t => k t * conj (h t)) = conj C := by
    have hfun : (fun t : ℝ => conj (h t * conj (k t))) = fun t : ℝ => k t * conj (h t) := by
      funext t
      rw [map_mul, Complex.conj_conj]
      ring
    have hcj : bohrMean (fun t : ℝ => conj (h t * conj (k t)))
        = conj (bohrMean (fun t : ℝ => h t * conj (k t))) :=
      bohrMean_conj (hhc.mul (Complex.continuous_conj.comp hkc))
        (isBohrAlmostPeriodic_mul hhc hha (Complex.continuous_conj.comp hkc)
          (isBohrAlmostPeriodic_conj hka))
    rw [hfun] at hcj
    rw [hcj, hC]
  -- the quadratic inequality
  have hkey : ∀ s : ℝ, 0 ≤ A - 2 * s * ‖C‖ ^ (2 : ℕ) + s ^ (2 : ℕ) * ‖C‖ ^ (2 : ℕ) * B := by
    intro s
    have hnonneg : 0 ≤ (bohrMean (fun t => (h t - ((s : ℂ) * C) * k t) *
        conj (h t - ((s : ℂ) * C) * k t))).re := by
      refine bohrMean_mul_conj_re_nonneg (hhc.sub (continuous_const.mul hkc)) ?_
      exact isBohrAlmostPeriodic_sub hhc hha (continuous_const.mul hkc)
        (isBohrAlmostPeriodic_const_mul _ hka)
    rw [bohrMean_sub_smul_mul_conj hhc hha hkc hka ((s : ℂ) * C), hCconj] at hnonneg
    have hCC : C * conj C = ((‖C‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [Complex.mul_conj']
      push_cast
      ring
    have hterm1 : conj ((s : ℂ) * C) * C = ((s * ‖C‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      rw [mul_assoc, mul_comm (conj C) C, hCC]
      push_cast
      ring
    have hterm2 : ((s : ℂ) * C) * conj C = ((s * ‖C‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [mul_assoc, hCC]
      push_cast
      ring
    have hterm3 : ((s : ℂ) * C) * conj ((s : ℂ) * C) = ((s ^ (2 : ℕ) * ‖C‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal]
      rw [show ((s : ℂ) * C) * ((s : ℂ) * conj C) = ((s : ℂ) * (s : ℂ)) * (C * conj C) by ring,
        hCC]
      push_cast
      ring
    rw [hterm1, hterm2, hterm3] at hnonneg
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hnonneg
    rw [← hA, ← hB] at hnonneg
    linarith
  rcases eq_or_lt_of_le (norm_nonneg C) with hC0 | hCpos
  · have : ‖C‖ ^ (2 : ℕ) = 0 := by rw [← hC0]; ring
    rw [this]
    exact mul_nonneg hAnonneg hBnonneg
  · have hCsq : 0 < ‖C‖ ^ (2 : ℕ) := by positivity
    rcases eq_or_lt_of_le hBnonneg with hB0 | hBpos
    · exfalso
      have := hkey ((A + 1) / ‖C‖ ^ (2 : ℕ))
      rw [← hB0] at this
      have hcancel : (A + 1) / ‖C‖ ^ (2 : ℕ) * ‖C‖ ^ (2 : ℕ) = A + 1 := by
        field_simp
      nlinarith [hcancel]
    · have hs := hkey (1 / B)
      have hBne : B ≠ 0 := ne_of_gt hBpos
      have hexp : A - 2 * (1 / B) * ‖C‖ ^ (2 : ℕ) + (1 / B) ^ (2 : ℕ) * ‖C‖ ^ (2 : ℕ) * B
          = A - ‖C‖ ^ (2 : ℕ) / B := by
        field_simp
        ring
      rw [hexp] at hs
      have hle : ‖C‖ ^ (2 : ℕ) / B ≤ A := by linarith
      calc ‖C‖ ^ (2 : ℕ) = (‖C‖ ^ (2 : ℕ) / B) * B := by field_simp
        _ ≤ A * B := mul_le_mul_of_nonneg_right hle hBnonneg

end

end GaloisForLFunctions
