import GaloisForLFunctions.RHTower.EisensteinHeckeResonantMoment

/-!
# The Hecke resonance identity at every zero

For every zero `ρ` of `Λ` in the strip off the real axis, `u = ρ/2 − ½`, every prime `p` and every
height `Y ≥ p`,

`∫_𝒟 (T_pΛ^Y E_u)·conj(Λ^Y E_u) = (p^u + p^{ū}) ‖Λ(ρ−1)‖² Y^{1−Re ρ}/(1 − Re ρ)`,

and the right side is the real number `2 Re(p^u) ‖Λ(ρ−1)‖² Y^{1−Re ρ}/(1 − Re ρ)`
(`heckeHermitianMoment_resonantZero`, `heckeHermitianMoment_resonantZero_re`).  For `Im ρ > 0`
this is `heckeHermitianMoment_resonant` combined with the Maass–Selberg norm
`integral_norm_sq_resonantState`; for `Im ρ < 0` it follows by complex conjugation, since the
Hecke operator has real coefficients and `Λ^Y E_ū = conj Λ^Y E_u` (`heckeHermitianMoment_conj`).
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem truncatedLeg_conj (u : ℂ) (Y x : ℝ) {y : ℝ} (hy : 0 < y) :
    (starRingEnd ℂ) (truncatedLeg u Y x y) = truncatedLeg ((starRingEnd ℂ) u) Y x y := by
  have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  have h := truncatedLineModel_conj u Y (UpperHalfPlane.mk ((x : ℂ) + (y : ℂ) * Complex.I) hz)
  rw [truncatedLineModel_eq_truncatedLeg, truncatedLineModel_eq_truncatedLeg] at h
  have hre : (UpperHalfPlane.mk ((x : ℂ) + (y : ℂ) * Complex.I) hz).re = x := by
    simp [UpperHalfPlane.re]
  have him : (UpperHalfPlane.mk ((x : ℂ) + (y : ℂ) * Complex.I) hz).im = y := by
    simp [UpperHalfPlane.im]
  rwa [hre, him] at h

theorem heckeTruncated_conj {p : ℕ} (hp : 0 < p) (u : ℂ) (Y : ℝ) (z : ℍ) :
    (starRingEnd ℂ) (heckeTruncated p u Y z) = heckeTruncated p ((starRingEnd ℂ) u) Y z := by
  have hy := z.im_pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold heckeTruncated heckeOp
  simp only [map_mul, map_add, map_sum, Complex.conj_ofReal]
  rw [truncatedLeg_conj u Y _ (mul_pos hpR hy)]
  congr 2
  exact Finset.sum_congr rfl fun b _ => truncatedLeg_conj u Y _ (div_pos hy hpR)

/-- Conjugating the parameter conjugates the Hermitian Hecke moment. -/
theorem heckeHermitianMoment_conj {p : ℕ} (hp : 0 < p) (u : ℂ) (Y : ℝ) :
    heckeHermitianMoment p ((starRingEnd ℂ) u) Y =
      (starRingEnd ℂ) (heckeHermitianMoment p u Y) := by
  unfold heckeHermitianMoment
  rw [← integral_conj]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  rw [map_mul, heckeTruncated_conj hp, Complex.conj_conj, ← truncatedLineModel_conj,
    Complex.conj_conj]

theorem resonantParameter_conj (ρ : ℂ) :
    resonantParameter ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (resonantParameter ρ) := by
  unfold resonantParameter
  simp [map_sub, map_div₀, map_ofNat]

/-- **The Hecke resonance identity at every zero of `Λ` in the strip.** -/
theorem heckeHermitianMoment_resonantZero {p : ℕ} (hp : p.Prime) {ρ : ℂ}
    (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0)
    {Y : ℝ} (hY : (p : ℝ) ≤ Y) :
    heckeHermitianMoment p (resonantParameter ρ) Y =
      ((p : ℂ) ^ resonantParameter ρ + (p : ℂ) ^ ((starRingEnd ℂ) (resonantParameter ρ))) *
        ((‖reflectedCompletedLambda (ρ - 1)‖ ^ 2 * Y ^ (1 - ρ.re) / (1 - ρ.re) : ℝ) : ℂ) := by
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
    linarith
  have hpos : ∀ {σ : ℂ}, reflectedCompletedLambda σ = 0 → 0 < σ.re → σ.re < 1 → 0 < σ.im →
      heckeHermitianMoment p (resonantParameter σ) Y =
        ((p : ℂ) ^ resonantParameter σ + (p : ℂ) ^ ((starRingEnd ℂ) (resonantParameter σ))) *
          ((‖reflectedCompletedLambda (σ - 1)‖ ^ 2 * Y ^ (1 - σ.re) / (1 - σ.re) : ℝ) : ℂ) := by
    intro σ hσ hσ0 hσ1 hσi
    rw [heckeHermitianMoment_resonant hp (resonantParameter_mem hσ0 hσi)
      (resonantParameter_re_neg hσ1) (by rw [msA_resonantParameter]; exact hσ) hY,
      integral_norm_sq_resonantState hσ hσ0 hσ1 hσi hY1]
  rcases lt_or_gt_of_ne him with hneg | hpos'
  · set σ := (starRingEnd ℂ) ρ with hσ
    have hσz : reflectedCompletedLambda σ = 0 := by
      rw [hσ, reflectedCompletedLambda_conj, hρ, map_zero]
    have hσre : σ.re = ρ.re := by simp [hσ]
    have hσim : 0 < σ.im := by simp [hσ]; linarith
    have hρσ : ρ = (starRingEnd ℂ) σ := by rw [hσ, Complex.conj_conj]
    have h := hpos hσz (by rw [hσre]; exact h0) (by rw [hσre]; exact h1) hσim
    rw [hρσ, resonantParameter_conj, heckeHermitianMoment_conj hp.pos, h, map_mul, map_add,
      conj_natCast_cpow, conj_natCast_cpow, Complex.conj_ofReal, Complex.conj_conj]
    have e : reflectedCompletedLambda ((starRingEnd ℂ) σ - 1) =
        (starRingEnd ℂ) (reflectedCompletedLambda (σ - 1)) := by
      rw [← reflectedCompletedLambda_conj, map_sub, map_one]
    rw [e, Complex.norm_conj]
    simp only [Complex.conj_re, hσre]
  · exact hpos hρ h0 h1 hpos'

/-- **The resonant Hecke moment is real** at every zero of `Λ` in the strip. -/
theorem heckeHermitianMoment_resonantZero_re {p : ℕ} (hp : p.Prime) {ρ : ℂ}
    (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0)
    {Y : ℝ} (hY : (p : ℝ) ≤ Y) :
    heckeHermitianMoment p (resonantParameter ρ) Y =
      ((2 * ((p : ℂ) ^ resonantParameter ρ).re *
        (‖reflectedCompletedLambda (ρ - 1)‖ ^ 2 * Y ^ (1 - ρ.re) / (1 - ρ.re)) : ℝ) : ℂ) := by
  rw [heckeHermitianMoment_resonantZero hp hρ h0 h1 him hY, ← conj_natCast_cpow, Complex.add_conj]
  push_cast
  ring

end

end RHTower
