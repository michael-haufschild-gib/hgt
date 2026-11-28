import GaloisForLFunctions.HTGeometry.RpowExpAsymptotics

/-! The two auxiliary-prime weights, including the distortion of
the count estimates, fit inside the final stretched exponential. -/

noncomputable section

open Filter GaloisForLFunctions.HTGeometry

namespace WindowedLandauTheory.ConcN

private theorem count_weight_envelope (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, 6 * (x ^ C * Real.exp (-(x ^ (ε / 6)))) ≤ Real.exp (-(x ^ (ε / 7))) := by
  have hgap : 0 < ε / 6 - ε / 7 := by linarith only [hε]
  have hlarge := (tendsto_rpow_atTop hgap).eventually_ge_atTop (2 : ℝ)
  have hpow := eventually_mul_rpow_le_exp_rpow (p := C) 6 (c := 1 / 2) (δ := ε / 6)
    (by norm_num) (by linarith only [hε])
  filter_upwards [hpow, hlarge, eventually_gt_atTop (0 : ℝ)] with x hx hlarge hx0
  have hhalf : x ^ (ε / 7) ≤ (1 / 2) * x ^ (ε / 6) := by
    have he : x ^ (ε / 6) = x ^ (ε / 7) * x ^ (ε / 6 - ε / 7) := by
      rw [← Real.rpow_add hx0]
      ring_nf
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hx0.le (ε / 7))
    linarith only [hh]
  calc
    6 * (x ^ C * Real.exp (-(x ^ (ε / 6)))) =
        (6 * x ^ C) * Real.exp (-(x ^ (ε / 6))) := by ring
    _ ≤ Real.exp ((1 / 2) * x ^ (ε / 6)) * Real.exp (-(x ^ (ε / 6))) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ ≤ Real.exp (-(x ^ (ε / 7))) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith only [hhalf])

theorem eventually_weight_distortion_le (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ e W₁ W₂ : ℝ, 0 ≤ e → e ≤ 1 / 2 →
      W₁ ≤ x ^ C * Real.exp (-(x ^ (ε / 6))) → W₂ ≤ x ^ C * Real.exp (-(x ^ (ε / 6))) →
      (1 + e) / (1 - e) * (W₁ + W₂) ≤ Real.exp (-(x ^ (ε / 7))) := by
  filter_upwards [count_weight_envelope C ε hε, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro e W₁ W₂ he he' hW₁ hW₂
  have hp : 0 < 1 - e := by linarith only [he']
  have hr₀ : 0 ≤ (1 + e) / (1 - e) := div_nonneg (by positivity) hp.le
  have hr : (1 + e) / (1 - e) ≤ 3 := (div_le_iff₀ hp).mpr (by linarith only [he'])
  let B := x ^ C * Real.exp (-(x ^ (ε / 6)))
  have hB : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.exp_pos _).le
  calc
    _ ≤ (1 + e) / (1 - e) * (B + B) := mul_le_mul_of_nonneg_left (add_le_add hW₁ hW₂) hr₀
    _ ≤ 3 * (B + B) := mul_le_mul_of_nonneg_right hr (add_nonneg hB hB)
    _ = 6 * B := by ring
    _ ≤ Real.exp (-(x ^ (ε / 7))) := hx

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.eventually_weight_distortion_le
