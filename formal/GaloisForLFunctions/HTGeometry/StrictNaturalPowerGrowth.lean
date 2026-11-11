import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strict power growth on positive integers

A sequence has threshold `θ` when every exponent strictly greater than
`θ` bounds it. Multiplication by a real power translates this threshold
exactly; addition preserves it.
-/

noncomputable section

namespace HTGeometry

/-- A power bound at every exponent strictly above `θ`, on positive integers. -/
def StrictNaturalPowerGrowth (u : ℕ → ℝ) (θ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |u N| ≤ C * (N : ℝ) ^ (θ + δ)

theorem StrictNaturalPowerGrowth.mono {u : ℕ → ℝ} {θ η : ℝ}
    (hu : StrictNaturalPowerGrowth u θ) (hθη : θ ≤ η) : StrictNaturalPowerGrowth u η := by
  intro δ hδ
  obtain ⟨C, hC, h⟩ := hu δ hδ
  refine ⟨C, hC, fun N hN => (h N hN).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hN) (add_le_add hθη le_rfl)) hC

theorem StrictNaturalPowerGrowth.add {u v : ℕ → ℝ} {θ : ℝ}
    (hu : StrictNaturalPowerGrowth u θ) (hv : StrictNaturalPowerGrowth v θ) :
    StrictNaturalPowerGrowth (fun N => u N + v N) θ := by
  intro δ hδ
  obtain ⟨C, hC, h⟩ := hu δ hδ
  obtain ⟨D, hD, k⟩ := hv δ hδ
  refine ⟨C + D, add_nonneg hC hD, fun N hN => ?_⟩
  exact (abs_add_le _ _).trans ((add_le_add (h N hN) (k N hN)).trans_eq (by ring))

theorem StrictNaturalPowerGrowth.neg {u : ℕ → ℝ} {θ : ℝ}
    (hu : StrictNaturalPowerGrowth u θ) : StrictNaturalPowerGrowth (fun N => -u N) θ := by
  simpa only [StrictNaturalPowerGrowth, abs_neg] using hu

theorem StrictNaturalPowerGrowth.sub {u v : ℕ → ℝ} {θ : ℝ}
    (hu : StrictNaturalPowerGrowth u θ) (hv : StrictNaturalPowerGrowth v θ) :
    StrictNaturalPowerGrowth (fun N => u N - v N) θ := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

theorem StrictNaturalPowerGrowth.const_mul {u : ℕ → ℝ} {θ : ℝ}
    (hu : StrictNaturalPowerGrowth u θ) (c : ℝ) :
    StrictNaturalPowerGrowth (fun N => c * u N) θ := by
  intro δ hδ
  obtain ⟨C, hC, h⟩ := hu δ hδ
  refine ⟨|c| * C, mul_nonneg (abs_nonneg _) hC, fun N hN => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h N hN) (abs_nonneg _)

theorem StrictNaturalPowerGrowth.rpow_mul {u : ℕ → ℝ} {θ : ℝ}
    (hu : StrictNaturalPowerGrowth u θ) (b : ℝ) :
    StrictNaturalPowerGrowth (fun N => (N : ℝ) ^ b * u N) (θ + b) := by
  intro δ hδ
  obtain ⟨C, hC, h⟩ := hu δ hδ
  refine ⟨C, hC, fun N hN => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hNp.le _)]
  calc
    _ ≤ (N : ℝ) ^ b * (C * (N : ℝ) ^ (θ + δ)) :=
      mul_le_mul_of_nonneg_left (h N hN) (Real.rpow_nonneg hNp.le _)
    _ = C * (N : ℝ) ^ (θ + b + δ) := by
      rw [mul_left_comm, ← Real.rpow_add hNp]
      congr 2
      ring

/-- Power rescaling is an exact translation of the growth threshold. -/
theorem strictNaturalPowerGrowth_rpow_mul_iff (u : ℕ → ℝ) (θ b : ℝ) :
    StrictNaturalPowerGrowth (fun N => (N : ℝ) ^ b * u N) (θ + b) ↔
      StrictNaturalPowerGrowth u θ := by
  constructor
  · intro h
    have hb := h.rpow_mul (-b)
    intro δ hδ
    obtain ⟨C, hC, hCbound⟩ := hb δ hδ
    refine ⟨C, hC, fun N hN => ?_⟩
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have hn := hCbound N hN
    dsimp only at hn
    rw [← mul_assoc, ← Real.rpow_add hNp, neg_add_cancel,
      Real.rpow_zero, one_mul] at hn
    simpa only [add_neg_cancel_right] using hn
  · intro h
    exact h.rpow_mul b

/-- For a sequence vanishing at zero and a nonnegative threshold, replacing
`N` by `N+1` in the bound changes only its constant. -/
theorem strictNaturalPowerGrowth_iff_succ {u : ℕ → ℝ} {θ : ℝ}
    (hzero : u 0 = 0) (hθ : 0 ≤ θ) :
    StrictNaturalPowerGrowth u θ ↔
      ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
        |u N| ≤ C * ((N : ℝ) + 1) ^ (θ + δ) := by
  constructor
  · intro h δ hδ
    obtain ⟨C, hC, hbound⟩ := h δ hδ
    refine ⟨C, hC, fun N => ?_⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [hzero, abs_zero]
      positivity
    exact (hbound N hN).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) (by linarith only [hθ, hδ])) hC)
  · intro h δ hδ
    obtain ⟨C, hC, hbound⟩ := h δ hδ
    refine ⟨C * (2 : ℝ) ^ (θ + δ), by positivity, fun N hN => ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    calc
      _ ≤ C * ((N : ℝ) + 1) ^ (θ + δ) := hbound N
      _ ≤ C * (2 * (N : ℝ)) ^ (θ + δ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith only [hN1])
          (by linarith only [hθ, hδ])) hC
      _ = _ := by rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N), mul_assoc]

end HTGeometry
