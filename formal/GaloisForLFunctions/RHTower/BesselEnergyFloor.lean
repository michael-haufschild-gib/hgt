import GaloisForLFunctions.RHTower.BesselOscillatorInstance
import GaloisForLFunctions.RHTower.ProlateDunsterRegularBranch

/-!
# The Bessel energy cannot be small

The Wronskian of the two normal-form solutions `√u J₀(u)` and `√u K(u)` is the constant `π/4`, and
the companion's energy is bounded above by its value at `u = 1` times `exp(1/2)`.  Weighted
Cauchy–Schwarz then floors the energy of `√u J₀`:

```text
(π/4)² / ((K_V(1)² + K_V'(1)²) exp(1/2))  ≤  besselEnergy u        for u ≥ 1 .
```

The constant is a definite real number, named rather than evaluated: no numerical bound on any
Bessel function at any point is used, and none is available in this development.  What makes that
possible is that the Wronskian is *exactly* `π/4` — a normalisation, not an asymptotic — and that the
companion energy law is already proved.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The Wronskian in normal-form variables.**  The `1/(2√u)` terms cancel. -/
theorem besselNormalForm_wronskian {u : ℝ} (hu : 0 < u) :
    besselNormalForm u * besselKVDeriv u - besselNormalFormDeriv u * besselKV u
      = besselWronskian u := by
  have hsu : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu
  obtain ⟨S, hS0, hSu, hSeq⟩ : ∃ S : ℝ, 0 < S ∧ S * S = u ∧ Real.sqrt u = S :=
    ⟨Real.sqrt u, hsu, Real.mul_self_sqrt hu.le, rfl⟩
  rw [besselNormalForm, besselNormalFormDeriv, besselKV, besselKVDeriv, besselWronskian,
    hSeq, ← hSu]
  field_simp
  ring

/-- The companion energy is bounded by its value at `u = 1`. -/
theorem besselKV_oscEnergy_le {u : ℝ} (hu : 1 ≤ u) :
    oscEnergy besselKV besselKVDeriv u
      ≤ (besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2) * Real.exp (1 / 2) := by
  rw [oscEnergy]
  exact sq_add_sq_le_of_perturbed_harmonic
    (fun x hx => hasDerivAt_besselKV (lt_of_lt_of_le zero_lt_one hx))
    (fun x hx => hasDerivAt_besselKVDeriv (lt_of_lt_of_le zero_lt_one hx)) hu

/-- The companion energy constant is positive, because the Wronskian is not zero. -/
theorem besselKV_energy_const_pos :
    0 < (besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2) * Real.exp (1 / 2) := by
  have hW : besselNormalForm 1 * besselKVDeriv 1 - besselNormalFormDeriv 1 * besselKV 1
      = Real.pi / 4 := by
    rw [besselNormalForm_wronskian (by norm_num : (0:ℝ) < 1)]
    exact besselWronskian_eq_pi_div_four (by norm_num)
  have hπ : (0 : ℝ) < Real.pi / 4 := by
    have := Real.pi_pos
    linarith
  have hne : besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2 ≠ 0 := by
    intro h
    have h1 : besselKV 1 = 0 := by nlinarith [sq_nonneg (besselKV 1), sq_nonneg (besselKVDeriv 1)]
    have h2 : besselKVDeriv 1 = 0 := by
      nlinarith [sq_nonneg (besselKV 1), sq_nonneg (besselKVDeriv 1)]
    rw [h1, h2] at hW
    simp at hW
    linarith [hW, hπ]
  have hnn : 0 ≤ besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2 := by positivity
  have hpos : 0 < besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2 := lt_of_le_of_ne hnn (Ne.symm hne)
  positivity

/-- **The Bessel energy floor.**  Absolute, and proved without evaluating any Bessel function. -/
theorem besselEnergy_lower {u : ℝ} (hu : 1 ≤ u) :
    (Real.pi / 4) ^ 2 / ((besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2) * Real.exp (1 / 2))
      ≤ besselEnergy u := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hWval : besselNormalForm u * besselKVDeriv u - besselNormalFormDeriv u * besselKV u
      = Real.pi / 4 := by
    rw [besselNormalForm_wronskian hu0]
    exact besselWronskian_eq_pi_div_four hu0
  have h := oscEnergy_lower_of_wronskian (w₁ := besselNormalForm) (Dw₁ := besselNormalFormDeriv)
    (w₂ := besselKV) (Dw₂ := besselKVDeriv) hWval (besselKV_oscEnergy_le hu)
    besselKV_energy_const_pos
  rwa [oscEnergy_bessel] at h

/-- The floor constant of the Bessel energy. -/
def besselEnergyFloor : ℝ :=
  (Real.pi / 4) ^ 2 / ((besselKV 1 ^ 2 + besselKVDeriv 1 ^ 2) * Real.exp (1 / 2))

theorem besselEnergyFloor_pos : 0 < besselEnergyFloor := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [besselEnergyFloor]
  exact div_pos (by positivity) besselKV_energy_const_pos

theorem exp_half_le_two : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h := Real.exp_lt_exp.2 hlog
  rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
  linarith

theorem half_le_exp_neg_half : (1 : ℝ) / 2 ≤ Real.exp (-(1 / 2 : ℝ)) := by
  have hpos : (0 : ℝ) < Real.exp ((1:ℝ) / 2) := Real.exp_pos _
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) hpos]
  linarith [exp_half_le_two]

/-- **The Bessel normal form carries absolute mass on every window of length four.**  The energy
floor and the virial mass bound combine with no numerical input beyond `e^(1/2) ≤ 2`. -/
theorem besselMass_lower_window {α : ℝ} (hα : 1 ≤ α) :
    4 / 9 * besselEnergyFloor ≤ ∫ u in α..(α + 4), besselNormalForm u ^ 2 := by
  have hα0 : (0 : ℝ) < α := lt_of_lt_of_le zero_lt_one hα
  have hαβ : α ≤ α + 4 := by linarith
  have hmain := besselMass_lower hα0 hαβ
  have hE : besselEnergyFloor ≤ besselEnergy α := besselEnergy_lower hα
  have hE0 : 0 < besselEnergy α := lt_of_lt_of_le besselEnergyFloor_pos hE
  -- the two exponential comparisons
  have hlow : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (1 / 4 / (α + 4) - 1 / 4 / α) := by
    rw [Real.exp_le_exp]
    have h1 : (0 : ℝ) < 1 / 4 / (α + 4) := by positivity
    have h2 : (1 : ℝ) / 4 / α ≤ 1 / 4 := by
      rw [div_le_iff₀ hα0]
      nlinarith [hα]
    linarith
  have hhigh : Real.exp (1 / 4 / α) ≤ 2 := by
    refine le_trans ?_ exp_half_le_two
    rw [Real.exp_le_exp]
    rw [div_le_iff₀ hα0]
    nlinarith [hα]
  -- the numerator
  have hnum : besselEnergyFloor
      ≤ (α + 4 - α) * (besselEnergy α * Real.exp (1 / 4 / (α + 4) - 1 / 4 / α))
        - besselEnergy α * Real.exp (1 / 4 / α) := by
    have h1 : besselEnergy α * Real.exp (-(1 / 4 : ℝ))
        ≤ besselEnergy α * Real.exp (1 / 4 / (α + 4) - 1 / 4 / α) :=
      mul_le_mul_of_nonneg_left hlow hE0.le
    have h2 : besselEnergy α * Real.exp (1 / 4 / α) ≤ besselEnergy α * 2 :=
      mul_le_mul_of_nonneg_left hhigh hE0.le
    have h3 : besselEnergy α * (3 / 4) ≤ besselEnergy α * Real.exp (-(1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (by have := Real.add_one_le_exp (-(1 / 4 : ℝ)); linarith) hE0.le
    have hsimp : α + 4 - α = 4 := by ring
    rw [hsimp]
    nlinarith [h1, h2, h3, hE, hE0]
  -- the denominator
  have hden : (0 : ℝ) < 2 + (1 / 4 : ℝ) / α ^ 2 := by positivity
  have hden' : 2 + (1 / 4 : ℝ) / α ^ 2 ≤ 9 / 4 := by
    have : (1 : ℝ) / 4 / α ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hα]
    linarith
  have hstep : 4 / 9 * besselEnergyFloor
      ≤ ((α + 4 - α) * (besselEnergy α * Real.exp (1 / 4 / (α + 4) - 1 / 4 / α))
          - besselEnergy α * Real.exp (1 / 4 / α)) / (2 + (1 / 4 : ℝ) / α ^ 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [hnum, hden', besselEnergyFloor_pos]
  linarith [hmain, hstep]

theorem continuous_besselNormalForm : Continuous besselNormalForm := by
  have hfun : besselNormalForm = fun u : ℝ => Real.sqrt u * besselJ0 u := by
    funext u
    rw [besselNormalForm]
  rw [hfun]
  exact Real.continuous_sqrt.mul continuous_besselJ0

/-- **Tiling the window bound.**  The mass of the Bessel normal form grows linearly: every four
units of the exterior ray contribute a fixed amount. -/
theorem besselMass_lower_tiled {α : ℝ} (hα : 1 ≤ α) (n : ℕ) :
    (n : ℝ) * (4 / 9 * besselEnergyFloor)
      ≤ ∫ u in α..(α + 4 * (n : ℝ)), besselNormalForm u ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : (1 : ℝ) ≤ α + 4 * (k : ℝ) := by
      have : (0 : ℝ) ≤ 4 * (k : ℝ) := by positivity
      linarith
    have hstep := besselMass_lower_window hk
    have hcont : Continuous fun u : ℝ => besselNormalForm u ^ 2 :=
      continuous_besselNormalForm.pow 2
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (f := fun u : ℝ => besselNormalForm u ^ 2) (μ := MeasureTheory.volume)
      (a := α) (b := α + 4 * (k : ℝ)) (c := α + 4 * ((k : ℝ) + 1))
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    have hshift : α + 4 * (k : ℝ) + 4 = α + 4 * ((k : ℝ) + 1) := by ring
    rw [hshift] at hstep
    push_cast
    linarith [ih, hstep, hadd]

end GaloisForLFunctions.RHTower

end
