import GaloisForLFunctions.BezoutValuationIncidence.BaezDuarteEnergyOfThePowerDampedMobiusRows

/-!
# The readout–energy uncertainty principle

For a row `c` write `R(c) = Σ_e Λ(e) Y_c(e)` for its von Mangoldt readout and `Q(c)` for its
energy-centered pronic energy. Under scaling `R(tc) = t R(c)` and `Q(tc) = t² Q(c)`. The Báez-Duarte
residual of `tc` is `(1 - tR)² + t²Q`, whose minimum over `t` is `Q/(R² + Q)`. The unconditional floor
`κ / log N` therefore becomes a scale-invariant inequality:

**Uncertainty principle.** For every `N ≥ 2` and every row on `[1, N]`,
`κ R(c)² ≤ (log N - κ) Q(c)`.

The von Mangoldt readout of a row is controlled by its energy-centered pronic energy at the cost
`O(log N)`. The criterion becomes a statement about the optimal constant:

**RH ⟺ the ratio `R(c)²/Q(c)` is unbounded over finite rows.**
-/

open Finset RHTower ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

theorem selbergMultiplesCoord_smul (N : ℕ) (t : ℝ) (c : ℕ → ℝ) (e : ℕ) :
    selbergMultiplesCoord N (fun d => t * c d) e = t * selbergMultiplesCoord N c e := by
  unfold selbergMultiplesCoord
  rw [mul_sum]
  exact sum_congr rfl fun d _ => by ring

theorem vonMangoldtReadout_smul (N : ℕ) (t : ℝ) (c : ℕ → ℝ) :
    vonMangoldtReadout N (fun d => t * c d) = t * vonMangoldtReadout N c := by
  unfold vonMangoldtReadout
  rw [mul_sum]
  exact sum_congr rfl fun e _ => by rw [selbergMultiplesCoord_smul]; ring

theorem sieveEnergyCenteredPronicGramForm_smul (N : ℕ) (t : ℝ) (c : ℕ → ℝ) :
    sieveEnergyCenteredPronicGramForm N (fun d => t * c d) =
      t ^ 2 * sieveEnergyCenteredPronicGramForm N c := by
  unfold sieveEnergyCenteredPronicGramForm
  rw [mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun q _ => by rw [selbergMultiplesCoord_smul, selbergMultiplesCoord_smul]; ring

/-- The scaled residual `(1 - tR)² + t²Q`. -/
theorem residual_smul (N : ℕ) (t : ℝ) (c : ℕ → ℝ) :
    (1 - vonMangoldtReadout N (fun d => t * c d)) ^ 2 +
        sieveEnergyCenteredPronicGramForm N (fun d => t * c d) =
      (1 - t * vonMangoldtReadout N c) ^ 2 + t ^ 2 * sieveEnergyCenteredPronicGramForm N c := by
  rw [vonMangoldtReadout_smul, sieveEnergyCenteredPronicGramForm_smul]

/-- The energy-centered pronic energy is nonnegative: it is the pronic energy of the centered prefix. -/
theorem sieveEnergyCenteredPronicGramForm_nonneg' (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ sieveEnergyCenteredPronicGramForm N c := by
  have h := sum_sum_mul_pmRamanujanEnergyCenteredGram_nonneg (Icc 2 N)
    (fun p hp => by have := (mem_Icc.mp hp).1; omega) (selbergMultiplesCoord N c)
  exact h

/-- **The readout–energy uncertainty principle.** -/
theorem exists_readout_energy_uncertainty :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 2 ≤ N → ∀ c : ℕ → ℝ,
      κ * vonMangoldtReadout N c ^ 2 ≤ (Real.log N - κ) * sieveEnergyCenteredPronicGramForm N c := by
  obtain ⟨κ, hκ, hfloor⟩ := exists_readout_centered_energy_floor
  refine ⟨κ, hκ, fun N hN c => ?_⟩
  set R := vonMangoldtReadout N c
  set Q := sieveEnergyCenteredPronicGramForm N c
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hQ : 0 ≤ Q := sieveEnergyCenteredPronicGramForm_nonneg' N c
  -- the floor at every scale `t`
  have hscale : ∀ t : ℝ, κ / Real.log N ≤ (1 - t * R) ^ 2 + t ^ 2 * Q := fun t => by
    have h := hfloor N hN (fun d => t * c d)
    rwa [residual_smul] at h
  rcases eq_or_lt_of_le hQ with hQ0 | hQpos
  · -- with zero energy the readout must vanish: scale `t = 1/R`
    rw [← hQ0, mul_zero]
    by_contra hR
    push Not at hR
    have hR0 : R ≠ 0 := by
      intro h0
      rw [h0] at hR
      simp at hR
    have h := hscale R⁻¹
    rw [← hQ0, mul_zero, add_zero, inv_mul_cancel₀ hR0, sub_self] at h
    have : 0 < κ / Real.log N := div_pos hκ hlog
    norm_num at h
    linarith
  · -- the optimal scale `t = R/(R² + Q)` gives `Q/(R² + Q) ≥ κ/log N`
    have hden : 0 < R ^ 2 + Q := by positivity
    have h := hscale (R / (R ^ 2 + Q))
    have hopt : (1 - R / (R ^ 2 + Q) * R) ^ 2 + (R / (R ^ 2 + Q)) ^ 2 * Q = Q / (R ^ 2 + Q) := by
      field_simp
      ring
    rw [hopt, div_le_div_iff₀ hlog hden] at h
    nlinarith

/-- **RH ⟺ the readout-to-energy ratio is unbounded.** -/
theorem riemannHypothesis_iff_readout_energy_ratio_unbounded :
    RiemannHypothesis ↔ ∀ K : ℝ, ∃ (N : ℕ) (c : ℕ → ℝ),
      K * sieveEnergyCenteredPronicGramForm N c < vonMangoldtReadout N c ^ 2 := by
  rw [riemannHypothesis_iff_readout_and_centered_energy]
  constructor
  · intro h K
    -- energy below `ε` forces readout near one and energy small
    obtain ⟨N, c, hc⟩ := h (1 / (4 * (|K| + 1))) (by positivity)
    refine ⟨N, c, ?_⟩
    set R := vonMangoldtReadout N c
    set Q := sieveEnergyCenteredPronicGramForm N c
    have hQ : 0 ≤ Q := sieveEnergyCenteredPronicGramForm_nonneg' N c
    have hK1 : (0 : ℝ) < |K| + 1 := by positivity
    have hsmall : 1 / (4 * (|K| + 1)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg K]
    have hR : (1 - R) ^ 2 < 1 / 4 := by nlinarith [sq_nonneg (1 - R)]
    have hRhalf : 1 / 2 < R := by nlinarith [sq_nonneg (1 - R)]
    have hQsmall : Q * (4 * (|K| + 1)) < 1 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (|K| + 1))).mp
        (lt_of_le_of_lt (le_add_of_nonneg_left (sq_nonneg (1 - R))) hc)
      linarith
    nlinarith [le_abs_self K, abs_nonneg K]
  · intro h ε hε
    obtain ⟨N, c, hc⟩ := h (1 / ε)
    set R := vonMangoldtReadout N c
    set Q := sieveEnergyCenteredPronicGramForm N c
    have hQ : 0 ≤ Q := sieveEnergyCenteredPronicGramForm_nonneg' N c
    have hR2 : 0 < R ^ 2 := lt_of_le_of_lt (mul_nonneg (by positivity) hQ) hc
    have hden : 0 < R ^ 2 + Q := by positivity
    refine ⟨N, fun d => R / (R ^ 2 + Q) * c d, ?_⟩
    rw [residual_smul]
    have hopt : (1 - R / (R ^ 2 + Q) * R) ^ 2 + (R / (R ^ 2 + Q)) ^ 2 * Q = Q / (R ^ 2 + Q) := by
      field_simp
      ring
    rw [hopt, div_lt_iff₀ hden]
    have : Q < ε * R ^ 2 := by
      have h1 : 1 / ε * Q < R ^ 2 := hc
      rw [one_div, inv_mul_lt_iff₀ hε] at h1
      linarith
    nlinarith

end

end GaloisForLFunctions.BezoutValuationIncidence
