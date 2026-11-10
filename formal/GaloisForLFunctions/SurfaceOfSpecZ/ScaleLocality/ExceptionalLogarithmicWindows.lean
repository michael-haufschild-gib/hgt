import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimeLogarithmicWindows
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ExceptionalPrimeWindowTransfer

/-! Logarithmic prime windows tolerate a fixed power-saving number of
exceptions. Their exceptional sets may vary independently between windows. -/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- A sublinear radius makes the exception count negligible at every interior
point when its exponent is strictly smaller than the avoidance exponent. -/
theorem primeLogarithmicRadius_exception_margin {δ γ : ℝ} (hδγ : δ < γ) :
    ∀ᶠ T : ℝ in atTop, 2 ≤ primeLogarithmicRadius T ∧ primeLogarithmicRadius T ≤ T ∧
      δ * T ≤ γ * (T - primeLogarithmicRadius T / 2) := by
  have hlim := primeLogarithmicRadius_div_tendsto_zero.const_mul (γ / 2)
  simp only [mul_zero] at hlim
  filter_upwards [primeLogarithmicRadius_shape,
    hlim.eventually_le_const (show (0 : ℝ) < γ - δ by linarith only [hδγ]),
    eventually_gt_atTop (0 : ℝ)] with T hshape hsmall hT
  refine ⟨hshape.1, hshape.2, ?_⟩
  have hh := mul_le_mul_of_nonneg_right hsmall hT.le
  have he : (γ / 2 * (primeLogarithmicRadius T / T)) * T =
      γ * (primeLogarithmicRadius T / 2) := by field_simp [hT.ne']
  rw [he] at hh
  nlinarith only [hh]

/-- One width reduction survives a separately chosen finite exceptional set
in each logarithmic prime window. -/
theorem zeta_logarithmic_width_step_off_finset {a σ δ γ β K C : ℝ}
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hγ : 0 < γ) (hδγ : δ < γ) (hγβ : γ < β)
    (hβ : 7 / 12 < β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧
      (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
      ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogarithmicRadius T →
        -(K * (p : ℝ) ^ σ) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + max σ (a + β - 1) := by
  obtain ⟨M, hM⟩ := prime_power_windows_transfer_off_finset temperedConfig_zetaZeroConfig
    ha hσ (le_max_left _ _) (le_max_right _ _) hγ.le hγβ hβ hβ1 hC
    primeLogarithmicRadius (primeLogarithmicRadius_exception_margin hδγ) hwidth hprime
  apply zeta_re_le_of_logarithmic_windows (hσ.trans (le_max_left _ _))
  intro U
  obtain ⟨T, hT, hbound⟩ := hM U
  refine ⟨T, hT, fun u hu => hbound u ?_⟩
  change |u - T| ≤ (32 * Real.log (T + 2)) / 2
  linarith only [hu]

/-- A power-saving number of exceptions in each selected window preserves
exact zero-width detection, without an attained deepest zero. -/
theorem zeta_re_le_iff_prime_logarithmic_power_windows_off_finset {σ δ : ℝ}
    (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) ↔
      ∃ K C : ℝ, 0 ≤ C ∧ ∀ U : ℝ, ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧
        (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogarithmicRadius T →
          -(K * (p : ℝ) ^ σ) ≤
            2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hwidth
    obtain ⟨K, hK⟩ := (zeta_re_le_iff_prime_logarithmic_power_windows hσ).mp hwidth
    refine ⟨K, 0, le_rfl, fun U => ?_⟩
    obtain ⟨T, hT, hbound⟩ := hK U
    exact ⟨T, ∅, hT, by simp, fun p hp _ hwin => hbound p hp hwin⟩
  · rintro ⟨K, C, hC, hprime⟩
    let γ : ℝ := (δ + 1) / 2
    let β : ℝ := max ((γ + 1) / 2) (2 / 3)
    have hδγ : δ < γ := by dsimp [γ]; linarith only [hδ1]
    have hγ : 0 < γ := lt_of_le_of_lt hδ hδγ
    have hγ1 : γ < 1 := by dsimp [γ]; linarith only [hδ1]
    have hγβ : γ < β := lt_of_lt_of_le
      (by linarith only [hγ1] : γ < (γ + 1) / 2) (le_max_left _ _)
    have hβ : (7 : ℝ) / 12 < β := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hβ1 : β < 1 := max_lt (by linarith only [hγ1]) (by norm_num)
    let a : ℝ := _root_.RHTower.zetaZeroAbscissa - 1 / 2
    have ha : 0 ≤ a := sub_nonneg.mpr _root_.RHTower.half_le_zetaZeroAbscissa
    have hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a :=
      (zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le ha).mp (by dsimp [a]; linarith only)
    have hstep := zeta_logarithmic_width_step_off_finset ha hσ hγ hδγ hγβ hβ hβ1 hC hwidth hprime
    have hnew := (zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le
      (hσ.trans (le_max_left σ (a + β - 1)))).mpr hstep
    have haσ : a ≤ σ := by
      by_contra h
      have hσa : σ < a := lt_of_not_ge h
      have hless : max σ (a + β - 1) < a := max_lt hσa (by linarith only [hβ1])
      dsimp [a] at hnew hless
      linarith only [hnew, hless]
    intro ρ hρ
    exact (hwidth ρ hρ).trans (by linarith only [haσ])

#print axioms zeta_re_le_iff_prime_logarithmic_power_windows_off_finset

/-- RH tolerates independently varying power-thin exceptional prime sets
on arbitrarily late logarithmic windows. -/
theorem riemannHypothesis_iff_prime_logarithmic_windows_off_finset {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    RiemannHypothesis ↔ ∃ K C : ℝ, 0 ≤ C ∧ ∀ U : ℝ,
      ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧ (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogarithmicRadius T →
          -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hRH
    have hw : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (0 : ℝ) := by
      intro ρ hρ
      rw [riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ hρ, add_zero]
    simpa only [Real.rpow_zero, mul_one] using
      (zeta_re_le_iff_prime_logarithmic_power_windows_off_finset le_rfl hδ hδ1).mp hw
  · intro h
    have hw := (zeta_re_le_iff_prime_logarithmic_power_windows_off_finset
      (σ := 0) le_rfl hδ hδ1).mpr (by simpa only [Real.rpow_zero, mul_one] using h)
    apply riemannHypothesis_of_forall_re_le
    simpa only [add_zero] using hw

#print axioms riemannHypothesis_iff_prime_logarithmic_windows_off_finset

/-- The arithmetic Stepanov error measures exact zero width even when each
logarithmic window discards a power-saving number of primes. -/
theorem zeta_re_le_iff_stepanov_logarithmic_power_windows_off_finset {σ δ : ℝ}
    (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) ↔
      ∃ K C : ℝ, 0 ≤ C ∧ ∀ U : ℝ, ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧
        (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogarithmicRadius T →
          primeWindow p ≤ archPoleWindow p + K * (p : ℝ) ^ σ := by
  rw [zeta_re_le_iff_prime_logarithmic_power_windows_off_finset hσ hδ hδ1]
  constructor
  · rintro ⟨K, C, hC, hK⟩
    refine ⟨K / 2, C, hC, fun U => ?_⟩
    obtain ⟨T, E, hT, hcard, hbound⟩ := hK U
    refine ⟨T, E, hT, hcard, fun p hp hpE hwin => ?_⟩
    have hh := hbound p hp hpE hwin
    rw [← orbitCorr_eq_re_lagStructure_spline,
      orbitCorr_log_eq_archPoleWindow_sub_primeWindow] at hh
    linarith only [hh]
  · rintro ⟨K, C, hC, hK⟩
    refine ⟨2 * K, C, hC, fun U => ?_⟩
    obtain ⟨T, E, hT, hcard, hbound⟩ := hK U
    refine ⟨T, E, hT, hcard, fun p hp hpE hwin => ?_⟩
    rw [← orbitCorr_eq_re_lagStructure_spline,
      orbitCorr_log_eq_archPoleWindow_sub_primeWindow]
    linarith only [hbound p hp hpE hwin]

/-- Failure of RH leaves a negative prime trace outside every finite set of
power-saving size, in every sufficiently late logarithmic window. -/
theorem eventually_prime_logarithmic_window_negative_off_finset
    (hnot : ¬ RiemannHypothesis) (K C : ℝ) (hC : 0 ≤ C) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ∃ U : ℝ, ∀ T : ℝ, U ≤ T → ∀ E : Finset ℕ,
      (E.card : ℝ) ≤ C * Real.exp (δ * T) →
      ∃ p : ℕ, p.Prime ∧ p ∉ E ∧ |Real.log p - T| ≤ primeLogarithmicRadius T ∧
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re < -K := by
  classical
  by_contra h
  push Not at h
  apply hnot
  apply (riemannHypothesis_iff_prime_logarithmic_windows_off_finset hδ hδ1).mpr
  refine ⟨K, C, hC, fun U => ?_⟩
  obtain ⟨T, hT, E, hE, hbound⟩ := h U
  exact ⟨T, E, hT, hE, hbound⟩

#print axioms zeta_re_le_iff_stepanov_logarithmic_power_windows_off_finset
#print axioms eventually_prime_logarithmic_window_negative_off_finset
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
