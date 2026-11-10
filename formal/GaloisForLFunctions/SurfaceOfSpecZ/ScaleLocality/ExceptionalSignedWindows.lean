import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ExceptionalAbsolutePrimeWindowTransfer
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SignedPrimeLogSquareWindows
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth

/-!
# Signed deletion with exceptional prime sets

Absolute prime avoidance transfers the observations to continuous
log-square windows. Complex deletion then bounds the width. Applying this
reduction at the zero abscissa removes every loss from the prime gaps.
-/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The log-square radius is sublinear, leaving room for prime avoidance. -/
theorem primeLogSquareRadius_exception_margin {δ γ : ℝ} (hδγ : δ < γ) :
    ∀ᶠ T : ℝ in atTop, 2 ≤ primeLogSquareRadius T ∧ primeLogSquareRadius T ≤ T ∧
      δ * T ≤ γ * (T - primeLogSquareRadius T / 2) := by
  have hX : Tendsto (fun T : ℝ => T + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hbase : Tendsto (fun T : ℝ => Real.log (T + 2) ^ 2 / T) atTop (𝓝 0) := by
    have hraw := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 2 one_ne_zero).comp hX
    refine hraw.congr' (Eventually.of_forall fun T => ?_)
    simp only [Function.comp_apply, one_mul]
    congr 1
    ring
  have hratio : Tendsto (fun T : ℝ => primeLogSquareRadius T / T) atTop (𝓝 0) := by
    have hh := hbase.const_mul (2 * zetaLogSquareRadius)
    simp only [mul_zero] at hh
    refine hh.congr' (Eventually.of_forall fun T => ?_)
    dsimp only [primeLogSquareRadius]
    ring
  have hlim := hratio.const_mul (γ / 2)
  simp only [mul_zero] at hlim
  filter_upwards [primeLogSquareRadius_eventually_shape,
    hlim.eventually_le_const (show (0 : ℝ) < γ - δ by linarith only [hδγ]),
    eventually_gt_atTop (0 : ℝ)] with T hshape hsmall hT
  refine ⟨hshape.1, hshape.2, ?_⟩
  have hh := mul_le_mul_of_nonneg_right hsmall hT.le
  have he : (γ / 2 * (primeLogSquareRadius T / T)) * T =
      γ * (primeLogSquareRadius T / 2) := by field_simp [hT.ne']
  rw [he] at hh
  nlinarith only [hh]

/-- One width reduction, using absolute transfer and complex deletion. -/
theorem zeta_signed_width_step_off_finset {a σ δ γ β K C : ℝ}
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hγ : 0 < γ) (hδγ : δ < γ) (hγβ : γ < β)
    (hβ : 7 / 12 < β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧
      (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
      ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogSquareRadius T →
        |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K * (p : ℝ) ^ σ) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + max σ (a + β - 1) := by
  obtain ⟨M, hM⟩ := abs_prime_power_windows_transfer_off_finset temperedConfig_zetaZeroConfig
    ha hσ (le_max_left _ _) (le_max_right _ _) hγ.le hγβ hβ hβ1 hC
    primeLogSquareRadius (primeLogSquareRadius_exception_margin hδγ) hwidth hprime
  apply zeta_re_le_of_abs_logSquare_windows_signed (hσ.trans (le_max_left _ _))
  intro U
  obtain ⟨T, hT, hbound⟩ := hM U
  refine ⟨T, hT, fun u hu => hbound u ?_⟩
  change |u - T| ≤ (2 * zetaLogSquareRadius * Real.log (T + 2) ^ 2) / 2
  linarith only [hu]

/-- Complex deletion detects the exact zero width despite power-thin exceptions. -/
theorem zeta_re_le_iff_abs_prime_logSquare_power_windows_signed_off_finset
    {σ δ : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) ↔
      ∃ K C : ℝ, 0 ≤ C ∧ ∀ U : ℝ, ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧
        (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogSquareRadius T →
          |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤
            K * (p : ℝ) ^ σ := by
  constructor
  · intro hwidth
    obtain ⟨K, hK⟩ := (zeta_re_le_iff_abs_prime_logSquare_power_windows_signed hσ).mp hwidth
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
    have hstep := zeta_signed_width_step_off_finset ha hσ hγ hδγ hγβ hβ hβ1 hC hwidth hprime
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

/-- The signed-deletion RH criterion on exceptional log-square prime windows. -/
theorem riemannHypothesis_iff_abs_prime_logSquare_windows_signed_off_finset
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    RiemannHypothesis ↔ ∃ K C : ℝ, 0 ≤ C ∧ ∀ U : ℝ,
      ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧ (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogSquareRadius T →
          |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K := by
  constructor
  · intro hRH
    have hw : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (0 : ℝ) := by
      intro ρ hρ
      rw [riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ hρ, add_zero]
    simpa only [Real.rpow_zero, mul_one] using
      (zeta_re_le_iff_abs_prime_logSquare_power_windows_signed_off_finset le_rfl hδ hδ1).mp hw
  · intro h
    have hw := (zeta_re_le_iff_abs_prime_logSquare_power_windows_signed_off_finset
      (σ := 0) le_rfl hδ hδ1).mpr (by simpa only [Real.rpow_zero, mul_one] using h)
    apply riemannHypothesis_of_forall_re_le
    simpa only [add_zero] using hw

#print axioms zeta_re_le_iff_abs_prime_logSquare_power_windows_signed_off_finset
#print axioms riemannHypothesis_iff_abs_prime_logSquare_windows_signed_off_finset
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
