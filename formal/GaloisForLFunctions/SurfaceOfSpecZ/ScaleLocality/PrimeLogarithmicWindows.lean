import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ZetaLogarithmicWindows
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimeWindowTransfer
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimePowerWindowTransfer
import GaloisForLFunctions.SurfaceOfSpecZ.TheWidthLawAtEveryGapSet
import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovBoundIsAPrimeCount
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth

/-!
# Logarithmic prime windows decide RH

A fixed radius equal to `32 log(T+2)` suffices at arbitrarily sparse
logarithmic centers. Prime gaps transfer bounds to the interior, and two
depth reductions give the critical line.
-/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Prime observation radius, twice the continuous detection radius. -/
def primeLogarithmicRadius (T : ℝ) : ℝ := 32 * Real.log (T + 2)

/-- The logarithmic observation radius is sublinear in its center. -/
theorem primeLogarithmicRadius_div_tendsto_zero :
    Tendsto (fun T : ℝ => primeLogarithmicRadius T / T) atTop (𝓝 0) := by
  have hX : Tendsto (fun T : ℝ => T + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hbase : Tendsto (fun T : ℝ => Real.log (T + 2) / T) atTop (𝓝 0) := by
    have hraw := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hX
    refine hraw.congr' (Eventually.of_forall fun T => ?_)
    simp only [Function.comp_apply, one_mul, pow_one]
    congr 1
    ring
  have hh := hbase.const_mul 32
  simp only [mul_zero] at hh
  refine hh.congr' (Eventually.of_forall fun T => ?_)
  dsimp only [primeLogarithmicRadius]
  ring

/-- The prime radius eventually lies between two and its center. -/
theorem primeLogarithmicRadius_shape :
    ∀ᶠ T : ℝ in atTop, 2 ≤ primeLogarithmicRadius T ∧ primeLogarithmicRadius T ≤ T := by
  have hX : Tendsto (fun T : ℝ => T + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hlog := Real.tendsto_log_atTop.comp hX
  have hgrowth : Tendsto primeLogarithmicRadius atTop atTop := by
    change Tendsto (fun T : ℝ => 32 * Real.log (T + 2)) atTop atTop
    exact hlog.const_mul_atTop (by norm_num)
  have hratio := primeLogarithmicRadius_div_tendsto_zero
  filter_upwards [hgrowth.eventually_ge_atTop 2,
    hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with T hlarge hsmall hT
  refine ⟨hlarge, ?_⟩
  have hh := (div_le_iff₀ hT).mp hsmall
  simpa only [one_mul] using hh

/-- Prime observations give the continuous bound at exactly the required logarithmic radius. -/
theorem zeta_prime_logarithmic_windows_transfer {a α K : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (haα : a - 1 / 3 ≤ α)
    (hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ primeLogarithmicRadius T →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ 16 * Real.log (T + 2) →
      -(M * Real.exp (α * u)) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re := by
  obtain ⟨M, hM⟩ := prime_windows_transfer temperedConfig_zetaZeroConfig ha hα haα
    primeLogarithmicRadius primeLogarithmicRadius_shape hwidth hprime
  refine ⟨M, fun U => ?_⟩
  obtain ⟨T, hT, hbound⟩ := hM U
  refine ⟨T, hT, fun u hu => hbound u ?_⟩
  change |u - T| ≤ (32 * Real.log (T + 2)) / 2
  have he : (32 * Real.log (T + 2)) / 2 =
      16 * Real.log (T + 2) := by ring
  rw [he]
  exact hu

/-- Bounded traces at all primes in arbitrarily late logarithmic windows force RH. -/
theorem riemannHypothesis_of_prime_logarithmic_windows {K : ℝ}
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ primeLogarithmicRadius T →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    RiemannHypothesis := by
  have hhalf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (1 / 2 : ℝ) := by
    intro ρ hρ
    have hh := hρ.2.2
    linarith only [hh]
  obtain ⟨M, hM⟩ := zeta_prime_logarithmic_windows_transfer (a := (1 : ℝ) / 2) (α := 1 / 6)
    (by norm_num) (by norm_num) (by norm_num) hhalf hprime
  have hwidth := zeta_re_le_of_logarithmic_windows (by norm_num : (0 : ℝ) ≤ 1 / 6) hM
  obtain ⟨N, hN⟩ := zeta_prime_logarithmic_windows_transfer (a := (1 : ℝ) / 6) (α := 0)
    (by norm_num) le_rfl (by norm_num) hwidth hprime
  have hzero := zeta_re_le_of_logarithmic_windows (α := 0) le_rfl hN
  apply riemannHypothesis_of_forall_re_le
  simpa only [add_zero] using hzero

/-- RH is equivalent to a lower bound on arbitrary sparse logarithmic prime windows. -/
theorem riemannHypothesis_iff_prime_logarithmic_windows :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      ∀ p : ℕ, p.Prime → |Real.log p - T| ≤ primeLogarithmicRadius T →
        -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_bddBelow_primeDegrees.mp hRH
    exact ⟨K, fun U => ⟨U, le_rfl, fun p hp _ => hK p hp⟩⟩
  · rintro ⟨K, hK⟩
    exact riemannHypothesis_of_prime_logarithmic_windows hK

/-- Failure of RH forces arbitrarily negative prime traces in every sufficiently late logarithmic window. -/
theorem eventually_prime_logarithmic_window_negative (hnot : ¬ RiemannHypothesis) (K : ℝ) :
    ∃ U : ℝ, ∀ T : ℝ, U ≤ T → ∃ p : ℕ, p.Prime ∧
      |Real.log p - T| ≤ primeLogarithmicRadius T ∧
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re < -K := by
  classical
  by_contra h
  push Not at h
  exact hnot (riemannHypothesis_of_prime_logarithmic_windows h)

#print axioms zeta_prime_logarithmic_windows_transfer
#print axioms riemannHypothesis_of_prime_logarithmic_windows
#print axioms riemannHypothesis_iff_prime_logarithmic_windows
#print axioms eventually_prime_logarithmic_window_negative

/-- Power bounds on prime windows transfer at every exponent above the prime-gap error. -/
theorem zeta_prime_logarithmic_power_windows_transfer {a α σ K : ℝ}
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσα : σ ≤ α) (haα : a - 1 / 3 ≤ α)
    (hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ primeLogarithmicRadius T →
      -(K * (p : ℝ) ^ σ) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ 16 * Real.log (T + 2) →
      -(M * Real.exp (α * u)) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re := by
  obtain ⟨M, hM⟩ := prime_power_windows_transfer temperedConfig_zetaZeroConfig ha hσ hσα haα
    primeLogarithmicRadius primeLogarithmicRadius_shape hwidth hprime
  refine ⟨M, fun U => ?_⟩
  obtain ⟨T, hT, hbound⟩ := hM U
  refine ⟨T, hT, fun u hu => hbound u ?_⟩
  change |u - T| ≤ (32 * Real.log (T + 2)) / 2
  linarith only [hu]

/-- The exponent of a one-sided prime-window bound is the exact upper zero width. -/
theorem zeta_re_le_iff_prime_logarithmic_power_windows {α : ℝ} (hα : 0 ≤ α) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + α) ↔
      ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
        |Real.log p - T| ≤ primeLogarithmicRadius T →
        -(K * (p : ℝ) ^ α) ≤
          2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hwidth
    refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖,
      fun U => ⟨U, le_rfl, fun p hp _ => ?_⟩⟩
    exact (abs_le.mp (abs_two_re_lagStructure_log_le_of_width
      temperedConfig_zetaZeroConfig hwidth hp.pos)).1
  · rintro ⟨K, hprime⟩
    have hhalf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (1 / 2 : ℝ) := by
      intro ρ hρ
      linarith only [hρ.2.2]
    have hβ : 0 ≤ max α (1 / 6 : ℝ) := hα.trans (le_max_left _ _)
    have hstep : (1 / 2 : ℝ) - 1 / 3 ≤ max α (1 / 6) := by
      linarith only [le_max_right α (1 / 6 : ℝ)]
    obtain ⟨M, hM⟩ := zeta_prime_logarithmic_power_windows_transfer
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hα (le_max_left _ _) hstep hhalf hprime
    have hwidth := zeta_re_le_of_logarithmic_windows hβ hM
    have hreduce : max α (1 / 6 : ℝ) - 1 / 3 ≤ α := by
      rw [sub_le_iff_le_add]
      exact max_le (by linarith only) (by linarith only [hα])
    obtain ⟨N, hN⟩ := zeta_prime_logarithmic_power_windows_transfer
      hβ hα le_rfl hreduce hwidth hprime
    exact zeta_re_le_of_logarithmic_windows hα hN

/-- Absolute prime-window bounds have the same exact width as one-sided bounds. -/
theorem zeta_re_le_iff_abs_prime_logarithmic_power_windows {α : ℝ} (hα : 0 ≤ α) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + α) ↔
      ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
        |Real.log p - T| ≤ primeLogarithmicRadius T →
        |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K * (p : ℝ) ^ α := by
  constructor
  · intro hwidth
    exact ⟨_, fun U => ⟨U, le_rfl, fun p hp _ =>
      abs_two_re_lagStructure_log_le_of_width temperedConfig_zetaZeroConfig hwidth hp.pos⟩⟩
  · rintro ⟨K, hK⟩
    apply (zeta_re_le_iff_prime_logarithmic_power_windows hα).mpr
    refine ⟨K, fun U => ?_⟩
    obtain ⟨T, hT, hbound⟩ := hK U
    exact ⟨T, hT, fun p hp hwin => (abs_le.mp (hbound p hp hwin)).1⟩

/-- RH is equivalent to an absolute bound on arbitrarily late logarithmic prime windows. -/
theorem riemannHypothesis_iff_abs_prime_logarithmic_windows :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      ∀ p : ℕ, p.Prime → |Real.log p - T| ≤ primeLogarithmicRadius T →
        |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K := by
  constructor
  · intro hRH
    have hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (0 : ℝ) := by
      intro ρ hρ
      rw [riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ hρ, add_zero]
    simpa only [Real.rpow_zero, mul_one] using
      (zeta_re_le_iff_abs_prime_logarithmic_power_windows (α := 0) le_rfl).mp hwidth
  · rintro ⟨K, hK⟩
    apply riemannHypothesis_of_prime_logarithmic_windows
    intro U
    obtain ⟨T, hT, hbound⟩ := hK U
    exact ⟨T, hT, fun p hp hwin => (abs_le.mp (hbound p hp hwin)).1⟩

#print axioms zeta_prime_logarithmic_power_windows_transfer
#print axioms zeta_re_le_iff_prime_logarithmic_power_windows
#print axioms zeta_re_le_iff_abs_prime_logarithmic_power_windows
#print axioms riemannHypothesis_iff_abs_prime_logarithmic_windows

/-- Quasi-RH is a one-sided power saving on arbitrarily sparse logarithmic prime windows. -/
theorem quasiRH_iff_prime_logarithmic_power_windows :
    _root_.RHTower.zetaZeroAbscissa < 1 ↔
      ∃ α : ℝ, 0 ≤ α ∧ α < 1 / 2 ∧ ∃ K : ℝ,
        ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
          |Real.log p - T| ≤ primeLogarithmicRadius T →
          -(K * (p : ℝ) ^ α) ≤
            2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hΘ
    have hα : 0 ≤ _root_.RHTower.zetaZeroAbscissa - 1 / 2 :=
      sub_nonneg.mpr _root_.RHTower.half_le_zetaZeroAbscissa
    refine ⟨_, hα, by linarith only [hΘ], ?_⟩
    apply (zeta_re_le_iff_prime_logarithmic_power_windows hα).mp
    exact (zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hα).mp (by linarith only)
  · rintro ⟨α, hα, hαhalf, hK⟩
    have hΘ := (zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hα).mpr
      ((zeta_re_le_iff_prime_logarithmic_power_windows hα).mpr hK)
    linarith only [hΘ, hαhalf]

#print axioms quasiRH_iff_prime_logarithmic_power_windows


/-- The one-sided arithmetic prime-count error on sparse logarithmic windows
measures the exact upper zero width. -/
theorem zeta_re_le_iff_stepanov_logarithmic_power_windows {α : ℝ} (hα : 0 ≤ α) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + α) ↔
      ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
        |Real.log p - T| ≤ primeLogarithmicRadius T →
        primeWindow p ≤ archPoleWindow p + K * (p : ℝ) ^ α := by
  rw [zeta_re_le_iff_prime_logarithmic_power_windows hα]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K / 2, fun U => ?_⟩
    obtain ⟨T, hT, hbound⟩ := hK U
    refine ⟨T, hT, fun p hp hwin => ?_⟩
    have hh := hbound p hp hwin
    rw [← orbitCorr_eq_re_lagStructure_spline,
      orbitCorr_log_eq_archPoleWindow_sub_primeWindow] at hh
    linarith only [hh]
  · rintro ⟨K, hK⟩
    refine ⟨2 * K, fun U => ?_⟩
    obtain ⟨T, hT, hbound⟩ := hK U
    refine ⟨T, hT, fun p hp hwin => ?_⟩
    rw [← orbitCorr_eq_re_lagStructure_spline,
      orbitCorr_log_eq_archPoleWindow_sub_primeWindow]
    linarith only [hbound p hp hwin]

/-- RH is exactly a bounded arithmetic Stepanov error on arbitrarily late
prime windows of logarithmic radius. -/
theorem riemannHypothesis_iff_stepanov_logarithmic_windows :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      ∀ p : ℕ, p.Prime → |Real.log p - T| ≤ primeLogarithmicRadius T →
        primeWindow p ≤ archPoleWindow p + K := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_primeWindow_le_primes.mp hRH
    exact ⟨K, fun U => ⟨U, le_rfl, fun p hp _ => hK p hp⟩⟩
  · rintro ⟨K, hK⟩
    have hw := (zeta_re_le_iff_stepanov_logarithmic_power_windows (α := 0) le_rfl).mpr
      (by simpa only [Real.rpow_zero, mul_one] using (show ∃ K : ℝ, ∀ U : ℝ,
        ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
          |Real.log p - T| ≤ primeLogarithmicRadius T →
          primeWindow p ≤ archPoleWindow p + K from ⟨K, hK⟩))
    apply riemannHypothesis_of_forall_re_le
    simpa only [add_zero] using hw

/-- Any fixed power saving in the arithmetic Stepanov error, needed only on
arbitrarily late logarithmic prime windows, is equivalent to quasi-RH. -/
theorem quasiRH_iff_stepanov_logarithmic_power_windows :
    _root_.RHTower.zetaZeroAbscissa < 1 ↔
      ∃ α : ℝ, 0 ≤ α ∧ α < 1 / 2 ∧ ∃ K : ℝ,
        ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
          |Real.log p - T| ≤ primeLogarithmicRadius T →
          primeWindow p ≤ archPoleWindow p + K * (p : ℝ) ^ α := by
  constructor
  · intro hΘ
    obtain ⟨α, hα, hαhalf, hprime⟩ := quasiRH_iff_prime_logarithmic_power_windows.mp hΘ
    exact ⟨α, hα, hαhalf, (zeta_re_le_iff_stepanov_logarithmic_power_windows hα).mp
      ((zeta_re_le_iff_prime_logarithmic_power_windows hα).mpr hprime)⟩
  · rintro ⟨α, hα, hαhalf, hprime⟩
    apply quasiRH_iff_prime_logarithmic_power_windows.mpr
    exact ⟨α, hα, hαhalf, (zeta_re_le_iff_prime_logarithmic_power_windows hα).mp
      ((zeta_re_le_iff_stepanov_logarithmic_power_windows hα).mpr hprime)⟩

#print axioms zeta_re_le_iff_stepanov_logarithmic_power_windows
#print axioms riemannHypothesis_iff_stepanov_logarithmic_windows
#print axioms quasiRH_iff_stepanov_logarithmic_power_windows
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
