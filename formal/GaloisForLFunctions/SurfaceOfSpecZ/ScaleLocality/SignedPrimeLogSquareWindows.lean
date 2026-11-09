import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SignedLogSquareWindows
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.AbsolutePrimeWindowTransfer
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimeLogSquareWindows
import GaloisForLFunctions.SurfaceOfSpecZ.TheWidthLawAtEveryGapSet

/-!
# The absolute prime-window criterion by signed deletion

Prime gaps transfer absolute bounds to continuous windows. Two depth
reductions then give the exact width, using complex deletion at each stage.
-/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

theorem primeLogSquareRadius_eventually_shape :
    ∀ᶠ T : ℝ in atTop, 2 ≤ primeLogSquareRadius T ∧ primeLogSquareRadius T ≤ T := by
  have hX : Tendsto (fun T : ℝ => T + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hlog := Real.tendsto_log_atTop.comp hX
  have hpow := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
  have hgrowth : Tendsto primeLogSquareRadius atTop atTop := by
    change Tendsto (fun T : ℝ => 2 * zetaLogSquareRadius * Real.log (T + 2) ^ 2) atTop atTop
    simpa only [Function.comp_def] using
      hpow.const_mul_atTop (mul_pos two_pos zetaLogSquareRadius_pos)
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
  filter_upwards [hgrowth.eventually_ge_atTop 2,
    hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with T hlarge hsmall hT
  refine ⟨hlarge, ?_⟩
  have hh := (div_le_iff₀ hT).mp hsmall
  simpa only [one_mul] using hh

/-- Power bounds on prime windows transfer at every exponent above the prime-gap error. -/
theorem zeta_abs_prime_logSquare_power_windows_transfer {a α σ K : ℝ}
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσα : σ ≤ α) (haα : a - 1 / 3 ≤ α)
    (hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ primeLogSquareRadius T →
      |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K * (p : ℝ) ^ σ) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ zetaLogSquareRadius * Real.log (T + 2) ^ 2 →
      |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re| ≤ M * Real.exp (α * u) := by
  obtain ⟨M, hM⟩ := abs_prime_power_windows_transfer temperedConfig_zetaZeroConfig ha hσ hσα haα
    primeLogSquareRadius primeLogSquareRadius_eventually_shape hwidth hprime
  refine ⟨M, fun U => ?_⟩
  obtain ⟨T, hT, hbound⟩ := hM U
  refine ⟨T, hT, fun u hu => hbound u ?_⟩
  change |u - T| ≤ (2 * zetaLogSquareRadius * Real.log (T + 2) ^ 2) / 2
  linarith only [hu]

/-- Complex deletion identifies the exact width of absolute prime-window bounds. -/
theorem zeta_re_le_iff_abs_prime_logSquare_power_windows_signed {α : ℝ} (hα : 0 ≤ α) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + α) ↔
      ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
        |Real.log p - T| ≤ primeLogSquareRadius T →
        |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K * (p : ℝ) ^ α := by
  constructor
  · intro hwidth
    refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖,
      fun U => ⟨U, le_rfl, fun p hp _ => ?_⟩⟩
    exact abs_two_re_lagStructure_log_le_of_width
      temperedConfig_zetaZeroConfig hwidth hp.pos
  · rintro ⟨K, hprime⟩
    have hhalf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (1 / 2 : ℝ) := by
      intro ρ hρ
      linarith only [hρ.2.2]
    have hβ : 0 ≤ max α (1 / 6 : ℝ) := hα.trans (le_max_left _ _)
    have hstep : (1 / 2 : ℝ) - 1 / 3 ≤ max α (1 / 6) := by
      linarith only [le_max_right α (1 / 6 : ℝ)]
    obtain ⟨M, hM⟩ := zeta_abs_prime_logSquare_power_windows_transfer
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hα (le_max_left _ _) hstep hhalf hprime
    have hwidth := zeta_re_le_of_abs_logSquare_windows_signed hβ hM
    have hreduce : max α (1 / 6 : ℝ) - 1 / 3 ≤ α := by
      rw [sub_le_iff_le_add]
      exact max_le (by linarith only) (by linarith only [hα])
    obtain ⟨N, hN⟩ := zeta_abs_prime_logSquare_power_windows_transfer
      hβ hα le_rfl hreduce hwidth hprime
    exact zeta_re_le_of_abs_logSquare_windows_signed hα hN

/-- RH is the bounded absolute prime-window criterion with a signed-deletion proof. -/
theorem riemannHypothesis_iff_abs_prime_logSquare_windows_signed :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      ∀ p : ℕ, p.Prime → |Real.log p - T| ≤ primeLogSquareRadius T →
        |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K := by
  constructor
  · intro hRH
    have hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (0 : ℝ) := by
      intro ρ hρ
      rw [riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ hρ, add_zero]
    simpa only [Real.rpow_zero, mul_one] using
      (zeta_re_le_iff_abs_prime_logSquare_power_windows_signed (α := 0) le_rfl).mp hwidth
  · intro hK
    have hwidth := (zeta_re_le_iff_abs_prime_logSquare_power_windows_signed (α := 0) le_rfl).mpr
      (by simpa only [Real.rpow_zero, mul_one] using hK)
    apply riemannHypothesis_of_forall_re_le
    simpa only [add_zero] using hwidth

#print axioms zeta_re_le_iff_abs_prime_logSquare_power_windows_signed
#print axioms riemannHypothesis_iff_abs_prime_logSquare_windows_signed

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
