import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ZetaLogSquareWindows
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimeWindowTransfer

/-!
# Logarithmic-square prime windows decide RH

A fixed radius proportional to `log²(T+2)` suffices at arbitrarily sparse
logarithmic centers. Prime gaps transfer bounds to the interior, and two
depth reductions give the critical line.
-/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Prime observation radius, twice the continuous detection radius. -/
def primeLogSquareRadius (T : ℝ) : ℝ := 2 * zetaLogSquareRadius * Real.log (T + 2) ^ 2

private theorem primeLogSquareRadius_shape :
    ∀ᶠ T : ℝ in atTop, 2 ≤ primeLogSquareRadius T ∧ primeLogSquareRadius T ≤ T := by
  have hX : Tendsto (fun T : ℝ => T + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hlog := Real.tendsto_log_atTop.comp hX
  have hpow := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
  have hgrowth : Tendsto primeLogSquareRadius atTop atTop := by
    simpa only [Function.comp_def, primeLogSquareRadius] using
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

/-- Prime observations give the continuous bound at exactly the required log-square radius. -/
theorem zeta_prime_logSquare_windows_transfer {a α K : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (haα : a - 1 / 3 ≤ α)
    (hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ primeLogSquareRadius T →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ zetaLogSquareRadius * Real.log (T + 2) ^ 2 →
      -(M * Real.exp (α * u)) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re := by
  obtain ⟨M, hM⟩ := prime_windows_transfer temperedConfig_zetaZeroConfig ha hα haα
    primeLogSquareRadius primeLogSquareRadius_shape hwidth hprime
  refine ⟨M, fun U => ?_⟩
  obtain ⟨T, hT, hbound⟩ := hM U
  refine ⟨T, hT, fun u hu => hbound u ?_⟩
  change |u - T| ≤ (2 * zetaLogSquareRadius * Real.log (T + 2) ^ 2) / 2
  have he : (2 * zetaLogSquareRadius * Real.log (T + 2) ^ 2) / 2 =
      zetaLogSquareRadius * Real.log (T + 2) ^ 2 := by ring
  rw [he]
  exact hu

/-- Bounded traces at all primes in arbitrarily late log-square windows force RH. -/
theorem riemannHypothesis_of_prime_logSquare_windows {K : ℝ}
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ primeLogSquareRadius T →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    RiemannHypothesis := by
  have hhalf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (1 / 2 : ℝ) := by
    intro ρ hρ
    have hh := hρ.2.2
    linarith only [hh]
  obtain ⟨M, hM⟩ := zeta_prime_logSquare_windows_transfer (a := (1 : ℝ) / 2) (α := 1 / 6)
    (by norm_num) (by norm_num) (by norm_num) hhalf hprime
  have hwidth := zeta_re_le_of_logSquare_windows (by norm_num : (0 : ℝ) ≤ 1 / 6) hM
  obtain ⟨N, hN⟩ := zeta_prime_logSquare_windows_transfer (a := (1 : ℝ) / 6) (α := 0)
    (by norm_num) le_rfl (by norm_num) hwidth hprime
  have hzero := zeta_re_le_of_logSquare_windows (α := 0) le_rfl hN
  apply riemannHypothesis_of_forall_re_le
  simpa only [add_zero] using hzero

/-- RH is equivalent to a lower bound on arbitrary sparse log-square prime windows. -/
theorem riemannHypothesis_iff_prime_logSquare_windows :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      ∀ p : ℕ, p.Prime → |Real.log p - T| ≤ primeLogSquareRadius T →
        -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_bddBelow_primeDegrees.mp hRH
    exact ⟨K, fun U => ⟨U, le_rfl, fun p hp _ => hK p hp⟩⟩
  · rintro ⟨K, hK⟩
    exact riemannHypothesis_of_prime_logSquare_windows hK

/-- Failure of RH forces arbitrarily negative prime traces in every sufficiently late log-square window. -/
theorem eventually_prime_logSquare_window_negative (hnot : ¬ RiemannHypothesis) (K : ℝ) :
    ∃ U : ℝ, ∀ T : ℝ, U ≤ T → ∃ p : ℕ, p.Prime ∧
      |Real.log p - T| ≤ primeLogSquareRadius T ∧
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re < -K := by
  classical
  by_contra h
  push Not at h
  exact hnot (riemannHypothesis_of_prime_logSquare_windows h)

#print axioms zeta_prime_logSquare_windows_transfer
#print axioms riemannHypothesis_of_prime_logSquare_windows
#print axioms riemannHypothesis_iff_prime_logSquare_windows
#print axioms eventually_prime_logSquare_window_negative

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
