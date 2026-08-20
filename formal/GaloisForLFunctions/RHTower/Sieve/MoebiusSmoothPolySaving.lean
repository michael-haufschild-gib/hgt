import GaloisForLFunctions.RHTower.Sieve.MoebiusDistanceAllFreq
import GaloisForLFunctions.RHTower.Sieve.MoebiusDistanceSharp
import GaloisForLFunctions.RHTower.Sieve.RouteTThresholdLimits
import GaloisForLFunctions.RHTower.Sieve.GSTailAssembly

/-!
# A power saving for the smooth Möbius sum at every frequency below the square of the cutoff

`Sieve/MoebiusDistanceAllFreq.exists_mulDistSqPair_ge_allFreq` bounds the pretentious distance of
`μ` from every character `n^{it}` with `|t| ≤ z²` below by `(1/100)·log log z − C₀`, subject to a
finite list of thresholds on `log z`.  Every threshold is a polylogarithmic inequality that holds for
all large `z`, so the distance bound holds eventually with no hypotheses beyond the frequency range.

Feeding it into the Euler damping bound
`Sieve/MoebiusEulerDamping.norm_sum_moebius_smooth_le_exp` turns the distance into a size bound:
the Dirichlet sum over squarefree `z`-smooth integers is at most `C·(log z)^{99/100}`, whereas its
trivial size `∏_{p ≤ z}(1 + 1/p)` is of order `log z`.  Unlike
`Sieve/MoebiusUniformFrequency.exists_norm_sum_moebius_smooth_le_uniform`, which is a
`(log T)⁷` bound gated on `log⁹T ≤ A log z`, and unlike
`Sieve/MoebiusDistanceSharp.exists_norm_sum_moebius_smooth_le_free`, whose bound
`(1 + log z)^{3/4}(3 + log(4 + 2|t|))^{1/4}` degenerates to the trivial size once `log|t| ≍ log z`,
this is a saving over the trivial size at *every* frequency of the range.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The worst-case reciprocal-width budget grows without bound. -/
theorem tendsto_routeTBudgetHat (A : ℝ) :
    Tendsto (fun L : ℝ => routeTBudgetHat A L) atTop atTop := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hminor : Tendsto
      (fun L : ℝ => 10 * routeTZeroFreeDeltaEnvelopeConstant A * L ^ ((9 : ℝ) / 10)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by linarith) (tendsto_rpow_atTop (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ hminor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  have hlog : (0 : ℝ) ≤ Real.log (23 + 4 * L) := Real.log_nonneg (by linarith)
  have hb : L ^ ((9 : ℝ) / 10) ≤ (23 + 4 * L) ^ ((9 : ℝ) / 10) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hp : (0 : ℝ) ≤ L ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
  have hsq : (1 : ℝ) ≤ (1 + Real.log (23 + 4 * L)) ^ 2 := by nlinarith
  have hY0 : (0 : ℝ) ≤ (23 + 4 * L) ^ ((9 : ℝ) / 10) := le_trans hp hb
  have hstep : 10 * routeTZeroFreeDeltaEnvelopeConstant A * (23 + 4 * L) ^ ((9 : ℝ) / 10) * 1
      ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A * (23 + 4 * L) ^ ((9 : ℝ) / 10)
        * (1 + Real.log (23 + 4 * L)) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  rw [routeTBudgetHat]
  nlinarith [hD, hb, hp, hY0, hstep]

/-- Every threshold of `exists_mulDistSqPair_ge_allFreq` holds for all large cutoffs, so the
distance bound is eventually free of hypotheses apart from the frequency range. -/
theorem eventually_mulDistSqPair_ge_allFreq :
    ∃ C₀ : ℝ, ∀ᶠ z : ℕ in atTop, ∀ (t : ℝ) (f : ℕ → ℂ),
      Real.log |t| ≤ 2 * Real.log (z : ℝ) → (∀ p ∈ Nat.primesLE z, f p = -1) →
      0.01 * Real.log (Real.log (z : ℝ)) - C₀
        ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  obtain ⟨A, delta, C, C₀, hdelta, hC, hall⟩ := exists_mulDistSqPair_ge_allFreq
  refine ⟨C₀, ?_⟩
  have h5 : ∀ᶠ L : ℝ in atTop, 1 / routeTBudgetHat A L ≤ delta := by
    filter_upwards [(tendsto_routeTBudgetHat A).eventually_ge_atTop (1 / delta)] with L hL
    have hpos : (0 : ℝ) < 1 / delta := by positivity
    have := one_div_le_one_div_of_le hpos hL
    rwa [one_div_one_div] at this
  have h6 : ∀ᶠ L : ℝ in atTop, Real.log (16 * Real.pi / 3) ≤ L ^ (0.6 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.6)).eventually_ge_atTop _
  have hcomb := ((eventually_contour_threshold (A := A) hC).and
    (((eventually_trunc_threshold (A := A) hC).and (eventually_cheb_threshold.and
      (eventually_gsCutoff_growth.and (h5.and (h6.and (eventually_ge_atTop (1 : ℝ))))))) ))
  filter_upwards [log_tendsto_atTop_nat.eventually hcomb, eventually_ge_atTop 2] with z hz hz2
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hz
  intro t f hthi hf
  exact hall z t f hz2 hc7 hc1 hc2 hc3 hc5 hc4 hc6 hthi hf

/-- **A power saving for the smooth Möbius sum, uniformly over `|t| ≤ z²`.**  The Dirichlet sum over
squarefree `z`-smooth integers is at most `C·(log z)^{99/100}`, against the trivial size `≍ log z`.
The saving comes from the pretentious distance `D²(μ, n^{it}) ≥ (1/100)·log log z − C₀`, which holds
at every frequency of the range. -/
theorem exists_norm_sum_moebius_smooth_le_polySaving :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ z : ℕ in atTop, ∀ t : ℝ, |t| ≤ (z : ℝ) ^ 2 →
      ‖∑ n ∈ (Nat.primesLE z).powerset.image (fun S => ∏ p ∈ S, p),
          ((1 / (n : ℝ) : ℝ) : ℂ)
            * (moebiusC n * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))‖
        ≤ C₁ * (Real.log (z : ℝ)) ^ (0.99 : ℝ) := by
  obtain ⟨C₀, hdist⟩ := eventually_mulDistSqPair_ge_allFreq
  refine ⟨Real.exp (Real.pi ^ 2 / 6 + mertensSecondUpperConst + C₀), Real.exp_pos _, ?_⟩
  filter_upwards [hdist, eventually_ge_atTop 2,
    log_tendsto_atTop_nat.eventually_ge_atTop (1 : ℝ)] with z hz hz2 hL1
  intro t ht
  have hz2' : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hLz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hthi : Real.log |t| ≤ 2 * Real.log (z : ℝ) := by
    rcases le_or_gt |t| 1 with h1 | h1
    · have : Real.log |t| ≤ 0 := Real.log_nonpos (abs_nonneg t) h1
      linarith
    · have h2 : Real.log |t| ≤ Real.log ((z : ℝ) ^ 2) := Real.log_le_log (by linarith) ht
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
  have hf : ∀ p ∈ Nat.primesLE z, (fun _ : ℕ => (-1 : ℂ)) p = -1 := fun _ _ => rfl
  have hD := hz t (fun _ : ℕ => (-1 : ℂ)) hthi hf
  rw [mulDistSqPair_neg_one_split hf t] at hD
  have hP : ∀ p ∈ Nat.primesLE z, p.Prime := fun p hp => (Nat.mem_primesLE.1 hp).2
  have hbase := norm_sum_moebius_smooth_le_exp t hP
  have hsq := sum_inv_sq_primesLE_le_pi z
  have hmert : (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
      ≤ Real.log (Real.log (z : ℝ)) + mertensSecondUpperConst := mertensS_le hz2
  refine le_trans hbase ?_
  rw [Real.rpow_def_of_pos hLz0, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith

end

end RHTower.Sieve
