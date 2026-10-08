import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticCoprimeEnergy
import GaloisForLFunctions.RHTower.PrimeHarmonicLogLower
import Mathlib.NumberTheory.Primorial

/-!
# The actual pole residue disappears under increasing prime deletion

One first takes the radial limit for each fixed primorial, then lets the
primorial cutoff grow. The proof does not interchange these limits.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

/-- The elementary finite Euler product suffices; no Mertens asymptotic is needed. -/
theorem coprimeDensity_primorial_le_inv_harmonic {N : ℕ} (hN : 1 ≤ N) :
    coprimeDensity (primorial N) ≤ ((_root_.harmonic N : ℝ))⁻¹ := by
  have hH : 0 < (_root_.harmonic N : ℝ) := by
    simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    apply Finset.sum_pos'
    · intro n _
      positivity
    · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, by norm_num⟩
  have hh : (_root_.harmonic N : ℝ) ≤ (coprimeDensity (primorial N))⁻¹ := by
    simpa only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      coprimeDensity, primeFactors_primorial, Nat.primesLE, Finset.prod_inv_distrib] using
      harmonic_sum_le_prod_primesBelow N
  simpa only [inv_inv] using
    (inv_le_inv₀ (inv_pos.mpr (coprimeDensity_pos (primorial N))) hH).mpr hh

theorem tendsto_coprimeDensity_primorial :
    Tendsto (fun N : ℕ => coprimeDensity (primorial N)) atTop (𝓝 0) := by
  have hH : Tendsto (fun N : ℕ => (_root_.harmonic N : ℝ)) atTop atTop := by
    simpa [_root_.harmonic, one_div] using Real.tendsto_sum_range_one_div_nat_succ_atTop
  apply squeeze_zero'
    (Eventually.of_forall fun N => (coprimeDensity_pos (primorial N)).le)
    (by filter_upwards [eventually_ge_atTop 1] with N hN
        exact coprimeDensity_primorial_le_inv_harmonic hN)
    (tendsto_inv_atTop_zero.comp hH)

/-- For every full-positive source, its actual coprime/full pole ratios
at primorial cutoffs tend to zero. No uniform radial error is a premise. -/
theorem exists_forward_sieve_residue_tendsto_zero {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ r : ℕ → ℝ, (∀ N, 0 < r N) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ N : ℕ, Tendsto (fun s : ℝ =>
        LSeries (coprimePart (primorial N) (sourceCoeff lam)) (s : ℂ) /
          LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (r N : ℂ)) := by
  obtain ⟨K, hK, _, hratios⟩ := exists_forward_coprime_energy hW
  choose r hr hratio hbound using fun N : ℕ =>
    hratios (primorial N) (primorial_ne_zero N)
  refine ⟨r, hr, ?_, hratio⟩
  have hB : 0 < ‖sourceCompletion hW 1‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sourceCompletion_one_ne_zero hW))
  have ht : Tendsto (fun N : ℕ =>
      K * coprimeDensity (primorial N) / ‖sourceCompletion hW 1‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using
      (tendsto_coprimeDensity_primorial.const_mul K).div_const (‖sourceCompletion hW 1‖ ^ 2)
  have hs : Tendsto (fun N : ℕ => r N ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => sq_nonneg (r N))
      (Eventually.of_forall fun N => ?_) ht
    exact (le_div_iff₀ hB).mpr (by simpa only [mul_comm] using hbound N)
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_pos (hr _), Real.sqrt_zero] using hroot

end RHTower.WeilSingularArithmetic
