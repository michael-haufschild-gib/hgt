import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramUniformRemainder

/-!
# A logarithmic plateau for the harmonic Gram remainder

The quadratic tail is sharp at long horizons but grows artificially at
short horizons. Positivity and monotonicity of the Gram form compare every
short prefix with the square of the conductor cutoff. The torsion norm
then gives a logarithmic bound independent of the horizon.
-/

open Finset
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics
noncomputable section

private def packetGram (Q : ℕ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)

private theorem packetGram_nonneg (Q N : ℕ) (a : ℕ → ℝ) : 0 ≤ packetGram Q a N :=
  sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

private theorem packetGram_mono (Q : ℕ) (a : ℕ → ℝ) : Monotone (packetGram Q a) := by
  intro N M hNM
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hNM)
  intro n _ _
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

private theorem harmonicReal_mono {N M : ℕ} (hNM : N ≤ M) :
    (harmonic N : ℝ) ≤ harmonic M := by
  rw [← HTGeometry.sum_Icc_one_div_eq_harmonic, ← HTGeometry.sum_Icc_one_div_eq_harmonic]
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hNM)
    fun n _ _ => div_nonneg zero_le_one (Nat.cast_nonneg n)

private theorem harmonicReal_nonneg (N : ℕ) : (0 : ℝ) ≤ harmonic N := by
  rw [← HTGeometry.sum_Icc_one_div_eq_harmonic]
  exact sum_nonneg fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n)

private theorem normalized_selfMass (Q : ℕ) (a : ℕ → ℝ) :
    selfMass Q (fun m => a m / Real.sqrt (m.totient : ℝ)) = ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  unfold selfMass
  apply sum_congr rfl
  intro m hm
  have hphi : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm).1).ne'
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  field_simp [hphi]

private theorem quadratic_scale_le_one {Q N : ℕ} (hQN : Q * Q ≤ N) :
    (Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1) ≤ 1 := by
  have h : (Q : ℝ) * Q ≤ N := by exact_mod_cast hQN
  apply (div_le_one (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr
  nlinarith only [h, Nat.cast_nonneg (α := ℝ) Q]

/-- The harmonic Gram remainder has a logarithmic bound at every horizon, including zero. -/
theorem abs_harmonicGram_torsion_remainder_le_log {Q : ℕ}
    (hQ : 2 ≤ Q) (N : ℕ) (a : ℕ → ℝ) :
    |(∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) -
        (harmonic N : ℝ) * (∑ m ∈ Icc 1 Q, a m ^ 2) +
        torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))| ≤
      (6 * Real.log Q + Real.log 4 + 5) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let M : ℝ := ∑ m ∈ Icc 1 Q, a m ^ 2
  let T := torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))
  let L : ℝ := 6 * Real.log Q + Real.log 4 + 5
  have hM : 0 ≤ M := sum_nonneg fun m _ => sq_nonneg (a m)
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hlogQ, hlog4]
  have ht : |T| ≤ (4 * Real.log Q + (Real.log 4 + 4)) * M := by
    simpa only [normalized_selfMass] using
      abs_torsionPairing_le_log Q (fun m => a m / Real.sqrt (m.totient : ℝ))
  change |packetGram Q a N - (harmonic N : ℝ) * M + T| ≤ L * M
  by_cases hQN : Q * Q ≤ N
  · exact (abs_harmonicGram_quadratic_torsion_remainder hQ N a).trans
      (mul_le_mul_of_nonneg_right ((quadratic_scale_le_one hQN).trans hL) hM)
  have hNQ : N ≤ Q * Q := (Nat.le_of_lt (Nat.lt_of_not_ge hQN))
  have hgram := packetGram_mono Q a hNQ
  have hH : (harmonic (Q * Q) : ℝ) ≤ 1 + 2 * Real.log Q := by
    have h := harmonic_le_one_add_log (Q * Q)
    have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
    simpa only [Nat.cast_mul, Real.log_mul hQ0 hQ0, two_mul] using h
  have hHN : (harmonic N : ℝ) * M ≤ (1 + 2 * Real.log Q) * M :=
    mul_le_mul_of_nonneg_right ((harmonicReal_mono hNQ).trans hH) hM
  have htop : packetGram Q a (Q * Q) - (harmonic (Q * Q) : ℝ) * M + T ≤ M := by
    have h := (abs_le.mp (abs_harmonicGram_quadratic_torsion_remainder hQ (Q * Q) a)).2
    exact h.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (quadratic_scale_le_one (le_refl (Q * Q))) hM)
  apply abs_le.mpr
  constructor
  · have hlo := (abs_le.mp ht).1
    have hpos := packetGram_nonneg Q N a
    dsimp only [L]
    linarith only [hlo, hpos, hHN]
  · have hzero := mul_nonneg (harmonicReal_nonneg N) hM
    have hHM := mul_le_mul_of_nonneg_right hH hM
    have hscale : 2 + 2 * Real.log Q ≤ L := by
      dsimp only [L]
      linarith only [hlogQ, hlog4]
    have hscaleM := mul_le_mul_of_nonneg_right hscale hM
    linarith only [htop, hgram, hzero, hHM, hscaleM]

/-- The same remainder has the smaller of the quadratic tail and its logarithmic plateau. -/
theorem abs_harmonicGram_torsion_remainder_le_min {Q : ℕ}
    (hQ : 2 ≤ Q) (N : ℕ) (a : ℕ → ℝ) :
    |(∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) -
        (harmonic N : ℝ) * (∑ m ∈ Icc 1 Q, a m ^ 2) +
        torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))| ≤
      min ((Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1))
        (6 * Real.log Q + Real.log 4 + 5) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  by_cases h : (Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1) ≤
      6 * Real.log Q + Real.log 4 + 5
  · rw [min_eq_left h]
    exact abs_harmonicGram_quadratic_torsion_remainder hQ N a
  · rw [min_eq_right (le_of_not_ge h)]
    exact abs_harmonicGram_torsion_remainder_le_log hQ N a

#print axioms abs_harmonicGram_torsion_remainder_le_log
#print axioms abs_harmonicGram_torsion_remainder_le_min

end
end GaloisForLFunctions.SuccessorShellArithmetic
