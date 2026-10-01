import GaloisForLFunctions.RHTower.SteinhausCofactorPrimeBlocks



open Filter Topology
noncomputable section
namespace RHTower

/-- Square smoothing scales and cubic polynomial cutoffs satisfy both the long-cofactor
requirement and the exact affine free-window seam. All fixed character prefixes are retained. -/
theorem eventually_squareScale_cubicCutoff_freeWindow_seam
    {K : ℕ} (hK : 0 < K) (B D : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ n ^ 2 ≤ n ^ 3 ∧ n ^ 2 * D ≤ n ^ 3 ∧
        B ≤ n ^ 2 / (2 * K) ∧ n ^ 3 < (n ^ 2 / (2 * K)) * (n ^ 2 / (2 * K)) := by
  have h2K : 0 < 2 * K := by omega
  have h4K : 0 < 4 * K := by omega
  have h16 : 0 < 16 * K ^ 2 := by positivity
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop D,
    eventually_ge_atTop (2 * K * (B + 1)), eventually_ge_atTop (16 * K ^ 2)]
    with n hn hD hB hbig
  have hnpow : n ≤ n ^ 2 := by nlinarith
  have hYB : B + 1 ≤ n ^ 2 / (2 * K) := (Nat.le_div_iff_mul_le h2K).mpr (by
    simpa only [Nat.mul_comm] using hB.trans hnpow)
  have hY : 0 < n ^ 2 / (2 * K) := by omega
  have hscale : n ^ 2 < 4 * K * (n ^ 2 / (2 * K)) := by
    have hfloor := Nat.lt_mul_div_succ (n ^ 2) h2K
    have hh : n ^ 2 / (2 * K) + 1 ≤ 2 * (n ^ 2 / (2 * K)) := by omega
    have hmul := Nat.mul_le_mul_left (2 * K) hh
    nlinarith
  have hsq : (n ^ 2) ^ 2 < (4 * K * (n ^ 2 / (2 * K))) ^ 2 := by
    exact Nat.pow_lt_pow_left hscale (by decide)
  have hcompare : (16 * K ^ 2) * n ^ 3 <
      (16 * K ^ 2) * ((n ^ 2 / (2 * K)) * (n ^ 2 / (2 * K))) := by
    calc
      _ ≤ n * n ^ 3 := Nat.mul_le_mul_right (n ^ 3) hbig
      _ = (n ^ 2) ^ 2 := by ring
      _ < (4 * K * (n ^ 2 / (2 * K))) ^ 2 := hsq
      _ = _ := by ring
  refine ⟨hn, ?_, ?_, by omega, (Nat.mul_lt_mul_left h16).mp hcompare⟩
  · nlinarith
  · calc
      n ^ 2 * D ≤ n ^ 2 * n := Nat.mul_le_mul_left (n ^ 2) hD
      _ = n ^ 3 := by ring

end RHTower
