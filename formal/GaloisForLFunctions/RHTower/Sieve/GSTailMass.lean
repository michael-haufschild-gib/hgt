import GaloisForLFunctions.RHTower.Sieve.MoebiusDistanceTail

/-!
# The harmonic mass surviving the Granville–Soundararajan cutoff

The cutoff `gsCutoff z = ⌈exp((log z)^{0.99})⌉` keeps a positive proportion of the harmonic mass of
the primes below `z`: `log gsCutoff z ≤ (log z)^{0.99} + 1`, so `log log gsCutoff z` is at most
`log 2 + 0.99·log log z`, and Mertens' second theorem leaves `0.01·log log z − O(1)`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The cutoff's logarithm is barely above the exponent. -/
theorem log_gsCutoff_le {z : ℕ} (hz : 1 ≤ Real.log (z : ℝ)) :
    Real.log ((gsCutoff z : ℕ) : ℝ) ≤ (Real.log (z : ℝ)) ^ (0.99 : ℝ) + 1 := by
  set u : ℝ := (Real.log (z : ℝ)) ^ (0.99 : ℝ) with hu
  have hu0 : (0 : ℝ) ≤ u := Real.rpow_nonneg (by linarith) _
  have hceil : ((gsCutoff z : ℕ) : ℝ) ≤ Real.exp u + 1 := by
    rw [gsCutoff, ← hu]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.exp_pos u).le)
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hstep : Real.exp u + 1 ≤ Real.exp (u + 1) := by
    rw [Real.exp_add]
    have h1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu0
    nlinarith [h1, he2]
  have hle : ((gsCutoff z : ℕ) : ℝ) ≤ Real.exp (u + 1) := le_trans hceil hstep
  have hpos : (0 : ℝ) < ((gsCutoff z : ℕ) : ℝ) := by
    have h2 : 2 ≤ gsCutoff z := two_le_gsCutoff (by linarith)
    have : (2 : ℝ) ≤ ((gsCutoff z : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  have hlog := Real.log_le_log hpos hle
  rwa [Real.log_exp] at hlog

/-- **The mass surviving the cutoff.** -/
theorem gs_tail_mass_ge {z : ℕ} (hz : 1 ≤ Real.log (z : ℝ)) (hz2 : 2 ≤ z) :
    0.01 * Real.log (Real.log (z : ℝ))
        - (mertensSecondLowerConst + mertensSecondUpperConst + Real.log 2)
      ≤ mertensS z - mertensS (gsCutoff z) := by
  have hy2 : 2 ≤ gsCutoff z := two_le_gsCutoff (by linarith)
  have hlow := le_mertensS (N := z) hz2
  have hup := mertensS_le (N := gsCutoff z) hy2
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  set u : ℝ := (Real.log (z : ℝ)) ^ (0.99 : ℝ) with hu
  have hu1 : (1 : ℝ) ≤ u := by
    rw [hu]
    exact Real.one_le_rpow hz (by norm_num)
  have hlogy := log_gsCutoff_le hz
  rw [← hu] at hlogy
  have hlogy0 : (0 : ℝ) < Real.log ((gsCutoff z : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((gsCutoff z : ℕ) : ℝ) := by exact_mod_cast hy2
    have := Real.log_le_log (by norm_num : (0:ℝ) < 2) h2
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hstep : Real.log ((gsCutoff z : ℕ) : ℝ) ≤ 2 * u := by linarith
  have hloglog : logLog (gsCutoff z) ≤ Real.log 2 + 0.99 * Real.log (Real.log (z : ℝ)) := by
    have h1 : Real.log (Real.log ((gsCutoff z : ℕ) : ℝ)) ≤ Real.log (2 * u) :=
      Real.log_le_log hlogy0 hstep
    have h2 : Real.log (2 * u) = Real.log 2 + 0.99 * Real.log (Real.log (z : ℝ)) := by
      rw [Real.log_mul (by norm_num) (by linarith), hu, Real.log_rpow hlogz0]
    rw [logLog]
    linarith [h1, h2.le, h2.ge]
  have hlogLz : logLog z = Real.log (Real.log (z : ℝ)) := rfl
  rw [hlogLz] at hlow
  linarith [hlow, hup, hloglog]

end

end RHTower.Sieve
