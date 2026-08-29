import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogPrincipalCollapse
import GaloisForLFunctions.RHTower.Sieve.SelbergDilatedLogMonomialAsymptotic

/-!
# Harmonic replacement for the gcd-logarithmic principal model

The logarithmically weighted rectangular model
`∑_{d ≤ N/max(a,b)} (log d / d)·K_{q+1}(N/(ad))·K_{r+1}(N/(bd))`
is replaced by its harmonic main term
`∑_{d} (log d / d)·(q+1)(r+1)·log(N/(ad))^q·log(N/(bd))^r`
with an error `o((log N)^{q+r+2})`.

The pointwise input is isolated first: the product of two Möbius log-power kernels is within a
prescribed *relative* error of its leading term as soon as both cutoffs are large.  That lemma is
independent of the weight, so it also reproves the unweighted replacement.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- **Relative closeness of a product of two Möbius log-power kernels to its leading term.** -/
theorem exists_kernelProduct_close (q r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 2 ≤ K ∧ ∀ Y Z : ℝ, K ≤ Y → K ≤ Z →
      |moebiusLogPowerKernelReal (q + 1) Y * moebiusLogPowerKernelReal (r + 1) Z -
          ((q + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) *
            (Real.log Y ^ q * Real.log Z ^ r)| ≤
        δ * (Real.log Y ^ q * Real.log Z ^ r) := by
  obtain ⟨DB, hDB, hDBbound⟩ :=
    exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow r
  set cq : ℝ := ((q + 1 : ℕ) : ℝ) with hcq
  set cr : ℝ := ((r + 1 : ℕ) : ℝ) with hcr
  have hcqpos : 0 < cq := by rw [hcq]; positivity
  have hden : 0 < DB + cq := by positivity
  set η : ℝ := δ / (DB + cq) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hAnear : ∀ᶠ Y : ℝ in atTop,
      |moebiusLogPowerKernelReal (q + 1) Y / Real.log Y ^ q - cq| < η :=
    (tendsto_moebiusLogPowerKernelReal_div_log_pow q).eventually
      (Metric.ball_mem_nhds cq hηpos)
  rw [eventually_atTop] at hAnear
  obtain ⟨KA, hKA⟩ := hAnear
  have hBnear : ∀ᶠ Z : ℝ in atTop,
      |moebiusLogPowerKernelReal (r + 1) Z / Real.log Z ^ r - cr| < η :=
    (tendsto_moebiusLogPowerKernelReal_div_log_pow r).eventually
      (Metric.ball_mem_nhds cr hηpos)
  rw [eventually_atTop] at hBnear
  obtain ⟨KB, hKB⟩ := hBnear
  refine ⟨max (max KA KB) 2, le_max_right _ _, ?_⟩
  intro Y Z hY hZ
  have hKAY : KA ≤ Y := le_trans (le_trans (le_max_left KA KB) (le_max_left _ _)) hY
  have hKBZ : KB ≤ Z := le_trans (le_trans (le_max_right KA KB) (le_max_left _ _)) hZ
  have hY2 : (2 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  have hZ2 : (2 : ℝ) ≤ Z := le_trans (le_max_right _ _) hZ
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hYone : (1 : ℝ) ≤ Y := by linarith
  have hZone : (1 : ℝ) ≤ Z := by linarith
  have hA : |moebiusLogPowerKernelReal (q + 1) Y - cq * Real.log Y ^ q| ≤
      η * Real.log Y ^ q := by
    have h := (hKA Y hKAY).le
    rw [div_sub' _ _ _ (pow_pos hlogY q).ne', abs_div,
      abs_of_pos (pow_pos hlogY q)] at h
    exact (div_le_iff₀ (pow_pos hlogY q)).mp h
  have hB : |moebiusLogPowerKernelReal (r + 1) Z - cr * Real.log Z ^ r| ≤
      η * Real.log Z ^ r := by
    have h := (hKB Z hKBZ).le
    rw [div_sub' _ _ _ (pow_pos hlogZ r).ne', abs_div,
      abs_of_pos (pow_pos hlogZ r)] at h
    exact (div_le_iff₀ (pow_pos hlogZ r)).mp h
  have hBglobal : |moebiusLogPowerKernelReal (r + 1) Z| ≤ DB * Real.log Z ^ r :=
    hDBbound Z hZone
  have hsplit :
      moebiusLogPowerKernelReal (q + 1) Y * moebiusLogPowerKernelReal (r + 1) Z -
          cq * cr * (Real.log Y ^ q * Real.log Z ^ r) =
        (moebiusLogPowerKernelReal (q + 1) Y - cq * Real.log Y ^ q) *
            moebiusLogPowerKernelReal (r + 1) Z +
          (cq * Real.log Y ^ q) *
            (moebiusLogPowerKernelReal (r + 1) Z - cr * Real.log Z ^ r) := by
    ring
  rw [hsplit]
  have hterm1 : |(moebiusLogPowerKernelReal (q + 1) Y - cq * Real.log Y ^ q) *
      moebiusLogPowerKernelReal (r + 1) Z| ≤
      (η * Real.log Y ^ q) * (DB * Real.log Z ^ r) := by
    rw [abs_mul]
    exact mul_le_mul hA hBglobal (abs_nonneg _)
      (mul_nonneg hηpos.le (pow_nonneg hlogY.le q))
  have hterm2 : |(cq * Real.log Y ^ q) *
      (moebiusLogPowerKernelReal (r + 1) Z - cr * Real.log Z ^ r)| ≤
      (cq * Real.log Y ^ q) * (η * Real.log Z ^ r) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ cq * Real.log Y ^ q)]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have hfinal : (η * Real.log Y ^ q) * (DB * Real.log Z ^ r) +
      (cq * Real.log Y ^ q) * (η * Real.log Z ^ r) ≤
      δ * (Real.log Y ^ q * Real.log Z ^ r) := by
    have hcollect : (η * Real.log Y ^ q) * (DB * Real.log Z ^ r) +
        (cq * Real.log Y ^ q) * (η * Real.log Z ^ r) =
        (η * (DB + cq)) * (Real.log Y ^ q * Real.log Z ^ r) := by ring
    rw [hcollect]
    have hηval : η * (DB + cq) = δ := by
      rw [hη]
      field_simp
    rw [hηval]
  exact le_trans (le_trans (abs_add_le _ _) (add_le_add hterm1 hterm2)) hfinal

end

end RHTower.Sieve
