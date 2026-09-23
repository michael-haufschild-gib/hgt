import GaloisForLFunctions.RHTower.ZetaOneLineUniformLower
import GaloisForLFunctions.RHTower.MoebiusPretentiousGap
import GaloisForLFunctions.RHTower.Sieve.MoebiusDistanceSharp

/-!
# Full-logarithmic saving for the smooth Möbius polynomial

The corpus previously combined its uniform frequency estimate with Euler damping only through the
weaker distance `D² ≥ (1/100) log log z - O(1)`.  The power-of-log lower bound for zeta on the
whole line gives the sharp dependence

`D² ≥ log log z - 11 log log (|t| + e) - O(1)`.

Substitution in the exact finite Euler product cancels the full prime harmonic mass.  Consequently
the squarefree `z`-smooth Möbius polynomial is bounded by a fixed multiple of
`(log (|t| + e))^(11 : ℕ)`, independently of `z`.  Both results below are closed eventual theorems; no
frequency cutoff, analytic premise, or computation is introduced.
-/

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-- The Möbius pretentious distance keeps its full `log log z` mass at every frequency, with only
the zeta-line power-of-log loss. -/
theorem eventually_mulDistSqPair_moebiusC_ge_logPower :
    ∃ C : ℝ, ∀ᶠ z : ℕ in atTop, ∀ t : ℝ,
      Real.log (Real.log (z : ℝ))
          - 11 * Real.log (Real.log (|t| + Real.exp 1)) - C
        ≤ mulDistSqPair moebiusC (charFn t) (Nat.primesLE z) := by
  obtain ⟨c, hc0, hzeta⟩ := RHTower.exists_uniform_lower_bound_riemannZeta
  let C : ℝ :=
    (2 * ((2 * mertensFirstConst + 1 / 2) + 1) + RHTower.zetaDeficitConst)
      - Real.log c - 2 * meisselMertensConst
  refine ⟨C, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 4)] with z hzc
  intro t
  have hz0 : (0 : ℝ) < (z : ℝ) := lt_of_lt_of_le (Real.exp_pos 4) hzc
  have hlogz4 : (4 : ℝ) ≤ Real.log (z : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 4) hzc
    rwa [Real.log_exp] at h
  have hσ1 : (1 : ℝ) < 1 + 1 / Real.log (z : ℝ) := by
    have : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
    linarith
  have hσ2 : 1 + 1 / Real.log (z : ℝ) ≤ 5 / 4 := by
    have hdiv : 1 / Real.log (z : ℝ) ≤ (1 : ℝ) / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  let L : ℝ := Real.log (|t| + Real.exp 1)
  have hL1 : (1 : ℝ) ≤ L := by
    dsimp [L]
    have harg : Real.exp 1 ≤ |t| + Real.exp 1 := by linarith [abs_nonneg t]
    have h := Real.log_le_log (Real.exp_pos 1) harg
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL1
  have hzLower := hzeta (1 + 1 / Real.log (z : ℝ)) t hσ1 hσ2
  have hcdiv : (0 : ℝ) < c / L ^ (11 : ℕ) := by positivity
  have hpoint :
      (((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = ((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
    ring
  rw [hpoint] at hzLower
  have hmain := RHTower.primeCosPlusSum_ge_of_zeta_lower hcdiv
    (show Real.exp 2 ≤ (z : ℝ) by
      exact (Real.exp_le_exp.mpr (by norm_num)).trans hzc)
    hzLower
  have hlogdiv : Real.log (c / L ^ (11 : ℕ)) = Real.log c - 11 * Real.log L := by
    rw [Real.log_div (ne_of_gt hc0) (ne_of_gt (by positivity : (0 : ℝ) < L ^ (11 : ℕ))),
      Real.log_pow]
    push_cast
    ring
  rw [hlogdiv] at hmain
  have hf : ∀ p ∈ Nat.primesLE z, moebiusC p = -1 :=
    fun p hp => moebiusC_prime (Nat.mem_primesLE.mp hp).2
  rw [mulDistSqPair_neg_one_charFn hf t]
  have hfloor : ⌊((z : ℕ) : ℝ)⌋₊ = z := Nat.floor_natCast z
  rw [RHTower.primeCosPlusSum, hfloor] at hmain
  dsimp [C, L]
  linarith

/-- The squarefree smooth Möbius polynomial is bounded by a fixed log-power of frequency,
uniformly in the smoothness cutoff. -/
theorem exists_norm_sum_moebius_smooth_le_logPower :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z : ℕ in atTop, ∀ t : ℝ,
      ‖∑ n ∈ (Nat.primesLE z).powerset.image (fun S => ∏ p ∈ S, p),
          ((1 / (n : ℝ) : ℝ) : ℂ)
            * (moebiusC n *
              Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))‖
        ≤ C * (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ) := by
  obtain ⟨C₀, hdist⟩ := eventually_mulDistSqPair_moebiusC_ge_logPower
  let C : ℝ := Real.exp (Real.pi ^ (2 : ℕ) / 6 + mertensSecondUpperConst + C₀)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hdist, eventually_ge_atTop 2] with z hz hz2
  intro t
  let L : ℝ := Real.log (|t| + Real.exp 1)
  have hL1 : (1 : ℝ) ≤ L := by
    dsimp [L]
    have harg : Real.exp 1 ≤ |t| + Real.exp 1 := by linarith [abs_nonneg t]
    have h := Real.log_le_log (Real.exp_pos 1) harg
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL1
  have hP : ∀ p ∈ Nat.primesLE z, p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp hp).2
  have hbase := norm_sum_moebius_smooth_le_exp t hP
  have hsq := sum_inv_sq_primesLE_le_pi z
  have hmert : (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
      ≤ Real.log (Real.log (z : ℝ)) + mertensSecondUpperConst := mertensS_le hz2
  have hf : ∀ p ∈ Nat.primesLE z, moebiusC p = -1 :=
    fun p hp => moebiusC_prime (Nat.mem_primesLE.mp hp).2
  have hD := hz t
  rw [mulDistSqPair_neg_one_charFn hf t] at hD
  have hsplit :
      (∑ p ∈ Nat.primesLE z,
          (1 + Real.cos (t * Real.log (p : ℝ))) / (p : ℝ))
        = (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
          + ∑ p ∈ Nat.primesLE z,
              Real.cos (t * Real.log (p : ℝ)) / (p : ℝ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit] at hD
  have hexp :
      (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ (2 : ℕ))
          - ∑ p ∈ Nat.primesLE z,
              Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)
        ≤ Real.pi ^ (2 : ℕ) / 6 + mertensSecondUpperConst + C₀ + 11 * Real.log L := by
    dsimp [L] at hD ⊢
    linarith
  refine hbase.trans (le_trans (Real.exp_le_exp.mpr hexp) ?_)
  change Real.exp (Real.pi ^ (2 : ℕ) / 6 + mertensSecondUpperConst + C₀ + 11 * Real.log L)
      ≤ C * L ^ (11 : ℕ)
  have hpow : Real.exp (11 * Real.log L) = L ^ (11 : ℕ) := by
    calc
      Real.exp (11 * Real.log L) = Real.exp (Real.log L) ^ (11 : ℕ) := by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log L) 11
      _ = L ^ (11 : ℕ) := by rw [Real.exp_log hL0]
  rw [show Real.pi ^ (2 : ℕ) / 6 + mertensSecondUpperConst + C₀ + 11 * Real.log L
      = (Real.pi ^ (2 : ℕ) / 6 + mertensSecondUpperConst + C₀) + 11 * Real.log L by ring,
    Real.exp_add, hpow]

end

end RHTower.Sieve
