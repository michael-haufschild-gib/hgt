import GaloisForLFunctions.HTGeometry.BohrSpectrum

/-!
# Simultaneous phase recurrence for a finite family of frequencies

A finite family of unimodular characters returns simultaneously to `1`, arbitrarily late: the
vector of characters sampled on an arithmetic progression lives in a compact ball, so two samples
are within `ε`, and their quotient is a late return.  This is the recurrence used to pick the times
at which a bottom off-line shell realizes its negative limit.
-/

open Filter Topology

namespace RHTower

open GaloisForLFunctions

noncomputable section

theorem bohrChar_add (lam s t : ℝ) :
    bohrChar lam (s + t) = bohrChar lam s * bohrChar lam t := by
  rw [bohrChar, bohrChar, bohrChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Simultaneous phase recurrence.**  For every finite family of real frequencies, every `ε > 0`
and every `T`, some time `t ≥ T` brings all the characters within `ε` of `1`. -/
theorem exists_simultaneous_phase_recurrence {ι : Type*} [Fintype ι] (B : ι → ℝ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ ∀ j, ‖bohrChar (B j) t - 1‖ ≤ ε := by
  classical
  set S : ℝ := max T 1 with hSdef
  have hSpos : (0 : ℝ) < S := lt_of_lt_of_le zero_lt_one (le_max_right T 1)
  have hST : T ≤ S := le_max_left T 1
  have hS1 : (1 : ℝ) ≤ S := le_max_right T 1
  set u : ℕ → (ι → ℂ) := fun n j => bohrChar (B j) ((n : ℝ) * S) with hudef
  have hmem : ∀ n, u n ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    rw [hudef]
    simp
  obtain ⟨a, _, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ι → ℂ) 1).tendsto_subseq hmem
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) hε2
  set n : ℕ := φ N with hn
  set m : ℕ := φ (N + 1) with hm
  have hnm : n < m := hφ (Nat.lt_succ_self N)
  have hdist : ‖u m - u n‖ ≤ ε := by
    have h1 : dist (u m) a < ε / 2 := hN (N + 1) (Nat.le_succ N)
    have h2 : dist a (u n) < ε / 2 := by
      rw [dist_comm]
      exact hN N (le_refl N)
    have htri := dist_triangle (u m) a (u n)
    rw [dist_eq_norm] at htri
    linarith
  set k : ℕ := m - n with hk
  have hk1 : 1 ≤ k := by omega
  have hnk : (m : ℝ) = (n : ℝ) + (k : ℝ) := by
    have : n + k = m := by omega
    exact_mod_cast this.symm
  refine ⟨(k : ℝ) * S, ?_, fun j => ?_⟩
  · have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    nlinarith [hSpos, hST, hkR]
  · have hsplit : u m j - u n j
        = bohrChar (B j) ((n : ℝ) * S) * (bohrChar (B j) ((k : ℝ) * S) - 1) := by
      rw [hudef]
      simp only
      rw [hnk, add_mul, bohrChar_add]
      ring
    have hnorm : ‖u m j - u n j‖ = ‖bohrChar (B j) ((k : ℝ) * S) - 1‖ := by
      rw [hsplit, norm_mul, norm_bohrChar, one_mul]
    rw [← hnorm]
    refine le_trans ?_ hdist
    have := norm_le_pi_norm (u m - u n) j
    simpa using this

end

end RHTower
