import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex

/-!
# The central index of a transcendental entire function diverges

For a polynomial the central index is eventually its degree.  For a transcendental entire function
there is no last nonzero coefficient, and every fixed index is eventually beaten: given `N`, choose a
nonzero coefficient at some `m > N`; once `r` exceeds the finitely many ratios `|a_n| / |a_m|` with
`n <= N`, the term of index `m` dominates all of them, so the maximum cannot be attained below `m`.

This is the statement that makes `nu(r)` an admissible scale in the first place — every asymptotic
law of Wiman--Valiron type is a statement about `nu(r) -> infinity`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ}

/-- **The central index diverges.**  If the coefficient sequence has nonzero entries arbitrarily far
out — which for an entire function is exactly transcendence — then the central index tends to
infinity with the radius. -/
theorem tendsto_centralIndex_atTop (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    Tendsto (fun r : ℝ => centralIndex a r) atTop atTop := by
  classical
  refine tendsto_atTop_atTop.mpr fun N => ?_
  obtain ⟨m, hm, hmne⟩ := htrans (N + 1)
  have hmpos : (0 : ℝ) < ‖a m‖ := norm_pos_iff.mpr hmne
  set C : ℝ := (Finset.range (N + 1)).sup' (by simp) (fun n => ‖a n‖ / ‖a m‖) with hC
  refine ⟨max 1 (C + 1), fun r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_left _ _) hr
  have hrC : C + 1 ≤ r := le_trans (le_max_right _ _) hr
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  by_contra hcon
  have hlt : centralIndex a r < N := by omega
  set v : ℕ := centralIndex a r with hv
  have hvm : v < m := by omega
  -- the central term is the maximum term
  have hterm : ‖a v‖ * r ^ v = maxTerm a r := term_centralIndex_eq ha hrpos hmne
  -- but the term of index `m` is strictly larger
  have hratio : ‖a v‖ / ‖a m‖ ≤ C := by
    refine Finset.le_sup' (fun n => ‖a n‖ / ‖a m‖) ?_
    exact Finset.mem_range.mpr (by omega)
  have hpow : r ≤ r ^ (m - v) := by
    have hone : 1 ≤ m - v := by omega
    calc r = r ^ (1 : ℕ) := (pow_one r).symm
      _ ≤ r ^ (m - v) := pow_le_pow_right₀ hr1 hone
  have hkey : ‖a v‖ < ‖a m‖ * r ^ (m - v) := by
    have h1 : ‖a v‖ / ‖a m‖ < r := by linarith
    have h2 : ‖a v‖ < ‖a m‖ * r := by
      rw [div_lt_iff₀ hmpos] at h1
      linarith [h1]
    have h3 : ‖a m‖ * r ≤ ‖a m‖ * r ^ (m - v) :=
      mul_le_mul_of_nonneg_left hpow hmpos.le
    linarith
  have hsplit : r ^ m = r ^ v * r ^ (m - v) := by
    rw [← pow_add]
    congr 1
    omega
  have hstrict : ‖a v‖ * r ^ v < ‖a m‖ * r ^ m := by
    rw [hsplit]
    have hrv : (0 : ℝ) < r ^ v := pow_pos hrpos v
    calc ‖a v‖ * r ^ v < (‖a m‖ * r ^ (m - v)) * r ^ v :=
          mul_lt_mul_of_pos_right hkey hrv
      _ = ‖a m‖ * (r ^ v * r ^ (m - v)) := by ring
  have hle : ‖a m‖ * r ^ m ≤ maxTerm a r := term_le_maxTerm ha hrpos m
  rw [hterm] at hstrict
  linarith

/-- The central index of a transcendental entire function is eventually positive. -/
theorem eventually_zero_lt_centralIndex (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    ∀ᶠ r : ℝ in atTop, 0 < ((centralIndex a r : ℕ) : ℝ) := by
  have h := (tendsto_centralIndex_atTop ha htrans).eventually_ge_atTop 1
  filter_upwards [h] with r hr
  exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hr

/-! ## Domination of every power -/

/-- **A transcendental entire maximum term outgrows every power.**  This is the step that kills every
term of lower total degree after dividing an algebraic differential equation by a power of the
solution: there is a nonzero coefficient beyond the exponent `k`, and its own term already exceeds
`r^k` by a factor tending to infinity. -/
theorem tendsto_maxTerm_div_pow_atTop (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) (k : ℕ) :
    Tendsto (fun r : ℝ => maxTerm a r / r ^ k) atTop atTop := by
  obtain ⟨m, hm, hmne⟩ := htrans (k + 1)
  have hmpos : (0 : ℝ) < ‖a m‖ := norm_pos_iff.mpr hmne
  have hbase : Tendsto (fun r : ℝ => ‖a m‖ * r) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hmpos tendsto_id
  refine tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr1
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have h1 : ‖a m‖ * r ^ m ≤ maxTerm a r := term_le_maxTerm ha hrpos m
  have hsplit : r ^ m = r ^ k * r ^ (m - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow : r ≤ r ^ (m - k) :=
    calc r = r ^ (1 : ℕ) := (pow_one r).symm
      _ ≤ r ^ (m - k) := pow_le_pow_right₀ hr1 (by omega)
  rw [le_div_iff₀ (pow_pos hrpos k)]
  calc ‖a m‖ * r * r ^ k ≤ ‖a m‖ * r ^ (m - k) * r ^ k := by gcongr
    _ = ‖a m‖ * r ^ m := by rw [hsplit]; ring
    _ ≤ maxTerm a r := h1

end GaloisForLFunctions.HTGeometry
