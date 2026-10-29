import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExactSuccessorShellWindows

/-!
# Exact thresholds for every successor shell

Among pairs `1 ≤ a ≤ N`, `b ≥ a+k`, the smallest logarithmic separation is
`log(N+k)-log N`. The geometric overlap threshold for gap at least `k` is
therefore `N log(1+k/N)`, strictly below `k` and converging to `k`.
Prime coefficients and profile autocorrelations are separate from eligibility.
-/

noncomputable section

set_option autoImplicit false

open Finset Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- The first geometric overlap admitting a successor gap at least `k`. -/
def exteriorShellOverlap (N k : ℕ) : ℝ :=
  (N : ℝ) * (Real.log (N + k : ℕ) - Real.log N)

theorem exteriorShellOverlap_one (N : ℕ) : exteriorShellOverlap N 1 = firstExteriorOverlap N := rfl

/-- A fixed additive gap has its smallest logarithmic size at the largest lower endpoint. -/
theorem log_gap_ge_horizon_gap {X a b r : ℝ} (ha : 0 < a) (haX : a ≤ X)
    (hr : 0 ≤ r) (hab : a + r ≤ b) :
    Real.log (X + r) - Real.log X ≤ Real.log b - Real.log a := by
  have hX := ha.trans_le haX
  have hXr : 0 < X + r := lt_of_lt_of_le hX (le_add_of_nonneg_right hr)
  have hb : 0 < b := (lt_of_lt_of_le ha (le_add_of_nonneg_right hr)).trans_le hab
  rw [← Real.log_div hXr.ne' hX.ne', ← Real.log_div hb.ne' ha.ne']
  apply Real.log_le_log (div_pos hXr hX)
  apply (div_le_div_iff₀ hX ha).mpr
  have h₁ := mul_le_mul_of_nonneg_right hab hX.le
  have h₂ := mul_le_mul_of_nonneg_left haX hr
  nlinarith only [h₁, h₂]

/-- Exact finite-horizon classification of the presence of a gap at least `k`. -/
theorem exists_successor_gap_iff {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (c : ℝ) :
    (∃ a b : ℕ, a ∈ Icc 1 N ∧ a + k ≤ b ∧
      |Real.log b - Real.log a| ≤ c / N) ↔ exteriorShellOverlap N k ≤ c := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · rintro ⟨a, b, ha, hab, hwindow⟩
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Icc.mp ha).1
    have haN : (a : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp ha).2
    have habR : (a : ℝ) + k ≤ b := by exact_mod_cast hab
    have hmin := log_gap_ge_horizon_gap ha0 haN (Nat.cast_nonneg k) habR
    have hbound := hmin.trans ((le_abs_self _).trans hwindow)
    have h := (le_div_iff₀ hN0).mp hbound
    simpa only [exteriorShellOverlap, Nat.cast_add, mul_comm] using h
  · intro hc
    refine ⟨N, N + k, mem_Icc.mpr ⟨hN, le_rfl⟩, le_rfl, ?_⟩
    have hlog : 0 ≤ Real.log (N + k : ℕ) - Real.log N :=
      sub_nonneg.mpr (Real.log_le_log hN0 (by exact_mod_cast Nat.le_add_right N k))
    rw [abs_of_nonneg hlog, le_div_iff₀ hN0]
    simpa only [exteriorShellOverlap, mul_comm] using hc

/-- Every positive integer shell enters strictly before its limiting overlap. -/
theorem exteriorShellOverlap_lt {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    exteriorShellOverlap N k < k := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hNk : (0 : ℝ) < N + k := by positivity
  have hratio : 1 < ((N : ℝ) + k) / N := (one_lt_div hN0).mpr (by linarith only [hk0])
  have h := Real.log_lt_sub_one_of_pos (div_pos hNk hN0) (ne_of_gt hratio)
  rw [Real.log_div hNk.ne' hN0.ne'] at h
  have heq : ((N : ℝ) + k) / N - 1 = (k : ℝ) / N := by field_simp; ring
  rw [heq] at h
  have hmul := (lt_div_iff₀ hN0).mp h
  simpa only [exteriorShellOverlap, Nat.cast_add, mul_comm] using hmul

/-- An elementary reciprocal bound quantifies convergence of each shell threshold. -/
theorem exteriorShellOverlap_ge {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    (k : ℝ) - (k : ℝ) ^ 2 / N ≤ exteriorShellOverlap N k := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNk : (0 : ℝ) < N + k := by positivity
  have hlog := HTGeometry.gap_div_le_log_div (show 0 < N by omega)
    (show N < N + k by omega)
  rw [Real.log_div (by positivity : (N + k : ℕ) ≠ (0 : ℝ)) hN0.ne'] at hlog
  simp only [Nat.cast_add, add_sub_cancel_left] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hN0.le
  have heq : (N : ℝ) * ((k : ℝ) / (N + k)) = k - (k : ℝ) ^ 2 / (N + k) := by
    field_simp
    ring
  rw [heq] at hmul
  have hfrac : (k : ℝ) ^ 2 / (N + k) ≤ (k : ℝ) ^ 2 / N :=
    div_le_div_of_nonneg_left (sq_nonneg (k : ℝ)) hN0
      (le_add_of_nonneg_right (Nat.cast_nonneg k))
  have h := (sub_le_sub_left hfrac (k : ℝ)).trans hmul
  simpa only [exteriorShellOverlap, Nat.cast_add] using h

/-- Shell number is the limiting overlap threshold; its finite-horizon threshold is smaller. -/
theorem tendsto_exteriorShellOverlap {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => exteriorShellOverlap N k) atTop (𝓝 (k : ℝ)) := by
  have hsmall : Tendsto (fun N : ℕ => (k : ℝ) ^ 2 / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun N : ℕ => (k : ℝ) - (k : ℝ) ^ 2 / N) atTop (𝓝 (k : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => (k : ℝ)) atTop (𝓝 (k : ℝ)) := tendsto_const_nhds
    simpa only [sub_zero] using hc.sub hsmall
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact exteriorShellOverlap_ge hN hk
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (exteriorShellOverlap_lt hN hk).le

/-- Below shell number `k`, all sufficiently large horizons exclude gaps of size at least `k`. -/
theorem eventually_no_successor_gap {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : c < k) :
    ∀ᶠ N : ℕ in atTop, ¬ ∃ a b : ℕ, a ∈ Icc 1 N ∧ a + k ≤ b ∧
      |Real.log b - Real.log a| ≤ c / N := by
  filter_upwards [(tendsto_exteriorShellOverlap hk).eventually (lt_mem_nhds hc),
    eventually_ge_atTop (1 : ℕ)] with N hthreshold hN
  exact fun h => (not_le_of_gt hthreshold) ((exists_successor_gap_iff hN hk c).mp h)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_successor_gap_iff
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exteriorShellOverlap_ge
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_exteriorShellOverlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_no_successor_gap
