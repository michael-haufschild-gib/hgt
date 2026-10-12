import GaloisForLFunctions.HTGeometry.AdaptiveAffinityReplication

/-! Minimal power crossings realize every intermediate affinity with escaping exponents. -/

open Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

theorem exists_ennreal_power_crossing {x q : ℝ≥0∞}
    (hx : x < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ n : ℕ, q * x ≤ x ^ n ∧ x ^ n < q := by
  classical
  have hex : ∃ n : ℕ, x ^ n < q :=
    ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hx).eventually
      (gt_mem_nhds hq0)).exists
  let n := Nat.find hex
  have hn : x ^ n < q := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro hzero
    have : 1 < q := by simpa only [hzero, pow_zero] using hn
    exact (not_lt_of_ge hq1.le) this
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨n, ?_, hn⟩
  have hprev : q ≤ x ^ j := le_of_not_gt (Nat.find_min hex (by omega : j < n))
  rw [hj, pow_succ]
  exact mul_le_mul_left hprev x

theorem exists_ennreal_powers_tendsto_intermediate {f : ℕ → ℝ≥0∞} {q : ℝ≥0∞}
    (hf : Tendsto f atTop (𝓝 1)) (hstrict : ∀ᶠ r in atTop, f r < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
      Tendsto (fun r => f r ^ m r) atTop (𝓝 q) := by
  classical
  have hchoice : ∀ r, ∃ n : ℕ, f r < 1 → q * f r ≤ f r ^ n ∧ f r ^ n < q := by
    intro r
    by_cases hr : f r < 1
    · obtain ⟨n, hn⟩ := exists_ennreal_power_crossing hr hq0 hq1
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (hr h).elim⟩
  choose m hm using hchoice
  refine ⟨m, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro N
    have hN := ((ENNReal.continuous_pow N).tendsto 1).comp hf
    rw [one_pow] at hN
    filter_upwards [hstrict, hN.eventually (lt_mem_nhds hq1)] with r hr hNr
    apply Nat.le_of_lt
    by_contra h
    have hle : m r ≤ N := le_of_not_gt h
    have hbound : f r ^ N ≤ q :=
      (pow_le_pow_right_of_le_one' hr.le hle).trans (hm r hr).2.le
    exact not_lt_of_ge hbound hNr
  · have hlow : Tendsto (fun r => q * f r) atTop (𝓝 q) := by
      simpa only [mul_one] using ENNReal.Tendsto.const_mul (a := q) hf (Or.inl one_ne_zero)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
      (hstrict.mono fun r hr => (hm r hr).1)
      (hstrict.mono fun r hr => (hm r hr).2.le)

end GaloisForLFunctions.HTGeometry
