import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OnlyTheBoundaryStarEntersAtTouching

/-!
# Exact successor windows and the finite-horizon onset

Logarithmic windows are asymmetric in additive coordinates. Their positive
and negative radii are `a(exp w-1)` and `a(1-exp(-w))`. The first unequal
integer pair with one endpoint at most `N` enters at overlap
`N log((N+1)/N)`, strictly below one and tending to one.

These statements classify geometric eligibility. A nonzero prime interaction
also reads the profile autocorrelation and the Mangoldt coefficient.
-/

noncomputable section

set_option autoImplicit false

open Finset Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- Exact radius on the upper side of a logarithmic window. -/
theorem upper_successor_window_iff {a r w : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    |Real.log (a + r) - Real.log a| < w ↔ r < a * (Real.exp w - 1) := by
  have har : 0 < a + r := lt_of_lt_of_le ha (le_add_of_nonneg_right hr)
  have hlog : 0 ≤ Real.log (a + r) - Real.log a :=
    sub_nonneg.mpr (Real.log_le_log ha (le_add_of_nonneg_right hr))
  rw [abs_of_nonneg hlog, ← Real.exp_lt_exp, Real.exp_sub,
    Real.exp_log har, Real.exp_log ha, div_lt_iff₀ ha]
  constructor <;> intro h <;> nlinarith only [h]

/-- Exact radius on the lower side; it differs from the upper radius at every positive width. -/
theorem lower_successor_window_iff {a r w : ℝ} (ha : 0 < a)
    (hr : 0 ≤ r) (hra : r < a) :
    |Real.log (a - r) - Real.log a| < w ↔ r < a * (1 - Real.exp (-w)) := by
  have har : 0 < a - r := sub_pos.mpr hra
  have hlog : Real.log (a - r) - Real.log a ≤ 0 :=
    sub_nonpos.mpr (Real.log_le_log har (sub_le_self a hr))
  rw [abs_of_nonpos hlog]
  have heq : -(Real.log (a - r) - Real.log a) < w ↔
      -w < Real.log (a - r) - Real.log a := by constructor <;> intro h <;> linarith only [h]
  rw [heq, ← Real.exp_lt_exp, Real.exp_sub, Real.exp_log har,
    Real.exp_log ha, lt_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith only [h]

/-- First overlap where an unequal integer pair can enter a horizon-`N` log window. -/
def firstExteriorOverlap (N : ℕ) : ℝ :=
  (N : ℝ) * (Real.log (N + 1 : ℕ) - Real.log N)

theorem firstExteriorOverlap_pos {N : ℕ} (hN : 1 ≤ N) : 0 < firstExteriorOverlap N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  apply mul_pos hN0
  apply sub_pos.mpr
  exact Real.log_lt_log hN0 (by exact_mod_cast Nat.lt_succ_self N)

/-- Finite-horizon shell onset occurs strictly before overlap one. -/
theorem firstExteriorOverlap_lt_one {N : ℕ} (hN : 1 ≤ N) : firstExteriorOverlap N < 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hratio : 1 < ((N : ℝ) + 1) / N := (one_lt_div hN0).mpr (by linarith)
  have h := Real.log_lt_sub_one_of_pos (div_pos hN1 hN0) (ne_of_gt hratio)
  rw [Real.log_div hN1.ne' hN0.ne'] at h
  have heq : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
  rw [heq] at h
  have hmul := (lt_div_iff₀ hN0).mp h
  simpa only [firstExteriorOverlap, Nat.cast_add, Nat.cast_one, mul_comm] using hmul

theorem one_sub_inv_lt_firstExteriorOverlap {N : ℕ} (hN : 1 ≤ N) :
    1 - 1 / (N : ℝ) < firstExteriorOverlap N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hratio : (N : ℝ) / (N + 1) < 1 := (div_lt_one hN1).mpr (by linarith)
  have h := Real.log_lt_sub_one_of_pos (div_pos hN0 hN1) (ne_of_lt hratio)
  rw [Real.log_div hN0.ne' hN1.ne'] at h
  have hgap : 1 / ((N : ℝ) + 1) < Real.log ((N : ℝ) + 1) - Real.log N := by
    have heq : (N : ℝ) / (N + 1) - 1 = -(1 / (N + 1)) := by field_simp; ring
    rw [heq] at h
    linarith only [h]
  have hmul := mul_lt_mul_of_pos_left hgap hN0
  have hfrac : 1 - 1 / (N : ℝ) ≤ (N : ℝ) / (N + 1) := by
    apply (le_div_iff₀ hN1).mpr
    field_simp
    nlinarith only [hN0]
  have hmid : (N : ℝ) / (N + 1) < firstExteriorOverlap N := by
    simpa only [firstExteriorOverlap, Nat.cast_add, Nat.cast_one, mul_one_div] using hmul
  exact hfrac.trans_lt hmid

theorem tendsto_firstExteriorOverlap : Tendsto firstExteriorOverlap atTop (𝓝 1) := by
  have hlo : Tendsto (fun N : ℕ => 1 - 1 / (N : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (show Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (one_sub_inv_lt_firstExteriorOverlap hN).le
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (firstExteriorOverlap_lt_one hN).le

/-- Exact existence criterion for an unequal integer pair in the logarithmic window. -/
theorem exists_integer_shell_iff {N : ℕ} (hN : 2 ≤ N) (c : ℝ) :
    (∃ a b : ℕ, a ∈ Icc 1 N ∧ 1 ≤ b ∧ a ≠ b ∧
      |Real.log b - Real.log a| ≤ c / N) ↔ firstExteriorOverlap N ≤ c := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  constructor
  · rintro ⟨a, b, ha, hb, hne, hgap⟩
    by_cases hc : 1 ≤ c
    · exact (firstExteriorOverlap_lt_one hN1).le.trans hc
    have hgap1 := hgap.trans (div_le_div_of_nonneg_right (not_le.mp hc).le hN0.le)
    obtain ⟨rfl, rfl⟩ := small_integer_log_gap_forces_boundary hN ha hb hne hgap1
    have hlog : 0 ≤ Real.log (N + 1 : ℕ) - Real.log N :=
      sub_nonneg.mpr (Real.log_le_log hN0 (by exact_mod_cast Nat.le_succ N))
    rw [abs_of_nonneg hlog] at hgap
    have h := (le_div_iff₀ hN0).mp hgap
    simpa only [firstExteriorOverlap, mul_comm] using h
  · intro hc
    refine ⟨N, N + 1, mem_Icc.mpr ⟨hN1, le_rfl⟩, by omega, by omega, ?_⟩
    have hlog : 0 ≤ Real.log (N + 1 : ℕ) - Real.log N :=
      sub_nonneg.mpr (Real.log_le_log hN0 (by exact_mod_cast Nat.le_succ N))
    rw [abs_of_nonneg hlog, le_div_iff₀ hN0]
    simpa only [firstExteriorOverlap, mul_comm] using hc

/-- Every fixed overlap below one eventually has no geometrically eligible unequal pair. -/
theorem eventually_no_integer_shell {c : ℝ} (hc : c < 1) :
    ∀ᶠ N : ℕ in atTop, ¬ ∃ a b : ℕ, a ∈ Icc 1 N ∧ 1 ≤ b ∧ a ≠ b ∧
      |Real.log b - Real.log a| ≤ c / N := by
  filter_upwards [tendsto_firstExteriorOverlap.eventually (lt_mem_nhds hc),
    eventually_ge_atTop (2 : ℕ)] with N hthreshold hN
  exact fun h => (not_le_of_gt hthreshold) ((exists_integer_shell_iff hN c).mp h)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.upper_successor_window_iff
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.lower_successor_window_iff
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_integer_shell_iff
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_no_integer_shell
