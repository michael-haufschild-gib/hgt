import Mathlib

/-!
# Choosing the degree and the jet order of a Siegel count

The two inequalities a chartwise Siegel count must satisfy pull in opposite directions: the linear
algebra needs the number of Taylor conditions `card ι · N^n` to stay below the number of unknowns
`(m+1)^(n+1)`, while the Schwarz gain must beat a comparison constant that grows like `D^m` in the
degree.

Both hold simultaneously with `N` proportional to `m`.  Choose the proportionality factor `κ` so
that `D·q^κ ≤ 1/2`, where `q` is the ratio of the two radii; then the gain side is at most
`(1/2)^m·(κm+1)^n·S`, which tends to zero, while the counting side needs only `m ≥ card ι · κ^n`
because `(m+1)^(n+1) ≥ (m+1)·m^n`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **The parameters of a Siegel count exist.** -/
theorem exists_siegel_count_params (n Icard : ℕ) {D S q : ℝ} (hD : 1 ≤ D) (hS : 0 ≤ S)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ N' m : ℕ, 0 < m ∧ Icard * N' ^ n < (m + 1) ^ (n + 1) ∧
      D ^ m * ((((N' + 1) ^ n : ℕ) : ℝ) * q ^ N' * S) < 1 := by
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD
  -- the proportionality factor
  have hqt : Filter.Tendsto (fun k : ℕ => D * q ^ k) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul D
    rwa [mul_zero] at h
  obtain ⟨κ₀, hκ₀⟩ := (hqt.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).exists_forall_of_atTop
  set κ : ℕ := max κ₀ 1 with hκdef
  have hκ1 : 1 ≤ κ := le_max_right _ _
  have hκspec : D * q ^ κ < 1 / 2 := hκ₀ κ (le_max_left _ _)
  have hκnn : 0 ≤ D * q ^ κ := mul_nonneg hDpos.le (pow_nonneg hq0 _)
  -- the degree
  set T : ℝ := ((κ + 1 : ℕ) : ℝ) ^ n * S + 1 with hT
  have hTpos : 0 < T := by
    have : (0 : ℝ) ≤ ((κ + 1 : ℕ) : ℝ) ^ n * S := mul_nonneg (pow_nonneg (by positivity) n) hS
    rw [hT]; linarith
  have hstep : Filter.Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ n * (1 / 2 : ℝ) ^ m)
      atTop (𝓝 0) := by
    have h0 := tendsto_pow_const_mul_const_pow_of_lt_one n (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)
    have h1 : Filter.Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ n * (1 / 2 : ℝ) ^ (m + 1))
        atTop (𝓝 0) := h0.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := h1.const_mul (2 : ℝ)
    rw [mul_zero] at h2
    refine h2.congr fun m => ?_
    rw [pow_succ]
    ring
  obtain ⟨M, hM⟩ :=
    ((hstep.eventually_lt_const (by positivity : (0 : ℝ) < 1 / T))).exists_forall_of_atTop
  set m : ℕ := max (max M 1) (Icard * κ ^ n) with hmdef
  have hm1 : 1 ≤ m := le_trans (le_max_right M 1) (le_max_left _ _)
  have hmM : M ≤ m := le_trans (le_max_left M 1) (le_max_left _ _)
  have hmI : Icard * κ ^ n ≤ m := le_max_right _ _
  refine ⟨κ * m, m, hm1, ?_, ?_⟩
  · -- the counting inequality
    calc Icard * (κ * m) ^ n = (Icard * κ ^ n) * m ^ n := by rw [mul_pow]; ring
      _ ≤ m * m ^ n := Nat.mul_le_mul_right _ hmI
      _ = m ^ (n + 1) := by rw [pow_succ]; ring
      _ < (m + 1) ^ (n + 1) := Nat.pow_lt_pow_left (Nat.lt_succ_self m) (Nat.succ_ne_zero n)
  · -- the gain inequality
    have hpow : D ^ m * q ^ (κ * m) = (D * q ^ κ) ^ m := by
      rw [mul_pow, ← pow_mul, mul_comm κ m]
    have hcast : (((κ * m + 1) ^ n : ℕ) : ℝ) = ((κ * m + 1 : ℕ) : ℝ) ^ n := by push_cast; ring
    have hle1 : ((κ * m + 1 : ℕ) : ℝ) ≤ ((κ + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by
      have hnat : κ * m + 1 ≤ (κ + 1) * (m + 1) := by
        have hexp : (κ + 1) * (m + 1) = κ * m + (κ + m + 1) := by ring
        rw [hexp]
        exact Nat.add_le_add_left (by omega) _
      calc ((κ * m + 1 : ℕ) : ℝ) ≤ (((κ + 1) * (m + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = ((κ + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    have hle2 : ((κ * m + 1 : ℕ) : ℝ) ^ n
        ≤ ((κ + 1 : ℕ) : ℝ) ^ n * ((m + 1 : ℕ) : ℝ) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hle1 n
    have hDq : (D * q ^ κ) ^ m ≤ (1 / 2 : ℝ) ^ m := pow_le_pow_left₀ hκnn hκspec.le m
    have hMspec : ((m + 1 : ℕ) : ℝ) ^ n * (1 / 2 : ℝ) ^ m < 1 / T := hM m hmM
    calc D ^ m * ((((κ * m + 1) ^ n : ℕ) : ℝ) * q ^ (κ * m) * S)
        = (D ^ m * q ^ (κ * m)) * (((κ * m + 1 : ℕ) : ℝ) ^ n * S) := by rw [hcast]; ring
      _ = (D * q ^ κ) ^ m * (((κ * m + 1 : ℕ) : ℝ) ^ n * S) := by rw [hpow]
      _ ≤ (1 / 2 : ℝ) ^ m * (((κ + 1 : ℕ) : ℝ) ^ n * ((m + 1 : ℕ) : ℝ) ^ n * S) := by
          refine mul_le_mul hDq ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hle2 hS
      _ = (((κ + 1 : ℕ) : ℝ) ^ n * S) * (((m + 1 : ℕ) : ℝ) ^ n * (1 / 2 : ℝ) ^ m) := by ring
      _ < 1 := by
          have hA : (0 : ℝ) ≤ ((κ + 1 : ℕ) : ℝ) ^ n * S :=
            mul_nonneg (pow_nonneg (by positivity) n) hS
          have hB : ((κ + 1 : ℕ) : ℝ) ^ n * S < T := by rw [hT]; linarith
          have hC : ((m + 1 : ℕ) : ℝ) ^ n * (1 / 2 : ℝ) ^ m < 1 / T := hMspec
          have hCnn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ n * (1 / 2 : ℝ) ^ m := by positivity
          calc (((κ + 1 : ℕ) : ℝ) ^ n * S) * (((m + 1 : ℕ) : ℝ) ^ n * (1 / 2 : ℝ) ^ m)
              ≤ (((κ + 1 : ℕ) : ℝ) ^ n * S) * (1 / T) := by
                exact mul_le_mul_of_nonneg_left hC.le hA
            _ < T * (1 / T) := by
                refine mul_lt_mul_of_pos_right hB ?_
                positivity
            _ = 1 := by field_simp

end GaloisForLFunctions.HTGeometry
