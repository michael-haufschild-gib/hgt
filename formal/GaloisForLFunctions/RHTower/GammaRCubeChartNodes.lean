import GaloisForLFunctions.RHTower.GammaRCubeAntiChartSpace

/-!
# Supercritical node sequences in the cube-root chart

The integers sit at `X_n = √3 n^{1/3}` in the chart (`X_n³/(3√3) = n`), and
`X_{n+2}(X_{n+2} - X_n) ≤ 4√3/X_n`. The node sequence `nodeSeq N₀ m` consists of `m+1` equally
spaced points `X_{N₀}(j+1)/(m+1)` followed by every other integer node `X_{N₀+2k}`. It is strictly
increasing, positive, unbounded, and satisfies the supercritical gap condition
`max(p_j,p_{j+1})(p_{j+1}-p_j) ≤ a/2` once `X_{N₀} ≥ 8√3/a` and `m+1 ≥ 2X_{N₀}²/a`. The skipped
integer nodes `X_{N₀+2k+1}` are never nodes.
-/

open Filter Set Topology

noncomputable section

namespace RHTower.DegreeThreeHankel

/-- The integer `n` in the cube-root chart: `X_n = √3 n^{1/3}`. -/
def nodeX (n : ℕ) : ℝ := Real.sqrt 3 * (n : ℝ) ^ (1 / 3 : ℝ)

theorem nodeX_nonneg (n : ℕ) : 0 ≤ nodeX n := by unfold nodeX; positivity

theorem nodeX_cube (n : ℕ) : nodeX n ^ 3 = 3 * Real.sqrt 3 * n := by
  unfold nodeX
  rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 3 : ℝ)), ← Real.rpow_mul (Nat.cast_nonneg n)]
  have h3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num)]
  rw [h3]; norm_num

theorem chartPoint_nodeX (n : ℕ) : chartPoint (nodeX n) = n := by
  unfold chartPoint
  rw [nodeX_cube]
  have : (0 : ℝ) < 3 * Real.sqrt 3 := by positivity
  field_simp

theorem nodeX_strictMono : StrictMono nodeX := by
  intro a b hab
  unfold nodeX
  have h : (a : ℝ) ^ (1 / 3 : ℝ) < (b : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_lt_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) (by norm_num)
  exact mul_lt_mul_of_pos_left h (by positivity)

theorem nodeX_pos {n : ℕ} (hn : 1 ≤ n) : 0 < nodeX n :=
  lt_of_le_of_lt (nodeX_nonneg 0) (nodeX_strictMono (by omega))

theorem one_le_nodeX {n : ℕ} (hn : 1 ≤ n) : 1 ≤ nodeX n := by
  unfold nodeX
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have h2 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith

theorem tendsto_nodeX : Tendsto nodeX atTop atTop := by
  unfold nodeX
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  exact h.const_mul_atTop (by positivity)

/-- Two chart steps: `X_{n+2} ≤ 2X_n` and `X_{n+2}(X_{n+2} - X_n) ≤ 4√3/X_n` for `n ≥ 1`. -/
theorem nodeX_two_step {n : ℕ} (hn : 1 ≤ n) :
    nodeX (n + 2) ≤ 2 * nodeX n ∧ nodeX (n + 2) * (nodeX (n + 2) - nodeX n) ≤ 4 * Real.sqrt 3 / nodeX n := by
  set u := nodeX (n + 2)
  set v := nodeX n
  have hv : 0 < v := nodeX_pos hn
  have hv1 : 1 ≤ v := one_le_nodeX hn
  have huv : v ≤ u := (nodeX_strictMono (by omega : n < n + 2)).le
  have hcube : u ^ 3 - v ^ 3 = 6 * Real.sqrt 3 := by
    simp only [u, v, nodeX_cube]; push_cast; ring
  have hs3 : Real.sqrt 3 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs3' : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hv3 : v ^ 3 = 3 * Real.sqrt 3 * n := nodeX_cube n
  have hvbig : 6 * Real.sqrt 3 ≤ 7 * v ^ 3 := by
    rw [hv3]; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hu2 : u ≤ 2 * v := by
    by_contra h
    push Not at h
    have : (2 * v) ^ 3 < u ^ 3 := by
      have h0 : 0 ≤ 2 * v := by positivity
      exact pow_lt_pow_left₀ h h0 (by norm_num)
    nlinarith
  refine ⟨hu2, ?_⟩
  have hdiff : (u - v) * (u ^ 2 + u * v + v ^ 2) = 6 * Real.sqrt 3 := by rw [← hcube]; ring
  have hden : 3 * v ^ 2 ≤ u ^ 2 + u * v + v ^ 2 := by nlinarith
  have huv0 : 0 ≤ u - v := by linarith
  have hgap : u - v ≤ 2 * Real.sqrt 3 / v ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc u * (u - v) ≤ 2 * v * (2 * Real.sqrt 3 / v ^ 2) :=
        mul_le_mul hu2 hgap huv0 (by positivity)
    _ = 4 * Real.sqrt 3 / v := by field_simp; ring

/-- The node sequence: `m+1` equally spaced points `L(j+1)/(m+1)`, `j ≤ m`, ending at
`L = X_{N₀}`, followed by every other integer chart node `X_{N₀+2k}`. -/
def nodeSeq (N₀ m : ℕ) (j : ℕ) : ℝ :=
  if j ≤ m then nodeX N₀ * ((j : ℝ) + 1) / ((m : ℝ) + 1) else nodeX (N₀ + 2 * (j - m))

theorem nodeSeq_of_le {N₀ m j : ℕ} (hj : j ≤ m) :
    nodeSeq N₀ m j = nodeX N₀ * ((j : ℝ) + 1) / ((m : ℝ) + 1) := by
  unfold nodeSeq; rw [if_pos hj]

theorem nodeSeq_add (N₀ m k : ℕ) : nodeSeq N₀ m (k + m) = nodeX (N₀ + 2 * k) := by
  unfold nodeSeq
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simp only [zero_add, mul_zero, add_zero]
    have : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · congr 2; omega

theorem nodeSeq_zero (N₀ m : ℕ) : nodeSeq N₀ m 0 = nodeX N₀ / ((m : ℝ) + 1) := by
  unfold nodeSeq; simp

theorem nodeSeq_strictMono {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (m : ℕ) : StrictMono (nodeSeq N₀ m) := by
  have hL := nodeX_pos hN₀
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine strictMono_nat_of_lt_succ fun j => ?_
  by_cases hj : j + 1 ≤ m
  · rw [nodeSeq_of_le (by omega : j ≤ m), nodeSeq_of_le hj, div_lt_div_iff_of_pos_right hm]
    push_cast
    nlinarith
  · by_cases hj' : j = m
    · rw [hj']
      have h1 := nodeSeq_add N₀ m 0
      have h2 := nodeSeq_add N₀ m 1
      simp only [zero_add, mul_zero, add_zero, mul_one] at h1 h2
      rw [h1, add_comm m 1, h2]
      exact nodeX_strictMono (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + m := ⟨j - m, by omega⟩
      rw [show k + m + 1 = (k + 1) + m by ring, nodeSeq_add, nodeSeq_add]
      exact nodeX_strictMono (by omega)

theorem nodeSeq_pos {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (m j : ℕ) : 0 < nodeSeq N₀ m j := by
  have h0 : 0 < nodeSeq N₀ m 0 := by
    rw [nodeSeq_zero]; exact div_pos (nodeX_pos hN₀) (by positivity)
  exact lt_of_lt_of_le h0 ((nodeSeq_strictMono hN₀ m).monotone (Nat.zero_le j))

theorem tendsto_nodeSeq (N₀ m : ℕ) : Tendsto (nodeSeq N₀ m) atTop atTop := by
  rw [← tendsto_add_atTop_iff_nat m]
  simp_rw [nodeSeq_add]
  have h : Tendsto (fun k : ℕ => N₀ + 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => show k ≤ N₀ + 2 * k by omega) tendsto_id
  exact tendsto_nodeX.comp h

/-- The gap condition `max(p_j,p_{j+1})(p_{j+1}-p_j) ≤ a/2` holds once `X_{N₀} ≥ 8√3/a` and
`m+1 ≥ 2X_{N₀}²/a`. -/
theorem nodeSeq_gap {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {m : ℕ} {a : ℝ} (ha : 0 < a)
    (hL : 8 * Real.sqrt 3 / a ≤ nodeX N₀) (hm : 2 * nodeX N₀ ^ 2 / a ≤ (m : ℝ) + 1) (j : ℕ) :
    max |nodeSeq N₀ m j| |nodeSeq N₀ m (j + 1)| * (nodeSeq N₀ m (j + 1) - nodeSeq N₀ m j) ≤ a / 2 := by
  have hpos := nodeSeq_pos hN₀ m
  have hmono := nodeSeq_strictMono hN₀ m
  have hmax : max |nodeSeq N₀ m j| |nodeSeq N₀ m (j + 1)| = nodeSeq N₀ m (j + 1) := by
    rw [abs_of_pos (hpos j), abs_of_pos (hpos (j + 1))]
    exact max_eq_right (hmono (Nat.lt_succ_self j)).le
  rw [hmax]
  have hL0 := nodeX_pos hN₀
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  by_cases hj : j + 1 ≤ m
  · rw [nodeSeq_of_le (by omega : j ≤ m), nodeSeq_of_le hj]
    have hjm : ((j : ℝ) + 1 + 1) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : j + 1 + 1 ≤ m + 1)
    have e : nodeX N₀ * ((↑(j + 1) : ℝ) + 1) / (↑m + 1) - nodeX N₀ * (↑j + 1) / (↑m + 1)
        = nodeX N₀ / ((m : ℝ) + 1) := by push_cast; field_simp; ring
    rw [e]
    have h1 : nodeX N₀ * ((↑(j + 1) : ℝ) + 1) / (↑m + 1) ≤ nodeX N₀ := by
      rw [div_le_iff₀ hm0]; push_cast; nlinarith
    calc nodeX N₀ * ((↑(j + 1) : ℝ) + 1) / (↑m + 1) * (nodeX N₀ / (↑m + 1))
        ≤ nodeX N₀ * (nodeX N₀ / (↑m + 1)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = nodeX N₀ ^ 2 / ((m : ℝ) + 1) := by ring
      _ ≤ a / 2 := by
          rw [div_le_iff₀ hm0]
          have := (div_le_iff₀ ha).mp hm
          nlinarith
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + m := ⟨j - m, by omega⟩
    rw [show k + m + 1 = (k + 1) + m by ring, nodeSeq_add, nodeSeq_add]
    have hn : 1 ≤ N₀ + 2 * k := by omega
    obtain ⟨-, h2⟩ := nodeX_two_step hn
    rw [show N₀ + 2 * (k + 1) = N₀ + 2 * k + 2 by ring]
    have hXk : nodeX N₀ ≤ nodeX (N₀ + 2 * k) := nodeX_strictMono.monotone (by omega)
    have hv := nodeX_pos hn
    refine h2.trans ?_
    rw [div_le_iff₀ hv]
    have := (div_le_iff₀ ha).mp hL
    nlinarith [Real.sqrt_nonneg 3]

end RHTower.DegreeThreeHankel
