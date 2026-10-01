import GaloisForLFunctions.RHTower.GammaRPowAntiChartSpace

/-!
# Supercritical node sequences in the degree-`d` chart

The integers sit at `X_n = n^{1/d}` in the chart `x = X^d`. For `d ≥ 3` and `n ≥ 1`,
`X_{n+2}(X_{n+2} - X_n) ≤ 4/X_n` (from `X_{n+2}^d - X_n^d = 2` and the geometric sum).
`nodeSeq d N₀ m` consists of `m+1` equally spaced points up to `X_{N₀}`, followed by every other
integer node `X_{N₀+2k}`. It satisfies the supercritical gap condition once `X_{N₀} ≥ 8/a` and
`m+1 ≥ 2X_{N₀}²/a`. The skipped integer nodes are never nodes.
-/

open Filter Set Topology

noncomputable section

namespace RHTower.GammaRPowTwins

/-- The integer `n` in the degree-`d` chart: `X_n = n^{1/d}`. -/
def nodeX (d : ℕ) (n : ℕ) : ℝ := (n : ℝ) ^ (1 / (d : ℝ))

theorem nodeX_nonneg (d n : ℕ) : 0 ≤ nodeX d n := by unfold nodeX; positivity

theorem nodeX_pow {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : nodeX d n ^ d = n := by
  unfold nodeX
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  have : (1 / (d : ℝ)) * (d : ℝ) = 1 := by
    have : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp
  rw [this, Real.rpow_one]

theorem nodeX_strictMono {d : ℕ} (hd : 1 ≤ d) : StrictMono (nodeX d) := by
  intro a b hab
  unfold nodeX
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  exact Real.rpow_lt_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) (by positivity)

theorem nodeX_pos {d : ℕ} (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n) : 0 < nodeX d n :=
  lt_of_le_of_lt (nodeX_nonneg d 0) (nodeX_strictMono hd (by omega))

theorem one_le_nodeX {d : ℕ} (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ nodeX d n := by
  unfold nodeX
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  exact Real.one_le_rpow (by exact_mod_cast hn) (by positivity)

theorem tendsto_nodeX {d : ℕ} (hd : 1 ≤ d) : Tendsto (nodeX d) atTop atTop := by
  unfold nodeX
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  exact (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (d : ℝ))).comp tendsto_natCast_atTop_atTop

theorem nodeX_le_two_mul (d n : ℕ) (hd : 1 ≤ d) : nodeX d n ≤ 2 * ((n : ℝ) + 1) := by
  unfold nodeX
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [Nat.cast_zero, Real.zero_rpow (by positivity)]; norm_num
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
    calc (n : ℝ) ^ (1 / (d : ℝ)) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by rw [div_le_one (by positivity)]; exact hd1)
      _ = n := Real.rpow_one _
      _ ≤ 2 * ((n : ℝ) + 1) := by linarith

/-- Two chart steps (`d ≥ 3`, `n ≥ 1`): `X_{n+2} ≤ 2X_n` and `X_{n+2}(X_{n+2} - X_n) ≤ 4/X_n`. -/
theorem nodeX_two_step {d : ℕ} (hd : 3 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    nodeX d (n + 2) ≤ 2 * nodeX d n ∧ nodeX d (n + 2) * (nodeX d (n + 2) - nodeX d n) ≤ 4 / nodeX d n := by
  set u := nodeX d (n + 2)
  set v := nodeX d n
  have hv1 : 1 ≤ v := one_le_nodeX (by omega) hn
  have hv : 0 < v := by linarith
  have huv : v ≤ u := (nodeX_strictMono (d := d) (by omega) (by omega : n < n + 2)).le
  have hpow : u ^ d - v ^ d = 2 := by
    simp only [u, v, nodeX_pow (by omega : 1 ≤ d)]; push_cast; ring
  have hgeom := geom_sum₂_mul u v d
  rw [hpow] at hgeom
  have hsum : (d : ℝ) * v ^ (d - 1) ≤ ∑ i ∈ Finset.range d, u ^ i * v ^ (d - 1 - i) := by
    have : ∀ i ∈ Finset.range d, v ^ (d - 1) ≤ u ^ i * v ^ (d - 1 - i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      calc v ^ (d - 1) = v ^ i * v ^ (d - 1 - i) := by rw [← pow_add]; congr 1; omega
        _ ≤ u ^ i * v ^ (d - 1 - i) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.le huv i) (by positivity)
    have := Finset.sum_le_sum this
    simpa using this
  have huv0 : 0 ≤ u - v := by linarith
  have hgap : (u - v) * ((d : ℝ) * v ^ (d - 1)) ≤ 2 := by
    rw [← hgeom, mul_comm]; exact mul_le_mul_of_nonneg_right hsum huv0
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hvd : v ≤ v ^ (d - 1) := by
    calc v = v ^ 1 := (pow_one v).symm
      _ ≤ v ^ (d - 1) := pow_le_pow_right₀ hv1 (by omega)
  have hvd2 : v ^ 2 ≤ v ^ (d - 1) := pow_le_pow_right₀ hv1 (by omega)
  have hu2 : u ≤ 2 * v := by
    by_contra h
    push Not at h
    have h8 : (2 * v) ^ d ≤ u ^ d := pow_le_pow_left₀ (by positivity) h.le d
    have h2d : (8 : ℝ) ≤ 2 ^ d := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
    have hvd1 : 1 ≤ v ^ d := one_le_pow₀ hv1
    rw [mul_pow] at h8
    nlinarith
  refine ⟨hu2, ?_⟩
  -- `u - v ≤ 2/(d v^{d-1}) ≤ 2/v²`, so `u(u-v) ≤ 2v · 2/v² = 4/v`
  have hden : 0 < (d : ℝ) * v ^ (d - 1) := by positivity
  have h1 : u - v ≤ 2 / ((d : ℝ) * v ^ (d - 1)) := by rw [le_div_iff₀ hden]; linarith
  have h2 : 2 / ((d : ℝ) * v ^ (d - 1)) ≤ 2 / v ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  calc u * (u - v) ≤ 2 * v * (2 / v ^ 2) :=
        mul_le_mul hu2 (h1.trans h2) huv0 (by positivity)
    _ = 4 / v := by field_simp; ring

/-- The node sequence: `m+1` equally spaced points `X_{N₀}(j+1)/(m+1)`, `j ≤ m`, followed by every
other integer node `X_{N₀+2k}`. -/
def nodeSeq (d N₀ m : ℕ) (j : ℕ) : ℝ :=
  if j ≤ m then nodeX d N₀ * ((j : ℝ) + 1) / ((m : ℝ) + 1) else nodeX d (N₀ + 2 * (j - m))

theorem nodeSeq_of_le {d N₀ m j : ℕ} (hj : j ≤ m) :
    nodeSeq d N₀ m j = nodeX d N₀ * ((j : ℝ) + 1) / ((m : ℝ) + 1) := by
  unfold nodeSeq; rw [if_pos hj]

theorem nodeSeq_add (d N₀ m k : ℕ) : nodeSeq d N₀ m (k + m) = nodeX d (N₀ + 2 * k) := by
  unfold nodeSeq
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simp only [zero_add, mul_zero, add_zero]
    have : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · congr 2; omega

theorem nodeSeq_zero (d N₀ m : ℕ) : nodeSeq d N₀ m 0 = nodeX d N₀ / ((m : ℝ) + 1) := by
  unfold nodeSeq; simp

theorem nodeSeq_strictMono {d : ℕ} (hd : 1 ≤ d) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (m : ℕ) : StrictMono (nodeSeq d N₀ m) := by
  have hL := nodeX_pos (d := d) (by omega) hN₀
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine strictMono_nat_of_lt_succ fun j => ?_
  by_cases hj : j + 1 ≤ m
  · rw [nodeSeq_of_le (by omega : j ≤ m), nodeSeq_of_le hj, div_lt_div_iff_of_pos_right hm]
    push_cast
    nlinarith
  · by_cases hj' : j = m
    · rw [hj']
      have h1 := nodeSeq_add d N₀ m 0
      have h2 := nodeSeq_add d N₀ m 1
      simp only [zero_add, mul_zero, add_zero, mul_one] at h1 h2
      rw [h1, add_comm m 1, h2]
      exact nodeX_strictMono (d := d) (by omega) (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + m := ⟨j - m, by omega⟩
      rw [show k + m + 1 = (k + 1) + m by ring, nodeSeq_add, nodeSeq_add]
      exact nodeX_strictMono (d := d) (by omega) (by omega)

theorem nodeSeq_pos {d : ℕ} (hd : 1 ≤ d) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (m j : ℕ) : 0 < nodeSeq d N₀ m j := by
  have h0 : 0 < nodeSeq d N₀ m 0 := by
    rw [nodeSeq_zero]; exact div_pos (nodeX_pos (d := d) (by omega) hN₀) (by positivity)
  exact lt_of_lt_of_le h0 ((nodeSeq_strictMono (d := d) (by omega) hN₀ m).monotone (Nat.zero_le j))

theorem tendsto_nodeSeq {d : ℕ} (hd : 1 ≤ d) (N₀ m : ℕ) : Tendsto (nodeSeq d N₀ m) atTop atTop := by
  rw [← tendsto_add_atTop_iff_nat m]
  simp_rw [nodeSeq_add]
  have h : Tendsto (fun k : ℕ => N₀ + 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => show k ≤ N₀ + 2 * k by omega) tendsto_id
  exact (tendsto_nodeX (d := d) (by omega)).comp h

/-- The gap condition `max(p_j,p_{j+1})(p_{j+1}-p_j) ≤ a/2` holds once `X_{N₀} ≥ 8/a` and
`m+1 ≥ 2X_{N₀}²/a`. -/
theorem nodeSeq_gap {d : ℕ} (hd : 3 ≤ d) {N₀ : ℕ} (hN₀ : 1 ≤ N₀) {m : ℕ} {a : ℝ} (ha : 0 < a)
    (hL : 8 / a ≤ nodeX d N₀) (hm : 2 * nodeX d N₀ ^ 2 / a ≤ (m : ℝ) + 1) (j : ℕ) :
    max |nodeSeq d N₀ m j| |nodeSeq d N₀ m (j + 1)| * (nodeSeq d N₀ m (j + 1) - nodeSeq d N₀ m j) ≤ a / 2 := by
  have hpos := nodeSeq_pos (d := d) (by omega) hN₀ m
  have hmono := nodeSeq_strictMono (d := d) (by omega) hN₀ m
  have hmax : max |nodeSeq d N₀ m j| |nodeSeq d N₀ m (j + 1)| = nodeSeq d N₀ m (j + 1) := by
    rw [abs_of_pos (hpos j), abs_of_pos (hpos (j + 1))]
    exact max_eq_right (hmono (Nat.lt_succ_self j)).le
  rw [hmax]
  have hL0 := nodeX_pos (d := d) (by omega) hN₀
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  by_cases hj : j + 1 ≤ m
  · rw [nodeSeq_of_le (by omega : j ≤ m), nodeSeq_of_le hj]
    have hjm : ((j : ℝ) + 1 + 1) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : j + 1 + 1 ≤ m + 1)
    have e : nodeX d N₀ * ((↑(j + 1) : ℝ) + 1) / (↑m + 1) - nodeX d N₀ * (↑j + 1) / (↑m + 1)
        = nodeX d N₀ / ((m : ℝ) + 1) := by push_cast; field_simp; ring
    rw [e]
    have h1 : nodeX d N₀ * ((↑(j + 1) : ℝ) + 1) / (↑m + 1) ≤ nodeX d N₀ := by
      rw [div_le_iff₀ hm0]; push_cast; nlinarith
    calc nodeX d N₀ * ((↑(j + 1) : ℝ) + 1) / (↑m + 1) * (nodeX d N₀ / (↑m + 1))
        ≤ nodeX d N₀ * (nodeX d N₀ / (↑m + 1)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = nodeX d N₀ ^ 2 / ((m : ℝ) + 1) := by ring
      _ ≤ a / 2 := by
          rw [div_le_iff₀ hm0]
          have := (div_le_iff₀ ha).mp hm
          nlinarith
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + m := ⟨j - m, by omega⟩
    rw [show k + m + 1 = (k + 1) + m by ring, nodeSeq_add, nodeSeq_add]
    have hn : 1 ≤ N₀ + 2 * k := by omega
    obtain ⟨-, h2⟩ := nodeX_two_step hd hn
    rw [show N₀ + 2 * (k + 1) = N₀ + 2 * k + 2 by ring]
    have hXk : nodeX d N₀ ≤ nodeX d (N₀ + 2 * k) := (nodeX_strictMono (d := d) (by omega)).monotone (by omega)
    have hv := nodeX_pos (d := d) (by omega) hn
    refine h2.trans ?_
    rw [div_le_iff₀ hv]
    have := (div_le_iff₀ ha).mp hL
    nlinarith

end RHTower.GammaRPowTwins
