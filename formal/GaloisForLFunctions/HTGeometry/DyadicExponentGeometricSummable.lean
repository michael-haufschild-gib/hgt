import Mathlib

/-!
# Doubly exponential radial decay beats geometric growth

For `0 ≤ r < 1` and any real `d`, the doubly exponential sequence `d ^ j * r ^ (2 ^ j)` is
summable and tends to `0` (`summable_geometric_mul_pow_two_pow`,
`tendsto_geometric_mul_pow_two_pow`).  The mechanism is that `2 ^ j` eventually dominates every
linear function `m * j`, so `r ^ (2 ^ j) ≤ r ^ (m * j)`; choosing `m` with `|d| * r ^ m < 1`
turns the tail into a geometric series.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Every linear function is eventually dominated by `2 ^ j`. -/
theorem eventually_mul_le_two_pow (m : ℕ) : ∀ᶠ j : ℕ in atTop, m * j ≤ 2 ^ j := by
  have h0 : Tendsto (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
  have hm : Tendsto (fun j : ℕ => (m : ℝ) * ((j : ℝ) * (1 / 2 : ℝ) ^ j)) atTop (𝓝 0) := by
    simpa using h0.const_mul (m : ℝ)
  have hev : ∀ᶠ j : ℕ in atTop, (m : ℝ) * ((j : ℝ) * (1 / 2 : ℝ) ^ j) < 1 := by
    have := hm.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    exact this
  filter_upwards [hev] with j hj
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hrw : (m : ℝ) * ((j : ℝ) * (1 / 2 : ℝ) ^ j) = ((m : ℝ) * j) / 2 ^ j := by
    rw [div_pow, one_pow]
    field_simp
  rw [hrw, div_lt_one hpow] at hj
  have : ((m * j : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- **Doubly exponential radial decay is summable against geometric growth.** -/
theorem summable_geometric_mul_pow_two_pow {r d : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun j : ℕ => |d| ^ j * r ^ (2 ^ j) := by
  rcases eq_or_lt_of_le hr0 with hr | hrpos
  · -- `r = 0`: every term vanishes because `2 ^ j ≥ 1`.
    refine summable_zero.congr fun j => ?_
    have h2 : 0 < 2 ^ j := pow_pos (by norm_num) j
    rw [← hr, zero_pow (by omega), mul_zero]
  · -- `r > 0`: pick `m` with `|d| * r ^ m < 1` and compare with a geometric tail.
    obtain ⟨m, hm⟩ : ∃ m : ℕ, |d| * r ^ m < 1 := by
      have htend : Tendsto (fun m : ℕ => |d| * r ^ m) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul |d|
      exact (htend.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).exists
    obtain ⟨J, hJ⟩ := (eventually_mul_le_two_pow m).exists_forall_of_atTop
    have hgeom : Summable fun j : ℕ => (|d| * r ^ m) ^ (j + J) := by
      refine ((summable_geometric_of_lt_one (by positivity) hm).mul_right
        ((|d| * r ^ m) ^ J)).congr ?_
      intro j
      rw [pow_add]
    rw [← summable_nat_add_iff J]
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hgeom
    have hle : m * (j + J) ≤ 2 ^ (j + J) := hJ (j + J) (Nat.le_add_left J j)
    have hpow : r ^ (2 ^ (j + J)) ≤ r ^ (m * (j + J)) :=
      pow_le_pow_of_le_one hr0 hr1.le hle
    calc |d| ^ (j + J) * r ^ (2 ^ (j + J))
        ≤ |d| ^ (j + J) * r ^ (m * (j + J)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (|d| * r ^ m) ^ (j + J) := by rw [mul_pow, ← pow_mul, mul_comm m (j + J)]

/-- **Doubly exponential radial decay tends to zero against geometric growth.** -/
theorem tendsto_geometric_mul_pow_two_pow {r d : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun j : ℕ => |d| ^ j * r ^ (2 ^ j)) atTop (𝓝 0) :=
  (summable_geometric_mul_pow_two_pow hr0 hr1).tendsto_atTop_zero

end GaloisForLFunctions.HTGeometry
