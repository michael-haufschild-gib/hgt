/-
# u₀ — Böttcher c-velocity at the monomial fiber

`u₀(z) = ∑_{n≥0} 2^{-(n+1)} z^{-(2^{n+1}-1)}`

Properties:
1. Absolutely convergent for `‖z‖ ≥ 1`.
2. Functional equation: `2 * z * u₀ z = 1 + u₀ (z ^ 2)`.
3. U₀(x) = u₀(1/x) has the series `Σ 2^{-(n+1)} x^{2^{n+1}-1}`, which diverges for `‖x‖ > 1`.
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

open Complex Filter Topology

namespace U0

/-! ## Definition -/

/-- `u₀(z) = ∑_{n≥0} 2^{-(n+1)} · z^{-(2^{n+1}-1)}` -/
noncomputable def u0 (z : ℂ) : ℂ :=
  ∑' n : ℕ, (2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 1) - 1 : ℤ))

/-! ## Bounding series -/

@[aesop safe]
private lemma summable_two_zpow_neg_nat :
    Summable (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) := by
  have hgeom := summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  refine hgeom.congr (fun n => ?_)
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- The bounding series `∑ 2^{-(n+1)}` is summable. -/
@[aesop safe]
theorem summable_two_zpow_neg : Summable (fun n : ℕ => (2 : ℝ) ^ (-(n + 1 : ℤ))) := by
  have hgeom := summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have hshift : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) := by
    simp_rw [pow_succ]; exact hgeom.mul_right _
  refine hshift.congr (fun n => ?_)
  rw [zpow_neg, inv_pow]; congr 1

/-! ## Absolute convergence for `‖z‖ ≥ 1` -/

/-- For `‖z‖ ≥ 1`, each term has norm ≤ `2^{-(n+1)}`. -/
@[aesop safe]
theorem norm_u0_term_le {z : ℂ} (hz : 1 ≤ ‖z‖) (n : ℕ) :
    ‖(2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 1) - 1 : ℤ))‖ ≤
    (2 : ℝ) ^ (-(n + 1 : ℤ)) := by
  rw [norm_mul, norm_zpow, norm_zpow, Complex.norm_two]
  have hzpow_le : ‖z‖ ^ (-(2 ^ (n + 1) - 1 : ℤ)) ≤ 1 := by
    apply zpow_le_one_of_nonpos₀ hz
    have h : (1 : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast Nat.one_le_two_pow
    linarith
  have h2pow_pos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(↑n + 1 : ℤ)) := zpow_nonneg (by norm_num) _
  linarith [mul_le_mul_of_nonneg_left hzpow_le h2pow_pos]

/-- `u₀(z)` is summable for `‖z‖ ≥ 1`. -/
@[aesop safe]
theorem summable_u0_terms {z : ℂ} (hz : 1 ≤ ‖z‖) :
    Summable (fun n : ℕ => (2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 1) - 1 : ℤ))) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (2 : ℝ) ^ (-(n + 1 : ℤ)))
  · exact summable_two_zpow_neg
  · exact fun n => norm_u0_term_le hz n

/-! ## Functional equation: `2 * z * u₀ z = 1 + u₀ (z ^ 2)` -/

/-- Rewriting the `u₀(z²)` series as shifted u₀(z) terms. -/
@[aesop safe]
theorem u0_sq_term {z : ℂ} (n : ℕ) :
    (2 : ℂ) ^ (-(n + 1 : ℤ)) * (z ^ 2) ^ (-(2 ^ (n + 1) - 1 : ℤ)) =
    (2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 2) - 2 : ℤ)) := by
  congr 1
  rw [← zpow_natCast z 2, ← zpow_mul]
  congr 1; push_cast; ring

/-- Multiplying the `n`-th term of `u₀(z)` by `2z` (requires `z ≠ 0`). -/
@[aesop safe]
theorem two_z_u0_term {z : ℂ} (hz0 : z ≠ 0) (n : ℕ) :
    2 * z * ((2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 1) - 1 : ℤ))) =
    (2 : ℂ) ^ (-(n : ℤ)) * z ^ (-(2 ^ (n + 1) - 2 : ℤ)) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hlhs : 2 * z * (2 ^ (-(↑n + 1 : ℤ)) * z ^ (-(2 ^ (n + 1) - 1 : ℤ))) =
      2 ^ (1 : ℤ) * 2 ^ (-(↑n + 1 : ℤ)) * (z ^ (1 : ℤ) * z ^ (-(2 ^ (n + 1) - 1 : ℤ))) := by
    simp [zpow_one]; ring
  rw [hlhs, ← zpow_add₀ h2, ← zpow_add₀ hz0]
  congr 1 <;> ring

/-- **Functional equation**: `2 * z * u₀ z = 1 + u₀ (z ^ 2)`. -/
@[aesop safe]
theorem functional_equation {z : ℂ} (hz : 1 ≤ ‖z‖) :
    2 * z * u0 z = 1 + u0 (z ^ 2) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le one_pos hz)
  simp only [u0]
  -- u₀(z²) = ∑_n 2^{-(n+1)} * z^{-(2^{n+2}-2)}
  have hrw : (fun n : ℕ => (2 : ℂ) ^ (-(n + 1 : ℤ)) * (z ^ 2) ^ (-(2 ^ (n + 1) - 1 : ℤ))) =
             (fun n : ℕ => (2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 2) - 2 : ℤ))) :=
    funext (fun n => u0_sq_term n)
  rw [hrw]
  -- 2z * ∑_n f(n) = ∑_n 2^{-n} * z^{-(2^{n+1}-2)}
  rw [← tsum_mul_left]
  rw [show (fun n : ℕ => 2 * z * ((2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 1) - 1 : ℤ)))) =
      (fun n : ℕ => (2 : ℂ) ^ (-(n : ℤ)) * z ^ (-(2 ^ (n + 1) - 2 : ℤ))) from
      funext (fun n => two_z_u0_term hz0 n)]
  -- Summability of the LHS series
  have h_lhs_sum : Summable (fun n : ℕ => (2 : ℂ) ^ (-(n : ℤ)) * z ^ (-(2 ^ (n + 1) - 2 : ℤ))) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ)))
    · exact summable_two_zpow_neg_nat
    · intro n
      rw [norm_mul, norm_zpow, norm_zpow, Complex.norm_two]
      have hzpow : ‖z‖ ^ (-(2 ^ (n + 1) - 2 : ℤ)) ≤ 1 := by
        apply zpow_le_one_of_nonpos₀ hz
        have h3 : (2 : ℤ) ^ n ≥ 1 := by exact_mod_cast Nat.one_le_two_pow
        linarith [show (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n by ring]
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(n : ℤ)) := zpow_nonneg (by norm_num) _
      linarith [mul_le_mul_of_nonneg_left hzpow h2]
  -- Tsum shift: ∑_n g(n) = g(0) + ∑_n g(n+1)
  set g := (fun n : ℕ => (2 : ℂ) ^ (-(n : ℤ)) * z ^ (-(2 ^ (n + 1) - 2 : ℤ))) with hg_def
  have hg0 : g 0 = 1 := by simp [g]
  have hgsucc : ∀ n : ℕ, g (n + 1) = (2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 2) - 2 : ℤ)) := by
    intro n; simp only [g]; push_cast; ring_nf
  obtain ⟨L, hL⟩ := h_lhs_sum
  have hshift : HasSum (fun n : ℕ => g (n + 1)) (L - g 0) := by
    rw [hasSum_nat_add_iff]; simp [hL]
  rw [hL.tsum_eq,
      show ∑' n : ℕ, (2 : ℂ) ^ (-(n + 1 : ℤ)) * z ^ (-(2 ^ (n + 2) - 2 : ℤ)) =
           ∑' n : ℕ, g (n + 1) from tsum_congr (fun n => (hgsucc n).symm),
      hshift.tsum_eq, hg0]
  ring

/-! ## U₀ diverges for `‖x‖ > 1` -/

/-- The n-th term of U₀(x) = u₀(1/x), given by `2^{-(n+1)} x^{2^{n+1}-1}`. -/
noncomputable def U0term (x : ℂ) (n : ℕ) : ℂ :=
  (2 : ℂ) ^ (-(n + 1 : ℤ)) * x ^ (2 ^ (n + 1) - 1 : ℤ)

@[aesop safe]
theorem U0term_norm_eq {x : ℂ} (n : ℕ) :
    ‖U0term x n‖ = (2 : ℝ) ^ (-(n + 1 : ℤ)) * ‖x‖ ^ (2 ^ (n + 1) - 1 : ℤ) := by
  simp only [U0term, norm_mul, norm_zpow, Complex.norm_two]

/-- Geometric growth criterion: if `a N > 0` and `2 · a n ≤ a (n+1)` for all `n ≥ N`,
then `a → +∞`. (From `a (N+k) ≥ 2^k · a N`.) -/
@[aesop safe]
private theorem tendsto_of_two_mul_le (a : ℕ → ℝ) (N : ℕ) (hpos : 0 < a N)
    (hgrow : ∀ n ≥ N, 2 * a n ≤ a (n + 1)) :
    Filter.Tendsto a Filter.atTop Filter.atTop := by
  have key : ∀ k : ℕ, 2 ^ k * a N ≤ a (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      have hm : N ≤ N + m := Nat.le_add_right N m
      calc 2 ^ (m + 1) * a N = 2 * (2 ^ m * a N) := by ring
        _ ≤ 2 * a (N + m) := by linarith [ih]
        _ ≤ a (N + m + 1) := hgrow (N + m) hm
        _ = a (N + (m + 1)) := by ring_nf
  have hgeo : Filter.Tendsto (fun k => 2 ^ k * a N) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_mul_const hpos
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h1 : Filter.Tendsto (fun k => a (N + k)) Filter.atTop Filter.atTop :=
    tendsto_atTop_mono key hgeo
  rw [show (fun k => a (N + k)) = (fun k => a (k + N)) from
      funext (fun k => by rw [Nat.add_comm])] at h1
  exact (tendsto_add_atTop_iff_nat N).mp h1

/-- For `‖x‖ > 1`, the norms `‖U0term x n‖` tend to `+∞`.
The ratio `a(n+1)/a(n) = ½·‖x‖^{2^{n+1}} → ∞`, so eventually `a(n+1) ≥ 2·a(n)` (geometric growth).
This is the doubly-exponential growth that makes the unit circle the natural boundary of u₀. -/
@[aesop safe]
theorem U0term_norm_tendsto_atTop {x : ℂ} (hx : 1 < ‖x‖) :
    Filter.Tendsto (fun n => ‖U0term x n‖) Filter.atTop Filter.atTop := by
  have hr1 : 1 < ‖x‖ := hx
  have hr0 : 0 < ‖x‖ := by linarith
  set a := fun n => ‖U0term x n‖ with hadef
  have ha : ∀ n, a n = (2:ℝ) ^ (-(↑n + 1 : ℤ)) * ‖x‖ ^ (2 ^ (n + 1) - 1 : ℤ) :=
    fun n => U0term_norm_eq n
  have hpow : Filter.Tendsto (fun n : ℕ => ‖x‖ ^ (2 ^ (n + 1))) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.comp (tendsto_pow_atTop_atTop_of_one_lt hr1)
    apply Filter.Tendsto.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℕ) < 2))
    exact tendsto_add_atTop_nat 1
  obtain ⟨N, hN⟩ := (hpow.eventually_ge_atTop 4).exists_forall_of_atTop
  have hposN : 0 < a N := by
    rw [ha]; exact mul_pos (zpow_pos (by norm_num) _) (zpow_pos hr0 _)
  have hgrow : ∀ n ≥ N, 2 * a n ≤ a (n + 1) := by
    intro n hn
    rw [ha n, ha (n + 1)]
    have hid : (2:ℝ) ^ (-(↑(n+1) + 1 : ℤ)) * ‖x‖ ^ (2 ^ ((n+1) + 1) - 1 : ℤ) =
        (1/2) * ‖x‖ ^ (2 ^ (n + 1) : ℤ) *
          ((2:ℝ) ^ (-(↑n + 1 : ℤ)) * ‖x‖ ^ (2 ^ (n + 1) - 1 : ℤ)) := by
      have e2 : (-(↑(n+1) + 1 : ℤ)) = (-1) + (-(↑n + 1)) := by push_cast; ring
      have er : (2 ^ ((n+1) + 1) - 1 : ℤ) = (2 ^ (n + 1)) + (2 ^ (n + 1) - 1) := by ring
      rw [e2, er, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_add₀ (ne_of_gt hr0)]
      rw [show (2:ℝ)^(-1 : ℤ) = 1/2 by norm_num]; ring
    rw [hid]
    have h4 : (4:ℝ) ≤ ‖x‖ ^ (2 ^ (n + 1) : ℤ) := by
      have hcast : ((2:ℤ)^(n+1)) = ((2^(n+1) : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, zpow_natCast]; exact hN n hn
    have hanpos : 0 ≤ (2:ℝ) ^ (-(↑n + 1 : ℤ)) * ‖x‖ ^ (2 ^ (n + 1) - 1 : ℤ) :=
      mul_nonneg (le_of_lt (zpow_pos (by norm_num) _)) (le_of_lt (zpow_pos hr0 _))
    have hfactor : (2:ℝ) ≤ 1/2 * ‖x‖ ^ (2 ^ (n + 1) : ℤ) := by linarith
    calc 2 * ((2:ℝ) ^ (-(↑n + 1 : ℤ)) * ‖x‖ ^ (2 ^ (n + 1) - 1 : ℤ))
        ≤ (1/2 * ‖x‖ ^ (2 ^ (n + 1) : ℤ)) *
            ((2:ℝ) ^ (-(↑n + 1 : ℤ)) * ‖x‖ ^ (2 ^ (n + 1) - 1 : ℤ)) :=
          mul_le_mul_of_nonneg_right hfactor hanpos
      _ = 1/2 * ‖x‖ ^ (2 ^ (n + 1) : ℤ) *
            ((2:ℝ) ^ (-(↑n + 1 : ℤ)) * ‖x‖ ^ (2 ^ (n + 1) - 1 : ℤ)) := by ring
  exact tendsto_of_two_mul_le a N hposN hgrow

end U0
