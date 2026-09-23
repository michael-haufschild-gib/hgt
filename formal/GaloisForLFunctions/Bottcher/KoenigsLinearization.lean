/-
# Koenigs linearization at the repelling fixed point (foundation)

For `f = z² + c` with fixed point `β` (so `β² + c = β`) and multiplier `λ = 2β`, the conjugacy
identity is EXACT: `f(β + u) = β + λu + u²`.  The Koenigs linearizer is the locally uniform limit
of `g_n(w) := f^[n](β + w/λⁿ)`, whose telescope obeys the exact recursion
`g_{n+1}(w) = g_n(w + w²/λ^{n+2})`.  This file builds the foundation: the approximants, the exact
recursion, and the geometric orbit-drift bound `‖f^[k](β+v) − β‖ ≤ 2‖v‖‖λ‖^k` with the product
error control — the inputs for the Cauchy telescope.  Route R1 of the dendrite-tip lane.
-/
import GaloisForLFunctions.Bottcher.GreenFunction
import GaloisForLFunctions.Bottcher.DendriteTip
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Complex Set Metric Finset

namespace Bottcher

/-- The Koenigs approximant `g_n(w) = f^[n](β + w/λⁿ)`. -/
noncomputable def koenigsApprox (c β : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  (quadratic c)^[n] (β + w / (2 * β) ^ n)

/-- **The exact conjugation identity** for the quadratic at a fixed point. -/
theorem quadratic_fixed_expansion {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (u : ℂ) :
    quadratic c (β + u) = β + (2 * β) * u + u ^ (2 : ℕ) := by
  unfold quadratic
  have h1 : (β + u) ^ (2 : ℕ) + c = β ^ (2 : ℕ) + c + 2 * β * u + u ^ (2 : ℕ) := by ring
  rw [h1, hβ]

/-- **The exact telescope recursion**: `g_{n+1}(w) = g_n(w + w²/λ^{n+2})`. -/
theorem koenigsApprox_succ {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam : (2 * β) ≠ 0)
    (n : ℕ) (w : ℂ) :
    koenigsApprox c β (n + 1) w
      = koenigsApprox c β n (w + w ^ (2 : ℕ) / (2 * β) ^ (n + 2)) := by
  unfold koenigsApprox
  rw [Function.iterate_succ_apply]
  congr 1
  have h1 : quadratic c (β + w / (2 * β) ^ (n + 1))
      = β + (2 * β) * (w / (2 * β) ^ (n + 1)) + (w / (2 * β) ^ (n + 1)) ^ (2 : ℕ) :=
    quadratic_fixed_expansion hβ _
  rw [h1]
  have hβ0 : β ≠ 0 := by
    intro h
    apply hlam
    rw [h]
    ring
  have hpow : ∀ m : ℕ, ((2 * β) ^ m : ℂ) ≠ 0 := fun m => pow_ne_zero m hlam
  field_simp
  ring

/-- **Orbit-drift bound with product error**: as long as the accumulated drifts stay below `‖λ‖/2`,
the orbit of `β + v` stays within `‖v‖·‖λ‖^k·(product error)` of `β`.  Stated as the exact
recursive inequality for one step. -/
theorem orbit_drift_step {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) {x : ℂ} :
    ‖quadratic c x - β‖ ≤ ‖x - β‖ * (‖2 * β‖ + ‖x - β‖) := by
  have h1 : quadratic c x = β + (2 * β) * (x - β) + (x - β) ^ (2 : ℕ) := by
    have := quadratic_fixed_expansion hβ (x - β)
    rw [show β + (x - β) = x by ring] at this
    exact this
  rw [h1]
  have h2 : β + 2 * β * (x - β) + (x - β) ^ (2 : ℕ) - β = 2 * β * (x - β) + (x - β) ^ (2 : ℕ) := by ring
  rw [h2]
  calc ‖2 * β * (x - β) + (x - β) ^ (2 : ℕ)‖
      ≤ ‖2 * β * (x - β)‖ + ‖(x - β) ^ (2 : ℕ)‖ := norm_add_le _ _
    _ = ‖2 * β‖ * ‖x - β‖ + ‖x - β‖ ^ (2 : ℕ) := by rw [norm_mul, norm_pow]
    _ = ‖x - β‖ * (‖2 * β‖ + ‖x - β‖) := by ring

/-- **Geometric orbit-drift bound.**  If `‖λ‖ ≥ 2` and the seed satisfies
`‖v‖·‖λ‖ⁿ ≤ 1/8`, then for all `k ≤ n` the orbit drift obeys
`‖f^[k](β+v) − β‖ ≤ 2‖v‖‖λ‖^k`.  The sharp invariant carried by the induction is
`d_k · 2^(n+2) ≤ ‖v‖·‖λ‖^k·(2^(n+2) + 2^k)`. -/
theorem orbit_drift_invariant {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {v : ℂ} {n : ℕ} (hv : ‖v‖ * ‖2 * β‖ ^ n ≤ 1 / 8) :
    ∀ k : ℕ, k ≤ n → ‖(quadratic c)^[k] (β + v) - β‖ * 2 ^ (n + 2)
      ≤ ‖v‖ * ‖2 * β‖ ^ k * (2 ^ (n + 2) + 2 ^ k) := by
  set L : ℝ := ‖2 * β‖ with hLdef
  set a : ℝ := ‖v‖ with hadef
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hlam2
  have ha0 : (0:ℝ) ≤ a := norm_nonneg v
  -- the base seed bound in pure form
  have hseed : a * L ^ n ≤ 1 / 8 := hv
  intro k hkn
  induction k with
  | zero =>
      have h1 : ‖(quadratic c)^[0] (β + v) - β‖ = a := by
        simp [hadef]
      rw [h1]
      have h2 : (0:ℝ) < 2 ^ (n + 2) := by positivity
      have h3 : a * L ^ (0 : ℕ) * (2 ^ (n + 2) + 2 ^ (0 : ℕ)) = a * (2 ^ (n + 2) + 1) := by
        norm_num
      rw [h3]
      nlinarith
  | succ m ih =>
      have hmn : m ≤ n := by omega
      have hdm := ih hmn
      set d : ℝ := ‖(quadratic c)^[m] (β + v) - β‖ with hddef
      have hd0 : (0:ℝ) ≤ d := norm_nonneg _
      have hstep : ‖(quadratic c)^[m+1] (β + v) - β‖ ≤ d * (L + d) := by
        rw [Function.iterate_succ_apply']
        exact orbit_drift_step hβ
      -- room facts
      have hp2 : (0:ℝ) < 2 ^ (n + 2) := by positivity
      have hpm : (0:ℝ) < 2 ^ m := by positivity
      have hLm : (0:ℝ) < L ^ m := by positivity
      have h2mn : (2:ℝ) ^ m ≤ 2 ^ n := by
        apply pow_le_pow_right₀ (by norm_num) hmn
      have h2m2 : (2:ℝ) ^ m ≤ 2 ^ (n + 2) := by
        calc (2:ℝ) ^ m ≤ 2 ^ n := h2mn
          _ ≤ 2 ^ (n + 2) := by
              apply pow_le_pow_right₀ (by norm_num)
              omega
      -- d ≤ 2 a L^m  (from the invariant)
      have hd2 : d ≤ 2 * a * L ^ m := by
        have h4 : a * L ^ m * (2 ^ (n + 2) + 2 ^ m) ≤ a * L ^ m * (2 * 2 ^ (n + 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
        have h5 : d * 2 ^ (n + 2) ≤ a * L ^ m * (2 * 2 ^ (n + 2)) := le_trans hdm h4
        nlinarith
      -- the key tight fact:  4 a L^m 2^(n+2) ≤ L 2^m  (uses L ≥ 2 and the seed bound)
      have hkey : 4 * a * L ^ m * 2 ^ (n + 2) ≤ L * 2 ^ m := by
        -- L^(n-m) ≥ 2^(n-m)  ⟹  a L^m ≤ a L^n / 2^(n-m) ≤ (1/8)·2^(m-n)
        have h6 : (2:ℝ) ^ (n - m) ≤ L ^ (n - m) :=
          pow_le_pow_left₀ (by norm_num) hlam2 (n - m)
        have h7 : L ^ m * L ^ (n - m) = L ^ n := by
          rw [← pow_add]
          congr 1
          omega
        have h8 : a * L ^ m * 2 ^ (n - m) ≤ a * L ^ n := by
          calc a * L ^ m * 2 ^ (n - m) ≤ a * L ^ m * L ^ (n - m) := by
                apply mul_le_mul_of_nonneg_left h6 (by positivity)
            _ = a * L ^ n := by rw [mul_assoc, h7]
        have h9 : a * L ^ m * 2 ^ (n - m) ≤ 1 / 8 := le_trans h8 hseed
        -- multiply through: 4·(aL^m)·2^(n+2) = 4·(aL^m)·2^(n-m)·2^(m+2)/1 ≤ (1/2)·2^(m+2) = 2^(m+1) ≤ L·2^m
        have h10 : (2:ℝ) ^ (n + 2) = 2 ^ (n - m) * 2 ^ (m + 2) := by
          rw [← pow_add]
          congr 1
          omega
        have h11 : 4 * a * L ^ m * 2 ^ (n + 2)
            = 4 * (a * L ^ m * 2 ^ (n - m)) * 2 ^ (m + 2) := by
          rw [h10]
          ring
        rw [h11]
        have h12 : (0:ℝ) < 2 ^ (m + 2) := by positivity
        have h13 : 4 * (a * L ^ m * 2 ^ (n - m)) * 2 ^ (m + 2)
            ≤ 4 * (1 / 8) * 2 ^ (m + 2) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt h12)
          nlinarith
        calc 4 * (a * L ^ m * 2 ^ (n - m)) * 2 ^ (m + 2)
            ≤ 4 * (1 / 8) * 2 ^ (m + 2) := h13
          _ = 2 ^ (m + 1) := by ring
          _ = 2 * 2 ^ m := by ring
          _ ≤ L * 2 ^ m := by nlinarith
      -- assemble the step
      have hgoal : d * (L + d) * 2 ^ (n + 2)
          ≤ a * L ^ (m + 1) * (2 ^ (n + 2) + 2 ^ (m + 1)) := by
        have hLm1 : a * L ^ (m + 1) = a * L ^ m * L := by ring
        -- expand: d L 2^(n+2) + d² 2^(n+2)
        have hA : d * L * 2 ^ (n + 2) ≤ a * L ^ m * L * (2 ^ (n + 2) + 2 ^ m) := by
          have := mul_le_mul_of_nonneg_right hdm (le_of_lt hL0)
          nlinarith
        have hB : d * d * 2 ^ (n + 2) ≤ (2 * a * L ^ m) * (2 * a * L ^ m) * 2 ^ (n + 2) := by
          have h14 := mul_le_mul hd2 hd2 hd0 (by positivity : (0:ℝ) ≤ 2 * a * L ^ m)
          apply mul_le_mul_of_nonneg_right h14 (le_of_lt hp2)
        have hC : (2 * a * L ^ m) * (2 * a * L ^ m) * 2 ^ (n + 2)
            ≤ a * L ^ m * (L * 2 ^ m) := by
          have h15 : (2 * a * L ^ m) * (2 * a * L ^ m) * 2 ^ (n + 2)
              = (a * L ^ m) * (4 * a * L ^ m * 2 ^ (n + 2)) := by ring
          rw [h15]
          apply mul_le_mul_of_nonneg_left hkey (by positivity)
        have hBC := le_trans hB hC
        have hexp : d * (L + d) * 2 ^ (n + 2)
            = d * L * 2 ^ (n + 2) + d * d * 2 ^ (n + 2) := by ring
        rw [hexp]
        calc d * L * 2 ^ (n + 2) + d * d * 2 ^ (n + 2)
            ≤ a * L ^ m * L * (2 ^ (n + 2) + 2 ^ m) + a * L ^ m * (L * 2 ^ m) :=
              add_le_add hA hBC
          _ = a * L ^ (m + 1) * (2 ^ (n + 2) + 2 ^ (m + 1)) := by ring
      calc ‖(quadratic c)^[m+1] (β + v) - β‖ * 2 ^ (n + 2)
          ≤ d * (L + d) * 2 ^ (n + 2) := by
            apply mul_le_mul_of_nonneg_right hstep (by positivity)
        _ ≤ a * L ^ (m + 1) * (2 ^ (n + 2) + 2 ^ (m + 1)) := hgoal

/-- **Geometric orbit-drift bound, clean form**: `‖f^[k](β+v) − β‖ ≤ 2‖v‖‖λ‖^k` for `k ≤ n`. -/
theorem orbit_drift_bound {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {v : ℂ} {n : ℕ} (hv : ‖v‖ * ‖2 * β‖ ^ n ≤ 1 / 8) :
    ∀ k : ℕ, k ≤ n → ‖(quadratic c)^[k] (β + v) - β‖ ≤ 2 * ‖v‖ * ‖2 * β‖ ^ k := by
  intro k hkn
  have h1 := orbit_drift_invariant hβ hlam2 hv k hkn
  have hp2 : (0:ℝ) < 2 ^ (n + 2) := by positivity
  have h2 : (2:ℝ) ^ k ≤ 2 ^ (n + 2) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have h3 : ‖v‖ * ‖2 * β‖ ^ k * (2 ^ (n + 2) + 2 ^ k)
      ≤ ‖v‖ * ‖2 * β‖ ^ k * (2 * 2 ^ (n + 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have h4 := le_trans h1 h3
  nlinarith [norm_nonneg ((quadratic c)^[k] (β + v) - β), norm_nonneg v,
    pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hlam2) k]

end Bottcher

namespace Bottcher

/-- One step of the two-orbit comparison: the quadratic difference factors EXACTLY, so
`‖f(x) − f(y)‖ = ‖x − y‖·‖x + y‖ ≤ ‖x − y‖(‖2β‖ + ‖x−β‖ + ‖y−β‖)`. -/
theorem orbit_compare_step {c β : ℂ} (x y : ℂ) :
    ‖quadratic c x - quadratic c y‖
      ≤ ‖x - y‖ * (‖2 * β‖ + ‖x - β‖ + ‖y - β‖) := by
  have h1 : quadratic c x - quadratic c y = (x - y) * (x + y) := by
    unfold quadratic
    ring
  rw [h1, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc ‖x + y‖ = ‖2 * β + ((x - β) + (y - β))‖ := by ring_nf
    _ ≤ ‖2 * β‖ + ‖(x - β) + (y - β)‖ := norm_add_le _ _
    _ ≤ ‖2 * β‖ + (‖x - β‖ + ‖y - β‖) := by
        have := norm_add_le (x - β) (y - β)
        linarith
    _ = ‖2 * β‖ + ‖x - β‖ + ‖y - β‖ := by ring

/-- **Two-orbit Lipschitz invariant**: under the halved seed bounds `‖v‖L^n, ‖v'‖L^n ≤ 1/16`,
the difference orbit obeys the same sharp invariant, giving the derivative-free Lipschitz bound
for the Koenigs approximants. -/
theorem orbit_compare_invariant {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {v v' : ℂ} {n : ℕ} (hv : ‖v‖ * ‖2 * β‖ ^ n ≤ 1 / 16) (hv' : ‖v'‖ * ‖2 * β‖ ^ n ≤ 1 / 16) :
    ∀ k : ℕ, k ≤ n → ‖(quadratic c)^[k] (β + v) - (quadratic c)^[k] (β + v')‖ * 2 ^ (n + 2)
      ≤ ‖v - v'‖ * ‖2 * β‖ ^ k * (2 ^ (n + 2) + 2 ^ k) := by
  set L : ℝ := ‖2 * β‖ with hLdef
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hlam2
  set e₀ : ℝ := ‖v - v'‖ with he₀def
  have he₀0 : (0:ℝ) ≤ e₀ := norm_nonneg _
  have hv8 : ‖v‖ * L ^ n ≤ 1 / 8 := by
    calc ‖v‖ * L ^ n ≤ 1 / 16 := hv
      _ ≤ 1 / 8 := by norm_num
  have hv'8 : ‖v'‖ * L ^ n ≤ 1 / 8 := by
    calc ‖v'‖ * L ^ n ≤ 1 / 16 := hv'
      _ ≤ 1 / 8 := by norm_num
  intro k hkn
  induction k with
  | zero =>
      have h1 : ‖(quadratic c)^[0] (β + v) - (quadratic c)^[0] (β + v')‖ = e₀ := by
        simp [he₀def]
      rw [h1]
      have h2 : (0:ℝ) < 2 ^ (n + 2) := by positivity
      have h3 : e₀ * L ^ (0 : ℕ) * (2 ^ (n + 2) + 2 ^ (0 : ℕ)) = e₀ * (2 ^ (n + 2) + 1) := by norm_num
      rw [h3]
      nlinarith
  | succ m ih =>
      have hmn : m ≤ n := by omega
      have hem := ih hmn
      set x : ℂ := (quadratic c)^[m] (β + v) with hxdef
      set y : ℂ := (quadratic c)^[m] (β + v') with hydef
      set e : ℝ := ‖x - y‖ with hedef
      have he0 : (0:ℝ) ≤ e := norm_nonneg _
      have hdx := orbit_drift_bound hβ hlam2 hv8 m hmn
      have hdy := orbit_drift_bound hβ hlam2 hv'8 m hmn
      rw [← hxdef] at hdx
      rw [← hydef] at hdy
      have hstep : ‖(quadratic c)^[m+1] (β + v) - (quadratic c)^[m+1] (β + v')‖
          ≤ e * (L + ‖x - β‖ + ‖y - β‖) := by
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact orbit_compare_step x y
      -- the combined drift D := ‖x−β‖ + ‖y−β‖ ≤ 2(‖v‖+‖v'‖)L^m with (‖v‖+‖v'‖)L^n ≤ 1/8
      set A : ℝ := ‖v‖ + ‖v'‖ with hAdef
      have hA0 : (0:ℝ) ≤ A := by positivity
      have hAseed : A * L ^ n ≤ 1 / 8 := by
        have h4 : A * L ^ n = ‖v‖ * L ^ n + ‖v'‖ * L ^ n := by ring
        rw [h4]
        linarith
      have hD : ‖x - β‖ + ‖y - β‖ ≤ 2 * A * L ^ m := by
        have h5 : 2 * ‖v‖ * L ^ m + 2 * ‖v'‖ * L ^ m = 2 * A * L ^ m := by
          rw [hAdef]
          ring
        linarith
      -- room facts (identical shape to orbit_drift_invariant)
      have hp2 : (0:ℝ) < 2 ^ (n + 2) := by positivity
      have hpm : (0:ℝ) < 2 ^ m := by positivity
      have hLm : (0:ℝ) < L ^ m := by positivity
      have h2m2 : (2:ℝ) ^ m ≤ 2 ^ (n + 2) := by
        calc (2:ℝ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hmn
          _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hkey : 4 * A * L ^ m * 2 ^ (n + 2) ≤ L * 2 ^ m := by
        have h6 : (2:ℝ) ^ (n - m) ≤ L ^ (n - m) :=
          pow_le_pow_left₀ (by norm_num) hlam2 (n - m)
        have h7 : L ^ m * L ^ (n - m) = L ^ n := by
          rw [← pow_add]
          congr 1
          omega
        have h8 : A * L ^ m * 2 ^ (n - m) ≤ 1 / 8 := by
          calc A * L ^ m * 2 ^ (n - m) ≤ A * L ^ m * L ^ (n - m) := by
                apply mul_le_mul_of_nonneg_left h6 (by positivity)
            _ = A * L ^ n := by rw [mul_assoc, h7]
            _ ≤ 1 / 8 := hAseed
        have h10 : (2:ℝ) ^ (n + 2) = 2 ^ (n - m) * 2 ^ (m + 2) := by
          rw [← pow_add]
          congr 1
          omega
        have h11 : 4 * A * L ^ m * 2 ^ (n + 2)
            = 4 * (A * L ^ m * 2 ^ (n - m)) * 2 ^ (m + 2) := by
          rw [h10]
          ring
        rw [h11]
        have h12 : (0:ℝ) < 2 ^ (m + 2) := by positivity
        calc 4 * (A * L ^ m * 2 ^ (n - m)) * 2 ^ (m + 2)
            ≤ 4 * (1 / 8) * 2 ^ (m + 2) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt h12)
              nlinarith
          _ = 2 * 2 ^ m := by ring
          _ ≤ L * 2 ^ m := by nlinarith
      -- assemble
      have hexp : e * (L + ‖x - β‖ + ‖y - β‖) * 2 ^ (n + 2)
          ≤ e * L * 2 ^ (n + 2) + e * (2 * A * L ^ m) * 2 ^ (n + 2) := by
        have h13 : e * (L + ‖x - β‖ + ‖y - β‖) * 2 ^ (n + 2)
            = e * L * 2 ^ (n + 2) + e * (‖x - β‖ + ‖y - β‖) * 2 ^ (n + 2) := by ring
        rw [h13]
        have h14 : e * (‖x - β‖ + ‖y - β‖) * 2 ^ (n + 2)
            ≤ e * (2 * A * L ^ m) * 2 ^ (n + 2) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hp2)
          exact mul_le_mul_of_nonneg_left hD he0
        linarith
      have hA' : e * L * 2 ^ (n + 2) ≤ e₀ * L ^ m * L * (2 ^ (n + 2) + 2 ^ m) := by
        have := mul_le_mul_of_nonneg_right hem (le_of_lt hL0)
        nlinarith
      -- e ≤ 2 e₀ L^m from the invariant
      have he2 : e ≤ 2 * e₀ * L ^ m := by
        have h15 : e₀ * L ^ m * (2 ^ (n + 2) + 2 ^ m) ≤ e₀ * L ^ m * (2 * 2 ^ (n + 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
        have h16 := le_trans hem h15
        nlinarith
      have hB' : e * (2 * A * L ^ m) * 2 ^ (n + 2)
          ≤ e₀ * L ^ m * (L * 2 ^ m) := by
        calc e * (2 * A * L ^ m) * 2 ^ (n + 2)
            ≤ (2 * e₀ * L ^ m) * (2 * A * L ^ m) * 2 ^ (n + 2) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hp2)
              apply mul_le_mul_of_nonneg_right he2 (by positivity)
          _ = (e₀ * L ^ m) * (4 * A * L ^ m * 2 ^ (n + 2)) := by ring
          _ ≤ (e₀ * L ^ m) * (L * 2 ^ m) := by
              apply mul_le_mul_of_nonneg_left hkey (by positivity)
      calc ‖(quadratic c)^[m+1] (β + v) - (quadratic c)^[m+1] (β + v')‖ * 2 ^ (n + 2)
          ≤ e * (L + ‖x - β‖ + ‖y - β‖) * 2 ^ (n + 2) := by
            apply mul_le_mul_of_nonneg_right hstep (by positivity)
        _ ≤ e * L * 2 ^ (n + 2) + e * (2 * A * L ^ m) * 2 ^ (n + 2) := hexp
        _ ≤ e₀ * L ^ m * L * (2 ^ (n + 2) + 2 ^ m) + e₀ * L ^ m * (L * 2 ^ m) :=
            add_le_add hA' hB'
        _ = e₀ * L ^ (m + 1) * (2 ^ (n + 2) + 2 ^ (m + 1)) := by ring

/-- **Koenigs-approximant Lipschitz bound (derivative-free)**: on the seed scale, the `n`-th
approximant is `2`-Lipschitz after the geometric normalization. -/
theorem orbit_compare_bound {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {v v' : ℂ} {n : ℕ} (hv : ‖v‖ * ‖2 * β‖ ^ n ≤ 1 / 16) (hv' : ‖v'‖ * ‖2 * β‖ ^ n ≤ 1 / 16) :
    ‖(quadratic c)^[n] (β + v) - (quadratic c)^[n] (β + v')‖
      ≤ 2 * ‖v - v'‖ * ‖2 * β‖ ^ n := by
  have h1 := orbit_compare_invariant hβ hlam2 hv hv' n le_rfl
  have hp2 : (0:ℝ) < 2 ^ (n + 2) := by positivity
  have h2 : (2:ℝ) ^ n ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : ‖v - v'‖ * ‖2 * β‖ ^ n * (2 ^ (n + 2) + 2 ^ n)
      ≤ ‖v - v'‖ * ‖2 * β‖ ^ n * (2 * 2 ^ (n + 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have h4 := le_trans h1 h3
  nlinarith [norm_nonneg ((quadratic c)^[n] (β + v) - (quadratic c)^[n] (β + v')),
    norm_nonneg (v - v'),
    pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hlam2) n]

end Bottcher

namespace Bottcher

/-- **The Cauchy telescope step**: on the disk `‖w‖ ≤ 1/32`, consecutive Koenigs approximants
differ by at most `2‖w‖²/L^(n+2) ≤ ‖w‖²·2^{-n-1}`. -/
theorem koenigsApprox_cauchy_step {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 32) (n : ℕ) :
    ‖koenigsApprox c β (n + 1) w - koenigsApprox c β n w‖
      ≤ 2 * ‖w‖ ^ (2 : ℕ) / ‖2 * β‖ ^ (n + 2) := by
  set L : ℝ := ‖2 * β‖ with hLdef
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hlam2
  have hlam : (2 * β) ≠ 0 := by
    intro h
    have h1 : L = 0 := by rw [hLdef, h, norm_zero]
    rw [h1] at hL0
    exact lt_irrefl _ hL0
  have hLn : ∀ m : ℕ, (0:ℝ) < L ^ m := fun m => pow_pos hL0 m
  have h2L : ∀ m : ℕ, (2:ℝ) ^ m ≤ L ^ m := fun m => pow_le_pow_left₀ (by norm_num) hlam2 m
  -- rewrite via the exact recursion
  rw [koenigsApprox_succ hβ hlam n w]
  -- both sides are the n-th orbit of nearby seeds
  set v : ℂ := (w + w ^ (2 : ℕ) / (2 * β) ^ (n + 2)) / (2 * β) ^ n with hvdef
  set v' : ℂ := w / (2 * β) ^ n with hv'def
  have hgv : koenigsApprox c β n (w + w ^ (2 : ℕ) / (2 * β) ^ (n + 2))
      = (quadratic c)^[n] (β + v) := rfl
  have hgv' : koenigsApprox c β n w = (quadratic c)^[n] (β + v') := rfl
  rw [hgv, hgv']
  -- seed bounds
  have hnormpow : ∀ m : ℕ, ‖((2 * β) ^ m : ℂ)‖ = L ^ m := by
    intro m
    rw [norm_pow]
  have hv'norm : ‖v'‖ * L ^ n = ‖w‖ := by
    rw [hv'def, norm_div, hnormpow]
    field_simp
  have hTw : ‖w + w ^ (2 : ℕ) / (2 * β) ^ (n + 2)‖ ≤ ‖w‖ + ‖w‖ ^ (2 : ℕ) / L ^ (n + 2) := by
    calc ‖w + w ^ (2 : ℕ) / (2 * β) ^ (n + 2)‖
        ≤ ‖w‖ + ‖w ^ (2 : ℕ) / (2 * β) ^ (n + 2)‖ := norm_add_le _ _
      _ = ‖w‖ + ‖w‖ ^ (2 : ℕ) / L ^ (n + 2) := by
          rw [norm_div, norm_pow, hnormpow]
  have hvnorm : ‖v‖ * L ^ n ≤ ‖w‖ + ‖w‖ ^ (2 : ℕ) / L ^ (n + 2) := by
    rw [hvdef, norm_div, hnormpow]
    rw [div_mul_cancel₀ _ (ne_of_gt (hLn n))]
    exact hTw
  -- the perturbation is tiny: ‖w‖²/L^(n+2) ≤ (1/32)²/4 and totals stay ≤ 1/16
  have hwsq : ‖w‖ ^ (2 : ℕ) / L ^ (n + 2) ≤ 1 / 32 := by
    have h1 : ‖w‖ ^ (2 : ℕ) ≤ (1/32) * (1/32) := by
      have := norm_nonneg w
      nlinarith
    have h2 : (4:ℝ) ≤ L ^ (n + 2) := by
      calc (4:ℝ) = 2 ^ (2 : ℕ) := by norm_num
        _ ≤ 2 ^ (n + 2) := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
        _ ≤ L ^ (n + 2) := h2L (n + 2)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hseedv' : ‖v'‖ * L ^ n ≤ 1 / 16 := by
    rw [hv'norm]
    linarith
  have hseedv : ‖v‖ * L ^ n ≤ 1 / 16 := by
    calc ‖v‖ * L ^ n ≤ ‖w‖ + ‖w‖ ^ (2 : ℕ) / L ^ (n + 2) := hvnorm
      _ ≤ 1 / 32 + 1 / 32 := by linarith
      _ = 1 / 16 := by norm_num
  -- apply the two-orbit comparison
  have hcmp := orbit_compare_bound hβ hlam2 hseedv hseedv'
  have hdiff : ‖v - v'‖ = ‖w‖ ^ (2 : ℕ) / L ^ (2 * n + 2) := by
    have h3 : v - v' = w ^ (2 : ℕ) / (2 * β) ^ (2 * n + 2) := by
      rw [hvdef, hv'def]
      have h4 : ((2 * β) ^ n : ℂ) ≠ 0 := pow_ne_zero n hlam
      have h5 : ((2 * β) ^ (n + 2) : ℂ) ≠ 0 := pow_ne_zero _ hlam
      field_simp
      ring
    rw [h3, norm_div, norm_pow, hnormpow]
  calc ‖(quadratic c)^[n] (β + v) - (quadratic c)^[n] (β + v')‖
      ≤ 2 * ‖v - v'‖ * L ^ n := hcmp
    _ = 2 * (‖w‖ ^ (2 : ℕ) / L ^ (2 * n + 2)) * L ^ n := by rw [hdiff]
    _ = 2 * ‖w‖ ^ (2 : ℕ) / L ^ (n + 2) := by
        rw [show 2 * n + 2 = (n + 2) + n by omega, pow_add]
        field_simp

end Bottcher

namespace Bottcher

/-- The Koenigs linearizer as a pointwise limit. -/
noncomputable def koenigsFun (c β : ℂ) (w : ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun n => koenigsApprox c β n w)

/-- Each approximant is entire in `w`. -/
theorem koenigsApprox_differentiable (c β : ℂ) (n : ℕ) :
    Differentiable ℂ (koenigsApprox c β n) := by
  have h1 : Differentiable ℂ (quadratic c) := by
    unfold quadratic
    fun_prop
  have h2 : Differentiable ℂ ((quadratic c)^[n]) := h1.iterate n
  have h3 : Differentiable ℂ (fun w : ℂ => β + w / (2 * β) ^ n) := by
    fun_prop
  exact h2.comp h3

/-- The approximant sequence is geometrically Cauchy on the working disk. -/
theorem koenigsApprox_cauchySeq {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 32) :
    CauchySeq (fun n => koenigsApprox c β n w) := by
  apply cauchySeq_of_le_geometric (r := 1/2) (C := ‖w‖ ^ (2 : ℕ) / 2) (by norm_num)
  intro n
  rw [dist_eq_norm]
  have h1 : ‖koenigsApprox c β n w - koenigsApprox c β (n+1) w‖
      = ‖koenigsApprox c β (n+1) w - koenigsApprox c β n w‖ := norm_sub_rev _ _
  rw [h1]
  have h2 := koenigsApprox_cauchy_step hβ hlam2 hw n
  have hL2 : (2:ℝ) ^ (n + 2) ≤ ‖2 * β‖ ^ (n + 2) :=
    pow_le_pow_left₀ (by norm_num) hlam2 (n + 2)
  have h2pos : (0:ℝ) < 2 ^ (n + 2) := by positivity
  have hLpos : (0:ℝ) < ‖2 * β‖ ^ (n + 2) :=
    pow_pos (lt_of_lt_of_le (by norm_num) hlam2) _
  have h3 : 2 * ‖w‖ ^ (2 : ℕ) / ‖2 * β‖ ^ (n + 2) ≤ 2 * ‖w‖ ^ (2 : ℕ) / 2 ^ (n + 2) := by
    apply div_le_div_of_nonneg_left _ h2pos hL2
    positivity
  have h4 : 2 * ‖w‖ ^ (2 : ℕ) / 2 ^ (n + 2) = ‖w‖ ^ (2 : ℕ) / 2 * (1/2) ^ n := by
    rw [div_pow, one_pow, pow_add]
    field_simp
  calc ‖koenigsApprox c β (n+1) w - koenigsApprox c β n w‖
      ≤ 2 * ‖w‖ ^ (2 : ℕ) / ‖2 * β‖ ^ (n + 2) := h2
    _ ≤ 2 * ‖w‖ ^ (2 : ℕ) / 2 ^ (n + 2) := h3
    _ = ‖w‖ ^ (2 : ℕ) / 2 * (1/2) ^ n := h4

/-- The approximants converge to `koenigsFun` on the working disk. -/
theorem koenigsApprox_tendsto {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 32) :
    Filter.Tendsto (fun n => koenigsApprox c β n w) Filter.atTop
      (nhds (koenigsFun c β w)) := by
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (koenigsApprox_cauchySeq hβ hlam2 hw)
  have h1 : koenigsFun c β w = l := hl.limUnder_eq
  rw [h1]
  exact hl

/-- **Distance to the limit**: the tail of the geometric telescope. -/
theorem koenigsFun_dist_approx {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 32) (n : ℕ) :
    dist (koenigsApprox c β n w) (koenigsFun c β w) ≤ ‖w‖ ^ (2 : ℕ) / 2 * (1/2) ^ n / (1 - 1/2) := by
  have hstep : ∀ m : ℕ, dist (koenigsApprox c β m w) (koenigsApprox c β (m+1) w)
      ≤ ‖w‖ ^ (2 : ℕ) / 2 * (1/2) ^ m := by
    intro m
    rw [dist_eq_norm, norm_sub_rev]
    have h2 := koenigsApprox_cauchy_step hβ hlam2 hw m
    have hL2 : (2:ℝ) ^ (m + 2) ≤ ‖2 * β‖ ^ (m + 2) :=
      pow_le_pow_left₀ (by norm_num) hlam2 (m + 2)
    have h2pos : (0:ℝ) < 2 ^ (m + 2) := by positivity
    have h3 : 2 * ‖w‖ ^ (2 : ℕ) / ‖2 * β‖ ^ (m + 2) ≤ 2 * ‖w‖ ^ (2 : ℕ) / 2 ^ (m + 2) := by
      apply div_le_div_of_nonneg_left _ h2pos hL2
      positivity
    have h4 : 2 * ‖w‖ ^ (2 : ℕ) / 2 ^ (m + 2) = ‖w‖ ^ (2 : ℕ) / 2 * (1/2) ^ m := by
      rw [div_pow, one_pow, pow_add]
      field_simp
    calc ‖koenigsApprox c β (m+1) w - koenigsApprox c β m w‖
        ≤ 2 * ‖w‖ ^ (2 : ℕ) / ‖2 * β‖ ^ (m + 2) := h2
      _ ≤ 2 * ‖w‖ ^ (2 : ℕ) / 2 ^ (m + 2) := h3
      _ = ‖w‖ ^ (2 : ℕ) / 2 * (1/2) ^ m := h4
  exact dist_le_of_le_geometric_of_tendsto (1/2) (‖w‖ ^ (2 : ℕ) / 2) (by norm_num) hstep
    (koenigsApprox_tendsto hβ hlam2 hw) n

end Bottcher

namespace Bottcher

/-- `g₀ = β + w` exactly. -/
theorem koenigsApprox_zero_fun (c β : ℂ) (w : ℂ) : koenigsApprox c β 0 w = β + w := by
  unfold koenigsApprox
  simp

/-- **Quadratic normalization of the linearizer**: `‖ψ(w) − β − w‖ ≤ ‖w‖²` on the working disk.
The tangency to the identity at the fixed point — derivative-free. -/
theorem koenigsFun_normalization {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 32) :
    ‖koenigsFun c β w - (β + w)‖ ≤ ‖w‖ ^ (2 : ℕ) := by
  have h1 := koenigsFun_dist_approx hβ hlam2 hw 0
  rw [koenigsApprox_zero_fun, dist_eq_norm, norm_sub_rev] at h1
  have h2 : ‖w‖ ^ (2 : ℕ) / 2 * (1/2) ^ (0 : ℕ) / (1 - 1/2) = ‖w‖ ^ (2 : ℕ) := by
    ring_nf
  rw [h2] at h1
  exact h1

/-- The linearizer sends `0` to the fixed point. -/
theorem koenigsFun_zero {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) : koenigsFun c β 0 = β := by
  have hfix : quadratic c β = β := by
    unfold quadratic
    exact hβ
  have h1 : ∀ n : ℕ, koenigsApprox c β n 0 = β := by
    intro n
    unfold koenigsApprox
    rw [zero_div, add_zero]
    induction n with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', ih, hfix]
  unfold koenigsFun
  have h2 : (fun n => koenigsApprox c β n 0) = fun _ : ℕ => β := funext h1
  rw [h2]
  exact tendsto_const_nhds.limUnder_eq

/-- **The Koenigs functional equation**: `ψ(λw) = f(ψ(w))` on the working disk. -/
theorem koenigsFun_semiconj {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 32) (hw2 : ‖2 * β * w‖ ≤ 1 / 32) :
    koenigsFun c β (2 * β * w) = quadratic c (koenigsFun c β w) := by
  have hlam : (2 * β) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlam2
    linarith
  -- the shift identity g_{m+1}(λw) = f(g_m(w))
  have hshift : ∀ m : ℕ, koenigsApprox c β (m + 1) (2 * β * w)
      = quadratic c (koenigsApprox c β m w) := by
    intro m
    unfold koenigsApprox
    rw [Function.iterate_succ_apply']
    congr 1
    congr 1
    have hβ0 : β ≠ 0 := by
      intro h
      apply hlam
      rw [h]
      ring
    have h1 : ((2 * β) ^ (m + 1) : ℂ) ≠ 0 := pow_ne_zero _ hlam
    have h2 : ((2 * β) ^ m : ℂ) ≠ 0 := pow_ne_zero _ hlam
    rw [pow_succ]
    field_simp
  -- limits on both sides
  have hL : Filter.Tendsto (fun m => koenigsApprox c β (m + 1) (2 * β * w)) Filter.atTop
      (nhds (koenigsFun c β (2 * β * w))) :=
    (koenigsApprox_tendsto hβ hlam2 hw2).comp (Filter.tendsto_add_atTop_nat 1)
  have hquadcont : Continuous (quadratic c) := by
    unfold quadratic
    fun_prop
  have hR : Filter.Tendsto (fun m => quadratic c (koenigsApprox c β m w)) Filter.atTop
      (nhds (quadratic c (koenigsFun c β w))) :=
    (hquadcont.tendsto _).comp (koenigsApprox_tendsto hβ hlam2 hw)
  have h3 : (fun m => koenigsApprox c β (m + 1) (2 * β * w))
      = fun m => quadratic c (koenigsApprox c β m w) := funext hshift
  rw [h3] at hL
  exact tendsto_nhds_unique hL hR

end Bottcher

namespace Bottcher

/-- **The linearizer is analytic** on the working disk: locally uniform limit of entire maps. -/
theorem koenigsFun_analyticOnNhd {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖) :
    AnalyticOnNhd ℂ (koenigsFun c β) (Metric.ball (0:ℂ) (1/32)) := by
  have huniform : TendstoUniformlyOn (fun n => koenigsApprox c β n) (koenigsFun c β)
      Filter.atTop (Metric.ball (0:ℂ) (1/32)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    -- uniform tail: dist ≤ (1/32)²·(1/2)^n → 0
    have htail : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/32) ^ (2 : ℕ) * (1/2) ^ n)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2) ^ n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h2 := h1.const_mul (((1:ℝ)/32) ^ (2 : ℕ))
      simpa using h2
    have hev : ∀ᶠ n in Filter.atTop, ((1:ℝ)/32) ^ (2 : ℕ) * (1/2) ^ n < ε := by
      filter_upwards [htail.eventually_lt_const hε] with n hn
      exact hn
    filter_upwards [hev] with n hn w hw
    have hw32 : ‖w‖ ≤ 1 / 32 := by
      rw [Metric.mem_ball, dist_zero_right] at hw
      linarith
    have h3 := koenigsFun_dist_approx hβ hlam2 hw32 n
    have h4 : ‖w‖ ^ (2 : ℕ) / 2 * (1/2) ^ n / (1 - 1/2) = ‖w‖ ^ (2 : ℕ) * (1/2) ^ n := by
      ring_nf
    rw [h4] at h3
    have h5 : ‖w‖ ^ (2 : ℕ) * (1/2) ^ n ≤ ((1:ℝ)/32) ^ (2 : ℕ) * (1/2) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have := norm_nonneg w
      nlinarith
    calc dist (koenigsFun c β w) (koenigsApprox c β n w)
        = dist (koenigsApprox c β n w) (koenigsFun c β w) := dist_comm _ _
      _ ≤ ‖w‖ ^ (2 : ℕ) * (1/2) ^ n := h3
      _ ≤ ((1:ℝ)/32) ^ (2 : ℕ) * (1/2) ^ n := h5
      _ < ε := hn
  have hdiff : DifferentiableOn ℂ (koenigsFun c β) (Metric.ball (0:ℂ) (1/32)) := by
    apply TendstoLocallyUniformlyOn.differentiableOn
      (huniform.tendstoLocallyUniformlyOn) ?_ Metric.isOpen_ball
    filter_upwards with n
    exact (koenigsApprox_differentiable c β n).differentiableOn
  intro z hz
  exact (hdiff.analyticAt (Metric.isOpen_ball.mem_nhds hz))

end Bottcher

namespace Bottcher

/-- **λ-self-similarity of the Julia pullback**: through the linearizer, membership of the filled
Julia set is invariant under multiplication by the multiplier — the formal germ of the
self-similar cone structure of `K` at the repelling fixed point. -/
theorem koenigs_pullback_invariant {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 32) (hw2 : ‖2 * β * w‖ ≤ 1 / 32) :
    koenigsFun c β (2 * β * w) ∈ filledJulia c ↔ koenigsFun c β w ∈ filledJulia c := by
  rw [koenigsFun_semiconj hβ hlam2 hw hw2]
  exact (mem_filledJulia_iff_quadratic_mem (c := c) (z := koenigsFun c β w)).symm

end Bottcher

namespace Bottcher

/-- **The linearizer is tangent to the identity**: `ψ'(0) = 1`, derivative-free from the
quadratic normalization bound. -/
theorem koenigsFun_hasDerivAt_zero {c β : ℂ} (hβ : β ^ (2 : ℕ) + c = β) (hlam2 : 2 ≤ ‖2 * β‖) :
    HasDerivAt (koenigsFun c β) 1 0 := by
  rw [hasDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hball : Metric.ball (0:ℂ) (min ε (1/32)) ∈ nhds (0:ℂ) :=
    Metric.ball_mem_nhds 0 (lt_min hε (by norm_num))
  filter_upwards [hball] with w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hw32 : ‖w‖ ≤ 1 / 32 := le_of_lt (lt_of_lt_of_le hw (min_le_right _ _))
  have hwε : ‖w‖ ≤ ε := le_of_lt (lt_of_lt_of_le hw (min_le_left _ _))
  have h1 := koenigsFun_normalization hβ hlam2 hw32
  have h2 : koenigsFun c β w - koenigsFun c β 0 - (w - 0) • (1:ℂ)
      = koenigsFun c β w - (β + w) := by
    rw [koenigsFun_zero hβ]
    simp
    ring
  rw [h2]
  calc ‖koenigsFun c β w - (β + w)‖ ≤ ‖w‖ ^ (2 : ℕ) := h1
    _ = ‖w‖ * ‖w‖ := sq ‖w‖
    _ ≤ ε * ‖w - 0‖ := by
        rw [sub_zero]
        apply mul_le_mul_of_nonneg_right hwε (norm_nonneg w)

end Bottcher

namespace Bottcher

/-- **Parabolic location of the Julia pullback** (real parameters): in linearizing coordinates
the filled Julia set lies in the parabolic region `{Re v ≤ ‖v‖²}` — because `K` sits inside the
`β`-disk whose boundary through `β` is vertical, and `ψ` is tangent to the identity.  The sector
`{Re v > ‖v‖²}` is therefore basin, at every scale: the formal lune. -/
theorem koenigs_pullback_re_le {c : ℝ} (hc0 : c ≤ 0)
    {v : ℂ} (hv : ‖v‖ ≤ 1 / 32)
    (hmem : koenigsFun (c:ℂ) ((betaFixed c : ℝ) : ℂ) v ∈ filledJulia (c:ℂ)) :
    v.re ≤ ‖v‖ ^ (2 : ℕ) := by
  set β : ℂ := ((betaFixed c : ℝ) : ℂ) with hβdef
  have hβsq : β ^ (2 : ℕ) + (c:ℂ) = β := by
    rw [hβdef]
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (betaFixed_sq hc0)
  have hβ1 : 1 ≤ betaFixed c := one_le_betaFixed hc0
  have hlam2 : 2 ≤ ‖2 * β‖ := by
    rw [hβdef]
    have h1 : (2 * ((betaFixed c : ℝ) : ℂ)) = (((2 * betaFixed c : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  -- the norm bound from the extreme-radius localization
  have hnorm : ‖koenigsFun (c:ℂ) β v‖ ≤ betaFixed c := by
    have h2 := filledJulia_subset_closedBall_betaFixed hc0 hmem
    rwa [Metric.mem_closedBall, dist_zero_right] at h2
  -- the tangency decomposition
  have htang := koenigsFun_normalization hβsq hlam2 hv
  set e : ℂ := koenigsFun (c:ℂ) β v - (β + v) with hedef
  have hψ : koenigsFun (c:ℂ) β v = β + v + e := by
    rw [hedef]
    ring
  -- real parts:  β + Re v + Re e ≤ ‖ψ v‖ ≤ β
  have hre : (β + v + e).re ≤ ‖koenigsFun (c:ℂ) β v‖ := by
    rw [hψ] at *
    exact Complex.re_le_norm _
  have hβre : (β + v + e).re = betaFixed c + v.re + e.re := by
    rw [hβdef]
    simp [Complex.add_re, Complex.ofReal_re]
  rw [hβre] at hre
  have h3 : v.re + e.re ≤ 0 := by linarith
  have h4 : -e.re ≤ ‖e‖ := by
    calc -e.re = (-e).re := by simp
      _ ≤ ‖-e‖ := Complex.re_le_norm _
      _ = ‖e‖ := norm_neg e
  linarith [htang]

/-- **The scale-invariant sector lune**: the convex sector `{Re v > ‖v‖/2}` inside the working
disk is disjoint from the Julia pullback and closed under shrinking by any positive real factor
— the fixed connected target for all scale-level connectors. -/
theorem sector_disjoint_pullback {c : ℝ} (hc0 : c ≤ 0)
    {v : ℂ} (hv : ‖v‖ ≤ 1 / 32) (hsec : ‖v‖ / 2 < v.re) :
    koenigsFun (c:ℂ) ((betaFixed c : ℝ) : ℂ) v ∉ filledJulia (c:ℂ) := by
  intro hmem
  have h1 := koenigs_pullback_re_le hc0 hv hmem
  have h2 : ‖v‖ ^ (2 : ℕ) ≤ ‖v‖ / 32 := by
    have h3 := norm_nonneg v
    nlinarith
  have h4 : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
  nlinarith

/-- The sector is convex (superlevel set of the concave `Re v − ‖v‖/2`), hence preconnected. -/
theorem sector_convex : Convex ℝ {v : ℂ | ‖v‖ / 2 < v.re} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h1 : ‖s • x + t • y‖ ≤ s * ‖x‖ + t * ‖y‖ := by
    calc ‖s • x + t • y‖ ≤ ‖s • x‖ + ‖t • y‖ := norm_add_le _ _
      _ = s * ‖x‖ + t * ‖y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hs, abs_of_nonneg ht]
  have h2 : (s • x + t • y).re = s * x.re + t * y.re := by
    simp [Complex.add_re]
  rw [h2]
  rcases lt_or_eq_of_le hs with hs' | hs'
  · nlinarith [mul_lt_mul_of_pos_left hx hs', mul_le_mul_of_nonneg_left (le_of_lt hy) ht]
  · have ht1 : t = 1 := by linarith
    rw [← hs', ht1]
    simpa using hy

end Bottcher
