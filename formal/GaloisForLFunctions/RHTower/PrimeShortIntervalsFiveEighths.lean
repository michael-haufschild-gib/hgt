import GaloisForLFunctions.RHTower.XiZeroShortWeightVanishing
import GaloisForLFunctions.RHTower.Sieve.ShortIntervalThetaEveryWindow

/-!
# Prime mass in every window of length `x^α`, `α > 5/8`

With `h = x^α/2` and `h' = h/16`, the two-window lower bound reads

`ψ(x+h) - ψ(x) ≥ (7/8)h - 128/x^{1+α} - 2h Σ_ρ x^{β-1} min(1, 512 x^{2(1-α)}/(|ρ||1-ρ|))`,

and for `1 - α < 3/8` the zero sum tends to `0`.  Hence `ψ(x + x^α/2) - ψ(x) ≥ (5/8)(x^α/2)` for large
`x`; subtracting the prime powers, `ψ - θ ≤ 2√x log x`, leaves `θ(x + x^α/2) - θ(x) ≥ x^α/4`.  Chaining
the windows `z ↦ z + z^α/2` gives the every-window form

`θ(y + L) - θ(y) ≥ (L - (y + L)^α)/2`   (`y ≥ X`, `L ≥ 0`).
-/

namespace RHTower

noncomputable section

open Filter Topology

/-- **Short `ψ` windows at every exponent `α > 5/8`.** -/
theorem eventually_psi_short_window {α : ℝ} (hα : 5 / 8 < α) (hα1 : α < 1) :
    ∀ᶠ x : ℝ in atTop, (5 / 8) * (x ^ α / 2)
      ≤ Chebyshev.psi (x + x ^ α / 2) - Chebyshev.psi x := by
  have hzero := tendsto_tsum_zeroShortWeight (u := 1 - α) (c := 512) (by linarith) (by linarith)
    (by norm_num)
  have hsmall := hzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hdecay : Tendsto (fun x : ℝ => x ^ (-(1 + 2 * α))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hdec := hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4096))
  filter_upwards [hsmall, hdec, eventually_ge_atTop (2 : ℝ)] with x hS hd hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set h := x ^ α / 2 with hh
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hh0 : 0 < h := by rw [hh]; positivity
  have hhx : h ≤ x := by
    rw [hh]
    have : x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hα1.le
    rw [Real.rpow_one] at this
    linarith
  have hmain := psi_window_ge_sub_zeroShortWeight (h := h) (h' := h / 16) hx (by positivity)
    (by linarith) hhx
  have hY : 8 * x ^ 2 / (h * (h / 16)) = 512 * x ^ (2 * (1 - α)) := by
    have e1 : x ^ (2 * (1 - α)) = x ^ 2 / (x ^ α * x ^ α) := by
      rw [show 2 * (1 - α) = (2 : ℝ) - (α + α) by ring, Real.rpow_sub hx0, Real.rpow_add hx0,
        Real.rpow_two]
    rw [e1, hh]
    field_simp
    ring
  rw [hY] at hmain
  -- the trivial-zero term
  have htriv : 4 / (x * (h / 16)) ≤ h / 16 := by
    have hpow : x ^ (-(1 + 2 * α)) = 1 / (x * x ^ α * x ^ α) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_add hx0, Real.rpow_one, Real.rpow_mul hx0.le]
      rw [show (x ^ (2 : ℝ)) ^ α = x ^ α * x ^ α by
        rw [← Real.rpow_mul hx0.le, mul_comm, Real.rpow_mul hx0.le, Real.rpow_two]; ring]
      rw [inv_eq_one_div]
      ring
    rw [hpow, div_lt_iff₀ (by positivity)] at hd
    rw [hh, div_le_div_iff₀ (by positivity) (by norm_num)]
    have e : x ^ α / 2 * (x * (x ^ α / 2 / 16)) = (x * x ^ α * x ^ α) / 64 := by ring
    rw [e]
    linarith
  have hzs : 2 * h * ∑' q : XiZeroCopy, zeroShortWeight x (512 * x ^ (2 * (1 - α))) (q.1 : ℂ)
      ≤ h / 8 := by
    have := hS.le
    nlinarith
  linarith

/-- **Short `θ` windows at every exponent `α > 5/8`.** -/
theorem eventually_theta_short_window {α : ℝ} (hα : 5 / 8 < α) (hα1 : α < 1) :
    ∀ᶠ x : ℝ in atTop, x ^ α / 2 / 2 ≤ Chebyshev.theta (x + x ^ α / 2) - Chebyshev.theta x := by
  have hlo := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by linarith : (0 : ℝ) < α - 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 256)
  filter_upwards [eventually_psi_short_window hα hα1, hlo, eventually_ge_atTop (2 : ℝ)]
    with x hψ hlog hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set h := x ^ α / 2 with hh
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hhx : h ≤ x := by
    rw [hh]
    have : x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hα1.le
    rw [Real.rpow_one] at this
    linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hlogx,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hlog
  -- prime powers
  have hpt := Chebyshev.psi_sub_theta_le (x := x + h) (by linarith)
  have htp := Chebyshev.theta_le_psi x
  have hsqrt : √(x + h) ≤ 2 * x ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc (x + h) ^ (1 / 2 : ℝ) ≤ (4 * x) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = 2 * x ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hx0.le]
          congr 1
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hlog2 : Real.log (x + h) ≤ 2 * Real.log x := by
    have h1 : Real.log (x + h) ≤ Real.log (x * x) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_mul hx0.ne' hx0.ne'] at h1
    linarith
  have hsplit : x ^ α = x ^ (1 / 2 : ℝ) * x ^ (α - 1 / 2) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hs0 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hpp : 2 * √(x + h) * Real.log (x + h) ≤ h / 8 := by
    have hl0 : 0 ≤ Real.log (x + h) := Real.log_nonneg (by linarith)
    have hsq0 : 0 ≤ √(x + h) := Real.sqrt_nonneg _
    calc 2 * √(x + h) * Real.log (x + h) ≤ 2 * (2 * x ^ (1 / 2 : ℝ)) * (2 * Real.log x) := by
          gcongr
      _ = 8 * (x ^ (1 / 2 : ℝ) * Real.log x) := by ring
      _ ≤ 8 * (x ^ (1 / 2 : ℝ) * (1 / 256 * x ^ (α - 1 / 2))) := by gcongr
      _ = h / 16 := by rw [hh, hsplit]; ring
      _ ≤ h / 8 := by
          have : 0 < h := by rw [hh]; positivity
          linarith
  linarith

/-- Chaining short windows: a mass bound `z^α/2/c` on every window `(z, z + z^α/2]` beyond `X₀` gives
`θ(y + L) - θ(y) ≥ (L - (y + L)^α)/c` for every `y ≥ X₀` and `L ≥ 0`. -/
theorem theta_window_lower_of_step {α c X₀ : ℝ} (hα0 : 0 ≤ α) (hc : 0 < c) (hX₀ : 1 ≤ X₀)
    (hstep : ∀ z : ℝ, X₀ ≤ z →
      z ^ α / 2 / c ≤ Chebyshev.theta (z + z ^ α / 2) - Chebyshev.theta z) :
    ∀ y L : ℝ, X₀ ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / c ≤ Chebyshev.theta (y + L) - Chebyshev.theta y := by
  classical
  intro y L hy hL
  have hy0 : (0 : ℝ) < y := by linarith
  have hchain : ∀ n : ℕ, (Sieve.thetaChainSeq α y n - y) / c
      ≤ Chebyshev.theta (Sieve.thetaChainSeq α y n) - Chebyshev.theta y := by
    intro n
    induction n with
    | zero => simp [Sieve.thetaChainSeq_zero]
    | succ n ih =>
        have hzy : y ≤ Sieve.thetaChainSeq α y n := Sieve.thetaChainSeq_ge hy0 n
        have hs := hstep (Sieve.thetaChainSeq α y n) (le_trans hy hzy)
        rw [Sieve.thetaChainSeq_succ]
        have e : (Sieve.thetaChainSeq α y n + Sieve.thetaChainSeq α y n ^ α / 2 - y) / c
            = (Sieve.thetaChainSeq α y n - y) / c + Sieve.thetaChainSeq α y n ^ α / 2 / c := by
          ring
        rw [e]
        linarith
  have hex : ∃ n : ℕ, y + L < Sieve.thetaChainSeq α y n :=
    ((Sieve.thetaChainSeq_tendsto hy0 hα0).eventually_gt_atTop (y + L)).exists
  set N := Nat.find hex with hNdef
  have hNspec : y + L < Sieve.thetaChainSeq α y N := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h
    rw [h, Sieve.thetaChainSeq_zero] at hNspec
    linarith
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hMle : Sieve.thetaChainSeq α y M ≤ y + L := by
    by_contra hcon
    exact absurd (lt_of_not_ge hcon) (Nat.find_min hex (by omega))
  have hstepM : Sieve.thetaChainSeq α y N
      = Sieve.thetaChainSeq α y M + (Sieve.thetaChainSeq α y M) ^ α / 2 := by
    rw [hM]
    exact Sieve.thetaChainSeq_succ α y M
  have hMy : y ≤ Sieve.thetaChainSeq α y M := Sieve.thetaChainSeq_ge hy0 M
  have hpowM : (Sieve.thetaChainSeq α y M) ^ α ≤ (y + L) ^ α :=
    Real.rpow_le_rpow (by linarith) hMle hα0
  have hMlow : y + L - (y + L) ^ α / 2 ≤ Sieve.thetaChainSeq α y M := by
    have := hNspec
    rw [hstepM] at this
    linarith
  have hmono : Chebyshev.theta (Sieve.thetaChainSeq α y M) ≤ Chebyshev.theta (y + L) :=
    Chebyshev.theta_mono hMle
  have hpow0 : (0 : ℝ) ≤ (y + L) ^ α := Real.rpow_nonneg (by linarith) α
  have h1 := hchain M
  have h2 : (L - (y + L) ^ α) / c ≤ (Sieve.thetaChainSeq α y M - y) / c :=
    div_le_div_of_nonneg_right (by linarith) hc.le
  linarith

/-- **Prime mass in every short window, exponent `5/8`.**  For every `5/8 < α < 1` there is `X ≥ 1`
with `θ(y + L) - θ(y) ≥ (L - (y + L)^α)/2` for all `y ≥ X` and `L ≥ 0`. -/
theorem exists_theta_window_lower_five_eighths {α : ℝ} (hα : 5 / 8 < α) (hα1 : α < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (eventually_theta_short_window hα hα1)
  refine ⟨max X₀ 1, le_max_right _ _, ?_⟩
  exact theta_window_lower_of_step (by linarith) (by norm_num) (le_max_right _ _)
    (fun z hz => hX₀ z (le_trans (le_max_left _ _) hz))

end

end RHTower
