import GaloisForLFunctions.RHTower.ChebyshevShortWindowUpperBound
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths

/-!
# Huxley's prime number theorem in short intervals

For every `7/12 < α < 1`,

`(ψ(x + x^α) - ψ(x)) / x^α → 1`   as `x → ∞`.

With `h = x^α` and `h' = h/M`, the two window bounds read
`h(1 - 2/M) - 4/(x h') - 2h Σ ≤ ψ(x+h) - ψ(x) ≤ h(1 + 2/M) + 4/(x h') + 8h Σ'`, where both zero sums
are weighted sums of the form `Σ_ρ x^{β-1} min(1, c x^{2u}/(|ρ||1-ρ|))` with `u = 1 - α < 5/12` and
`c = 8M`, resp. `4M`; they tend to `0` (`tendsto_tsum_zeroShortWeight_seven_twelfths`), as does
`4/(x h' h) = 4M/x^{1+2α}`.  Letting `M → ∞` gives the limit.
-/

noncomputable section

namespace RHTower

open Filter Topology RHTower.Sieve

/-- `C x²/(x^α · x^α/M) = (C M) x^{2(1-α)}`. -/
theorem sq_div_rpow_mul_rpow_div_eq {x α C M : ℝ} (hx : 0 < x) (hM : 0 < M) :
    C * x ^ 2 / (x ^ α * (x ^ α / M)) = (C * M) * x ^ (2 * (1 - α)) := by
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have h2 : x ^ (2 * (1 - α)) = x ^ 2 / (x ^ α * x ^ α) := by
    rw [show 2 * (1 - α) = (2 : ℝ) - (α + α) by ring, Real.rpow_sub hx, Real.rpow_add hx,
      Real.rpow_two]
  rw [h2]
  field_simp

/-- **Huxley's prime number theorem in short intervals.** -/
theorem tendsto_psi_short_window_div_seven_twelfths {α : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1) :
    Tendsto (fun x : ℝ => (Chebyshev.psi (x + x ^ α) - Chebyshev.psi x) / x ^ α) atTop (𝓝 1) := by
  have hu : 0 < 1 - α := by linarith
  have hu' : 1 - α < 5 / 12 := by linarith
  have hsmall4 : Tendsto (fun x : ℝ => x ^ (-(1 + 2 * α))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  -- the size facts at height `x`
  have hfacts : ∀ᶠ x : ℝ in atTop, 4 ≤ x ∧ x ^ α ≤ x / 2 := by
    have h := (tendsto_rpow_atTop (show 0 < 1 - α by linarith)).eventually_ge_atTop 2
    filter_upwards [h, eventually_ge_atTop (4 : ℝ)] with x hx hx4
    refine ⟨hx4, ?_⟩
    have hx0 : 0 < x := by linarith
    have hsplit : x = x ^ α * x ^ (1 - α) := by
      rw [← Real.rpow_add hx0]; simp
    have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
    nlinarith
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨M, hM⟩ : ∃ M : ℕ, 6 / (1 - a) < M ∧ 4 ≤ M := by
      obtain ⟨M, hM⟩ := exists_nat_gt (max (6 / (1 - a)) 4)
      exact ⟨M, lt_of_le_of_lt (le_max_left _ _) hM,
        by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hM).le⟩
    have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM.2
    have hM0 : (0 : ℝ) < M := by linarith
    have hMa : 2 / (M : ℝ) < (1 - a) / 3 := by
      rw [div_lt_iff₀ hM0]
      have := hM.1
      rw [div_lt_iff₀ (by linarith)] at this
      linarith
    have hzero := tendsto_tsum_zeroShortWeight_seven_twelfths (u := 1 - α) (c := 8 * M) hu hu'
      (by linarith)
    have hz := hzero.eventually (gt_mem_nhds (show (0 : ℝ) < (1 - a) / 6 by linarith))
    have h4t : Tendsto (fun x : ℝ => 4 * (M : ℝ) * x ^ (-(1 + 2 * α))) atTop (𝓝 0) := by
      simpa using hsmall4.const_mul (4 * (M : ℝ))
    have h4 := h4t.eventually (gt_mem_nhds (show (0 : ℝ) < (1 - a) / 6 by linarith))
    filter_upwards [hfacts, hz, h4] with x ⟨hx4, hxα⟩ hzx h4x
    have hx0 : 0 < x := by linarith
    have hh0 : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
    have hh' : 0 < x ^ α / M := div_pos hh0 hM0
    have hmain := psi_window_ge_sub_zeroShortWeight (x := x) (h := x ^ α) (h' := x ^ α / M)
      (by linarith) hh' (by rw [mul_div_assoc']; rw [div_le_iff₀ hM0]; nlinarith) (by linarith)
    rw [sq_div_rpow_mul_rpow_div_eq hx0 hM0] at hmain
    obtain ⟨h, hh⟩ : ∃ h : ℝ, h = x ^ α := ⟨_, rfl⟩
    rw [← hh] at hmain hh0 hh' ⊢
    have hterm : 4 / (x * (h / M)) / h = 4 * M * x ^ (-(1 + 2 * α)) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_add hx0, Real.rpow_one, Real.rpow_mul hx0.le, hh]
      rw [show (x ^ (2 : ℝ)) ^ α = x ^ α * x ^ α by
        rw [← Real.rpow_mul hx0.le, mul_comm, Real.rpow_mul hx0.le, Real.rpow_two]; ring]
      field_simp
    rw [lt_div_iff₀ hh0]
    have hS0 : 0 ≤ ∑' q : XiZeroCopy, zeroShortWeight x (8 * M * x ^ (2 * (1 - α))) (q.1 : ℂ) :=
      tsum_nonneg fun q => zeroShortWeight_nonneg hx0.le (by positivity) _
    have h4' : 4 / (x * (h / M)) < (1 - a) / 6 * h := by
      rw [← div_lt_iff₀ hh0, hterm]
      exact h4x
    have hzx' : 2 * h * ∑' q : XiZeroCopy, zeroShortWeight x (8 * M * x ^ (2 * (1 - α))) (q.1 : ℂ)
        ≤ 2 * h * ((1 - a) / 6) := mul_le_mul_of_nonneg_left hzx.le (by positivity)
    have h2M : 2 * (h / M) = 2 / M * h := by ring
    have h2Mle : 2 / (M : ℝ) * h ≤ (1 - a) / 3 * h := mul_le_mul_of_nonneg_right hMa.le hh0.le
    nlinarith
  · intro b hb
    obtain ⟨M, hM⟩ : ∃ M : ℕ, 6 / (b - 1) < M ∧ 4 ≤ M := by
      obtain ⟨M, hM⟩ := exists_nat_gt (max (6 / (b - 1)) 4)
      exact ⟨M, lt_of_le_of_lt (le_max_left _ _) hM,
        by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hM).le⟩
    have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM.2
    have hM0 : (0 : ℝ) < M := by linarith
    have hMb : 2 / (M : ℝ) < (b - 1) / 3 := by
      rw [div_lt_iff₀ hM0]
      have := hM.1
      rw [div_lt_iff₀ (by linarith)] at this
      linarith
    have hzero := tendsto_tsum_zeroShortWeight_seven_twelfths (u := 1 - α) (c := 4 * M) hu hu'
      (by linarith)
    have hz := hzero.eventually (gt_mem_nhds (show (0 : ℝ) < (b - 1) / 24 by linarith))
    have h4t : Tendsto (fun x : ℝ => 4 * (M : ℝ) * x ^ (-(1 + 2 * α))) atTop (𝓝 0) := by
      simpa using hsmall4.const_mul (4 * (M : ℝ))
    have h4 := h4t.eventually (gt_mem_nhds (show (0 : ℝ) < (b - 1) / 6 by linarith))
    filter_upwards [hfacts, hz, h4] with x ⟨hx4, hxα⟩ hzx h4x
    have hx0 : 0 < x := by linarith
    have hh0 : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
    have hh' : 0 < x ^ α / M := div_pos hh0 hM0
    have hmain := psi_window_le_add_zeroShortWeight (x := x) (h := x ^ α) (h' := x ^ α / M) hx4
      hh' (by rw [mul_div_assoc']; rw [div_le_iff₀ hM0]; nlinarith) hxα
    rw [sq_div_rpow_mul_rpow_div_eq hx0 hM0] at hmain
    obtain ⟨h, hh⟩ : ∃ h : ℝ, h = x ^ α := ⟨_, rfl⟩
    rw [← hh] at hmain hh0 hh' ⊢
    have hterm : 4 / (x * (h / M)) / h = 4 * M * x ^ (-(1 + 2 * α)) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_add hx0, Real.rpow_one, Real.rpow_mul hx0.le, hh]
      rw [show (x ^ (2 : ℝ)) ^ α = x ^ α * x ^ α by
        rw [← Real.rpow_mul hx0.le, mul_comm, Real.rpow_mul hx0.le, Real.rpow_two]; ring]
      field_simp
    rw [div_lt_iff₀ hh0]
    have h4' : 4 / (x * (h / M)) < (b - 1) / 6 * h := by
      rw [← div_lt_iff₀ hh0, hterm]
      exact h4x
    have hzx' : 8 * h * ∑' q : XiZeroCopy, zeroShortWeight x (4 * M * x ^ (2 * (1 - α))) (q.1 : ℂ)
        ≤ 8 * h * ((b - 1) / 24) := mul_le_mul_of_nonneg_left hzx.le (by positivity)
    have h2Mle : 2 / (M : ℝ) * h ≤ (b - 1) / 3 * h := mul_le_mul_of_nonneg_right hMb.le hh0.le
    have h2M : 2 * (h / M) = 2 / M * h := by ring
    nlinarith

end RHTower
