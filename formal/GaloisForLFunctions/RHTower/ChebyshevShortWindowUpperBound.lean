import GaloisForLFunctions.RHTower.ChebyshevShortWindowLowerBound

/-!
# An upper bound for `ψ(x + h) - ψ(x)` by a single absolutely convergent zero sum

The squeeze of `ChebyshevShortWindowLowerBound`, used on the outer windows: `ψ(x+h) ≤ J(a,b)/w` on
the right window `[x+h, x+h+h']`, and `J(a,b)/w ≤ ψ(x)` on the left window `[x-h', x]`.  With the
logarithmic means in `[a, b]` and the trivial-zero correction this gives, for `4 ≤ x`, `0 < h'`,
`2h' ≤ h ≤ x/2`,

`ψ(x+h) - ψ(x) ≤ h + 2h' + 4/(x h') + Σ_ρ |T(ρ; x+h, x+h+h') - T(ρ; x-h', x)|`,

and each summand is at most `8h · x^{β-1} · min(1, 4x²/(h h' |ρ||1-ρ|))`.
-/

namespace RHTower

noncomputable section

open Complex Finset

/-- **The `ψ` window upper bound.** -/
theorem psi_window_le_add_tsum {x h h' : ℝ} (hx : 4 ≤ x) (hh' : 0 < h') (hh'h : 2 * h' ≤ h)
    (hhx : h ≤ x / 2) :
    Chebyshev.psi (x + h) - Chebyshev.psi x ≤
      h + 2 * h' + 4 / (x * h')
        + ∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) (x + h) (x + h + h')
            - lagWindowZeroTerm (q.1 : ℂ) (x - h') x‖ := by
  set a₃ := x + h with ha₃
  set b₃ := x + h + h' with hb₃
  set a₄ := x - h' with ha₄
  have hx0 : 0 < x := by linarith
  have ha₃1 : 1 < a₃ := by rw [ha₃]; linarith
  have hab₃ : a₃ < b₃ := by rw [ha₃, hb₃]; linarith
  have ha₄1 : 1 < a₄ := by rw [ha₄]; linarith
  have hab₄ : a₄ < x := by rw [ha₄]; linarith
  have ha₃0 : 0 < a₃ := by linarith
  have ha₄0 : 0 < a₄ := by linarith
  have hw₃ : 0 < 1 / a₃ - 1 / b₃ := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha₃0 hab₃
  have hw₄ : 0 < 1 / a₄ - 1 / x := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha₄0 hab₄
  -- the squeeze
  have hsq₃ := (chebyshevLagWindow_bounds ha₃0 hab₃.le).1
  have hsq₄ := (chebyshevLagWindow_bounds ha₄0 hab₄.le).2
  have hψ₃ : Chebyshev.psi a₃ ≤ chebyshevLagWindow a₃ b₃ / (1 / a₃ - 1 / b₃) := by
    rw [le_div_iff₀ hw₃]
    exact hsq₃
  have hψ₄ : chebyshevLagWindow a₄ x / (1 / a₄ - 1 / x) ≤ Chebyshev.psi x := by
    rw [div_le_iff₀ hw₄]
    exact hsq₄
  rw [chebyshevLagWindow_div_eq ha₃1 hab₃] at hψ₃
  rw [chebyshevLagWindow_div_eq ha₄1 hab₄] at hψ₄
  -- logarithmic means
  have hL₃ : Real.log (b₃ / a₃) / (1 / a₃ - 1 / b₃) ≤ b₃ := by
    rw [div_le_iff₀ hw₃]
    exact (log_div_le_mul_inv_sub ha₃0 hab₃.le).2
  have hL₄ : a₄ ≤ Real.log (x / a₄) / (1 / a₄ - 1 / x) := by
    rw [le_div_iff₀ hw₄]
    exact (log_div_le_mul_inv_sub ha₄0 hab₄.le).1
  -- trivial zeros
  have hE₄ : 0 ≤ (trivialZeroSeriesReal a₄ / a₄ - trivialZeroSeriesReal x / x)
      / (1 / a₄ - 1 / x) :=
    div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti ha₄1.le hab₄.le)) hw₄.le
  have hE₃ : (trivialZeroSeriesReal a₃ / a₃ - trivialZeroSeriesReal b₃ / b₃)
      / (1 / a₃ - 1 / b₃) ≤ 4 / (x * h') := by
    have hEb := trivialZeroSeriesReal_nonneg (ha₃1.le.trans hab₃.le)
    have hEa := trivialZeroSeriesReal_le_two_div_sq (show 2 ≤ a₃ by rw [ha₃]; linarith)
    have hb₃0 : 0 < b₃ := by linarith
    have hnum : trivialZeroSeriesReal a₃ / a₃ - trivialZeroSeriesReal b₃ / b₃ ≤
        2 / a₃ ^ 2 / a₃ := by
      have : 0 ≤ trivialZeroSeriesReal b₃ / b₃ := div_nonneg hEb hb₃0.le
      have : trivialZeroSeriesReal a₃ / a₃ ≤ 2 / a₃ ^ 2 / a₃ :=
        div_le_div_of_nonneg_right hEa ha₃0.le
      linarith
    have hweq : 1 / a₃ - 1 / b₃ = h' / (a₃ * b₃) := by
      have hne1 : a₃ ≠ 0 := ha₃0.ne'
      have hne2 : b₃ ≠ 0 := hb₃0.ne'
      field_simp
      rw [hb₃, ha₃]
      ring
    rw [div_le_iff₀ hw₃, hweq]
    refine le_trans hnum ?_
    rw [show 4 / (x * h') * (h' / (a₃ * b₃)) = 4 / (x * (a₃ * b₃)) by field_simp, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have k1 : x * b₃ ≤ a₃ * (2 * a₃) :=
      mul_le_mul (by rw [ha₃]; linarith) (by rw [hb₃, ha₃]; linarith) (by linarith) (by linarith)
    nlinarith [k1, ha₃0]
  -- the zero sums
  have hs₃ := summable_norm_lagWindowZeroTerm ha₃1.le hab₃
  have hs₄ := summable_norm_lagWindowZeroTerm ha₄1.le hab₄
  have hsd : Summable (fun q : XiZeroCopy => ‖lagWindowZeroTerm (q.1 : ℂ) a₃ b₃
      - lagWindowZeroTerm (q.1 : ℂ) a₄ x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _) (hs₃.add hs₄)
  have hdiff : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a₃ b₃).re
      - (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a₄ x).re
      ≤ ∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) a₃ b₃
          - lagWindowZeroTerm (q.1 : ℂ) a₄ x‖ := by
    rw [← Complex.sub_re, ← (Summable.of_norm hs₃).tsum_sub (Summable.of_norm hs₄)]
    have h1 := Complex.abs_re_le_norm (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) a₃ b₃
      - lagWindowZeroTerm (q.1 : ℂ) a₄ x))
    have h2 := norm_tsum_le_tsum_norm hsd
    have h3 := le_abs_self (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) a₃ b₃
      - lagWindowZeroTerm (q.1 : ℂ) a₄ x)).re
    linarith
  have hab : b₃ - a₄ = h + 2 * h' := by rw [hb₃, ha₄]; ring
  linarith

/-- **The per-zero majorant for the outer windows.** -/
theorem norm_outer_window_diff_le_zeroShortWeight {x h h' : ℝ} (hx : 4 ≤ x) (hh' : 0 < h')
    (hh'h : 2 * h' ≤ h) (hhx : h ≤ x / 2) (q : XiZeroCopy) :
    ‖lagWindowZeroTerm (q.1 : ℂ) (x + h) (x + h + h') - lagWindowZeroTerm (q.1 : ℂ) (x - h') x‖
      ≤ 8 * h * zeroShortWeight x (4 * x ^ 2 / (h * h')) (q.1 : ℂ) := by
  have hx0 : 0 < x := by linarith
  have hh : 0 < h := by linarith
  have hρ0 := xiZeroCopy_re_pos q
  have hρ1 := xiZeroCopy_re_lt_one q
  set β := ((q.1 : ℂ)).re with hβ
  set N := ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ with hN
  have hN0 : 0 < N := mul_pos (norm_pos_iff.mpr (xiZeroCopy_ne_zero q))
    (norm_pos_iff.mpr (xiZeroCopy_one_sub_ne_zero q))
  have hxβ : 0 ≤ x ^ (β - 1) := Real.rpow_nonneg hx0.le _
  -- `(x/2)^{β-1} ≤ 2 x^{β-1}`
  have hhalf : ∀ y : ℝ, x / 2 ≤ y → y ^ (β - 1) ≤ 2 * x ^ (β - 1) := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have h1 : y ^ (β - 1) ≤ (x / 2) ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hy (by linarith)
    have h2 : (x / 2) ^ (β - 1) = (1 / 2) ^ (β - 1) * x ^ (β - 1) := by
      rw [div_eq_mul_inv, mul_comm, Real.mul_rpow (by norm_num) hx0.le, one_div]
    have h3 : ((1 : ℝ) / 2) ^ (β - 1) ≤ 2 := by
      rw [show ((1 : ℝ) / 2) ^ (β - 1) = 2 ^ (1 - β) by
        rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]; ring_nf]
      calc (2 : ℝ) ^ (1 - β) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    rw [h2] at h1
    calc y ^ (β - 1) ≤ (1 / 2) ^ (β - 1) * x ^ (β - 1) := h1
      _ ≤ 2 * x ^ (β - 1) := mul_le_mul_of_nonneg_right h3 hxβ
  -- short range
  have hshort : ‖lagWindowZeroTerm (q.1 : ℂ) (x + h) (x + h + h')
      - lagWindowZeroTerm (q.1 : ℂ) (x - h') x‖ ≤ 8 * h * x ^ (β - 1) := by
    have h1 := norm_lagWindowZeroTerm_sub_le (x := x - h') (H := h + 2 * h') (by linarith)
      (by linarith) (by linarith) (by linarith) le_rfl (by linarith) (by linarith) hρ0 hρ1
      (a₁ := x + h) (b₁ := x + h + h') (a₂ := x - h') (b₂ := x)
    have h2 := hhalf (x - h') (by linarith)
    calc _ ≤ 2 * (h + 2 * h') * (x - h') ^ (β - 1) := h1
      _ ≤ 2 * (2 * h) * (2 * x ^ (β - 1)) := by
          apply mul_le_mul (by linarith) h2 (Real.rpow_nonneg (by linarith) _) (by positivity)
      _ = 8 * h * x ^ (β - 1) := by ring
  -- long range, one window at a time
  have hlong : ∀ a b : ℝ, x / 2 ≤ a → b - a = h' → b ≤ 2 * x →
      ‖lagWindowZeroTerm (q.1 : ℂ) a b‖ ≤ 16 * x ^ (β - 1) * x ^ 2 / (h' * N) := by
    intro a b hxa hba hb2
    have ha0 : 0 < a := by linarith
    have hab : a < b := by linarith
    have hb0 : 0 < b := by linarith
    have hpa := hhalf a hxa
    have hpb := hhalf b (by linarith)
    have hweq : 1 / a - 1 / b = h' / (a * b) := by
      rw [← hba]
      field_simp
    refine le_trans (norm_lagWindowZeroTerm_le ha0 hab _) ?_
    rw [← hβ, ← hN, hweq]
    have hab4 : a * b ≤ 4 * x ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsum : a ^ (β - 1) + b ^ (β - 1) ≤ 4 * x ^ (β - 1) := by linarith
    have e1 : (a ^ (β - 1) + b ^ (β - 1)) * (h' * N) ≤ 4 * x ^ (β - 1) * (h' * N) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    have e2 : 16 * x ^ (β - 1) * x ^ 2 * (N * (h' / (a * b)))
        = 4 * x ^ (β - 1) * (h' * N) * (4 * x ^ 2 / (a * b)) := by
      field_simp
      ring
    have e3 : 1 ≤ 4 * x ^ 2 / (a * b) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [e2]
    calc (a ^ (β - 1) + b ^ (β - 1)) * (h' * N) ≤ 4 * x ^ (β - 1) * (h' * N) := e1
      _ = 4 * x ^ (β - 1) * (h' * N) * 1 := by ring
      _ ≤ 4 * x ^ (β - 1) * (h' * N) * (4 * x ^ 2 / (a * b)) :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
  have h1 := hlong (x + h) (x + h + h') (by linarith) (by ring) (by linarith)
  have h2 := hlong (x - h') x (by linarith) (by ring) (by linarith)
  have hlong2 : ‖lagWindowZeroTerm (q.1 : ℂ) (x + h) (x + h + h')
      - lagWindowZeroTerm (q.1 : ℂ) (x - h') x‖ ≤ 32 * x ^ (β - 1) * x ^ 2 / (h' * N) := by
    refine le_trans (norm_sub_le _ _) ?_
    have : 32 * x ^ (β - 1) * x ^ 2 / (h' * N)
        = 16 * x ^ (β - 1) * x ^ 2 / (h' * N) + 16 * x ^ (β - 1) * x ^ 2 / (h' * N) := by ring
    rw [this]
    exact add_le_add h1 h2
  rw [zeroShortWeight, ← hβ, ← hN, ← mul_assoc, mul_min_of_nonneg _ _ (by positivity), mul_one]
  refine le_min hshort (le_of_le_of_eq hlong2 ?_)
  field_simp
  ring

/-- **The `ψ` window upper bound, weighted form.** -/
theorem psi_window_le_add_zeroShortWeight {x h h' : ℝ} (hx : 4 ≤ x) (hh' : 0 < h')
    (hh'h : 2 * h' ≤ h) (hhx : h ≤ x / 2) :
    Chebyshev.psi (x + h) - Chebyshev.psi x ≤
      h + 2 * h' + 4 / (x * h')
        + 8 * h * ∑' q : XiZeroCopy, zeroShortWeight x (4 * x ^ 2 / (h * h')) (q.1 : ℂ) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hh : 0 < h := by linarith
  have hY : (0 : ℝ) ≤ 4 * x ^ 2 / (h * h') := by positivity
  have hmain := psi_window_le_add_tsum hx hh' hh'h hhx
  have hs₃ := summable_norm_lagWindowZeroTerm (a := x + h) (b := x + h + h') (by linarith)
    (by linarith)
  have hs₄ := summable_norm_lagWindowZeroTerm (a := x - h') (b := x) (by linarith) (by linarith)
  have hsd : Summable (fun q : XiZeroCopy => ‖lagWindowZeroTerm (q.1 : ℂ) (x + h) (x + h + h')
      - lagWindowZeroTerm (q.1 : ℂ) (x - h') x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _) (hs₃.add hs₄)
  have hcmp : ∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) (x + h) (x + h + h')
      - lagWindowZeroTerm (q.1 : ℂ) (x - h') x‖
      ≤ 8 * h * ∑' q : XiZeroCopy, zeroShortWeight x (4 * x ^ 2 / (h * h')) (q.1 : ℂ) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum
      (fun q => norm_outer_window_diff_le_zeroShortWeight hx hh' hh'h hhx q)
      hsd ((summable_zeroShortWeight hx1 hY).mul_left _)
  linarith

end

end RHTower
