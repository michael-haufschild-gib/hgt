import GaloisForLFunctions.RHTower.CosDilationShortSupportRigidity

/-!
# Blind cores of support ratio below `3/2` vanish, without a mean condition

Let `f` be continuous and supported in `[α, β]` with `0 < α ≤ β`, dilation autocorrelation
`A_f(r) = ∫_0^∞ f(y) f(ry) dy` and cosine–dilation kernel `Ψ_f = Cf ⋆ f`.  Poisson periodization
gives, for a kernel blind at every integer `|n| ≥ 2`,

`Σ_{k ∈ ℤ} A_f(|x + k|) = Ψ_f(0) + 2 Ψ_f(1) cos 2πx`   (`tsum_dilationAutocorr_abs_eq`).

**Theorem** (`eq_zero_of_cosDilationKernel_blind_of_lt_three_halves_mul`).  If `β < 3α/2` and
`Ψ_f(n) = 0` for every integer `n ≥ 2`, then `f = 0`.  No hypothesis on `Ψ_f(0)` (equivalently on
`∫ f`) is needed; `eq_zero_of_cosDilationKernel_blind_of_le_two_mul` assumes `Ψ_f(0) = 0`.

Proof.  `A_f` vanishes off `(α/β, β/α)`.  With `R = β/α < 3/2`, every point `x` of `[0, 1]` with
`x ≤ 1/R`, `1 − x ≤ 1/R`, `1 + x ≥ R` and `2 − x ≥ R` has `|x + k| ∉ (1/R, R)` for every `k`, so the
periodization vanishes there (`cosDilationKernel_zero_add_eq_zero_of_gap`).  Both `x = ½` and
`x₀ = (2R − 1)/4 ∈ [¼, ½)` are such gap points.  Hence `Ψ_f(0) − 2Ψ_f(1) = 0` and
`Ψ_f(0) + 2Ψ_f(1) cos 2πx₀ = 0` with `cos 2πx₀ > −1`, so `Ψ_f(1) = Ψ_f(0) = 0`, and the short-core
rigidity theorem applies.

For doubly blind cores (`A_f(n) = Ψ_f(n) = 0` for `n ≥ 2`, `RHTower.DoublyBlindCorePoleDistance`)
the dilation side is automatic when `β < 2α`.  So a nonzero doubly blind compact core has support
ratio at least `3/2`.
-/

open MeasureTheory Set Real

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-- At a gap point every term of the periodization vanishes, so the trigonometric side does. -/
theorem cosDilationKernel_zero_add_eq_zero_of_gap (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) {x : ℝ} (hx0 : 0 ≤ x)
    (h1 : x ≤ α / β) (h2 : 1 - x ≤ α / β) (h3 : β / α ≤ 1 + x) (h4 : β / α ≤ 2 - x) :
    cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) = 0 := by
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have h := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ x
  have hab : α / β ≤ 1 := (div_le_one (lt_of_lt_of_le hα hαβ)).mpr hαβ
  have hz : ∀ k : ℤ, dilationAutocorr f |x + k| = 0 := by
    intro k
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun hk => ?_
    rcases le_or_gt 1 k with hk1 | hk1
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      rw [abs_of_nonneg (by linarith)] at hk
      linarith [hk.2]
    rcases le_or_gt 0 k with hk0 | hk0
    · have : k = 0 := by omega
      subst this
      rw [Int.cast_zero, add_zero, abs_of_nonneg hx0] at hk
      linarith [hk.1]
    rcases le_or_gt (-1) k with hkm | hkm
    · have : k = -1 := by omega
      subst this
      rw [abs_of_nonpos (by push_cast; linarith)] at hk
      push_cast at hk
      linarith [hk.1]
    · have : (k : ℝ) ≤ -2 := by exact_mod_cast (by omega : k ≤ -2)
      rw [abs_of_neg (by linarith)] at hk
      linarith [hk.2]
  simp only [hz, Complex.ofReal_zero, tsum_zero] at h
  exact_mod_cast h.symm

/-- **Blind cores of support ratio below `3/2` vanish.** -/
theorem eq_zero_of_cosDilationKernel_blind_of_lt_three_halves_mul (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < 3 / 2 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) (y : ℝ) : f y = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  set R := β / α with hR
  have hR1 : 1 ≤ R := by rw [hR, le_div_iff₀ hα]; linarith
  have hR32 : R < 3 / 2 := by rw [hR, div_lt_iff₀ hα]; linarith
  have hinv : α / β = 1 / R := by rw [hR]; field_simp
  have hR0 : 0 < R := by linarith
  -- the gap point `x = ½`
  have e1 := cosDilationKernel_zero_add_eq_zero_of_gap hf hα hαβ hsupp hblind (x := 1 / 2)
    (by norm_num) (by rw [hinv, le_div_iff₀ hR0]; linarith)
    (by rw [hinv, le_div_iff₀ hR0]; linarith) (by linarith) (by linarith)
  -- the gap point `x₀ = (2R − 1)/4`
  set x₀ := (2 * R - 1) / 4 with hx₀
  have e2 := cosDilationKernel_zero_add_eq_zero_of_gap hf hα hαβ hsupp hblind (x := x₀)
    (by rw [hx₀]; linarith) (by rw [hinv, le_div_iff₀ hR0, hx₀]; nlinarith)
    (by rw [hinv, le_div_iff₀ hR0, hx₀]; nlinarith [sq_nonneg (R - 5 / 4)])
    (by rw [hx₀]; linarith) (by rw [hx₀]; linarith)
  have hcos1 : Real.cos (2 * π * (1 / 2)) = -1 := by
    rw [show 2 * π * (1 / 2) = π by ring, Real.cos_pi]
  have hcos2 : -1 < Real.cos (2 * π * x₀) := by
    rw [← Real.cos_pi]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · have : 0 ≤ x₀ := by rw [hx₀]; linarith
      positivity
    · exact le_rfl
    · have : x₀ < 1 / 2 := by rw [hx₀]; linarith
      nlinarith [Real.pi_pos]
  rw [hcos1] at e1
  have hΨ1 : cosDilationKernel f 1 = 0 := by
    have : 2 * cosDilationKernel f 1 * (Real.cos (2 * π * x₀) + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hΨ0 : cosDilationKernel f 0 = 0 := by rw [hΨ1] at e1; linarith
  exact eq_zero_of_cosDilationKernel_blind_of_le_two_mul hf hα hαβ (by linarith) hsupp hΨ0
    hblind y

end

end RHTower
