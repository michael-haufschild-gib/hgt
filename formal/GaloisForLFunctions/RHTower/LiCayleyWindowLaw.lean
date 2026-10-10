import GaloisForLFunctions.RHTower.LiSubexponentialCriterion
import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance

/-!
# The Li window law

By the Li growth law (`cayley_le_iff_xiLiPaired_lower`), a lower bound `Re(2λ_n) ≥ -C r'ⁿ` for
every `r' > r` says exactly that every zero has normalised Cayley modulus
`max(|1 - 1/ρ|, |1 - 1/ρ|⁻¹) ≤ r`. This module makes the condition geometric.

**Theorem** (`xiLiPaired_lower_iff_window`). For `r ≥ 1`, the rate-`r` Li bound holds iff every
zero `ρ = β + iγ` of `ξ` satisfies

`2β - 1 ≤ (r² - 1) |1 - ρ|²`.

Since `|1 - ρ|² ≥ γ²` and `2β - 1 < 1`, the condition is automatic once `(r² - 1)γ² ≥ 1`
(`window_of_one_le_mul_im_sq`). A rate-`r` Li bound is therefore the Riemann hypothesis in a lens
below the height `(r² - 1)^{-1/2}`, and nothing above it. Every fixed exponential rate sees only
finitely many zeros.

**Unconditional rate** (`exists_xiLiPaired_lower_of_432_div_431_lt`). Every off-line zero has
`γ² ≥ 431/2` (`xiZeroCopy_re_eq_half_of_im_sq_lt_fourHundredThirtyOne_halves`), so the window
holds at `r = 432/431`. Hence `Re(2λ_n) ≥ -C r'ⁿ` for every `r' > 432/431`.
-/

open Complex
noncomputable section
namespace RHTower

/-- `‖ρ - 1‖² - ‖ρ‖² = 1 - 2 Re ρ`. -/
theorem norm_sub_one_sq_eq (ρ : ℂ) : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 + (1 - 2 * ρ.re) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  ring

/-- **The Cayley bound as a lens.** For `r ≥ 0`, `max(‖w_ρ‖, ‖w_ρ‖⁻¹) ≤ r` iff
`1 - 2β ≤ (r² - 1)‖ρ‖²` and `2β - 1 ≤ (r² - 1)‖1 - ρ‖²`. -/
theorem norm_xiRootV_le_iff {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) {r : ℝ} (hr : 0 ≤ r) :
    ‖xiRootV ρ‖ ≤ r ↔
      1 - 2 * ρ.re ≤ (r ^ 2 - 1) * ‖ρ‖ ^ 2 ∧ 2 * ρ.re - 1 ≤ (r ^ 2 - 1) * ‖1 - ρ‖ ^ 2 := by
  have hp : 0 < ‖ρ‖ := norm_pos_iff.mpr h0
  have hq : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
  have hsq := norm_sub_one_sq_eq ρ
  have hrev : ‖1 - ρ‖ = ‖ρ - 1‖ := norm_sub_rev 1 ρ
  rw [norm_xiRootV h0 h1, max_le_iff, norm_xiRootW h0, inv_div,
    div_le_iff₀ hp, div_le_iff₀ hq, hrev]
  have e1 : ‖ρ - 1‖ ≤ r * ‖ρ‖ ↔ ‖ρ - 1‖ ^ 2 ≤ (r * ‖ρ‖) ^ 2 :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).symm
  have e2 : ‖ρ‖ ≤ r * ‖ρ - 1‖ ↔ ‖ρ‖ ^ 2 ≤ (r * ‖ρ - 1‖) ^ 2 :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).symm
  rw [e1, e2, mul_pow, mul_pow]
  constructor
  · rintro ⟨ha, hb⟩; constructor <;> nlinarith
  · rintro ⟨ha, hb⟩; constructor <;> nlinarith

/-- **The Cayley bound over all zeros is one inequality.** By the symmetry `ρ ↦ 1 - ρ`, every zero
has Cayley modulus at most `r` iff every zero has `2β - 1 ≤ (r² - 1)‖1 - ρ‖²`. -/
theorem cayley_le_iff_window {r : ℝ} (hr : 0 ≤ r) :
    (∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ r) ↔
      ∀ ρ : ℂ, xi ρ = 0 → 2 * ρ.re - 1 ≤ (r ^ 2 - 1) * ‖1 - ρ‖ ^ 2 := by
  have hne : ∀ ρ : ℂ, xi ρ = 0 → ρ ≠ 0 ∧ ρ ≠ 1 := fun ρ hρ =>
    ⟨liSupport_ne_zero ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩,
      liSupport_ne_one ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩⟩
  constructor
  · intro h ρ hρ
    exact ((norm_xiRootV_le_iff (hne ρ hρ).1 (hne ρ hρ).2 hr).mp (h ρ hρ)).2
  · intro h ρ hρ
    refine (norm_xiRootV_le_iff (hne ρ hρ).1 (hne ρ hρ).2 hr).mpr ⟨?_, h ρ hρ⟩
    have hρ' : xi (1 - ρ) = 0 := by rw [xi_one_sub]; exact hρ
    have := h (1 - ρ) hρ'
    rw [sub_sub_cancel, Complex.sub_re, Complex.one_re] at this
    linarith

/-- **The Li window law.** For `r ≥ 1`, the rate-`r` Li lower bound holds iff every zero
`ρ = β + iγ` of `ξ` has `2β - 1 ≤ (r² - 1)‖1 - ρ‖²`. -/
theorem xiLiPaired_lower_iff_window {r : ℝ} (hr : 1 ≤ r) :
    (∀ r' : ℝ, r < r' → ∃ C : ℝ, ∀ n : ℕ, -(C * r' ^ n) ≤ (xiLiPaired n).re) ↔
      ∀ ρ : ℂ, xi ρ = 0 → 2 * ρ.re - 1 ≤ (r ^ 2 - 1) * ‖1 - ρ‖ ^ 2 := by
  rw [← cayley_le_iff_xiLiPaired_lower hr, cayley_le_iff_window (by linarith)]

/-- **The horizon.** A zero with `(r² - 1)γ² ≥ 1` satisfies the rate-`r` window. -/
theorem window_of_one_le_mul_im_sq {r : ℝ} {ρ : ℂ} (hρ : xi ρ = 0)
    (hγ : 1 ≤ (r ^ 2 - 1) * ρ.im ^ 2) : 2 * ρ.re - 1 ≤ (r ^ 2 - 1) * ‖1 - ρ‖ ^ 2 := by
  have hstrip := xi_divisor_support_re_mem_open_unit ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩
  have hr : 0 ≤ r ^ 2 - 1 := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg ρ.im]
  have him : ρ.im ^ 2 ≤ ‖1 - ρ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
    nlinarith [sq_nonneg (1 - ρ.re)]
  have : (r ^ 2 - 1) * ρ.im ^ 2 ≤ (r ^ 2 - 1) * ‖1 - ρ‖ ^ 2 :=
    mul_le_mul_of_nonneg_left him hr
  simp only at hstrip
  linarith [hstrip.2]

/-- **The Li window law in horizon form.** For `r ≥ 1`, the rate-`r` Li bound holds iff the window
inequality holds for the zeros below the height `(r² - 1)^{-1/2}`. -/
theorem xiLiPaired_lower_iff_window_below_horizon {r : ℝ} (hr : 1 ≤ r) :
    (∀ r' : ℝ, r < r' → ∃ C : ℝ, ∀ n : ℕ, -(C * r' ^ n) ≤ (xiLiPaired n).re) ↔
      ∀ ρ : ℂ, xi ρ = 0 → (r ^ 2 - 1) * ρ.im ^ 2 < 1 →
        2 * ρ.re - 1 ≤ (r ^ 2 - 1) * ‖1 - ρ‖ ^ 2 := by
  rw [xiLiPaired_lower_iff_window hr]
  refine ⟨fun h ρ hρ _ => h ρ hρ, fun h ρ hρ => ?_⟩
  rcases lt_or_ge ((r ^ 2 - 1) * ρ.im ^ 2) 1 with hlt | hge
  · exact h ρ hρ hlt
  · exact window_of_one_le_mul_im_sq hρ hge

/-- Every off-line zero of `ξ` has `γ² ≥ 431/2`. -/
theorem im_sq_ge_of_xi_eq_zero_of_re_ne_half {ρ : ℂ} (hρ : xi ρ = 0) (hoff : ρ.re ≠ 1 / 2) :
    431 / 2 ≤ ρ.im ^ 2 := by
  set s : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩
  have hpos := xi_divisor_pos_on_support s
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (s : ℂ)) := by omega
  set q : XiZeroCopy := ⟨s, ⟨0, hn⟩⟩
  by_contra hlt
  push Not at hlt
  exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_fourHundredThirtyOne_halves q hlt)

/-- **An unconditional Li lower bound.** For every `r' > 432/431` there is `C` with
`Re(2λ_n) ≥ -C r'ⁿ` for all `n`. -/
theorem exists_xiLiPaired_lower_of_432_div_431_lt {r' : ℝ} (hr' : 432 / 431 < r') :
    ∃ C : ℝ, ∀ n : ℕ, -(C * r' ^ n) ≤ (xiLiPaired n).re := by
  refine (xiLiPaired_lower_iff_window (r := 432 / 431) (by norm_num)).mpr (fun ρ hρ => ?_) r' hr'
  by_cases hoff : ρ.re = 1 / 2
  · rw [hoff]
    have : (0 : ℝ) ≤ ((432 / 431 : ℝ) ^ 2 - 1) * ‖1 - ρ‖ ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    linarith
  · refine window_of_one_le_mul_im_sq hρ ?_
    have h := im_sq_ge_of_xi_eq_zero_of_re_ne_half hρ hoff
    nlinarith

end RHTower
