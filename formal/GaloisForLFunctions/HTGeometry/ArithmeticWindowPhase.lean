import Mathlib

/-!
# The arithmetic window: separation and oscillation

A nonzero algebraic integer whose conjugates are all bounded by `B` cannot be smaller than
`B^{-(m-1)}`: the product of all conjugates is a nonzero rational integer, so dividing it by the
`m-1` other conjugates bounds the one that is left.

A nonzero frequency oscillates away: the integral of `e^{itβ}` over any window has modulus at most
`2/|β|`, uniformly in the window position, because the antiderivative is bounded by `1/|β|`.

Together these turn a bounded integer spectral action into a uniform moving-window phase law.
-/

open intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-! ## The separation from a bounded conjugate family -/

section Separation

/-- **The Liouville separation.**  If a product of `m` reals has modulus at least one and all but
one factor are bounded by `B`, then the remaining factor is at least `B^{-(m-1)}`. -/
theorem abs_ge_of_abs_prod_ge_one {m : ℕ} (a : Fin m → ℝ) (i₀ : Fin m) {B : ℝ}
    (hprod : 1 ≤ |∏ i, a i|) (hbound : ∀ i, i ≠ i₀ → |a i| ≤ B) :
    B ^ (m - 1) * |a i₀| ≥ 1 := by
  classical
  have hsplit : |∏ i, a i| = |a i₀| * ∏ i ∈ Finset.univ.erase i₀, |a i| := by
    rw [Finset.abs_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  have hrest : ∏ i ∈ Finset.univ.erase i₀, |a i| ≤ B ^ (m - 1) := by
    have hcard : (Finset.univ.erase i₀).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
    calc ∏ i ∈ Finset.univ.erase i₀, |a i| ≤ ∏ _i ∈ Finset.univ.erase i₀, B := by
          refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi => ?_
          exact hbound i (Finset.ne_of_mem_erase hi)
      _ = B ^ (m - 1) := by rw [Finset.prod_const, hcard]
  have hnn : 0 ≤ |a i₀| := abs_nonneg _
  have hrestnn : 0 ≤ ∏ i ∈ Finset.univ.erase i₀, |a i| :=
    Finset.prod_nonneg fun i _ => abs_nonneg _
  calc (1 : ℝ) ≤ |∏ i, a i| := hprod
    _ = |a i₀| * ∏ i ∈ Finset.univ.erase i₀, |a i| := hsplit
    _ ≤ |a i₀| * B ^ (m - 1) := mul_le_mul_of_nonneg_left hrest hnn
    _ = B ^ (m - 1) * |a i₀| := by ring

/-- The separation in the displayed form `|β| ≥ B^{-(m-1)}`. -/
theorem inv_pow_le_abs {m : ℕ} (a : Fin m → ℝ) (i₀ : Fin m) {B : ℝ} (hB : 0 < B)
    (hprod : 1 ≤ |∏ i, a i|) (hbound : ∀ i, i ≠ i₀ → |a i| ≤ B) :
    (B ^ (m - 1))⁻¹ ≤ |a i₀| := by
  have h := abs_ge_of_abs_prod_ge_one a i₀ hprod hbound
  have hBpow : 0 < B ^ (m - 1) := by positivity
  rw [inv_le_iff_one_le_mul₀ hBpow]
  linarith [h]

end Separation

/-! ## The oscillation of a nonzero frequency -/

section Oscillation

/-- The antiderivative of a pure oscillation. -/
theorem hasDerivAt_expWindow {β : ℝ} (hβ : β ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (β : ℂ) * Complex.I) / ((β : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * (β : ℂ) * Complex.I)) t := by
  have hne : ((β : ℂ) * Complex.I) ≠ 0 := by
    have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
    exact mul_ne_zero hβC Complex.I_ne_zero
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * (β : ℂ)) (1 * (β : ℂ)) t := h1.mul_const _
  have h3 : HasDerivAt (fun s : ℝ => (s : ℂ) * (β : ℂ) * Complex.I)
      ((1 * (β : ℂ)) * Complex.I) t := h2.mul_const _
  rw [one_mul] at h3
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (β : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * (β : ℂ) * Complex.I) * ((β : ℂ) * Complex.I)) t := h3.cexp
  have hdiv := hexp.div_const ((β : ℂ) * Complex.I)
  have hval : (Complex.exp ((t : ℂ) * (β : ℂ) * Complex.I) * ((β : ℂ) * Complex.I))
      / ((β : ℂ) * Complex.I) = Complex.exp ((t : ℂ) * (β : ℂ) * Complex.I) := by
    field_simp
    have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
    field_simp
  rw [hval] at hdiv
  exact hdiv

/-- **The window oscillation bound.**  A nonzero frequency integrates to at most `2/|β|` over any
window, uniformly in its position. -/
theorem norm_integral_exp_window_le {β : ℝ} (hβ : β ≠ 0) (u T : ℝ) :
    ‖∫ t in u..(u + T), Complex.exp ((t : ℂ) * (β : ℂ) * Complex.I)‖ ≤ 2 / |β| := by
  have hne : ((β : ℂ) * Complex.I) ≠ 0 := by
    have hβC : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
    exact mul_ne_zero hβC Complex.I_ne_zero
  have hcont : Continuous fun t : ℝ => Complex.exp ((t : ℂ) * (β : ℂ) * Complex.I) := by
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => Complex.exp ((s : ℂ) * (β : ℂ) * Complex.I) / ((β : ℂ) * Complex.I))
    (f' := fun t : ℝ => Complex.exp ((t : ℂ) * (β : ℂ) * Complex.I))
    (fun t _ => hasDerivAt_expWindow hβ t)
    (hcont.intervalIntegrable u (u + T))
  rw [hint]
  have hnormExp : ∀ s : ℝ, ‖Complex.exp ((s : ℂ) * (β : ℂ) * Complex.I)‖ = 1 := by
    intro s
    rw [Complex.norm_exp]
    have hre : ((s : ℂ) * (β : ℂ) * Complex.I).re = 0 := by
      simp
    rw [hre, Real.exp_zero]
  have hnormDiv : ∀ s : ℝ,
      ‖Complex.exp ((s : ℂ) * (β : ℂ) * Complex.I) / ((β : ℂ) * Complex.I)‖ = 1 / |β| := by
    intro s
    rw [norm_div, hnormExp s, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  calc ‖Complex.exp (((u + T : ℝ) : ℂ) * (β : ℂ) * Complex.I) / ((β : ℂ) * Complex.I)
        - Complex.exp (((u : ℝ) : ℂ) * (β : ℂ) * Complex.I) / ((β : ℂ) * Complex.I)‖
      ≤ ‖Complex.exp (((u + T : ℝ) : ℂ) * (β : ℂ) * Complex.I) / ((β : ℂ) * Complex.I)‖
        + ‖Complex.exp (((u : ℝ) : ℂ) * (β : ℂ) * Complex.I) / ((β : ℂ) * Complex.I)‖ :=
        norm_sub_le _ _
    _ = 2 / |β| := by
        rw [hnormDiv, hnormDiv]
        ring

end Oscillation

end GaloisForLFunctions.HTGeometry
