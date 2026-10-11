import Mathlib

/-!
# Finitely many nonnegative Taylor coefficients bound the modulus by the positive axis

If every Taylor coefficient of a holomorphic `g` at `0` is a nonnegative real number, then
`‖g z‖ ≤ g(‖z‖)` (Pringsheim's minimum-modulus mechanism, `ReciprocalPositivityMinimumModulus`).
This file proves the finite-order version.

**Theorem** (`norm_le_re_add_two_mul_tail_of_taylor_nonneg_lt`).  Let `g` be holomorphic on
`‖z‖ < d`, bounded by `M` on the circle `‖z‖ = ρ < d`, and let `0 ≤ r < ρ`.  If the Taylor
coefficients of order `< N` are nonnegative reals, then for `‖z‖ ≤ r`:

  `‖g z‖ ≤ Re g(r) + 2 M (r/ρ)^N / (1 − r/ρ)`.

The head of the Taylor series is dominated by its value on the positive axis.  Each tail is at
most `M (r/ρ)^N/(1 − r/ρ)` by Cauchy's estimate.  Contrapositive: a modulus at `z` exceeding the
positive-axis value by more than twice the tail forces a negative coefficient of order `< N`.
-/

open Complex Metric
open scoped ComplexOrder Nat

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Cauchy's estimate for the normalized Taylor coefficients. -/
theorem norm_taylorCoeff_le_of_sphere {g : ℂ → ℂ} {d ρ M : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 d)) (hρ : 0 < ρ) (hρd : ρ < d)
    (hM : ∀ z ∈ sphere (0 : ℂ) ρ, ‖g z‖ ≤ M) (n : ℕ) :
    ‖((n ! : ℂ))⁻¹ * iteratedDeriv n g 0‖ ≤ M / ρ ^ n := by
  have hdiff : DiffContOnCl ℂ g (ball 0 ρ) := by
    refine ⟨hg.mono (ball_subset_ball hρd.le), ?_⟩
    rw [closure_ball _ hρ.ne']
    exact (hg.mono (closedBall_subset_ball hρd)).continuousOn
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ hdiff hM
  have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc ((n ! : ℝ))⁻¹ * ‖iteratedDeriv n g 0‖ ≤ ((n ! : ℝ))⁻¹ * ((n ! : ℝ) * M / ρ ^ n) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hfac.le)
    _ = M / ρ ^ n := by field_simp

/-- **Finite-order positive-axis bound.** -/
theorem norm_le_re_add_two_mul_tail_of_taylor_nonneg_lt {g : ℂ → ℂ} {d ρ M r : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 d)) (hρ : 0 < ρ) (hρd : ρ < d)
    (hM : ∀ z ∈ sphere (0 : ℂ) ρ, ‖g z‖ ≤ M) (hr0 : 0 ≤ r) (hrρ : r < ρ) {N : ℕ}
    (hpos : ∀ n < N, 0 ≤ iteratedDeriv n g 0) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖g z‖ ≤ (g (r : ℂ)).re + 2 * (M * (r / ρ) ^ N / (1 - r / ρ)) := by
  set a : ℕ → ℂ := fun n => ((n ! : ℂ))⁻¹ * iteratedDeriv n g 0 with ha
  have hcoef : ∀ n, ‖a n‖ ≤ M / ρ ^ n := norm_taylorCoeff_le_of_sphere hg hρ hρd hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans ((hcoef 0).trans (by simp))
  set q : ℝ := r / ρ with hq
  have hq0 : 0 ≤ q := div_nonneg hr0 hρ.le
  have hq1 : q < 1 := (div_lt_one hρ).mpr hrρ
  -- the Taylor series at a point of norm at most `r`
  have hseries : ∀ w : ℂ, ‖w‖ ≤ r → HasSum (fun n => a n * w ^ n) (g w) := by
    intro w hw
    have hwmem : w ∈ ball (0 : ℂ) d := by
      rw [mem_ball, dist_zero_right]; linarith
    have h := Complex.hasSum_taylorSeries_on_ball hg hwmem
    simp only [sub_zero, smul_eq_mul] at h
    refine h.congr_fun fun n => ?_
    simp only [ha]
    ring
  -- the tail is small
  have htail : ∀ w : ℂ, ‖w‖ ≤ r →
      ‖g w - ∑ n ∈ Finset.range N, a n * w ^ n‖ ≤ M * q ^ N / (1 - q) := by
    intro w hw
    have h := (hasSum_nat_add_iff' N).mpr (hseries w hw)
    have hgeo : HasSum (fun n : ℕ => M * q ^ N * q ^ n) (M * q ^ N / (1 - q)) := by
      have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * q ^ N)
      simpa [div_eq_mul_inv] using this
    refine h.norm_le_of_bounded hgeo fun n => ?_
    rw [norm_mul, norm_pow]
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
    calc ‖a (n + N)‖ * ‖w‖ ^ (n + N) ≤ M / ρ ^ (n + N) * r ^ (n + N) :=
          mul_le_mul (hcoef _) (pow_le_pow_left₀ hw0 hw _) (by positivity)
            (div_nonneg hM0 (by positivity))
      _ = M * q ^ N * q ^ n := by
          rw [hq, div_pow, div_pow, pow_add, pow_add]
          field_simp
  -- the head at `z` is dominated by the head at `r`
  have hreal : ∀ n < N, a n = (((a n).re : ℝ) : ℂ) ∧ 0 ≤ (a n).re := by
    intro n hn
    have hD := hpos n hn
    have hfac : ((n ! : ℂ))⁻¹ = (((n ! : ℝ))⁻¹ : ℝ) := by push_cast; rfl
    have hnn : 0 ≤ a n := by
      simp only [ha, hfac]
      exact mul_nonneg (Complex.zero_le_real.mpr (by positivity)) hD
    exact ⟨Complex.ext (by simp) (by simp [(Complex.nonneg_iff.mp hnn).2.symm]),
      (Complex.nonneg_iff.mp hnn).1⟩
  have hhead : ‖∑ n ∈ Finset.range N, a n * z ^ n‖ ≤
      (∑ n ∈ Finset.range N, a n * (r : ℂ) ^ n).re := by
    rw [Complex.re_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    obtain ⟨he, hnn⟩ := hreal n (Finset.mem_range.mp hn)
    rw [norm_mul, norm_pow, ← Complex.ofReal_pow, Complex.re_mul_ofReal]
    have hlt : ‖a n‖ = (a n).re := by
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]; simp
    rw [hlt]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz n) hnn
  have hrnorm : ‖(r : ℂ)‖ ≤ r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have h1 := htail z hz
  have h2 := htail (r : ℂ) hrnorm
  have h3 : (∑ n ∈ Finset.range N, a n * (r : ℂ) ^ n).re ≤
      (g (r : ℂ)).re + ‖g (r : ℂ) - ∑ n ∈ Finset.range N, a n * (r : ℂ) ^ n‖ := by
    have := Complex.re_le_norm (∑ n ∈ Finset.range N, a n * (r : ℂ) ^ n - g (r : ℂ))
    rw [Complex.sub_re, norm_sub_rev] at this
    linarith
  calc ‖g z‖ = ‖(∑ n ∈ Finset.range N, a n * z ^ n) +
        (g z - ∑ n ∈ Finset.range N, a n * z ^ n)‖ := by rw [add_sub_cancel]
    _ ≤ ‖∑ n ∈ Finset.range N, a n * z ^ n‖ + ‖g z - ∑ n ∈ Finset.range N, a n * z ^ n‖ :=
        norm_add_le _ _
    _ ≤ (g (r : ℂ)).re + 2 * (M * q ^ N / (1 - q)) := by linarith

end

end GaloisForLFunctions.HTGeometry
