/-
Tier (T1) bricks (doc 53 §6): digamma workhorse identities.

The assembly consumes only derivative-level frame data (θ_RS′ = ½·Re
digamma(¼ + it/2) − ½·log π; phase differences are Gamma-free). This module
banks the identities that reduce vertical-line digamma bounds to explicit
finite sums:

* `digamma_apply_add_nat` — the iterated recursion digamma(z + N) =
  digamma(z) + Σ_{n<N} (z+n)⁻¹.
* `re_inv_shift` — the vertical summand in closed form:
  Re((σ + it + n)⁻¹) = (σ+n)/((σ+n)² + t²).
* `digamma_reflection` — digamma(z) − digamma(1−z) = −π·cos(πz)/sin(πz),
  by log-differentiating Γ(z)Γ(1−z) = π/sin(πz): ties the σ and 1−σ lines.

The remaining (T1) content is the asymptotic anchor on ONE vertical line
(integral-representation grade), named in doc 53 — after which the
misalignment supply of `birthKilled_of_perturbed_rotation` closes.
-/
import Mathlib

namespace RHTower

open Complex

/-- Iterated digamma recursion: vertical-line bounds reduce to explicit
finite sums. -/
theorem digamma_apply_add_nat (z : ℂ) (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) (N : ℕ) :
    digamma (z + N) = digamma z + ∑ n ∈ Finset.range N, (z + n)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hzN : ∀ m : ℕ, z + (N : ℂ) ≠ -(m : ℂ) := by
      intro m hc
      apply hz (m + N)
      push_cast
      linear_combination hc
    have hstep := Complex.digamma_apply_add_one (z + (N : ℂ)) hzN
    rw [show z + ((N + 1 : ℕ) : ℂ) = z + (N : ℂ) + 1 from by push_cast; ring,
      hstep, ih, Finset.sum_range_succ]
    ring

/-- The vertical summand in closed form. -/
theorem re_inv_shift (σ t : ℝ) (n : ℕ) :
    (((σ : ℂ) + (t : ℂ) * Complex.I + n)⁻¹).re
      = (σ + n) / ((σ + n) ^ 2 + t ^ 2) := by
  have hz : (σ : ℂ) + (t : ℂ) * Complex.I + n
      = ((σ + n : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hz, Complex.inv_re, Complex.normSq_add_mul_I]
  congr 1
  simp

/-- **Digamma reflection**: log-differentiating the banked
Γ(z)Γ(1−z) = π/sin(πz). -/
theorem digamma_reflection {z : ℂ} (hz : ∀ m : ℤ, z ≠ (m : ℂ)) :
    digamma z - digamma (1 - z)
      = -(Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z)
        / Complex.sin ((Real.pi : ℂ) * z) := by
  -- nonvanishing and differentiability inputs
  have hzn : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hc
    exact hz (-(m : ℤ)) (by push_cast at hc ⊢; exact hc)
  have h1zn : ∀ m : ℕ, 1 - z ≠ -(m : ℂ) := by
    intro m hc
    apply hz ((m : ℤ) + 1)
    push_cast
    linear_combination -hc
  have hΓz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzn
  have hΓ1z : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero h1zn
  have hdz : DifferentiableAt ℂ Complex.Gamma z :=
    Complex.differentiableAt_Gamma z hzn
  have hd1z : DifferentiableAt ℂ Complex.Gamma (1 - z) :=
    Complex.differentiableAt_Gamma (1 - z) h1zn
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hc
    apply hz k
    have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hswap : ((Real.pi : ℝ) : ℂ) * z = ((Real.pi : ℝ) : ℂ) * (k : ℂ) := by
      rw [hc]
      ring
    exact mul_left_cancel₀ hπ hswap
  -- left side: logDeriv of the product
  have hcompd : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 - w)) z := by
    have : (fun w : ℂ => Complex.Gamma (1 - w))
        = Complex.Gamma ∘ (fun w : ℂ => 1 - w) := rfl
    rw [this]
    exact hd1z.comp z ((differentiableAt_const _).sub differentiableAt_id)
  have hLHS : logDeriv (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w)) z
      = digamma z - digamma (1 - z) := by
    rw [logDeriv_mul z hΓz hΓ1z hdz hcompd]
    have hcomp : logDeriv (fun w : ℂ => Complex.Gamma (1 - w)) z
        = -digamma (1 - z) := by
      have hco : (fun w : ℂ => Complex.Gamma (1 - w))
          = Complex.Gamma ∘ (fun w : ℂ => 1 - w) := rfl
      rw [hco, logDeriv_comp hd1z ((differentiableAt_const _).sub
        differentiableAt_id)]
      have hderiv : deriv (fun w : ℂ => 1 - w) z = -1 := by
        rw [deriv_const_sub, deriv_id'']
      rw [hderiv, Complex.digamma_def]
      ring
    rw [hcomp, Complex.digamma_def]
    ring
  -- right side: logDeriv of π/sin(πw)
  have hsind : HasDerivAt (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w))
      ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z)) z := by
    have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) ((Real.pi : ℂ)) z := by
      simpa using (hasDerivAt_id z).const_mul (((Real.pi : ℝ) : ℂ))
    have h2 := (Complex.hasDerivAt_sin (((Real.pi : ℂ)) * z)).comp z h1
    have h3 : (Complex.sin ∘ fun w : ℂ => (Real.pi : ℂ) * w)
        = fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w) := rfl
    rw [h3] at h2
    exact h2.congr_deriv (mul_comm _ _)
  have hRHS : logDeriv (fun w : ℂ => (Real.pi : ℂ)
      / Complex.sin ((Real.pi : ℂ) * w)) z
      = -(Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z)
        / Complex.sin ((Real.pi : ℂ) * z) := by
    have hq : HasDerivAt (fun w : ℂ => (Real.pi : ℂ)
        / Complex.sin ((Real.pi : ℂ) * w))
        ((0 * Complex.sin ((Real.pi : ℂ) * z) - (Real.pi : ℂ)
          * ((Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z)))
          / (Complex.sin ((Real.pi : ℂ) * z)) ^ 2) z :=
      (hasDerivAt_const z ((Real.pi : ℂ))).div hsind hsin
    rw [logDeriv_apply, hq.deriv]
    field_simp
    ring
  -- glue via the reflection identity
  have hfun : (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w))
      = (fun w : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) := by
    funext w
    exact Complex.Gamma_mul_Gamma_one_sub w
  rw [← hLHS, hfun, hRHS]

end RHTower

namespace RHTower

/-- **Error-mass bound (T1-a input)**: the Poisson-tail sum is uniformly
bounded, Σ_{n<N} 1/((a+n)² + t²) ≤ 1/t² + π/(2t) — the arctan telescope. -/
theorem sum_inv_sq_add_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ((a + (n : ℝ)) ^ 2 + t ^ 2)
      ≤ 1 / t ^ 2 + Real.pi / (2 * t) := by
  have hpi := Real.pi_pos
  rcases N with _ | M
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  rw [Finset.sum_range_succ']
  have hterm0 : 1 / ((a + ((0 : ℕ) : ℝ)) ^ 2 + t ^ 2) ≤ 1 / t ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    nlinarith
  set F : ℝ → ℝ := fun x => 1 / t * Real.arctan (x / t) with hF
  have hFderiv : ∀ x : ℝ, HasDerivAt F (1 / (x ^ 2 + t ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y / t) (1 / t) x := by
      simpa using (hasDerivAt_id x).div_const t
    have h2 := (Real.hasDerivAt_arctan (x / t)).comp x h1
    have h3 := h2.const_mul (1 / t)
    have hfun :
        F = fun y : ℝ => 1 / t * (Real.arctan ∘ fun z : ℝ => z / t) y := by
      funext y
      simp only [hF, Function.comp_apply]
    have hcoef :
        1 / t * (1 / (1 + (x / t) ^ 2) * (1 / t)) = 1 / (x ^ 2 + t ^ 2) := by
      have ht2 : t ^ 2 > 0 := by positivity
      field_simp
      ring
    rw [hfun]
    exact h3.congr_deriv hcoef
  have hcont : ∀ (lo hi : ℝ), ContinuousOn (fun x : ℝ => 1 / (x ^ 2 + t ^ 2))
      (Set.uIcc lo hi) := by
    intro lo hi
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro x _
      positivity
  have hstep : ∀ n : ℕ, 1 / ((a + ((n : ℝ) + 1)) ^ 2 + t ^ 2)
      ≤ F ((n : ℝ) + 1) - F (n : ℝ) := by
    intro n
    have hFTC : F ((n : ℝ) + 1) - F (n : ℝ)
        = ∫ x in (n : ℝ)..((n : ℝ) + 1), 1 / (x ^ 2 + t ^ 2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hFderiv x)
        (ContinuousOn.intervalIntegrable (hcont _ _))]
    rw [hFTC]
    have hconst : 1 / ((a + ((n : ℝ) + 1)) ^ 2 + t ^ 2)
        = ∫ _x in (n : ℝ)..((n : ℝ) + 1),
            1 / ((a + ((n : ℝ) + 1)) ^ 2 + t ^ 2) := by
      rw [intervalIntegral.integral_const]
      simp
    rw [hconst]
    apply intervalIntegral.integral_mono_on (by linarith)
      intervalIntegrable_const
      (ContinuousOn.intervalIntegrable (hcont _ _))
    intro x hx
    apply one_div_le_one_div_of_le (by positivity)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rcases hx with ⟨hx1, hx2⟩
    nlinarith
  have hsum : ∑ n ∈ Finset.range M, 1 / ((a + (((n + 1 : ℕ)) : ℝ)) ^ 2 + t ^ 2)
      ≤ ∑ n ∈ Finset.range M,
          ((fun k : ℕ => F (k : ℝ)) (n + 1) - (fun k : ℕ => F (k : ℝ)) n) := by
    apply Finset.sum_le_sum
    intro n _
    have := hstep n
    push_cast
    exact this
  have htel : ∑ n ∈ Finset.range M,
      ((fun k : ℕ => F (k : ℝ)) (n + 1) - (fun k : ℕ => F (k : ℝ)) n)
      = F (M : ℝ) - F 0 := by
    rw [Finset.sum_range_sub (fun k : ℕ => F (k : ℝ))]
    norm_num
  have hF0 : F 0 = 0 := by
    simp [hF]
  have hFM : F (M : ℝ) ≤ 1 / t * (Real.pi / 2) := by
    apply mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two _).le
    positivity
  have hfin : 1 / t * (Real.pi / 2) = Real.pi / (2 * t) := by
    field_simp
  calc (∑ n ∈ Finset.range M, 1 / ((a + (((n + 1 : ℕ)) : ℝ)) ^ 2 + t ^ 2))
        + 1 / ((a + ((0 : ℕ) : ℝ)) ^ 2 + t ^ 2)
      ≤ (F (M : ℝ) - F 0) + 1 / t ^ 2 := by
        rw [← htel]
        exact add_le_add hsum hterm0
    _ ≤ 1 / t ^ 2 + Real.pi / (2 * t) := by
        rw [hF0]
        linarith [hFM, hfin.le]

end RHTower

namespace RHTower

/-- Pointwise kernel comparison: for 0 ≤ u ≤ x ≤ u+1 the Poisson-Re kernel
moves by at most 1/(u²+t²) — fully algebraic via
(u²+t²)(x²+t²) = (ux+t²)² + t²(x−u)². -/
theorem re_kernel_move_le {u x t : ℝ} (ht : 0 < t) (hu0 : 0 ≤ u)
    (hux : u ≤ x) (hx1 : x ≤ u + 1) :
    |u / (u ^ 2 + t ^ 2) - x / (x ^ 2 + t ^ 2)| ≤ 1 / (u ^ 2 + t ^ 2) := by
  have hDu : (0 : ℝ) < u ^ 2 + t ^ 2 := by positivity
  have hDx : (0 : ℝ) < x ^ 2 + t ^ 2 := by positivity
  have hx0 : 0 ≤ x := le_trans hu0 hux
  have hux0 : 0 ≤ u * x := mul_nonneg hu0 hx0
  have hnum : u / (u ^ 2 + t ^ 2) - x / (x ^ 2 + t ^ 2)
      = (x - u) * (u * x - t ^ 2) / ((u ^ 2 + t ^ 2) * (x ^ 2 + t ^ 2)) := by
    field_simp
    ring
  rw [hnum, abs_div,
    abs_of_pos (by positivity : (0:ℝ) < (u ^ 2 + t ^ 2) * (x ^ 2 + t ^ 2))]
  have hnumle : |(x - u) * (u * x - t ^ 2)| ≤ x ^ 2 + t ^ 2 := by
    calc |(x - u) * (u * x - t ^ 2)| = |x - u| * |u * x - t ^ 2| := abs_mul _ _
      _ ≤ 1 * (x ^ 2 + t ^ 2) := by
          apply mul_le_mul
          · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - u)]
            linarith
          · rw [abs_le]
            constructor <;> nlinarith
          · exact abs_nonneg _
          · positivity
      _ = x ^ 2 + t ^ 2 := one_mul _
  calc |(x - u) * (u * x - t ^ 2)| / ((u ^ 2 + t ^ 2) * (x ^ 2 + t ^ 2))
      ≤ (x ^ 2 + t ^ 2) / ((u ^ 2 + t ^ 2) * (x ^ 2 + t ^ 2)) := by gcongr
    _ = 1 / (u ^ 2 + t ^ 2) := by
        rw [show x ^ 2 + t ^ 2 = (x ^ 2 + t ^ 2) * 1 from (mul_one _).symm,
          mul_comm (u ^ 2 + t ^ 2) ((x ^ 2 + t ^ 2) * 1)]
        rw [show (x ^ 2 + t ^ 2) * 1 * (u ^ 2 + t ^ 2)
            = (x ^ 2 + t ^ 2) * ((u ^ 2 + t ^ 2)) from by ring]
        exact mul_div_mul_left 1 _ hDx.ne'

/-- **(T1-a) The vertical log comparison**: the Re-digamma finite sums track
½·log((x²+t²)-growth) with total error ≤ 1/t² + π/(2t), uniformly in N. -/
theorem vertical_sum_log_comparison {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (N : ℕ) :
    |(∑ n ∈ Finset.range N, (σ + (n : ℝ)) / ((σ + (n : ℝ)) ^ 2 + t ^ 2))
      - (1 / 2 * Real.log ((σ + (N : ℝ)) ^ 2 + t ^ 2)
         - 1 / 2 * Real.log (σ ^ 2 + t ^ 2))|
      ≤ 1 / t ^ 2 + Real.pi / (2 * t) := by
  set f : ℝ → ℝ := fun x => 1 / 2 * Real.log (x ^ 2 + t ^ 2) with hf
  have hfd : ∀ x : ℝ, HasDerivAt f (x / (x ^ 2 + t ^ 2)) x := by
    intro x
    have hpos : (0 : ℝ) < x ^ 2 + t ^ 2 := by positivity
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + t ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (t ^ 2)
    have h2 := (Real.hasDerivAt_log hpos.ne').comp x h1
    have h3 := h2.const_mul (1 / 2 : ℝ)
    have hfun :
        f = fun y : ℝ => 1 / 2 * (Real.log ∘ fun z : ℝ => z ^ 2 + t ^ 2) y := by
      funext y
      simp only [hf, Function.comp_apply]
    have hcoef :
        (1 / 2 : ℝ) * ((x ^ 2 + t ^ 2)⁻¹ * (2 * x)) = x / (x ^ 2 + t ^ 2) := by
      field_simp
    rw [hfun]
    exact h3.congr_deriv hcoef
  have hcontd : ∀ (lo hi : ℝ),
      ContinuousOn (fun x : ℝ => x / (x ^ 2 + t ^ 2)) (Set.uIcc lo hi) := by
    intro lo hi
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x _
    positivity
  have herr : ∀ n : ℕ, |(σ + (n : ℝ)) / ((σ + (n : ℝ)) ^ 2 + t ^ 2)
      - (f (σ + (n : ℝ) + 1) - f (σ + (n : ℝ)))|
      ≤ 1 / ((σ + (n : ℝ)) ^ 2 + t ^ 2) := by
    intro n
    set u : ℝ := σ + (n : ℝ) with hu
    have hu0 : 0 ≤ u := by
      have hn := Nat.cast_nonneg (α := ℝ) n
      simp only [hu]
      linarith
    have hFTC : f (u + 1) - f u
        = ∫ x in u..(u + 1), x / (x ^ 2 + t ^ 2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hfd x)
        (ContinuousOn.intervalIntegrable (hcontd _ _))]
    have hconst : u / (u ^ 2 + t ^ 2)
        = ∫ _x in u..(u + 1), u / (u ^ 2 + t ^ 2) := by
      rw [intervalIntegral.integral_const]
      simp
    rw [hFTC, hconst, ← intervalIntegral.integral_sub
      intervalIntegrable_const
      (ContinuousOn.intervalIntegrable (hcontd _ _))]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1 / (u ^ 2 + t ^ 2))
      (f := fun x => u / (u ^ 2 + t ^ 2) - x / (x ^ 2 + t ^ 2))
      (a := u) (b := u + 1) ?_
    · calc |∫ x in u..(u + 1), (u / (u ^ 2 + t ^ 2) - x / (x ^ 2 + t ^ 2))|
          ≤ 1 / (u ^ 2 + t ^ 2) * |u + 1 - u| := hbound
        _ = 1 / (u ^ 2 + t ^ 2) := by
            norm_num
    · intro x hx
      rw [Set.uIoc_of_le (by linarith : u ≤ u + 1)] at hx
      rw [Real.norm_eq_abs]
      exact re_kernel_move_le ht hu0 hx.1.le hx.2
  have htel : ∑ n ∈ Finset.range N, (f (σ + (n : ℝ) + 1) - f (σ + (n : ℝ)))
      = f (σ + (N : ℝ)) - f σ := by
    calc ∑ n ∈ Finset.range N, (f (σ + (n : ℝ) + 1) - f (σ + (n : ℝ)))
        = ∑ n ∈ Finset.range N, ((fun k : ℕ => f (σ + (k : ℝ))) (n + 1)
            - (fun k : ℕ => f (σ + (k : ℝ))) n) := by
          apply Finset.sum_congr rfl
          intro n _
          simp only []
          congr 2
          push_cast
          ring
      _ = f (σ + (N : ℝ)) - f (σ + ((0 : ℕ) : ℝ)) :=
          Finset.sum_range_sub (fun k : ℕ => f (σ + (k : ℝ))) N
      _ = f (σ + (N : ℝ)) - f σ := by norm_num
  have hsplit : (∑ n ∈ Finset.range N,
        (σ + (n : ℝ)) / ((σ + (n : ℝ)) ^ 2 + t ^ 2))
      - (f (σ + (N : ℝ)) - f σ)
      = ∑ n ∈ Finset.range N, ((σ + (n : ℝ)) / ((σ + (n : ℝ)) ^ 2 + t ^ 2)
          - (f (σ + (n : ℝ) + 1) - f (σ + (n : ℝ)))) := by
    rw [Finset.sum_sub_distrib, htel]
  have hgoal : (1 / 2 * Real.log ((σ + (N : ℝ)) ^ 2 + t ^ 2)
      - 1 / 2 * Real.log (σ ^ 2 + t ^ 2)) = f (σ + (N : ℝ)) - f σ := by
    simp only [hf]
  rw [hgoal, hsplit]
  calc |∑ n ∈ Finset.range N, ((σ + (n : ℝ)) / ((σ + (n : ℝ)) ^ 2 + t ^ 2)
        - (f (σ + (n : ℝ) + 1) - f (σ + (n : ℝ))))|
      ≤ ∑ n ∈ Finset.range N, |(σ + (n : ℝ)) / ((σ + (n : ℝ)) ^ 2 + t ^ 2)
        - (f (σ + (n : ℝ) + 1) - f (σ + (n : ℝ)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, 1 / ((σ + (n : ℝ)) ^ 2 + t ^ 2) :=
        Finset.sum_le_sum fun n _ => herr n
    _ ≤ 1 / t ^ 2 + Real.pi / (2 * t) := sum_inv_sq_add_le hσ ht N

/-- **(T1) The vertical-line anchor identity.** Combining the digamma recursion
`digamma_apply_add_nat`, the summand `re_inv_shift`, and the log comparison
`vertical_sum_log_comparison`: for every `N` the real part of digamma on the vertical
line equals `½·log(σ²+t²)` up to a `far-field anchor` term
`Re digamma(σ+N+it) − ½·log((σ+N)²+t²)`, with the difference controlled by the same
`1/t² + π/(2t)` error. The two `½·log((σ+N)²+t²)` terms cancel between the recursion and
the comparison — the anchor is all that survives, and it vanishes as `N → ∞`
(the digamma asymptotic, the one input off the `dip_kills` critical path, doc 54 §6). -/
theorem re_digamma_vertical_anchor {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) (N : ℕ) :
    |(Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        - (1 / 2) * Real.log (σ ^ 2 + t ^ 2)
      - ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I + N)).re
          - (1 / 2) * Real.log ((σ + N) ^ 2 + t ^ 2))|
      ≤ 1 / t ^ 2 + Real.pi / (2 * t) := by
  have hz : ∀ m : ℕ, (σ : ℂ) + (t : ℂ) * Complex.I ≠ -(m : ℂ) := by
    intro m hc
    have him := congrArg Complex.im hc
    simp at him
    linarith
  have hrec := digamma_apply_add_nat ((σ : ℂ) + (t : ℂ) * Complex.I) hz N
  have hre : (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I + N)).re
      = (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        + ∑ n ∈ Finset.range N, (σ + (n : ℝ)) / ((σ + (n : ℝ)) ^ 2 + t ^ 2) := by
    rw [hrec, Complex.add_re, Complex.re_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact re_inv_shift σ t n
  have hcomp := vertical_sum_log_comparison hσ ht N
  rw [hre]
  have halg : (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        - (1 / 2) * Real.log (σ ^ 2 + t ^ 2)
      - ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re
          + ∑ n ∈ Finset.range N, (σ + (n : ℝ)) / ((σ + (n : ℝ)) ^ 2 + t ^ 2)
          - (1 / 2) * Real.log ((σ + N) ^ 2 + t ^ 2))
      = -((∑ n ∈ Finset.range N, (σ + (n : ℝ)) / ((σ + (n : ℝ)) ^ 2 + t ^ 2))
          - ((1 / 2) * Real.log ((σ + (N : ℝ)) ^ 2 + t ^ 2)
             - (1 / 2) * Real.log (σ ^ 2 + t ^ 2))) := by ring
  rw [halg, abs_neg]
  exact hcomp

/-- **(T1) The vertical-line bound.** With the far-field anchor supplied as the explicit
asymptotic hypothesis `hanchor` (`Re digamma(σ+N+it) − ½·log((σ+N)²+t²) → 0`, the
integral-representation-grade digamma input named in doc 53), the anchor identity's
`N → ∞` limit gives the clean two-sided bound
`|Re digamma(σ+it) − ½·log(σ²+t²)| ≤ 1/t² + π/(2t)`. -/
theorem re_digamma_vertical_bound {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (hanchor : Filter.Tendsto
      (fun N : ℕ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I + N)).re
          - (1 / 2) * Real.log ((σ + N) ^ 2 + t ^ 2)) Filter.atTop (nhds 0)) :
    |(Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        - (1 / 2) * Real.log (σ ^ 2 + t ^ 2)|
      ≤ 1 / t ^ 2 + Real.pi / (2 * t) := by
  have key := Filter.Tendsto.sub
    (tendsto_const_nhds (x := (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      - (1 / 2) * Real.log (σ ^ 2 + t ^ 2)) (f := Filter.atTop (α := ℕ))) hanchor
  rw [sub_zero] at key
  refine le_of_tendsto key.abs (Filter.Eventually.of_forall (fun N => ?_))
  exact re_digamma_vertical_anchor hσ ht N

end RHTower
