import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonOperator

/-!
# The Poisson sum is smooth along the multiplicative flow

In the logarithmic coordinate the Poisson sum is `G_f(t) = ∑_{n≥1} f(n e^t)`.  On every half line
`t > T` the terms and their derivatives are bounded by a summable sequence — the Schwartz decay of
order two applied at the point `n e^T` — so the series may be differentiated term by term.  The
derivative of the `n`-th term is the Euler operator evaluated at the same point, so

`G_f' = G_{θf}`.

Iterating, `G_f` is smooth and its `k`-th derivative is `G_{θᵏf}`.  Since Meyer's space is stable
under the Euler operator, every derivative of the Poisson sum of a member is again the Poisson sum
of a member, and therefore inherits the two-ended decay.

* `deningerPoissonLog` : the Poisson sum in the logarithmic coordinate.
* `hasDerivAt_deningerPoissonLog` : **`G_f' = G_{θf}`.**
* `contDiff_deningerPoissonLog` : **the Poisson sum is smooth.**
* `iteratedDeriv_deningerPoissonLog` : **`G_f^{(k)} = G_{θᵏf}`.**
-/

open scoped Real SchwartzMap FourierTransform ContDiff
open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## The Poisson sum in the logarithmic coordinate -/

/-- **The Poisson sum in the logarithmic coordinate**, `G_f(t) = ∑_{n≥1} f(n e^t)`. -/
def deningerPoissonLog (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ := ∑' n : ℕ, f (((n : ℝ) + 1) * Real.exp t)

theorem deningerPoissonLog_eq (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    deningerPoissonLog f t = deningerPoissonValue f (Real.exp t) := by
  rw [deningerPoissonLog, deningerPoissonValue]
  refine tsum_congr fun n => ?_
  rw [mul_comm]

theorem summable_deningerPoissonLogTerm (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Summable fun n : ℕ => f (((n : ℝ) + 1) * Real.exp t) := by
  have h := summable_deningerPoissonTerm f (Real.exp_ne_zero t)
  refine h.congr fun n => ?_
  rw [mul_comm]

/-! ## The uniform bound on a half line -/

theorem norm_deningerPoissonLogTerm_le (f : 𝓢(ℝ, ℂ)) (T : ℝ) {y : ℝ} (hy : T < y) (n : ℕ) :
    ‖f (((n : ℝ) + 1) * Real.exp y)‖
      ≤ SchwartzMap.seminorm ℂ 2 0 f / (((n : ℝ) + 1) * Real.exp T) ^ (2 : ℕ) := by
  set S : ℝ := SchwartzMap.seminorm ℂ 2 0 f with hS
  have hSnn : 0 ≤ S := apply_nonneg _ _
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * Real.exp T := by positivity
  have hposy : (0 : ℝ) < ((n : ℝ) + 1) * Real.exp y := by positivity
  have hle : ((n : ℝ) + 1) * Real.exp T ≤ ((n : ℝ) + 1) * Real.exp y := by
    have hexp : Real.exp T ≤ Real.exp y := Real.exp_le_exp.mpr hy.le
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2 (((n : ℝ) + 1) * Real.exp y)
  have hnorm : ‖((n : ℝ) + 1) * Real.exp y‖ = ((n : ℝ) + 1) * Real.exp y := by
    rw [Real.norm_eq_abs, abs_of_pos hposy]
  rw [hnorm] at hsem
  have hstep : ‖f (((n : ℝ) + 1) * Real.exp y)‖
      ≤ S / (((n : ℝ) + 1) * Real.exp y) ^ (2 : ℕ) := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖f (((n : ℝ) + 1) * Real.exp y)‖ * (((n : ℝ) + 1) * Real.exp y) ^ (2 : ℕ)
        = (((n : ℝ) + 1) * Real.exp y) ^ (2 : ℕ) * ‖f (((n : ℝ) + 1) * Real.exp y)‖ := by ring
      _ ≤ S := hsem
  refine hstep.trans ?_
  refine div_le_div_of_nonneg_left hSnn (by positivity) ?_
  exact pow_le_pow_left₀ hpos.le hle 2

theorem summable_deningerPoissonBound (f : 𝓢(ℝ, ℂ)) (T : ℝ) :
    Summable fun n : ℕ =>
      SchwartzMap.seminorm ℂ 2 0 f / (((n : ℝ) + 1) * Real.exp T) ^ (2 : ℕ) := by
  have h1 : Summable fun n : ℕ => 1 / ((n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have h2 : Summable fun n : ℕ => 1 / ((((n + 1 : ℕ)) : ℝ) ^ (2 : ℕ)) := (summable_nat_add_iff 1).mpr h1
  have hfun : (fun n : ℕ =>
      SchwartzMap.seminorm ℂ 2 0 f / (((n : ℝ) + 1) * Real.exp T) ^ (2 : ℕ))
      = fun n : ℕ => (SchwartzMap.seminorm ℂ 2 0 f / (Real.exp T) ^ (2 : ℕ))
        * (1 / ((((n + 1 : ℕ)) : ℝ) ^ (2 : ℕ))) := by
    funext n
    have hexp : (Real.exp T) ≠ 0 := Real.exp_ne_zero T
    push_cast
    field_simp
  rw [hfun]
  exact h2.mul_left _

/-! ## Term-by-term differentiation -/

/-- **The Poisson sum differentiates to the Poisson sum of the Euler transform.** -/
theorem hasDerivAt_deningerPoissonLog (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (deningerPoissonLog f) (deningerPoissonLog (eulerSCLM f) t) t := by
  set T : ℝ := t - 1 with hT
  have hopen : IsOpen (Set.Ioi T) := isOpen_Ioi
  have hconn : IsPreconnected (Set.Ioi T) := (convex_Ioi T).isPreconnected
  have ht : t ∈ Set.Ioi T := by
    rw [hT]
    exact Set.mem_Ioi.mpr (by linarith)
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioi T →
      HasDerivAt (fun z : ℝ => f (((n : ℝ) + 1) * Real.exp z))
        (eulerSCLM f (((n : ℝ) + 1) * Real.exp y)) y := fun n y _ =>
    hasDerivAt_comp_exp f ((n : ℝ) + 1) y
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioi T →
      ‖eulerSCLM f (((n : ℝ) + 1) * Real.exp y)‖
        ≤ SchwartzMap.seminorm ℂ 2 0 (eulerSCLM f) / (((n : ℝ) + 1) * Real.exp T) ^ (2 : ℕ) :=
    fun n y hy => norm_deningerPoissonLogTerm_le (eulerSCLM f) T (Set.mem_Ioi.mp hy) n
  have hsum0 : Summable fun n : ℕ => f (((n : ℝ) + 1) * Real.exp t) :=
    summable_deningerPoissonLogTerm f t
  exact hasDerivAt_tsum_of_isPreconnected (summable_deningerPoissonBound (eulerSCLM f) T)
    hopen hconn hderiv hbound ht hsum0 ht

theorem differentiable_deningerPoissonLog (f : 𝓢(ℝ, ℂ)) :
    Differentiable ℝ (deningerPoissonLog f) := fun t =>
  (hasDerivAt_deningerPoissonLog f t).differentiableAt

theorem deriv_deningerPoissonLog (f : 𝓢(ℝ, ℂ)) :
    deriv (deningerPoissonLog f) = deningerPoissonLog (eulerSCLM f) := by
  funext t
  exact (hasDerivAt_deningerPoissonLog f t).deriv

/-! ## Smoothness -/

theorem contDiff_nat_deningerPoissonLog (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ n (deningerPoissonLog f) := by
  induction n generalizing f with
  | zero =>
    have h : ContDiff ℝ 0 (deningerPoissonLog f) :=
      contDiff_zero.mpr (differentiable_deningerPoissonLog f).continuous
    simpa using h
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
      push_cast
      ring
    rw [hcast]
    refine contDiff_succ_iff_deriv.mpr ⟨differentiable_deningerPoissonLog f, ?_, ?_⟩
    · intro hω
      exact absurd hω (by simp)
    · rw [deriv_deningerPoissonLog]
      exact ih (eulerSCLM f)

/-- **The Poisson sum is smooth in the logarithmic coordinate.** -/
theorem contDiff_deningerPoissonLog (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (deningerPoissonLog f) :=
  contDiff_infty.mpr fun n => contDiff_nat_deningerPoissonLog n f

/-- **Every derivative of the Poisson sum is the Poisson sum of an Euler iterate.** -/
theorem iteratedDeriv_deningerPoissonLog (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    iteratedDeriv k (deningerPoissonLog f) = deningerPoissonLog ((eulerSCLM^[k]) f) := by
  induction k generalizing f with
  | zero =>
    rw [iteratedDeriv_zero, Function.iterate_zero_apply]
  | succ k ih =>
    rw [iteratedDeriv_succ', deriv_deningerPoissonLog, ih (eulerSCLM f),
      Function.iterate_succ_apply]

end RHTower

end
