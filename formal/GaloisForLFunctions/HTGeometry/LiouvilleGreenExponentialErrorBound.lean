import GaloisForLFunctions.HTGeometry.GronwallBackward

/-!
# Olver's error bound for the exponential Liouville–Green approximation

On a barrier, where the normal form is `W'' = (u² + ψ)W`, the unperturbed pair is `e^{±uξ}` and the
recessive branch is the one that decays to the right.  Its Volterra equation must be anchored at the
*right* endpoint, because that is the direction in which the kernel is bounded: writing
`V(ξ) = e^{u(ξ-a)} W(ξ)` for the normalized recessive solution,

```text
V(ξ) = 1 + (1/u) ∫_ξ^b κ(ξ,t) ψ(t) V(t) dt ,     κ(ξ,t) = (1 − e^{−2u(t−ξ)})/2 ,
```

and `0 ≤ κ ≤ 1/2` for `ξ ≤ t`.  The unnormalized kernel `sinh(u(ξ−t))` is unbounded; the whole
content of the normalization is that `e^{u(ξ−t)} sinh(u(t−ξ))` is not.

Backward Grönwall then gives Olver's bound

```text
|V(ξ) − 1| ≤ exp( (1/2u) ∫_ξ^b |ψ| ) − 1 ,
```

the error-control function being the *mass* of the perturbation on the remaining interval, not a
pointwise bound times its length — which is what makes the estimate usable on long barriers.

This is the barrier counterpart of `LiouvilleGreenErrorBound`, whose kernel is `sin` and whose
anchor is the left endpoint.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

variable {a b u : ℝ} {V ψ : ℝ → ℝ}

/-- The normalized kernel of the exponential Volterra equation. -/
def expLGKernel (u ξ t : ℝ) : ℝ := (1 - Real.exp (-(2 * u * (t - ξ)))) / 2

theorem expLGKernel_le_half (u ξ t : ℝ) : expLGKernel u ξ t ≤ 1 / 2 := by
  have := (Real.exp_pos (-(2 * u * (t - ξ)))).le
  rw [expLGKernel]
  linarith

theorem expLGKernel_nonneg {u ξ t : ℝ} (hu : 0 ≤ u) (h : ξ ≤ t) :
    0 ≤ expLGKernel u ξ t := by
  have hexp : Real.exp (-(2 * u * (t - ξ))) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ 2 * u * (t - ξ) := by
      have : (0 : ℝ) ≤ t - ξ := by linarith
      positivity
    linarith
  rw [expLGKernel]
  linarith

theorem abs_expLGKernel_le_half {u ξ t : ℝ} (hu : 0 ≤ u) (h : ξ ≤ t) :
    |expLGKernel u ξ t| ≤ 1 / 2 :=
  abs_le.2 ⟨by linarith [expLGKernel_nonneg hu h], expLGKernel_le_half u ξ t⟩

theorem continuous_expLGKernel (u ξ : ℝ) : Continuous (expLGKernel u ξ) := by
  unfold expLGKernel
  fun_prop

/-- The Volterra form of the normalized recessive branch on a barrier. -/
def IsExponentialLGSolution (b u : ℝ) (ψ V : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ξ ∈ Icc a b, V ξ = 1 + (1 / u) * ∫ t in ξ..b, expLGKernel u ξ t * ψ t * V t

theorem integral_abs_psi_div_two (u a ξ : ℝ) :
    ∫ t in a..ξ, |ψ t| / (2 * u) = (1 / (2 * u)) * ∫ t in a..ξ, |ψ t| := by
  rw [intervalIntegral.integral_div, one_div, inv_mul_eq_div]

/-- The defect of the Volterra equation is bounded by the mass of the perturbation. -/
theorem volterra_defect_of_exponentialLG (hu : 0 < u)
    (hV : Continuous V) (hψ : Continuous ψ) (heq : IsExponentialLGSolution b u ψ V a)
    {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
    |V ξ - 1| ≤ ∫ t in ξ..b, (|ψ t| / (2 * u)) * |V t| := by
  have hξb : ξ ≤ b := hξ.2
  have hcontF : Continuous fun t : ℝ => expLGKernel u ξ t * ψ t * V t :=
    ((continuous_expLGKernel u ξ).mul hψ).mul hV
  have hcontG : Continuous fun t : ℝ => |ψ t| / (2 * u) * |V t| :=
    (hψ.abs.div_const (2 * u)).mul hV.abs
  have h1 : |∫ t in ξ..b, expLGKernel u ξ t * ψ t * V t|
      ≤ ∫ t in ξ..b, |expLGKernel u ξ t * ψ t * V t| :=
    intervalIntegral.abs_integral_le_integral_abs hξb
  have hpt : ∀ t ∈ Icc ξ b, |expLGKernel u ξ t * ψ t * V t| ≤ (1 / 2) * (|ψ t| * |V t|) := by
    intro t ht
    rw [abs_mul, abs_mul]
    have hk := abs_expLGKernel_le_half hu.le ht.1
    have hnn : (0 : ℝ) ≤ |ψ t| * |V t| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc |expLGKernel u ξ t| * |ψ t| * |V t|
        ≤ (1 / 2) * |ψ t| * |V t| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
      _ = (1 / 2) * (|ψ t| * |V t|) := by ring
  have h2 : (∫ t in ξ..b, |expLGKernel u ξ t * ψ t * V t|)
      ≤ ∫ t in ξ..b, (1 / 2) * (|ψ t| * |V t|) :=
    intervalIntegral.integral_mono_on hξb (hcontF.abs.intervalIntegrable ξ b)
      (((hψ.abs.mul hV.abs).const_mul (1 / 2 : ℝ)).intervalIntegrable ξ b) hpt
  have hdiv : (1 / u) * ∫ t in ξ..b, (1 / 2) * (|ψ t| * |V t|)
      = ∫ t in ξ..b, |ψ t| / (2 * u) * |V t| := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    field_simp
  have hupos : (0 : ℝ) < 1 / u := by positivity
  have hstep : |(1 / u) * ∫ t in ξ..b, expLGKernel u ξ t * ψ t * V t|
      ≤ ∫ t in ξ..b, |ψ t| / (2 * u) * |V t| := by
    rw [abs_mul, abs_of_pos hupos, ← hdiv]
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hupos.le
  have hVξ := heq ξ hξ
  have : V ξ - 1 = (1 / u) * ∫ t in ξ..b, expLGKernel u ξ t * ψ t * V t := by
    rw [hVξ]
    ring
  rw [this]
  exact hstep

/-- The Volterra equation gives the backward Grönwall hypothesis. -/
theorem volterra_bound_of_exponentialLG (hu : 0 < u)
    (hV : Continuous V) (hψ : Continuous ψ) (heq : IsExponentialLGSolution b u ψ V a) :
    ∀ ξ ∈ Icc a b, |V ξ| ≤ 1 + ∫ t in ξ..b, (|ψ t| / (2 * u)) * |V t| := by
  intro ξ hξ
  have hdef := volterra_defect_of_exponentialLG hu hV hψ heq hξ
  have := abs_sub_abs_le_abs_sub (V ξ) 1
  have habs1 : |(1 : ℝ)| = 1 := abs_one
  rw [habs1] at this
  linarith

/-- **Olver's exponential bound: the normalized recessive branch stays inside the error-control
exponential.** -/
theorem abs_le_exp_of_exponentialLG (hab : a ≤ b) (hu : 0 < u)
    (hV : Continuous V) (hψ : Continuous ψ) (heq : IsExponentialLGSolution b u ψ V a) :
    ∀ ξ ∈ Icc a b, |V ξ| ≤ Real.exp ((1 / (2 * u)) * ∫ t in ξ..b, |ψ t|) := by
  intro ξ hξ
  have hφ : Continuous fun t : ℝ => |ψ t| / (2 * u) := hψ.abs.div_const (2 * u)
  have hφ0 : ∀ t : ℝ, 0 ≤ |ψ t| / (2 * u) := fun t => by positivity
  have hmain := abs_le_exp_integral_of_volterra_bound_backward hab hV hφ hφ0
    (volterra_bound_of_exponentialLG hu hV hψ heq) ξ hξ
  rwa [integral_abs_psi_div_two (ψ := ψ) u ξ b] at hmain

/-- **Olver's exponential error bound: the deviation of the normalized recessive branch from one.**
-/
theorem abs_sub_one_le_exp_sub_one_of_exponentialLG (hab : a ≤ b) (hu : 0 < u)
    (hV : Continuous V) (hψ : Continuous ψ) (heq : IsExponentialLGSolution b u ψ V a) :
    ∀ ξ ∈ Icc a b, |V ξ - 1| ≤ Real.exp ((1 / (2 * u)) * ∫ t in ξ..b, |ψ t|) - 1 := by
  intro ξ hξ
  have hφ : Continuous fun t : ℝ => |ψ t| / (2 * u) := hψ.abs.div_const (2 * u)
  have hφ0 : ∀ t : ℝ, 0 ≤ |ψ t| / (2 * u) := fun t => by positivity
  have hmain := abs_sub_one_le_exp_sub_one_of_volterra_bound_backward hab hV hφ hφ0
    (volterra_bound_of_exponentialLG hu hV hψ heq)
    (fun η hη => volterra_defect_of_exponentialLG hu hV hψ heq hη) ξ hξ
  rwa [integral_abs_psi_div_two (ψ := ψ) u ξ b] at hmain

end GaloisForLFunctions.HTGeometry
