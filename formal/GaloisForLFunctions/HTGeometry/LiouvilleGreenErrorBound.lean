import GaloisForLFunctions.HTGeometry.GronwallVariableCoefficient

/-!
# Olver's error bound for the oscillatory Liouville--Green approximation

A solution of `W'' + (u² + ψ) W = 0` with the initial data of `cos(u(ξ − a))` satisfies, by
variation of constants against the unperturbed pair `cos(uξ), sin(uξ)`, the Volterra equation

```text
W(ξ) = cos(u(ξ − a)) − (1/u) ∫_a^ξ sin(u(ξ − t)) ψ(t) W(t) dt .
```

Because the kernel is bounded by `1/u` uniformly in both variables, the variable-coefficient
Grönwall inequality turns that equation into Olver's error bound: the solution differs from the
unperturbed cosine by at most `exp(V/u) − 1`, where `V = ∫|ψ|` is the total mass of the perturbation
— the *error-control function*.  The bound involves the mass of `ψ`, not a bound on `ψ` times the
length of the interval, which is what makes it usable on long and on unbounded intervals.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

variable {a b u : ℝ} {W ψ : ℝ → ℝ}

/-- The Volterra form of the perturbed oscillator. -/
def IsOscillatoryLGSolution (a u : ℝ) (ψ W : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ξ ∈ Icc a b, W ξ
    = Real.cos (u * (ξ - a)) - (1 / u) * ∫ t in a..ξ, Real.sin (u * (ξ - t)) * ψ t * W t

theorem integral_abs_psi_div (a ξ : ℝ) :
    ∫ t in a..ξ, |ψ t| / u = (1 / u) * ∫ t in a..ξ, |ψ t| := by
  rw [intervalIntegral.integral_div, one_div, inv_mul_eq_div]

/-- The Volterra equation gives the Grönwall hypothesis. -/
theorem volterra_bound_of_oscillatoryLG (hu : 0 < u)
    (hW : Continuous W) (hψ : Continuous ψ) (heq : IsOscillatoryLGSolution a u ψ W b) :
    ∀ ξ ∈ Icc a b, |W ξ| ≤ 1 + ∫ t in a..ξ, (|ψ t| / u) * |W t| := by
  intro ξ hξ
  have haξ : a ≤ ξ := hξ.1
  have hcontF : Continuous fun t : ℝ => Real.sin (u * (ξ - t)) * ψ t * W t :=
    ((Real.continuous_sin.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      hψ).mul hW
  have hcontG : Continuous fun t : ℝ => |ψ t| / u * |W t| :=
    (hψ.abs.div_const u).mul hW.abs
  have h1 : |∫ t in a..ξ, Real.sin (u * (ξ - t)) * ψ t * W t|
      ≤ ∫ t in a..ξ, |Real.sin (u * (ξ - t)) * ψ t * W t| :=
    intervalIntegral.abs_integral_le_integral_abs haξ
  have hpt : ∀ t ∈ Icc a ξ, |Real.sin (u * (ξ - t)) * ψ t * W t| ≤ |ψ t| * |W t| := by
    intro t _
    rw [abs_mul, abs_mul]
    have hs : |Real.sin (u * (ξ - t))| ≤ 1 := Real.abs_sin_le_one _
    have hnn : (0 : ℝ) ≤ |ψ t| * |W t| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc |Real.sin (u * (ξ - t))| * |ψ t| * |W t|
        ≤ 1 * |ψ t| * |W t| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ = |ψ t| * |W t| := by rw [one_mul]
  have h2 : ∫ t in a..ξ, |Real.sin (u * (ξ - t)) * ψ t * W t| ≤ ∫ t in a..ξ, |ψ t| * |W t| :=
    intervalIntegral.integral_mono_on haξ (hcontF.abs.intervalIntegrable a ξ)
      ((hψ.abs.mul hW.abs).intervalIntegrable a ξ) hpt
  have hdiv : (1 / u) * ∫ t in a..ξ, |ψ t| * |W t| = ∫ t in a..ξ, |ψ t| / u * |W t| := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    field_simp
  have hupos : (0 : ℝ) < 1 / u := by positivity
  have hstep : |(1 / u) * ∫ t in a..ξ, Real.sin (u * (ξ - t)) * ψ t * W t|
      ≤ ∫ t in a..ξ, |ψ t| / u * |W t| := by
    rw [abs_mul, abs_of_pos hupos, ← hdiv]
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hupos.le
  rw [heq ξ hξ]
  refine le_trans (abs_sub _ _) ?_
  exact add_le_add (Real.abs_cos_le_one _) hstep

/-- **Olver's bound: the solution stays inside the error-control exponential.** -/
theorem abs_le_exp_of_oscillatoryLG (hab : a ≤ b) (hu : 0 < u)
    (hW : Continuous W) (hψ : Continuous ψ) (heq : IsOscillatoryLGSolution a u ψ W b) :
    ∀ ξ ∈ Icc a b, |W ξ| ≤ Real.exp ((1 / u) * ∫ t in a..ξ, |ψ t|) := by
  intro ξ hξ
  have hφ : Continuous fun t : ℝ => |ψ t| / u := hψ.abs.div_const u
  have hφ0 : ∀ t : ℝ, 0 ≤ |ψ t| / u := fun t => div_nonneg (abs_nonneg _) hu.le
  have hmain := abs_le_exp_integral_of_volterra_bound hab hW hφ hφ0
    (volterra_bound_of_oscillatoryLG hu hW hψ heq) ξ hξ
  rwa [integral_abs_psi_div (ψ := ψ) (u := u) a ξ] at hmain

/-- **Olver's error bound: the deviation from the unperturbed cosine.** -/
theorem abs_sub_cos_le_of_oscillatoryLG (hab : a ≤ b) (hu : 0 < u)
    (hW : Continuous W) (hψ : Continuous ψ) (heq : IsOscillatoryLGSolution a u ψ W b) :
    ∀ ξ ∈ Icc a b, |W ξ - Real.cos (u * (ξ - a))|
      ≤ Real.exp ((1 / u) * ∫ t in a..ξ, |ψ t|) - 1 := by
  intro ξ hξ
  have haξ : a ≤ ξ := hξ.1
  have hφ : Continuous fun t : ℝ => |ψ t| / u := hψ.abs.div_const u
  have hφ0 : ∀ t : ℝ, 0 ≤ |ψ t| / u := fun t => div_nonneg (abs_nonneg _) hu.le
  have hbd : ∀ η ∈ Icc a b, |W η - 1 * Real.cos (u * (η - a))|
      ≤ ∫ t in a..η, (|ψ t| / u) * |W t| := by
    intro η hη
    have haη : a ≤ η := hη.1
    have hcontF : Continuous fun t : ℝ => Real.sin (u * (η - t)) * ψ t * W t :=
      ((Real.continuous_sin.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
        hψ).mul hW
    have h1 : |∫ t in a..η, Real.sin (u * (η - t)) * ψ t * W t|
        ≤ ∫ t in a..η, |Real.sin (u * (η - t)) * ψ t * W t| :=
      intervalIntegral.abs_integral_le_integral_abs haη
    have hpt : ∀ t ∈ Icc a η, |Real.sin (u * (η - t)) * ψ t * W t| ≤ |ψ t| * |W t| := by
      intro t _
      rw [abs_mul, abs_mul]
      calc |Real.sin (u * (η - t))| * |ψ t| * |W t|
          ≤ 1 * |ψ t| * |W t| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |ψ t| * |W t| := by rw [one_mul]
    have h2 : ∫ t in a..η, |Real.sin (u * (η - t)) * ψ t * W t| ≤ ∫ t in a..η, |ψ t| * |W t| :=
      intervalIntegral.integral_mono_on haη (hcontF.abs.intervalIntegrable a η)
        ((hψ.abs.mul hW.abs).intervalIntegrable a η) hpt
    have hdiv : (1 / u) * ∫ t in a..η, |ψ t| * |W t| = ∫ t in a..η, |ψ t| / u * |W t| := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      field_simp
    have hupos : (0 : ℝ) < 1 / u := by positivity
    have hsub : W η - 1 * Real.cos (u * (η - a))
        = -((1 / u) * ∫ t in a..η, Real.sin (u * (η - t)) * ψ t * W t) := by
      rw [heq η hη]
      ring
    rw [hsub, abs_neg, abs_mul, abs_of_pos hupos, ← hdiv]
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hupos.le
  have henv : ∀ η ∈ Icc a b, |W η| ≤ Real.exp (∫ t in a..η, |ψ t| / u) := by
    intro η hη
    have h := abs_le_exp_of_oscillatoryLG hab hu hW hψ heq η hη
    rwa [← integral_abs_psi_div (ψ := ψ) (u := u) a η] at h
  have htail := integral_mul_abs_le_exp_sub_one hW hφ hφ0 henv ξ hξ
  have hstart := hbd ξ hξ
  rw [one_mul] at hstart
  have hfin : |W ξ - Real.cos (u * (ξ - a))| ≤ Real.exp (∫ t in a..ξ, |ψ t| / u) - 1 :=
    le_trans hstart htail
  rwa [integral_abs_psi_div (ψ := ψ) (u := u) a ξ] at hfin

end GaloisForLFunctions.HTGeometry
