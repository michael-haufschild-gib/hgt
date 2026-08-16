import GaloisForLFunctions.HTGeometry.GronwallBackward

/-!
# The Liouville–Green error bound in the original variable

Writing the exact solution of `Φ'' = Q Φ` as `Φ = G·R` against the Liouville–Green approximant
`G = A e^{−Ξ}`, `A = Q^{−1/4}`, `Ξ = ∫ √Q`, the Wronskian `H = Φ'G − ΦG'` satisfies
`H' = −(A''/A) G Φ`, and one integration by parts collapses the resulting nested integral to a
*single* Volterra equation

```text
R(y) = 1 − ∫_y^b κ(y,t) · (A A'')(t) · R(t) dt ,
κ(y,t) = (1 − e^{−2(Ξ t − Ξ y)})/2 ∈ [0, 1/2] .
```

Backward Grönwall then gives Olver's bound `|R − 1| ≤ exp(½ ∫_y^b |A A''|) − 1`, the error-control
function being the mass of `A A'' = Q^{−1/4}(Q^{−1/4})''`.

Everything is stated in the original variable: the phase enters only through `Ξ`, which is an
explicit integral, so no change of variable and no inverse function is constructed.  This is what
makes the estimate usable on an equation whose Liouville variable has no closed form — the prolate
barrier being the case at hand.
-/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

variable {a b : ℝ} {Ξ ψ R : ℝ → ℝ}

/-- The Liouville–Green kernel of a phase. -/
def lgPhaseKernel (Ξ : ℝ → ℝ) (ξ t : ℝ) : ℝ := (1 - Real.exp (-(2 * (Ξ t - Ξ ξ)))) / 2

theorem lgPhaseKernel_le_half (Ξ : ℝ → ℝ) (ξ t : ℝ) : lgPhaseKernel Ξ ξ t ≤ 1 / 2 := by
  have := (Real.exp_pos (-(2 * (Ξ t - Ξ ξ)))).le
  rw [lgPhaseKernel]
  linarith

theorem lgPhaseKernel_nonneg {ξ t : ℝ} (h : Ξ ξ ≤ Ξ t) : 0 ≤ lgPhaseKernel Ξ ξ t := by
  have hexp : Real.exp (-(2 * (Ξ t - Ξ ξ))) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    linarith
  rw [lgPhaseKernel]
  linarith

theorem abs_lgPhaseKernel_le_half {ξ t : ℝ} (h : Ξ ξ ≤ Ξ t) :
    |lgPhaseKernel Ξ ξ t| ≤ 1 / 2 :=
  abs_le.2 ⟨by linarith [lgPhaseKernel_nonneg (Ξ := Ξ) h], lgPhaseKernel_le_half Ξ ξ t⟩

theorem continuous_lgPhaseKernel (hΞ : Continuous Ξ) (ξ : ℝ) :
    Continuous (lgPhaseKernel Ξ ξ) := by
  unfold lgPhaseKernel
  fun_prop

/-- The Volterra form of the Liouville–Green ratio. -/
def IsPhaseLGSolution (b : ℝ) (Ξ ψ R : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ξ ∈ Icc a b, R ξ = 1 - ∫ t in ξ..b, lgPhaseKernel Ξ ξ t * ψ t * R t

theorem integral_abs_psi_half (a ξ : ℝ) :
    ∫ t in a..ξ, |ψ t| / 2 = (1 / 2) * ∫ t in a..ξ, |ψ t| := by
  rw [intervalIntegral.integral_div, one_div, inv_mul_eq_div]

/-- The defect of the Volterra equation is at most half the mass of the error-control function. -/
theorem phase_volterra_defect (hΞ : Continuous Ξ) (hmono : Monotone Ξ)
    (hR : Continuous R) (hψ : Continuous ψ) (heq : IsPhaseLGSolution b Ξ ψ R a)
    {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
    |R ξ - 1| ≤ ∫ t in ξ..b, (|ψ t| / 2) * |R t| := by
  have hξb : ξ ≤ b := hξ.2
  have hcontF : Continuous fun t : ℝ => lgPhaseKernel Ξ ξ t * ψ t * R t :=
    ((continuous_lgPhaseKernel hΞ ξ).mul hψ).mul hR
  have h1 : |∫ t in ξ..b, lgPhaseKernel Ξ ξ t * ψ t * R t|
      ≤ ∫ t in ξ..b, |lgPhaseKernel Ξ ξ t * ψ t * R t| :=
    intervalIntegral.abs_integral_le_integral_abs hξb
  have hpt : ∀ t ∈ Icc ξ b, |lgPhaseKernel Ξ ξ t * ψ t * R t| ≤ (|ψ t| / 2) * |R t| := by
    intro t ht
    rw [abs_mul, abs_mul]
    have hk : |lgPhaseKernel Ξ ξ t| ≤ 1 / 2 := abs_lgPhaseKernel_le_half (hmono ht.1)
    calc |lgPhaseKernel Ξ ξ t| * |ψ t| * |R t|
        ≤ (1 / 2) * |ψ t| * |R t| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
      _ = (|ψ t| / 2) * |R t| := by ring
  have h2 : (∫ t in ξ..b, |lgPhaseKernel Ξ ξ t * ψ t * R t|)
      ≤ ∫ t in ξ..b, (|ψ t| / 2) * |R t| :=
    intervalIntegral.integral_mono_on hξb (hcontF.abs.intervalIntegrable ξ b)
      (((hψ.abs.div_const 2).mul hR.abs).intervalIntegrable ξ b) hpt
  have hRξ := heq ξ hξ
  have hval : R ξ - 1 = -∫ t in ξ..b, lgPhaseKernel Ξ ξ t * ψ t * R t := by
    rw [hRξ]
    ring
  rw [hval, abs_neg]
  exact le_trans h1 h2

/-- The Volterra equation gives the backward Grönwall hypothesis. -/
theorem phase_volterra_bound (hΞ : Continuous Ξ) (hmono : Monotone Ξ)
    (hR : Continuous R) (hψ : Continuous ψ) (heq : IsPhaseLGSolution b Ξ ψ R a) :
    ∀ ξ ∈ Icc a b, |R ξ| ≤ 1 + ∫ t in ξ..b, (|ψ t| / 2) * |R t| := by
  intro ξ hξ
  have hdef := phase_volterra_defect hΞ hmono hR hψ heq hξ
  have habs := abs_sub_abs_le_abs_sub (R ξ) 1
  rw [abs_one] at habs
  linarith

/-- **Olver's bound in the original variable.** -/
theorem abs_le_exp_of_phaseLG (hab : a ≤ b) (hΞ : Continuous Ξ) (hmono : Monotone Ξ)
    (hR : Continuous R) (hψ : Continuous ψ) (heq : IsPhaseLGSolution b Ξ ψ R a) :
    ∀ ξ ∈ Icc a b, |R ξ| ≤ Real.exp ((1 / 2) * ∫ t in ξ..b, |ψ t|) := by
  intro ξ hξ
  have hφ : Continuous fun t : ℝ => |ψ t| / 2 := hψ.abs.div_const 2
  have hφ0 : ∀ t : ℝ, 0 ≤ |ψ t| / 2 := fun t => by positivity
  have hmain := abs_le_exp_integral_of_volterra_bound_backward hab hR hφ hφ0
    (phase_volterra_bound hΞ hmono hR hψ heq) ξ hξ
  rwa [integral_abs_psi_half (ψ := ψ) ξ b] at hmain

/-- **Olver's error bound in the original variable.**  The Liouville–Green ratio differs from one by
at most `exp(½ ∫ |A A''|) − 1`. -/
theorem abs_sub_one_le_exp_sub_one_of_phaseLG (hab : a ≤ b) (hΞ : Continuous Ξ)
    (hmono : Monotone Ξ) (hR : Continuous R) (hψ : Continuous ψ)
    (heq : IsPhaseLGSolution b Ξ ψ R a) :
    ∀ ξ ∈ Icc a b, |R ξ - 1| ≤ Real.exp ((1 / 2) * ∫ t in ξ..b, |ψ t|) - 1 := by
  intro ξ hξ
  have hφ : Continuous fun t : ℝ => |ψ t| / 2 := hψ.abs.div_const 2
  have hφ0 : ∀ t : ℝ, 0 ≤ |ψ t| / 2 := fun t => by positivity
  have hmain := abs_sub_one_le_exp_sub_one_of_volterra_bound_backward hab hR hφ hφ0
    (phase_volterra_bound hΞ hmono hR hψ heq)
    (fun η hη => phase_volterra_defect hΞ hmono hR hψ heq hη) ξ hξ
  rwa [integral_abs_psi_half (ψ := ψ) ξ b] at hmain

/-- **The two-sided form.**  The ratio is trapped between `2 − E` and `E`. -/
theorem phaseLG_two_sided (hab : a ≤ b) (hΞ : Continuous Ξ) (hmono : Monotone Ξ)
    (hR : Continuous R) (hψ : Continuous ψ) (heq : IsPhaseLGSolution b Ξ ψ R a)
    {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
    2 - Real.exp ((1 / 2) * ∫ t in ξ..b, |ψ t|) ≤ R ξ ∧
      R ξ ≤ Real.exp ((1 / 2) * ∫ t in ξ..b, |ψ t|) := by
  have h := abs_sub_one_le_exp_sub_one_of_phaseLG hab hΞ hmono hR hψ heq ξ hξ
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end GaloisForLFunctions.HTGeometry
