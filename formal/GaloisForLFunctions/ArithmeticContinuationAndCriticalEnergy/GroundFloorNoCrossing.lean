import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.BackwardContinuationCalculus

/-!
# No crossing from a bounded relative decay

The aperture side of the critical form asks a mirror question to the damping side.  There the
energy must not become infinite as the parameter decreases; here a *ground floor* must not reach
zero as the aperture grows.  Both are continuation statements, and both are the same monotonicity
statement read through a different scale: taking `Ψ = log` on a positive floor,

`−μ'(A) ≤ β'(A) · μ(A)` on `[a, c]`  ⟹  `μ(c) ≥ μ(a) · exp(−(β(c) − β(a)))`.

The hypothesis is a bound on the *relative* decay — the logarithmic derivative — not on the decay
itself.  A floor may fall arbitrarily fast in absolute terms and still never reach zero, which is
why the relative form is the right one: it is scale-free, and it is exactly what a no-crossing law
needs.

The second statement is the usable form: under a budget with nonnegative derivative, the same
explicit lower bound holds *uniformly* at every parameter of `[a, c)`, so a floor obeying a
relative-decay budget cannot approach zero inside the interval.  Contrapositively, a first crossing
forces the relative decay to be unpaid by any budget of finite total on the interval leading to it.
-/

open Set

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

variable {a c : ℝ}

/-- **The floor transport.**  A bound on the relative decay of a positive floor gives an explicit
positive lower bound at the far end of the interval. -/
theorem floor_le_of_relative_decay (hac : a ≤ c) {μ μ' β β' : ℝ → ℝ}
    (hpos : ∀ A ∈ Icc a c, 0 < μ A)
    (hμ : ∀ A ∈ Icc a c, HasDerivAt μ (μ' A) A)
    (hβ : ∀ A ∈ Icc a c, HasDerivAt β (β' A) A)
    (hdecay : ∀ A ∈ Icc a c, -μ' A ≤ β' A * μ A) :
    μ a * Real.exp (-(β c - β a)) ≤ μ c := by
  have key := scaledEnergy_add_budget_le (f := μ) (f' := μ') (Ψ := Real.log)
    (ψ := fun A => (μ A)⁻¹) (β := β) (β' := β') hac hμ
    (fun A hA => Real.hasDerivAt_log (hpos A hA).ne') hβ ?_
  · have hpa := hpos a (left_mem_Icc.mpr hac)
    have hpc := hpos c (right_mem_Icc.mpr hac)
    have hlog : Real.log (μ a) - (β c - β a) ≤ Real.log (μ c) := by linarith
    calc μ a * Real.exp (-(β c - β a))
        = Real.exp (Real.log (μ a) - (β c - β a)) := by
          rw [Real.exp_sub, Real.exp_log hpa, Real.exp_neg, div_eq_mul_inv]
      _ ≤ Real.exp (Real.log (μ c)) := Real.exp_le_exp.mpr hlog
      _ = μ c := Real.exp_log hpc
  · intro A hA
    have hp := hpos A hA
    have h := hdecay A hA
    have hdiv : 0 ≤ (β' A * μ A + μ' A) / μ A := div_nonneg (by linarith) hp.le
    have heq : (β' A * μ A + μ' A) / μ A = (μ A)⁻¹ * μ' A + β' A := by
      field_simp
      ring
    rwa [heq] at hdiv

/-- A budget with nonnegative derivative is monotone on the interval. -/
theorem monotoneOn_budget (hac : a ≤ c) {β β' : ℝ → ℝ}
    (hβ : ∀ A ∈ Icc a c, HasDerivAt β (β' A) A) (hβ0 : ∀ A ∈ Icc a c, 0 ≤ β' A) :
    MonotoneOn β (Icc a c) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a c) (f' := β')
    (fun A hA => ((hβ A hA).continuousAt).continuousWithinAt) ?_ ?_
  · intro A hA
    rw [interior_Icc] at hA
    exact (hβ A (Ioo_subset_Icc_self hA)).hasDerivWithinAt
  · intro A hA
    rw [interior_Icc] at hA
    exact hβ0 A (Ioo_subset_Icc_self hA)

/-- **No crossing inside the interval.**  Under a relative-decay budget with nonnegative
derivative, one explicit positive bound holds at every parameter of `[a, c)`: the floor cannot
approach zero before `c`.  A first crossing therefore forces the relative decay to exceed every
budget of finite total on the interval leading to it. -/
theorem floor_le_of_relative_decay_Ico (hac : a ≤ c) {μ μ' β β' : ℝ → ℝ}
    (hpos : ∀ A ∈ Icc a c, 0 < μ A)
    (hμ : ∀ A ∈ Icc a c, HasDerivAt μ (μ' A) A)
    (hβ : ∀ A ∈ Icc a c, HasDerivAt β (β' A) A)
    (hβ0 : ∀ A ∈ Icc a c, 0 ≤ β' A)
    (hdecay : ∀ A ∈ Icc a c, -μ' A ≤ β' A * μ A) :
    ∀ A ∈ Icc a c, μ a * Real.exp (-(β c - β a)) ≤ μ A := by
  intro A hA
  have hsub : Icc a A ⊆ Icc a c := Icc_subset_Icc le_rfl hA.2
  have hstep := floor_le_of_relative_decay hA.1 (μ := μ) (μ' := μ') (β := β) (β' := β')
    (fun x hx => hpos x (hsub hx)) (fun x hx => hμ x (hsub hx)) (fun x hx => hβ x (hsub hx))
    (fun x hx => hdecay x (hsub hx))
  have hmono := monotoneOn_budget hac hβ hβ0
  have hβA : β A ≤ β c := hmono hA (right_mem_Icc.mpr hac) hA.2
  have hexp : Real.exp (-(β c - β a)) ≤ Real.exp (-(β A - β a)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpa := hpos a (left_mem_Icc.mpr hac)
  exact le_trans (mul_le_mul_of_nonneg_left hexp hpa.le) hstep

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
