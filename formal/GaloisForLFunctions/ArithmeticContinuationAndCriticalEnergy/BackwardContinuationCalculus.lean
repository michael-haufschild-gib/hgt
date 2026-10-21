import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The backward continuation calculus

A *continuation* statement propagates a finite bound on an energy from one end of a parameter
interval to the other.  The energy family of interest is bounded at the endpoint `c` of a damping
interval `[a, c]` and the question is whether that bound survives the walk back to `a`, with a
constant that does not depend on the observation horizon.

The whole mechanism is one monotonicity statement.  Fix a *scale* `Ψ` (a primitive of `1/Φ`) and a
*budget primitive* `β`.  If along the interval

`0 ≤ ψ(ε) · f'(ε) + β'(ε)`,

that is, the energy can only lose as much as the budget pays when read through the scale, then
`Ψ ∘ f + β` is nondecreasing and therefore

`Ψ(f a) ≤ Ψ(f c) + (β c − β a)`.

Two specialisations are used downstream:

* `Ψ = log(1 + ·)`, giving the linear (Grönwall) form `1 + f a ≤ (1 + f c) exp(β c − β a)`;
* a general coercive `Ψ` with nonnegative derivative, giving the Osgood form: any scale whose
  reciprocal derivative `Φ` satisfies `∫^∞ du/Φ(u) = ∞` still forbids escape over a finite
  parameter interval.  Coercivity enters only through `Tendsto Ψ atTop atTop`, which converts a
  bound on `Ψ ∘ f` back into a bound on `f`.

Nothing here is arithmetic: these are the hypotheses a continuation theorem must meet, stated so
that the arithmetic input is exactly the one inequality `hwork`.
-/

open Set Filter Topology

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

variable {a c : ℝ}

/-! ## §1. The master inequality -/

/-- **Continuation through a scale.**  If the scaled energy loses no faster than the budget pays,
the sum `Ψ ∘ f + β` is monotone on `[a, c]`.  `ψ ε` is the derivative of `Ψ` at the point `f ε`;
indexing it by `ε` rather than by the value keeps the hypothesis pointwise and avoids demanding
differentiability of `Ψ` off the range of `f`. -/
theorem scaledEnergy_add_budget_le {f f' Ψ ψ β β' : ℝ → ℝ} (hac : a ≤ c)
    (hf : ∀ ε ∈ Icc a c, HasDerivAt f (f' ε) ε)
    (hΨ : ∀ ε ∈ Icc a c, HasDerivAt Ψ (ψ ε) (f ε))
    (hβ : ∀ ε ∈ Icc a c, HasDerivAt β (β' ε) ε)
    (hwork : ∀ ε ∈ Icc a c, 0 ≤ ψ ε * f' ε + β' ε) :
    Ψ (f a) + β a ≤ Ψ (f c) + β c := by
  have hderiv : ∀ ε ∈ Icc a c,
      HasDerivAt (fun x => Ψ (f x) + β x) (ψ ε * f' ε + β' ε) ε := by
    intro ε hε
    have hcomp : HasDerivAt (fun x => Ψ (f x)) (ψ ε * f' ε) ε :=
      (hΨ ε hε).comp ε (hf ε hε)
    exact hcomp.add (hβ ε hε)
  have hmono : MonotoneOn (fun x => Ψ (f x) + β x) (Icc a c) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a c)
      (f' := fun ε => ψ ε * f' ε + β' ε)
      (fun ε hε => ((hderiv ε hε).continuousAt).continuousWithinAt) ?_ ?_
    · intro ε hε
      rw [interior_Icc] at hε
      exact (hderiv ε (Ioo_subset_Icc_self hε)).hasDerivWithinAt
    · intro ε hε
      rw [interior_Icc] at hε
      exact hwork ε (Ioo_subset_Icc_self hε)
  exact hmono (left_mem_Icc.mpr hac) (right_mem_Icc.mpr hac) hac

/-! ## §2. The linear (Grönwall) form -/

/-- The logarithmic scale is differentiable wherever the energy is nonnegative. -/
theorem hasDerivAt_log_one_add {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun x => Real.log (1 + x)) (1 + u)⁻¹ u := by
  have h1 : (1 : ℝ) + u ≠ 0 := by positivity
  simpa [one_div] using ((hasDerivAt_id' (x := u)).const_add (1 : ℝ)).log h1

/-- **Linear continuation.**  If the energy's loss is at most `β'(ε) · (1 + f ε)` along `[a, c]`,
then `1 + f a ≤ (1 + f c) exp(β c − β a)`.  The bound at `a` depends on the endpoint value and on
the total budget only — this is the step that turns an endpoint budget into a budget at `a`. -/
theorem one_add_le_mul_exp_of_linear_work {f f' β β' : ℝ → ℝ} (hac : a ≤ c)
    (hf0 : ∀ ε ∈ Icc a c, 0 ≤ f ε)
    (hf : ∀ ε ∈ Icc a c, HasDerivAt f (f' ε) ε)
    (hβ : ∀ ε ∈ Icc a c, HasDerivAt β (β' ε) ε)
    (hwork : ∀ ε ∈ Icc a c, -f' ε ≤ β' ε * (1 + f ε)) :
    1 + f a ≤ (1 + f c) * Real.exp (β c - β a) := by
  have key := scaledEnergy_add_budget_le (f := f) (f' := f')
    (Ψ := fun x => Real.log (1 + x)) (ψ := fun ε => (1 + f ε)⁻¹) (β := β) (β' := β') hac hf
    (fun ε hε => hasDerivAt_log_one_add (hf0 ε hε)) hβ ?_
  · have hca : (0 : ℝ) < 1 + f a := by linarith [hf0 a (left_mem_Icc.mpr hac)]
    have hcc : (0 : ℝ) < 1 + f c := by linarith [hf0 c (right_mem_Icc.mpr hac)]
    have hlog : Real.log (1 + f a) ≤ Real.log (1 + f c) + (β c - β a) := by linarith
    calc 1 + f a = Real.exp (Real.log (1 + f a)) := (Real.exp_log hca).symm
      _ ≤ Real.exp (Real.log (1 + f c) + (β c - β a)) := Real.exp_le_exp.mpr hlog
      _ = (1 + f c) * Real.exp (β c - β a) := by
          rw [Real.exp_add, Real.exp_log hcc]
  · intro ε hε
    have hpos : (0 : ℝ) < 1 + f ε := by linarith [hf0 ε hε]
    have h := hwork ε hε
    have hdiv : 0 ≤ (β' ε * (1 + f ε) + f' ε) / (1 + f ε) :=
      div_nonneg (by linarith) hpos.le
    have heq : (β' ε * (1 + f ε) + f' ε) / (1 + f ε) = (1 + f ε)⁻¹ * f' ε + β' ε := by
      field_simp
      ring
    rwa [heq] at hdiv

/-! ## §3. Coercive scales and the Osgood form -/

/-- **A coercive scale returns the bound.**  If `Ψ` tends to infinity and `Ψ ∘ g` is bounded above,
then `g` is bounded above.  This is the step that makes a nonlinear scale usable: without
coercivity a bound on `Ψ ∘ g` says nothing about `g`. -/
theorem bddAbove_of_tendsto_atTop {Ψ : ℝ → ℝ} (hcoe : Tendsto Ψ atTop atTop) {g : ℕ → ℝ} {C : ℝ}
    (hC : ∀ T, Ψ (g T) ≤ C) : ∃ B : ℝ, ∀ T, g T ≤ B := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hcoe.eventually_gt_atTop C)
  refine ⟨x₀, fun T => ?_⟩
  by_contra hlt
  exact absurd (hC T) (not_le.mpr (hx₀ (g T) (le_of_lt (not_le.mp hlt))))

/-- A scale with nonnegative derivative on `[0, ∞)` is monotone there.  Used to read an endpoint
energy budget as an endpoint budget for the scaled energy. -/
theorem monotoneOn_of_hasDerivAt_nonneg_Ici {Ψ ψ : ℝ → ℝ}
    (hΨ : ∀ u, 0 ≤ u → HasDerivAt Ψ (ψ u) u) (hψ : ∀ u, 0 ≤ u → 0 ≤ ψ u) :
    MonotoneOn Ψ (Ici (0 : ℝ)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := ψ)
    (fun u hu => ((hΨ u (mem_Ici.mp hu)).continuousAt).continuousWithinAt) ?_ ?_
  · intro u hu
    rw [interior_Ici] at hu
    exact (hΨ u (le_of_lt (mem_Ioi.mp hu))).hasDerivWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    exact hψ u (le_of_lt (mem_Ioi.mp hu))

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
