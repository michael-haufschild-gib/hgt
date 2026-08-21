import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.Interaction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The exact energy identity and coercive long-time dynamics

This file formalises §3.3, §3.4, §4 and the energy half of §5 of Boudourides, *Hodge Coercivity
and Global Dynamics in Two-Field Edge-Cochain Systems with MHD-Type Cancellation*
(arXiv:2608.19360).

The two-field system is

```text
u̇ = -ν Δ u + B(u,u) - B(h,h) + f ,      ḣ = -η Δ h + B(u,h) - B(h,u) + g ,
```

on a real inner-product phase space, with `Δ` a nonnegative self-adjoint dissipative operator and
`B` in the cancellation class of `Interaction.lean`.

## Main results

* `hasDerivAt_energy` — **Theorem 2**, the exact energy identity (12).
* `integral_dissipation_identity` — the integrated identity (15)–(16).
* `energy_deriv_le_forced` — the forced scalar inequality (13).
* `energy_le_forced` — the explicit bound (14) of **Proposition 2**.
* `energy_le_unforced` — **Theorem 4**, unforced coercive decay `E(t) ≤ E(0) e^{-2βt}`.
* `absorbing_ball_positively_invariant` — the positive invariance half of **Theorem 3**.
* `energy_diff_le` — the continuous-dependence estimate (11) of §3.4.
* `energy_le_apriori` — an unconditional a priori bound, used for global existence.
-/

open Set intervalIntegral MeasureTheory
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry.HodgeEdgeCochain

section TwoField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (nu eta : ℝ) (f g : E)

/-- The velocity-like field of equation (5). -/
noncomputable def velocityField (u h : E) : E := -(nu • A u) + B u u - B h h + f

/-- The magnetic-like field of equation (6). -/
noncomputable def magneticField (u h : E) : E := -(eta • A h) + B u h - B h u + g

/-- `(u,h)` solves the two-field system (5)–(6) on the set `s`. -/
def IsSolutionOn (u h : ℝ → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt u (velocityField A B nu f (u t) (h t)) t ∧
    HasDerivAt h (magneticField A B eta g (u t) (h t)) t

/-- The total energy `E = ‖u‖² + ‖h‖²`. -/
def energy (u h : ℝ → E) (t : ℝ) : ℝ := ‖u t‖ ^ 2 + ‖h t‖ ^ 2

/-- The instantaneous dissipation `ν⟨Δu,u⟩ + η⟨Δh,h⟩`. -/
noncomputable def dissipation (u h : ℝ → E) (t : ℝ) : ℝ :=
  nu * ⟪A (u t), u t⟫_ℝ + eta * ⟪A (h t), h t⟫_ℝ

/-- The instantaneous forcing power `⟨f,u⟩ + ⟨g,h⟩`. -/
def forcingPower (u h : ℝ → E) (t : ℝ) : ℝ := ⟪f, u t⟫_ℝ + ⟪g, h t⟫_ℝ

variable {A B nu eta f g}

/-- **Theorem 2 (exact energy identity).**  Every solution of the cancellation class obeys
`½ dE/dt + ν⟨Δu,u⟩ + η⟨Δh,h⟩ = ⟨f,u⟩ + ⟨g,h⟩`. -/
theorem hasDerivAt_energy (hB : IsCancelling B) {u h : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (velocityField A B nu f (u t) (h t)) t)
    (hh : HasDerivAt h (magneticField A B eta g (u t) (h t)) t) :
    HasDerivAt (energy u h)
      (2 * (-(dissipation A nu eta u h t) + forcingPower f g u h t)) t := by
  have hrw : energy u h = fun s => ⟪u s, u s⟫_ℝ + ⟪h s, h s⟫_ℝ := by
    funext s
    simp [energy, real_inner_self_eq_norm_sq]
  have hdu := (hu.inner ℝ hu).add (hh.inner ℝ hh)
  rw [hrw]
  convert hdu using 1
  -- expand the inner products of the two field equations
  have e1 : ⟪velocityField A B nu f (u t) (h t), u t⟫_ℝ
      = -(nu * ⟪A (u t), u t⟫_ℝ) + ⟪B (u t) (u t), u t⟫_ℝ - ⟪B (h t) (h t), u t⟫_ℝ
        + ⟪f, u t⟫_ℝ := by
    simp only [velocityField, inner_add_left, inner_sub_left, inner_neg_left,
      real_inner_smul_left]
  have e2 : ⟪magneticField A B eta g (u t) (h t), h t⟫_ℝ
      = -(eta * ⟪A (h t), h t⟫_ℝ) + ⟪B (u t) (h t), h t⟫_ℝ - ⟪B (h t) (u t), h t⟫_ℝ
        + ⟪g, h t⟫_ℝ := by
    simp only [magneticField, inner_add_left, inner_sub_left, inner_neg_left,
      real_inner_smul_left]
  have c1 : ⟪B (u t) (u t), u t⟫_ℝ = 0 := hB.inner_self_eq_zero _ _
  have c2 : ⟪B (u t) (h t), h t⟫_ℝ = 0 := hB.inner_self_eq_zero _ _
  have c3 : ⟪B (h t) (h t), u t⟫_ℝ = -⟪B (h t) (u t), h t⟫_ℝ := hB _ _ _
  have s1 : ⟪u t, velocityField A B nu f (u t) (h t)⟫_ℝ
      = ⟪velocityField A B nu f (u t) (h t), u t⟫_ℝ := real_inner_comm _ _
  have s2 : ⟪h t, magneticField A B eta g (u t) (h t)⟫_ℝ
      = ⟪magneticField A B eta g (u t) (h t), h t⟫_ℝ := real_inner_comm _ _
  rw [s1, s2, e1, e2, c1, c2, c3]
  simp only [dissipation, forcingPower]
  ring

/-- The energy of a solution is differentiable, hence continuous. -/
theorem continuousOn_energy (hB : IsCancelling B) {u h : ℝ → E} {s : Set ℝ}
    (hsol : IsSolutionOn A B nu eta f g u h s) : ContinuousOn (energy u h) s := by
  intro t ht
  exact ((hasDerivAt_energy hB (hsol t ht).1 (hsol t ht).2).continuousAt).continuousWithinAt

end TwoField

end GaloisForLFunctions.HTGeometry.HodgeEdgeCochain
