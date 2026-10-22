import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.BackwardContinuationCalculus
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CriticalEnergyFamilies

/-!
# Continuation transports admission

This is the step the programme exists for: a budget at one parameter plus a *continuation bound*
on the interval between gives a budget at the other parameter, with a constant that depends on the
interval and not on the observation horizon.

Two continuation hypotheses are isolated.

* `LinearContinuation E E' a c`: one primitive `β`, the same for every horizon, with
  `−E'_T(ε) ≤ β'(ε) · (1 + E_T(ε))` on `[a, c]`.  Linear control of the loss.
* `OsgoodContinuation E E' a c`: a coercive scale `Ψ` with derivative `ψ` and a primitive `β` with
  `−ψ(E_T(ε)) · E'_T(ε) ≤ β'(ε)`.  This permits loss growing faster than linearly, provided the
  reciprocal of the growth has infinite integral — the Osgood condition, which enters here as
  coercivity of `Ψ`.

In both the horizon is quantified *inside*: one budget function for all `T`.  That placement is
the whole hypothesis, and `HorizonUniformityIsTheTheorem` shows it cannot be relaxed.
-/

open Set Filter

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

variable {E : ℝ → ℕ → ℝ} {E' : ℕ → ℝ → ℝ} {a c : ℝ}

/-! ## §1. Linear continuation -/

/-- **A linear continuation budget on `[a, c]`.**  A primitive `β`, independent of the horizon,
whose derivative pays the energy's loss against `1 + E`. -/
def LinearContinuation (E : ℝ → ℕ → ℝ) (E' : ℕ → ℝ → ℝ) (a c : ℝ) : Prop :=
  ∃ β β' : ℝ → ℝ, (∀ ε ∈ Icc a c, HasDerivAt β (β' ε) ε) ∧
    ∀ T : ℕ, ∀ ε ∈ Icc a c, -E' T ε ≤ β' ε * (1 + E ε T)

/-- **Linear continuation transports admission backwards.**  The bound at `a` is the bound at `c`
amplified by `exp(β c − β a)`; no horizon appears. -/
theorem Admits.of_linearContinuation (hac : a ≤ c)
    (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε ∈ Icc a c, HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hcont : LinearContinuation E E' a c) (hc : Admits E c) : Admits E a := by
  obtain ⟨β, β', hβ, hwork⟩ := hcont
  obtain ⟨B, hB⟩ := hc
  refine ⟨(1 + max B 0) * Real.exp (β c - β a) - 1, fun T => ?_⟩
  have key := one_add_le_mul_exp_of_linear_work (f := fun x => E x T) (f' := fun x => E' T x)
    hac (fun ε hε => hE0 ε hε T) (fun ε hε => hEd T ε hε) hβ (fun ε hε => hwork T ε hε)
  have hstep : (1 + E c T) * Real.exp (β c - β a) ≤ (1 + max B 0) * Real.exp (β c - β a) :=
    mul_le_mul_of_nonneg_right (by linarith [(hB T).trans (le_max_left B 0)])
      (Real.exp_pos _).le
  linarith

/-- **Cofinal admission from continuation on every compact subinterval.**  The endpoint budget is
the only arithmetic input besides the continuation bounds; the bound is allowed to deteriorate
arbitrarily fast as the left endpoint approaches `0`. -/
theorem cofinallyAdmits_of_linearContinuation (hc0 : 0 < c)
    (hE0 : ∀ ε, 0 < ε → ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε, 0 < ε → HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hcont : ∀ x, 0 < x → x ≤ c → LinearContinuation E E' x c)
    (hadm : Admits E c) : CofinallyAdmits E := by
  intro δ hδ
  have hmin : 0 < min c δ := lt_min hc0 hδ
  refine ⟨min c δ / 2, by positivity, by linarith [min_le_right c δ], ?_⟩
  have hxc : min c δ / 2 ≤ c := by linarith [min_le_left c δ]
  have hx0 : 0 < min c δ / 2 := by positivity
  refine Admits.of_linearContinuation hxc
    (fun ε hε T => hE0 ε (lt_of_lt_of_le hx0 hε.1) T)
    (fun T ε hε => hEd T ε (lt_of_lt_of_le hx0 hε.1))
    (hcont _ hx0 hxc) hadm

/-! ## §2. Osgood continuation -/

/-- **An Osgood continuation budget on `[a, c]`.**  A coercive scale `Ψ` with nonnegative
derivative `ψ` on `[0, ∞)` and a primitive `β` paying the scaled loss.  Taking
`Ψ = log(1 + ·)` recovers the linear case; a slower-growing `ψ`, i.e. `Φ = 1/ψ` growing faster
than linearly, is admissible exactly as long as `Ψ` still tends to infinity. -/
def OsgoodContinuation (E : ℝ → ℕ → ℝ) (E' : ℕ → ℝ → ℝ) (a c : ℝ) : Prop :=
  ∃ Ψ ψ β β' : ℝ → ℝ,
    (∀ u, 0 ≤ u → HasDerivAt Ψ (ψ u) u) ∧ (∀ u, 0 ≤ u → 0 ≤ ψ u) ∧
      Tendsto Ψ atTop atTop ∧ (∀ ε ∈ Icc a c, HasDerivAt β (β' ε) ε) ∧
      ∀ T : ℕ, ∀ ε ∈ Icc a c, -(ψ (E ε T) * E' T ε) ≤ β' ε

/-- **Osgood continuation transports admission backwards.**  Coercivity of the scale is what
returns the bound: without it a bound on `Ψ ∘ E` says nothing about `E`. -/
theorem Admits.of_osgoodContinuation (hac : a ≤ c)
    (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε ∈ Icc a c, HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hcont : OsgoodContinuation E E' a c) (hc : Admits E c) : Admits E a := by
  obtain ⟨Ψ, ψ, β, β', hΨ, hψ, hcoe, hβ, hwork⟩ := hcont
  obtain ⟨B, hB⟩ := hc
  have hmono := monotoneOn_of_hasDerivAt_nonneg_Ici hΨ hψ
  refine bddAbove_of_tendsto_atTop hcoe (g := E a) (C := Ψ (max B 0) + (β c - β a)) fun T => ?_
  have key := scaledEnergy_add_budget_le (f := fun x => E x T) (f' := fun x => E' T x)
    (Ψ := Ψ) (ψ := fun ε => ψ (E ε T)) (β := β) (β' := β') hac (fun ε hε => hEd T ε hε)
    (fun ε hε => hΨ (E ε T) (hE0 ε hε T)) hβ (fun ε hε => by linarith [hwork T ε hε])
  have hmem : E c T ∈ Ici (0 : ℝ) := mem_Ici.mpr (hE0 c (right_mem_Icc.mpr hac) T)
  have hstep : Ψ (E c T) ≤ Ψ (max B 0) :=
    hmono hmem (mem_Ici.mpr (le_max_right B 0)) ((hB T).trans (le_max_left B 0))
  linarith

/-- Cofinal admission from Osgood continuation on every compact subinterval. -/
theorem cofinallyAdmits_of_osgoodContinuation (hc0 : 0 < c)
    (hE0 : ∀ ε, 0 < ε → ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε, 0 < ε → HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hcont : ∀ x, 0 < x → x ≤ c → OsgoodContinuation E E' x c)
    (hadm : Admits E c) : CofinallyAdmits E := by
  intro δ hδ
  have hmin : 0 < min c δ := lt_min hc0 hδ
  refine ⟨min c δ / 2, by positivity, by linarith [min_le_right c δ], ?_⟩
  have hxc : min c δ / 2 ≤ c := by linarith [min_le_left c δ]
  have hx0 : 0 < min c δ / 2 := by positivity
  exact Admits.of_osgoodContinuation hxc
    (fun ε hε T => hE0 ε (lt_of_lt_of_le hx0 hε.1) T)
    (fun T ε hε => hEd T ε (lt_of_lt_of_le hx0 hε.1))
    (hcont _ hx0 hxc) hadm

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
