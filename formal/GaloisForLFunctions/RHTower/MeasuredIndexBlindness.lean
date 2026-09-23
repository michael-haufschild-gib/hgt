/-
The faithful–measured index dichotomy: why a flow-invariant (type-II₁) trace cannot express RH.

The negative index `κ₋` of the FE-forced indefinite Weil/Krein form counts off-line zeros: for the
finite conjugate-pair carrier it is *exactly* the number of off-line pairs (`KreinLangerInertia`,
`exact_neg_inertia`), an integer, and RH ⟺ `κ₋ = 0`.  That count is **faithful / point-resolving**:
a single off-line pair forces `κ₋ ≥ 1`.

The scaling flow's von Neumann trace is a different object.  A type-III₁ scaling `τ∘θ_s = e^{-s}τ`
admits only ratios, so the natural measured index is the **normalised** ratio `Noff(T)/N(T)` against
the total density of states `N(T)`.  This normalisation destroys the integer: it cannot see a bounded
(let alone density-zero) off-line set.

This file makes that method limitation a theorem.  Define a measured index as vanishing when
`Noff(T)/N(T) → 0`.  Then three off-line configurations — no off-line zeros (RH), one off-line zero
(¬RH), and an unbounded density-zero dust (¬RH with infinitely many off-line zeros) — all share
measured index `0`.  So the measured index does **not** determine RH; only the faithful integer count
does.  This is the constraint-side reason the type-II₁ / measured-trace program stalls at the same
wall: it lives at the level of a normalised ratio, and RH is the un-normalisable integer remainder.
No carrier is constructed; the statement is a rigidity/blindness contrast between two indices.
-/
import Mathlib

open Filter Topology

namespace GaloisForLFunctions

/-- The **measured index vanishes**: the off-line count `Noff`, normalised by the total density of
states `N`, tends to `0`. This is the flow-invariant (type-II₁) reading — a ratio, not a count. -/
def MeasuredIndexZero (Noff N : ℕ → ℝ) : Prop :=
  Tendsto (fun n => Noff n / N n) atTop (𝓝 0)

/-- A bounded (constant) off-line count normalises to a vanishing measured index: `c/n → 0`.  In
particular a *fixed* finite number of off-line zeros is invisible to the measured index. -/
theorem measuredIndexZero_const (c : ℝ) : MeasuredIndexZero (fun _ => c) (fun n => (n : ℝ)) :=
  tendsto_const_div_atTop_nhds_zero_nat c

/-- An unbounded **density-zero dust**: an off-line count going to infinity whose normalised ratio
still vanishes (`n / n² = 1/n → 0`).  Infinitely many off-line zeros, yet measured index `0`. -/
theorem measuredIndexZero_dust :
    ∃ Noff N : ℕ → ℝ,
      Tendsto Noff atTop atTop ∧ MeasuredIndexZero Noff N := by
  refine ⟨fun n => (n : ℝ), fun n => (n : ℝ) ^ (2 : ℕ), tendsto_natCast_atTop_atTop, ?_⟩
  have hev : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) = (n : ℝ) / (n : ℝ) ^ (2 : ℕ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [pow_two, ← div_div, div_self hn0]
  exact (tendsto_const_div_atTop_nhds_zero_nat 1).congr' hev

/-- **The faithful–measured dichotomy — the operator-spectral no-go.**  Three off-line
configurations distinguished by their *faithful* index `κ₋` (the exact negative inertia of the
Krein carrier, `exact_neg_inertia`): none (RH, `κ₋ = 0`), one off-line zero (¬RH, `κ₋ = 1`), and an
unbounded density-zero dust (¬RH, `κ₋ → ∞`).  All three have the **same measured index** `0`.  Hence
the normalised (type-II₁, flow-invariant) index cannot distinguish RH from its failure — not even
from a single off-line zero.  RH is the faithful integer count the normalisation destroys; a measured
trace, seeing only the ratio, is structurally blind to it. -/
theorem faithful_measured_dichotomy :
    MeasuredIndexZero (fun _ => 0) (fun n => (n : ℝ)) ∧
      MeasuredIndexZero (fun _ => 1) (fun n => (n : ℝ)) ∧
      (∃ Noff N : ℕ → ℝ, Tendsto Noff atTop atTop ∧ MeasuredIndexZero Noff N) :=
  ⟨measuredIndexZero_const 0, measuredIndexZero_const 1, measuredIndexZero_dust⟩

/-- **Type-III scaling obstruction.**  A real functional that is both scaling-*covariant*
(`τ(θ_s P) = e^{-s}·τ(P)`, the type-III₁ modular scaling of the adele-class trace) and flow-*invariant*
(`τ(θ_s P) = τ(P)`, as an honest off-line count must be — the count of off-line zeros does not change
along the scaling orbit) is forced to vanish: `τ(P) = 0`.  Since `e^{-1} ≠ 1`, covariance and
invariance together give `e^{-1}·τ(P) = τ(P)`, hence `τ(P) = 0`.  So no scaling-covariant trace can be
a nonzero absolute count: it reads `0` on every configuration, RH-blind, regardless of how many
off-line zeros there are.  This is the structural reason — beyond the density normalisation — that a
type-II₁/III₁ trace cannot express RH; only a flow-*breaking* faithful index can carry the integer. -/
theorem typeIII_scaling_forces_zero {X : Type*} (τ : X → ℝ) (θ : ℝ → X → X) (P : X)
    (hcov : ∀ s, τ (θ s P) = Real.exp (-s) * τ P)
    (hinv : ∀ s, τ (θ s P) = τ P) :
    τ P = 0 := by
  have h1 : Real.exp (-1) * τ P = τ P := by rw [← hcov 1, hinv 1]
  have he : Real.exp (-1) ≠ 1 := ne_of_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  have h2 : (Real.exp (-1) - 1) * τ P = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) he
  · exact h

end GaloisForLFunctions
