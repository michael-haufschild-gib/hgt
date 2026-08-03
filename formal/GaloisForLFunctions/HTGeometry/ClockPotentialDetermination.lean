import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exactly which part of a clock potential probe solutions determine

Step 1 of the continuum-gravity bridge asks for the effective zeroth-order potential of a scalar
clock species. This file settles the determination question exactly, for an arbitrary wave operator
and with no linearity, smoothness or geometry assumed.

A family of probes solving the potential-dressed wave equation determines the potential at an event
precisely when some probe of the family is nonvanishing there. On the common zero set of the whole
family the potential is entirely invisible: it can be altered arbitrarily without disturbing a
single probe solution.

So the missing input of step 1 is exactly a probe family without a common zero. Data that locate
only where solutions are singular do not supply it.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {X : Type u}

/-- A scalar probe solves the potential-dressed wave equation. -/
def SolvesPotentialWave (wave : (X → ℝ) → (X → ℝ)) (potential u : X → ℝ) : Prop :=
  ∀ x, wave u x + potential x * u x = 0

/-- The events at which some probe of the family is nonvanishing. -/
def potentialDeterminationSet (probes : Set (X → ℝ)) : Set X :=
  {x | ∃ u ∈ probes, u x ≠ 0}

theorem mem_potentialDeterminationSet_iff (probes : Set (X → ℝ)) (x : X) :
    x ∈ potentialDeterminationSet probes ↔ ∃ u ∈ probes, u x ≠ 0 := Iff.rfl

/-- **A nonvanishing probe pins the potential pointwise.** -/
theorem potential_eq_of_solvesPotentialWave {wave : (X → ℝ) → (X → ℝ)}
    {potential₁ potential₂ u : X → ℝ}
    (h₁ : SolvesPotentialWave wave potential₁ u)
    (h₂ : SolvesPotentialWave wave potential₂ u)
    {x : X} (hu : u x ≠ 0) : potential₁ x = potential₂ x := by
  have hdiff : (potential₁ x - potential₂ x) * u x = 0 := by
    have e₁ := h₁ x
    have e₂ := h₂ x
    nlinarith [e₁, e₂]
  rcases mul_eq_zero.mp hdiff with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hu

/-- **Probe solutions determine the potential exactly on the determination set.** -/
theorem potential_eqOn_potentialDeterminationSet {wave : (X → ℝ) → (X → ℝ)}
    {potential₁ potential₂ : X → ℝ} {probes : Set (X → ℝ)}
    (h₁ : ∀ u ∈ probes, SolvesPotentialWave wave potential₁ u)
    (h₂ : ∀ u ∈ probes, SolvesPotentialWave wave potential₂ u) :
    Set.EqOn potential₁ potential₂ (potentialDeterminationSet probes) := by
  rintro x ⟨u, hu, hux⟩
  exact potential_eq_of_solvesPotentialWave (h₁ u hu) (h₂ u hu) hux

/-- Off the determination set the potential may be altered without disturbing any probe. -/
theorem solvesPotentialWave_update_of_notMem_potentialDeterminationSet
    [DecidableEq X] {wave : (X → ℝ) → (X → ℝ)} {potential : X → ℝ} {probes : Set (X → ℝ)}
    (hsolve : ∀ u ∈ probes, SolvesPotentialWave wave potential u)
    {x₀ : X} (hx₀ : x₀ ∉ potentialDeterminationSet probes) (value : ℝ) :
    ∀ u ∈ probes, SolvesPotentialWave wave (Function.update potential x₀ value) u := by
  intro u hu x
  by_cases hx : x = x₀
  · subst hx
    have hzero : u x = 0 := by
      by_contra hne
      exact hx₀ ⟨u, hu, hne⟩
    have horig := hsolve u hu x
    rw [hzero, mul_zero, add_zero] at horig
    rw [hzero, mul_zero, add_zero]
    exact horig
  · rw [Function.update_of_ne hx]
    exact hsolve u hu x

/-- **Off the determination set the potential is invisible.** -/
theorem exists_ne_potential_with_same_probeSolutions
    [DecidableEq X] {wave : (X → ℝ) → (X → ℝ)} {potential : X → ℝ} {probes : Set (X → ℝ)}
    (hsolve : ∀ u ∈ probes, SolvesPotentialWave wave potential u)
    {x₀ : X} (hx₀ : x₀ ∉ potentialDeterminationSet probes) :
    ∃ other : X → ℝ,
      other x₀ ≠ potential x₀ ∧
        ∀ u ∈ probes, SolvesPotentialWave wave other u := by
  refine ⟨Function.update potential x₀ (potential x₀ + 1), ?_, ?_⟩
  · rw [Function.update_self]
    intro hEq
    linarith
  · exact solvesPotentialWave_update_of_notMem_potentialDeterminationSet hsolve hx₀ _

/-- **Exact determination criterion.**

Given one potential explaining the probe family, the potential's value at an event is fixed by the
family precisely when some probe of the family is nonvanishing there. -/
theorem potential_determined_iff_mem_potentialDeterminationSet
    [DecidableEq X] {wave : (X → ℝ) → (X → ℝ)} {potential : X → ℝ} {probes : Set (X → ℝ)}
    (hsolve : ∀ u ∈ probes, SolvesPotentialWave wave potential u) (x₀ : X) :
    (∀ other : X → ℝ, (∀ u ∈ probes, SolvesPotentialWave wave other u) →
        other x₀ = potential x₀) ↔
      x₀ ∈ potentialDeterminationSet probes := by
  constructor
  · intro hdet
    by_contra hx₀
    obtain ⟨other, hne, hother⟩ :=
      exists_ne_potential_with_same_probeSolutions hsolve hx₀
    exact hne (hdet other hother)
  · rintro ⟨u, hu, hux⟩ other hother
    exact potential_eq_of_solvesPotentialWave (hother u hu) (hsolve u hu) hux

/-- A probe family with a common zero leaves a genuinely undetermined event, so the criterion is
not vacuous. -/
theorem exists_notMem_potentialDeterminationSet_of_common_zero
    {probes : Set (X → ℝ)} {x₀ : X} (hzero : ∀ u ∈ probes, u x₀ = 0) :
    x₀ ∉ potentialDeterminationSet probes := by
  rintro ⟨u, hu, hux⟩
  exact hux (hzero u hu)

/-- The empty probe family determines nothing. -/
theorem potentialDeterminationSet_empty :
    potentialDeterminationSet (∅ : Set (X → ℝ)) = ∅ := by
  ext x
  simp [potentialDeterminationSet]

end GaloisForLFunctions.HTGeometry
