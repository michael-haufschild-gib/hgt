import GaloisForLFunctions.RHTower.DivisorSliceGenus

/-!
# The fixed part of a slice is unconditionally trivial

Gate G4 of the genus programme asks for an exact sequence computing the Tate group
`Ĥ⁰(σ, 𝔽₂[S_t])` of a slice — the object Chevalley's ambiguous class number formula produces from
ramification data.  This module computes what that group can possibly be.

The only point of the complex plane fixed by the Hermitian reflection at height `t` is `1/2 + it`.
So the reflection-**fixed** part of a slice is a subsingleton **unconditionally**, whatever the truth
of the hypothesis, and hence `dim_{𝔽₂} Ĥ⁰` of a slice is at most one, always.  By contrast the
hypothesis is the statement that the **whole** slice is a subsingleton
(`riemannHypothesis_iff_forall_xiSlice_subsingleton`).

Consequently the two halves of the slice separate:

* the fixed part — what the genus machine computes — is already known, with no hypothesis;
* the free part — the off-line pairs — is where the entire content sits, and it is a **rank**, not a
  cohomology class.

A computation of the fixed part therefore cannot decide the hypothesis.  This closes G4 in the form
in which it was posed and leaves the sharp survivor: the target is the rank of a slice, i.e. the
number of **distinct** zeros at a single ordinate.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The reflection-fixed part of the slice at height `t`. -/
def xiSliceFixed (t : ℝ) : Set XiDivisorSupport :=
  {ρ | ρ ∈ xiSlice t ∧ supportPartner ρ = ρ}

theorem xiSliceFixed_subset (t : ℝ) : xiSliceFixed t ⊆ xiSlice t := fun _ h => h.1

/-- **The fixed part of a slice is a subsingleton, unconditionally.**  At height `t` the only point
the reflection can fix is `1/2 + it`. -/
theorem xiSliceFixed_subsingleton (t : ℝ) : (xiSliceFixed t).Subsingleton := by
  intro ρ hρ ρ' hρ'
  apply Subtype.ext
  apply Complex.ext
  · rw [(supportPartner_eq_self_iff ρ).mp hρ.2, (supportPartner_eq_self_iff ρ').mp hρ'.2]
  · have h1 : (ρ : ℂ).im = t := hρ.1
    have h2 : (ρ' : ℂ).im = t := hρ'.1
    rw [h1, h2]

/-- The fixed part is finite, of cardinality at most one. -/
theorem xiSliceFixed_finite (t : ℝ) : (xiSliceFixed t).Finite :=
  (xiSlice_finite t).subset (xiSliceFixed_subset t)

/-- **The hypothesis is that the whole slice equals its fixed part.**  Side by side with
`xiSliceFixed_subsingleton`, this is the separation of the two halves: the fixed part is a
subsingleton with no hypothesis, and the hypothesis is that the free part is empty. -/
theorem riemannHypothesis_iff_xiSlice_eq_xiSliceFixed :
    RiemannHypothesis ↔ ∀ t : ℝ, xiSlice t = xiSliceFixed t := by
  rw [riemannHypothesis_iff_supportPartner_eq_id]
  constructor
  · intro h t
    apply Set.eq_of_subset_of_subset
    · intro ρ hρ; exact ⟨hρ, h ρ⟩
    · exact xiSliceFixed_subset t
  · intro h ρ
    have : ρ ∈ xiSliceFixed ((ρ : ℂ).im) := by
      rw [← h ((ρ : ℂ).im)]; exact self_mem_xiSlice ρ
    exact this.2

/-- Two distinct points in one slice force a genuinely free orbit: the pair cannot both be fixed. -/
theorem not_both_fixed_of_two_in_slice {t : ℝ} {ρ ρ' : XiDivisorSupport}
    (hρ : ρ ∈ xiSlice t) (hρ' : ρ' ∈ xiSlice t) (hne : ρ ≠ ρ') :
    supportPartner ρ ≠ ρ ∨ supportPartner ρ' ≠ ρ' := by
  by_contra hc
  push Not at hc
  exact hne (xiSliceFixed_subsingleton t ⟨hρ, hc.1⟩ ⟨hρ', hc.2⟩)

/-- **The cohomological half carries no information.**  For every height, the fixed part of the
slice is a subsingleton whether or not the hypothesis holds; so the hypothesis is equivalent to a
statement about the slice's *rank*, and is invisible to any computation of the fixed part alone. -/
theorem xiSliceFixed_subsingleton_unconditional :
    (∀ t : ℝ, (xiSliceFixed t).Subsingleton) ∧
      (RiemannHypothesis ↔ ∀ t : ℝ, (xiSlice t).Subsingleton) :=
  ⟨xiSliceFixed_subsingleton, riemannHypothesis_iff_forall_xiSlice_subsingleton⟩

end

end RHTower
