import Mathlib

/-!
# The positive cone inside finite-support tail fibres

Differential tail invariants quotient coefficient functions by finite-support changes.  Pointwise
positivity does not descend to that quotient.  This file gives the exact replacement: a tail fibre
meets the positive cone precisely when the negative support of one (hence every) representative is
finite, and then the positive representatives are exactly the finite-support corrections lying
above the coordinatewise lower wall.

The result is deliberately independent of Dirichlet series, Herglotz functions, and RH.  It is the
bare coefficient geometry needed when a tail matroid is coupled to a positivity constraint.
-/

namespace HTGeometry

noncomputable section

/-- Two coefficient functions define the same tail when they differ at only finitely many
coordinates. -/
def FiniteTailEquivalent {ι : Type*} (a b : ι → ℝ) : Prop :=
  {i | a i ≠ b i}.Finite

/-- The negative coordinates of a coefficient function. -/
def negativeSupport {ι : Type*} (a : ι → ℝ) : Set ι :=
  {i | a i < 0}

/-- Coordinatewise nonnegativity. -/
def InPositiveCone {ι : Type*} (a : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ a i

theorem finiteTailEquivalent_refl {ι : Type*} (a : ι → ℝ) :
    FiniteTailEquivalent a a := by
  simp [FiniteTailEquivalent]

theorem finiteTailEquivalent_symm {ι : Type*} {a b : ι → ℝ}
    (h : FiniteTailEquivalent a b) :
    FiniteTailEquivalent b a := by
  apply h.subset
  intro i hi
  simpa only [Set.mem_setOf_eq] using Ne.symm hi

theorem finiteTailEquivalent_trans {ι : Type*} {a b c : ι → ℝ}
    (hab : FiniteTailEquivalent a b) (hbc : FiniteTailEquivalent b c) :
    FiniteTailEquivalent a c := by
  apply (hab.union hbc).subset
  intro i hi
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_cases hab' : a i = b i
  · exact Or.inr fun hbc' => hi (hab'.trans hbc')
  · exact Or.inl hab'

/-- Exact correction form of membership in the positive part of a tail fibre. -/
theorem inPositiveCone_and_finiteTailEquivalent_iff
    {ι : Type*} (a b : ι → ℝ) :
    InPositiveCone b ∧ FiniteTailEquivalent a b ↔
      {i | a i ≠ b i}.Finite ∧ ∀ i, -a i ≤ b i - a i := by
  constructor
  · rintro ⟨hb, htail⟩
    refine ⟨htail, ?_⟩
    intro i
    linarith [hb i]
  · rintro ⟨htail, hwall⟩
    refine ⟨?_, htail⟩
    intro i
    linarith [hwall i]

/-- **Tail-cone fibre law.**  A finite-support tail fibre contains a nonnegative representative
if and only if the negative support of the given representative is finite. -/
theorem exists_positiveCone_finiteTailEquivalent_iff
    {ι : Type*} (a : ι → ℝ) :
    (∃ b : ι → ℝ, InPositiveCone b ∧ FiniteTailEquivalent a b) ↔
      (negativeSupport a).Finite := by
  constructor
  · rintro ⟨b, hb, htail⟩
    apply htail.subset
    intro i hi
    simp only [negativeSupport, Set.mem_setOf_eq] at hi
    simp only [Set.mem_setOf_eq]
    exact ne_of_lt (lt_of_lt_of_le hi (hb i))
  · intro hneg
    let b : ι → ℝ := fun i => max (a i) 0
    refine ⟨b, ?_, ?_⟩
    · intro i
      exact le_max_right _ _
    · apply hneg.subset
      intro i hi
      simp only [b, Set.mem_setOf_eq] at hi
      simp only [negativeSupport, Set.mem_setOf_eq]
      by_contra hai
      have ha0 : 0 ≤ a i := le_of_not_gt hai
      exact hi (max_eq_left ha0).symm

/-- Every tail fibre containing a positive representative also contains a nonpositive one, as
soon as the coordinate set is nonempty.  Positivity therefore cannot be a predicate of the tail
class alone. -/
theorem exists_not_positiveCone_finiteTailEquivalent
    {ι : Type*} [Nonempty ι] (a : ι → ℝ) :
    ∃ b : ι → ℝ, FiniteTailEquivalent a b ∧ ¬InPositiveCone b := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  let b : ι → ℝ := fun i => if i = i₀ then -1 else a i
  refine ⟨b, ?_, ?_⟩
  · apply Set.Finite.subset (Set.finite_singleton i₀)
    intro i hi
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact hi (by simp [b, hne])
  · intro hb
    have := hb i₀
    simp [b] at this
    norm_num at this

end

end HTGeometry
