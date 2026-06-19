import GaloisForLFunctions.Core

/-!
# Orbit-balance: finite augmentation-kernel algebra

This file formalizes the elementary finite-support algebra behind the
`σ`-orbit-balance criterion in
`docs/drafts/pipeline/2-fully-proven/two-sources-of-hypertranscendence.md`.

On a single orbit, a rational divisor is modeled by a finitely supported
integer-valued function. The orbit degree is the augmentation map, and a
degree-zero finite divisor decomposes as a finite sum of balanced point-masses
against any chosen base point.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- The finite orbit-degree/augmentation of an integer-valued finitely
supported divisor on an orbit. -/
def orbitDegree {α : Type*} (D : α →₀ ℤ) : ℤ :=
  D.sum (fun _ n => n)

/-- A balanced point-mass `n[a]-n[b]` has orbit degree zero. -/
theorem orbitDegree_single_sub_single {α : Type*} [DecidableEq α] (a b : α) (n : ℤ) :
    orbitDegree (Finsupp.single a n - Finsupp.single b n) = 0 := by
  by_cases hab : a = b
  · subst hab
    simp [orbitDegree]
  · rw [orbitDegree, Finsupp.sum_sub_index]
    · simp
    · intro x y z
      rfl

/-- **Finite orbit-balance decomposition.** If an integer-valued finite divisor
has orbit degree zero, then it is a finite sum of balanced point-masses against
any chosen base point. This is the augmentation-kernel core of the paper
statement that degree-zero finite orbit divisors telescope. -/
theorem eq_sum_single_sub_base_of_orbitDegree_zero {α : Type*} [DecidableEq α]
    (base : α) (D : α →₀ ℤ) (hD : orbitDegree D = 0) :
    D = D.support.sum (fun a => Finsupp.single a (D a) - Finsupp.single base (D a)) := by
  have hbase : D.support.sum (fun a => Finsupp.single base (D a)) = (0 : α →₀ ℤ) := by
    ext x
    by_cases hx : x = base
    · subst hx
      simpa [orbitDegree] using hD
    · simp [hx]
  calc
    D = D.support.sum (fun a => Finsupp.single a (D a)) := by
      simpa [Finsupp.sum] using (Finsupp.sum_single D).symm
    _ = D.support.sum (fun a => Finsupp.single a (D a) - Finsupp.single base (D a)) := by
      rw [Finset.sum_sub_distrib, hbase, sub_zero]

end

end GaloisForLFunctions
