import GaloisForLFunctions.HTGeometry.GammaIterationHypertranscendence

/-!
# The Gamma microscope domain is inhabited

The microscope domain of a region is the set of nonzero points whose negated reciprocal lies in the
region.  At iteration order zero the regular set is everything, so the microscope domain there is
exactly the punctured plane — nonempty, and containing every nonzero point.

At higher order the membership unfolds to two checkable conditions on the negated reciprocal, which
is the form the iteration arguments consume.
-/

namespace GaloisForLFunctions

/-- Membership in the microscope domain is nonvanishing together with membership of the negated
reciprocal. -/
theorem mem_localGammaMicroscopeDomain_iff {Ω : Set ℂ} {x : ℂ} :
    x ∈ localGammaMicroscopeDomain Ω ↔ x ≠ 0 ∧ (-x)⁻¹ ∈ Ω := Iff.rfl

/-- **At order zero the microscope domain is the punctured plane.** -/
theorem mem_localGammaMicroscopeDomain_regularSet_zero {x : ℂ} (hx : x ≠ 0) :
    x ∈ localGammaMicroscopeDomain (gammaIterateRegularSet 0) :=
  ⟨hx, by rw [gammaIterateRegularSet_zero]; exact Set.mem_univ _⟩

/-- Hence the microscope domain at order zero is nonempty. -/
theorem localGammaMicroscopeDomain_regularSet_zero_nonempty :
    (localGammaMicroscopeDomain (gammaIterateRegularSet 0)).Nonempty :=
  ⟨1, mem_localGammaMicroscopeDomain_regularSet_zero one_ne_zero⟩

/-- The microscope domain is monotone in the region. -/
theorem localGammaMicroscopeDomain_mono {Ω Ω' : Set ℂ} (h : Ω ⊆ Ω') :
    localGammaMicroscopeDomain Ω ⊆ localGammaMicroscopeDomain Ω' :=
  fun _ hx => ⟨hx.1, h hx.2⟩

end GaloisForLFunctions
