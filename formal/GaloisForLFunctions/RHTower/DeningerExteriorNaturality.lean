import GaloisForLFunctions.RHTower.DeningerCohomologyFunctor

/-!
# The comparison with the exterior power is natural in the lattice

The coordinates of a constant alternating form in the basis of determinant forms are its coefficients
along the `k`-element sets of coordinates, and the coordinates of an exterior product of coordinate
vectors in the basis of the exterior power are the corresponding minors.  Since a transition map
takes a determinant form to the composition with its exponent matrix, whose coefficients are exactly
those minors, the comparison of the cohomology of a stage with the exterior power of the covering
space intertwines the map induced by a transition with the exterior power of the transposed matrix.

* `deningerDetFormBasis_repr` : the coordinates in the basis of determinant forms.
* `deningerCohomologyExterior_naturality` : the comparison is natural in the lattice.
-/

set_option maxSynthPendingDepth 3

namespace RHTower

open Complex

section BasisRepr

variable {r k : ℕ}

/-- The component of a constant form along a `k`-element set is its coefficient times the
determinant form of that set. -/
theorem deningerSubsetForm_eq (α : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ)
    (S : {S : Finset (Fin r) // S.card = k}) :
    deningerSubsetForm α S.1 =
      deningerSubsetCoeff α S.1 • deningerDetForm (deningerSubsetTuple S) := by
  rw [deningerSubsetForm, dif_pos S.2, deningerSubsetCoeff, dif_pos S.2]
  rfl

/-- **A constant alternating form is the sum of its components along the `k`-element sets.** -/
theorem deningerDetForm_subtype_sum (α : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ) :
    α = ∑ S : {S : Finset (Fin r) // S.card = k},
      deningerSubsetCoeff α S.1 • deningerDetForm (deningerSubsetTuple S) := by
  classical
  have h1 : ∑ s : Finset (Fin r), deningerSubsetForm α s =
      ∑ s ∈ Finset.univ.filter (fun s : Finset (Fin r) => s.card = k),
        deningerSubsetForm α s := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_).symm
    rw [deningerSubsetForm, dif_neg (by simpa using hs)]
  have h2 : ∑ s ∈ Finset.univ.filter (fun s : Finset (Fin r) => s.card = k),
      deningerSubsetForm α s =
      ∑ S : {S : Finset (Fin r) // S.card = k}, deningerSubsetForm α S.1 :=
    Finset.sum_subtype _ (fun s => by simp) _
  have h3 : ∑ S : {S : Finset (Fin r) // S.card = k}, deningerSubsetForm α S.1 =
      ∑ S : {S : Finset (Fin r) // S.card = k},
        deningerSubsetCoeff α S.1 • deningerDetForm (deningerSubsetTuple S) :=
    Finset.sum_congr rfl fun S _ => deningerSubsetForm_eq α S
  rw [← h3, ← h2, ← h1]
  exact deningerDetForm_span α

/-- **The coordinates of a constant alternating form in the basis of determinant forms** are its
coefficients along the `k`-element sets. -/
theorem deningerDetFormBasis_repr (α : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ)
    (T : {S : Finset (Fin r) // S.card = k}) :
    (deningerDetFormBasis r k).repr α T = deningerSubsetCoeff α T.1 := by
  classical
  conv_lhs => rw [deningerDetForm_subtype_sum α]
  rw [map_sum]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single T]
  · rw [map_smul, ← deningerDetFormBasis_apply T, Module.Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_same]
  · intro S _ hST
    rw [map_smul, ← deningerDetFormBasis_apply S, Module.Basis.repr_self,
      Finsupp.smul_single, Finsupp.single_apply, if_neg hST]
  · intro h
    exact absurd (Finset.mem_univ T) h

end BasisRepr

end RHTower
