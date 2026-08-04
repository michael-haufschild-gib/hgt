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

namespace RHTower

open Complex

section Naturality

variable {r s n : ℕ}

/-- The coordinates of a class of a constant form in the basis of the cohomology are the
coordinates of the form in the basis of determinant forms. -/
theorem deningerCohomologyBasis_repr (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (T : {S : Finset (Fin r) // S.card = n + 1}) :
    (deningerCohomologyBasis r n).repr (deningerConstantClass r n α) T =
      deningerSubsetCoeff α T.1 := by
  rw [deningerCohomologyBasis, Module.Basis.map_repr]
  show (deningerDetFormBasis r (n + 1)).repr
    ((deningerCohomologyEquiv r n).symm (deningerConstantClass r n α)) T = _
  rw [show (deningerCohomologyEquiv r n).symm (deningerConstantClass r n α) = α from
    (deningerCohomologyEquiv r n).symm_apply_apply α]
  exact deningerDetFormBasis_repr α T

/-- **The matrix of the map induced on cohomology by a transition, in the bases of the classes of
the logarithmic wedges, is the matrix of minors of the exponent matrix.** -/
theorem deningerCohomologyBasis_repr_map (m : Fin r → Fin s → ℤ)
    (S : {S : Finset (Fin r) // S.card = n + 1})
    (T : {S : Finset (Fin s) // S.card = n + 1}) :
    (deningerCohomologyBasis s n).repr
        (deningerCohomologyMap m n (deningerCohomologyBasis r n S)) T =
      Matrix.det (Matrix.of fun a b =>
        ((m (deningerSubsetTuple S a) (deningerSubsetTuple T b) : ℤ) : ℂ)) := by
  have hbasis : deningerCohomologyBasis r n S =
      deningerConstantClass r n (deningerDetForm (deningerSubsetTuple S)) := by
    rw [deningerCohomologyBasis, Module.Basis.map_apply, deningerDetFormBasis_apply]
    rfl
  rw [hbasis, deningerCohomologyMap_constantClass, deningerCohomologyBasis_repr,
    deningerSubsetCoeff_detForm_comp _ _ _ T.2]
  rfl

/-- **The matrix of the exterior power of the transposed exponent matrix, in the bases of the
exterior powers, is the same matrix of minors.** -/
theorem deningerExteriorMap_basis_repr (m : Fin r → Fin s → ℤ)
    (S : {S : Finset (Fin r) // S.card = n + 1})
    (T : {S : Finset (Fin s) // S.card = n + 1}) :
    ((Pi.basisFun ℂ (Fin s)).exteriorPower (n + 1)).repr
        (exteriorPower.map (n + 1)
          ((deningerMatrixCLM (fun j i => m i j)).toLinearMap)
          ((Pi.basisFun ℂ (Fin r)).exteriorPower (n + 1) S)) T =
      Matrix.det (Matrix.of fun a b =>
        ((m (deningerSubsetTuple S a) (deningerSubsetTuple T b) : ℤ) : ℂ)) := by
  have hS : (Pi.basisFun ℂ (Fin r)).exteriorPower (n + 1) S =
      exteriorPower.ιMulti ℂ (n + 1)
        (fun a => (Pi.basisFun ℂ (Fin r)) (deningerSubsetTuple S a)) := by
    rw [exteriorPower.basis_apply]
    rfl
  rw [hS, exteriorPower.map_apply_ιMulti, ← Module.Basis.coord_apply,
    exteriorPower.basis_coord, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  ext a b
  show (Pi.basisFun ℂ (Fin s)).coord (deningerSubsetTuple T b)
      ((deningerMatrixCLM (fun j i => m i j)).toLinearMap
        ((Pi.basisFun ℂ (Fin r)) (deningerSubsetTuple S a))) =
    ((m (deningerSubsetTuple S a) (deningerSubsetTuple T b) : ℤ) : ℂ)
  rw [Module.Basis.coord_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  show deningerMatrixCLM (fun j i => m i j)
      (Pi.single (deningerSubsetTuple S a) (1 : ℂ)) (deningerSubsetTuple T b) = _
  rw [deningerMatrixCLM_single]

/-- **The comparison of the cohomology of a stage with the exterior power of the covering space is
natural in the lattice**: it intertwines the map induced by a transition with the exterior power of
the transposed exponent matrix.  Both maps have the matrix of minors of the exponent matrix in the
corresponding bases. -/
theorem deningerCohomologyExterior_naturality (m : Fin r → Fin s → ℤ) (n : ℕ)
    (ξ : deningerCohomology r n) :
    deningerCohomologyExteriorEquiv s n (deningerCohomologyMap m n ξ) =
      exteriorPower.map (n + 1) ((deningerMatrixCLM (fun j i => m i j)).toLinearMap)
        (deningerCohomologyExteriorEquiv r n ξ) := by
  classical
  have hbasis : ∀ S : {S : Finset (Fin r) // S.card = n + 1},
      deningerCohomologyExteriorEquiv s n
          (deningerCohomologyMap m n (deningerCohomologyBasis r n S)) =
        exteriorPower.map (n + 1) ((deningerMatrixCLM (fun j i => m i j)).toLinearMap)
          (deningerCohomologyExteriorEquiv r n (deningerCohomologyBasis r n S)) := by
    intro S
    have hleft : deningerCohomologyExteriorEquiv s n
        (deningerCohomologyMap m n (deningerCohomologyBasis r n S)) =
        ∑ T : {S : Finset (Fin s) // S.card = n + 1},
          (deningerCohomologyBasis s n).repr
              (deningerCohomologyMap m n (deningerCohomologyBasis r n S)) T •
            (Pi.basisFun ℂ (Fin s)).exteriorPower (n + 1) T := by
      conv_lhs => rw [← Module.Basis.sum_repr (deningerCohomologyBasis s n)
        (deningerCohomologyMap m n (deningerCohomologyBasis r n S))]
      rw [map_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [map_smul]
      congr 1
      exact Module.Basis.equiv_apply _ _ _ _
    have hright : exteriorPower.map (n + 1)
        ((deningerMatrixCLM (fun j i => m i j)).toLinearMap)
        (deningerCohomologyExteriorEquiv r n (deningerCohomologyBasis r n S)) =
        ∑ T : {S : Finset (Fin s) // S.card = n + 1},
          ((Pi.basisFun ℂ (Fin s)).exteriorPower (n + 1)).repr
              (exteriorPower.map (n + 1)
                ((deningerMatrixCLM (fun j i => m i j)).toLinearMap)
                ((Pi.basisFun ℂ (Fin r)).exteriorPower (n + 1) S)) T •
            (Pi.basisFun ℂ (Fin s)).exteriorPower (n + 1) T := by
      rw [show deningerCohomologyExteriorEquiv r n (deningerCohomologyBasis r n S) =
        (Pi.basisFun ℂ (Fin r)).exteriorPower (n + 1) S from
          Module.Basis.equiv_apply _ _ _ _]
      exact (Module.Basis.sum_repr _ _).symm
    rw [hleft, hright]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [deningerCohomologyBasis_repr_map, deningerExteriorMap_basis_repr]
  have hlin : (deningerCohomologyExteriorEquiv s n).toLinearMap ∘ₗ
      (deningerCohomologyMap m n) =
      (exteriorPower.map (n + 1) ((deningerMatrixCLM (fun j i => m i j)).toLinearMap)) ∘ₗ
        (deningerCohomologyExteriorEquiv r n).toLinearMap :=
    Module.Basis.ext (deningerCohomologyBasis r n) hbasis
  exact congrArg (fun L : deningerCohomology r n →ₗ[ℂ] ⋀[ℂ]^(n + 1) (Fin s → ℂ) => L ξ) hlin

end Naturality

end RHTower
