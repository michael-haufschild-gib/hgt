import GaloisForLFunctions.HTGeometry.SymmetricCoefficientField

/-!
# The generic polynomial and its splitting field

The product of the linear factors attached to the variables is invariant under permuting them, so
each of its coefficients is symmetric and the product descends to a polynomial over the symmetric
part.  That is the generic monic polynomial of degree `d`.

It splits in the rational function field by construction, and its roots generate that field over
the symmetric part, because a subalgebra of a finite extension is a field and the variables
generate the polynomial ring.  So the rational function field is its splitting field.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Polynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- The variables, read as rational functions: the roots of the generic polynomial. -/
noncomputable def genericRoot (K : Type*) [Field K] (d : ℕ) (i : Fin d) :
    SymmetricRationalField K d :=
  algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) (MvPolynomial.X i)

theorem smul_genericRoot (e : Equiv.Perm (Fin d)) (i : Fin d) :
    e • genericRoot K d i = genericRoot K d (e i) := by
  rw [genericRoot, ← algebraMap_smul_mvPolynomial, perm_smul_X]
  rfl

/-- The generic monic polynomial, read over the rational function field. -/
noncomputable def genericMonicF (K : Type*) [Field K] (d : ℕ) :
    Polynomial (SymmetricRationalField K d) :=
  ∏ i : Fin d, (Polynomial.X - Polynomial.C (genericRoot K d i))

theorem monic_genericMonicF : (genericMonicF K d).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _

theorem natDegree_genericMonicF : (genericMonicF K d).natDegree = d := by
  rw [genericMonicF, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (genericRoot K d i)]
  simp

/-- **The generic polynomial is permutation invariant.** -/
theorem map_genericMonicF (e : Equiv.Perm (Fin d)) :
    Polynomial.map
        (MulSemiringAction.toRingHom (Equiv.Perm (Fin d)) (SymmetricRationalField K d) e)
        (genericMonicF K d) = genericMonicF K d := by
  rw [genericMonicF, Polynomial.map_prod]
  have hterm : ∀ i : Fin d,
      Polynomial.map
          (MulSemiringAction.toRingHom (Equiv.Perm (Fin d)) (SymmetricRationalField K d) e)
          (Polynomial.X - Polynomial.C (genericRoot K d i)) =
        Polynomial.X - Polynomial.C (genericRoot K d (e i)) := by
    intro i
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 1
    congr 1
    exact smul_genericRoot e i
  rw [Finset.prod_congr rfl fun i _ => hterm i]
  exact Equiv.prod_comp e fun i => Polynomial.X - Polynomial.C (genericRoot K d i)

theorem coeff_genericMonicF_mem (k : ℕ) :
    (genericMonicF K d).coeff k ∈ symmetricPart K d := by
  have hfix : ∀ e : Equiv.Perm (Fin d), e • (genericMonicF K d).coeff k =
      (genericMonicF K d).coeff k := by
    intro e
    have h := congrArg (fun p : Polynomial (SymmetricRationalField K d) => p.coeff k)
      (map_genericMonicF (K := K) (d := d) e)
    rwa [Polynomial.coeff_map] at h
  exact hfix

theorem coeffs_genericMonicF_subset :
    ↑(genericMonicF K d).coeffs ⊆ ((symmetricPart K d).toSubring : Set (SymmetricRationalField K d)) := by
  intro c hc
  obtain ⟨k, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc
  exact coeff_genericMonicF_mem k

/-- **The generic monic polynomial of degree `d`**, over the symmetric part. -/
noncomputable def genericMonic (K : Type*) [Field K] (d : ℕ) :
    Polynomial (symmetricPart K d) :=
  (genericMonicF K d).toSubring (symmetricPart K d).toSubring coeffs_genericMonicF_subset

theorem map_genericMonic :
    Polynomial.map (algebraMap (symmetricPart K d) (SymmetricRationalField K d))
      (genericMonic K d) = genericMonicF K d :=
  Polynomial.map_toSubring _ _ _

theorem genericMonic_ne_zero : genericMonic K d ≠ 0 := by
  intro hcon
  have h := map_genericMonic (K := K) (d := d)
  rw [hcon, Polynomial.map_zero] at h
  exact (monic_genericMonicF (K := K) (d := d)).ne_zero h.symm

/-! ## Splitting -/

theorem splits_genericMonic :
    Polynomial.Splits (algebraMap (symmetricPart K d) (SymmetricRationalField K d))
      (genericMonic K d) := by
  rw [Polynomial.splits_iff_exists_multiset]
  refine ⟨(Finset.univ.val : Multiset (Fin d)).map (genericRoot K d), ?_⟩
  rw [map_genericMonic, genericMonicF]
  rw [Polynomial.leadingCoeff, ← Polynomial.coeff_map (algebraMap (symmetricPart K d)
    (SymmetricRationalField K d))]
  rw [map_genericMonic]
  rw [show (genericMonicF K d).natDegree = d from natDegree_genericMonicF]
  sorry

end GaloisForLFunctions.HTGeometry
