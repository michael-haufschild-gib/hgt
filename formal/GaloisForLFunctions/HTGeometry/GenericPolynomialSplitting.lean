import GaloisForLFunctions.HTGeometry.SymmetricCoefficientField
import Mathlib.FieldTheory.PolynomialGaloisGroup

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
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_genericMonicF : (genericMonicF K d).natDegree = d := by
  rw [genericMonicF,
    natDegree_prod_of_monic _ _ fun (i : Fin d) _ => monic_X_sub_C (genericRoot K d i)]
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
    (Polynomial.map (algebraMap (symmetricPart K d) (SymmetricRationalField K d))
      (genericMonic K d)).Splits := by
  rw [map_genericMonic, genericMonicF]
  exact Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _

theorem genericRoot_mem_rootSet (i : Fin d) :
    genericRoot K d i ∈ (genericMonic K d).rootSet (SymmetricRationalField K d) := by
  rw [Polynomial.mem_rootSet]
  refine ⟨genericMonic_ne_zero, ?_⟩
  have heval : Polynomial.aeval (genericRoot K d i) (genericMonic K d) =
      Polynomial.eval (genericRoot K d i) (genericMonicF K d) := by
    rw [← map_genericMonic, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rw [heval, genericMonicF, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- **The roots generate the rational function field over the symmetric part.** -/
theorem adjoin_rootSet_genericMonic :
    Algebra.adjoin (symmetricPart K d)
      ((genericMonic K d).rootSet (SymmetricRationalField K d)) = ⊤ := by
  classical
  set S := Algebra.adjoin (symmetricPart K d)
    ((genericMonic K d).rootSet (SymmetricRationalField K d)) with hS
  have hroots : ∀ i : Fin d, genericRoot K d i ∈ S := fun i =>
    Algebra.subset_adjoin (genericRoot_mem_rootSet i)
  have hpoly : ∀ p : MvPolynomial (Fin d) K,
      algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        have hC : algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)
            (MvPolynomial.C a) = algebraMap K (SymmetricRationalField K d) a := by
          rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin d) K)
            (SymmetricRationalField K d)]
          rfl
        have hmem : algebraMap K (SymmetricRationalField K d) a ∈ symmetricPart K d :=
          (symmetricPartField K d).algebraMap_mem' a
        rw [hC]
        exact Subalgebra.algebraMap_mem S ⟨_, hmem⟩
    | add p q hp hq =>
        rw [map_add]
        exact add_mem hp hq
    | mul_X p i hp =>
        rw [map_mul]
        exact mul_mem hp (hroots i)
  have hfield : IsField S := Subalgebra.isField_of_algebraic S
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d)) :=
    IsFractionRing.injective _ _
  refine le_antisymm le_top fun z _ => ?_
  obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective
    (A := MvPolynomial (Fin d) K) (K := SymmetricRationalField K d) z
  have hb0 : algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) b ≠ 0 :=
    fun hcon => nonZeroDivisors.ne_zero hb (hinj (by rw [hcon, map_zero]))
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel
    (a := (⟨_, hpoly b⟩ : S)) (fun hcon => hb0 (congrArg Subtype.val hcon))
  have hyF : algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) b * (y : SymmetricRationalField K d) = 1 :=
    congrArg Subtype.val hy
  have hyinv : (y : SymmetricRationalField K d) =
      (algebraMap (MvPolynomial (Fin d) K) (SymmetricRationalField K d) b)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm] at hyF; exact hyF)
  rw [← hz, div_eq_mul_inv, ← hyinv]
  exact mul_mem (hpoly a) y.2

instance isSplittingField_genericMonic (K : Type*) [Field K] (d : ℕ) :
    Polynomial.IsSplittingField (symmetricPart K d) (SymmetricRationalField K d)
      (genericMonic K d) :=
  ⟨splits_genericMonic, adjoin_rootSet_genericMonic⟩

/-! ## The Galois group of the generic polynomial -/

/-- **The Galois group of the generic monic polynomial of degree `d` is the full symmetric
group.** -/
noncomputable def genericMonicGaloisEquiv (K : Type*) [Field K] (d : ℕ) :
    Equiv.Perm (Fin d) ≃* (genericMonic K d).Gal :=
  (symmetricGaloisEquiv K d).trans
    (AlgEquiv.autCongr
      (Polynomial.IsSplittingField.algEquiv (SymmetricRationalField K d) (genericMonic K d)))

theorem card_genericMonicGal (K : Type*) [Field K] (d : ℕ) :
    Nat.card (genericMonic K d).Gal = Nat.factorial d := by
  rw [← Nat.card_congr (genericMonicGaloisEquiv K d).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]

theorem natDegree_genericMonic : (genericMonic K d).natDegree = d := by
  have h := congrArg Polynomial.natDegree (map_genericMonic (K := K) (d := d))
  rwa [Polynomial.natDegree_map_eq_of_injective
    (algebraMap (symmetricPart K d) (SymmetricRationalField K d)).injective,
    natDegree_genericMonicF] at h

end GaloisForLFunctions.HTGeometry
