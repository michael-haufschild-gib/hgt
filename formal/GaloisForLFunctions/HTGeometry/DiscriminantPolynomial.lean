import GaloisForLFunctions.HTGeometry.VandermondeSign
import GaloisForLFunctions.HTGeometry.SymmetricCoefficientField

/-!
# The discriminant is a polynomial in the elementary symmetric functions

Renaming the variables multiplies the Vandermonde product of the coordinates by the sign, so its
square is a symmetric polynomial.  By the fundamental theorem of symmetric polynomials it is
therefore a polynomial in the elementary symmetric functions.

Those are the coefficients of the generic polynomial up to sign, so the discriminant is a
polynomial -- not merely a rational function -- in the coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- The Vandermonde product of the coordinates. -/
noncomputable def vandermondePoly (K : Type*) [Field K] (d : ℕ) : MvPolynomial (Fin d) K :=
  vandermondeProd (fun i : Fin d => MvPolynomial.X i)

theorem rename_vandermondePoly (e : Equiv.Perm (Fin d)) :
    MvPolynomial.rename (e : Fin d → Fin d) (vandermondePoly K d) =
      (Equiv.Perm.sign e : ℤ) • vandermondePoly K d := by
  have hcomp : MvPolynomial.rename (e : Fin d → Fin d) (vandermondePoly K d) =
      vandermondeProd ((fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) K)) ∘ e) := by
    rw [vandermondePoly, vandermondeProd, vandermondeProd, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, MvPolynomial.rename_X, MvPolynomial.rename_X]
    rfl
  rw [hcomp, vandermondeProd_comp, vandermondePoly]

/-- **The square of the Vandermonde product is symmetric.** -/
theorem isSymmetric_sq_vandermondePoly :
    (vandermondePoly K d * vandermondePoly K d).IsSymmetric := by
  intro e
  rw [map_mul, rename_vandermondePoly]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h1 | h1
  · rw [h1]
    simp
  · rw [h1]
    simp only [Units.coe_neg_one, neg_smul, one_smul, neg_mul_neg]

/-- **The discriminant is a polynomial in the elementary symmetric functions.** -/
theorem sq_vandermondePoly_mem_adjoin :
    vandermondePoly K d * vandermondePoly K d ∈
      Algebra.adjoin K (Set.range fun i : Fin d => MvPolynomial.esymm (Fin d) K ((i : ℕ) + 1)) := by
  obtain ⟨P, hP⟩ := MvPolynomial.esymmAlgHom_surjective (σ := Fin d) (R := K) (n := d)
    (by simp) ⟨vandermondePoly K d * vandermondePoly K d,
      (MvPolynomial.mem_symmetricSubalgebra _).2 isSymmetric_sq_vandermondePoly⟩
  have hval : vandermondePoly K d * vandermondePoly K d =
      MvPolynomial.aeval (fun i : Fin d => MvPolynomial.esymm (Fin d) K ((i : ℕ) + 1)) P := by
    rw [← MvPolynomial.esymmAlgHom_apply, hP]
  rw [hval, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨P, rfl⟩

/-! ## The top elementary symmetric function does not divide the discriminant -/

/-- The substitution setting the last coordinate to zero. -/
noncomputable def zeroLast (K : Type*) [Field K] (d : ℕ) (hd : 0 < d) (i : Fin d) :
    MvPolynomial (Fin d) K :=
  if i = (⟨d - 1, by omega⟩ : Fin d) then 0 else MvPolynomial.X i

theorem zeroLast_injective (hd : 0 < d) : Function.Injective (zeroLast K d hd) := by
  intro i j hij
  rw [zeroLast, zeroLast] at hij
  by_cases hi : i = (⟨d - 1, by omega⟩ : Fin d) <;> by_cases hj : j = (⟨d - 1, by omega⟩ : Fin d)
  · rw [hi, hj]
  · rw [if_pos hi, if_neg hj] at hij
    exact absurd hij.symm (MvPolynomial.X_ne_zero j)
  · rw [if_neg hi, if_pos hj] at hij
    exact absurd hij (MvPolynomial.X_ne_zero i)
  · rw [if_neg hi, if_neg hj] at hij
    exact MvPolynomial.X_injective hij

theorem esymm_top_eq_prod : MvPolynomial.esymm (Fin d) K d = ∏ i : Fin d, MvPolynomial.X i := by
  have hcard : (Finset.univ : Finset (Fin d)).card = d := by simp
  have h : Finset.powersetCard d (Finset.univ : Finset (Fin d)) = {Finset.univ} := by
    have hself := Finset.powersetCard_self (Finset.univ : Finset (Fin d))
    rwa [hcard] at hself
  rw [MvPolynomial.esymm, h, Finset.sum_singleton]

theorem aeval_zeroLast_esymm_top (hd : 0 < d) :
    MvPolynomial.aeval (zeroLast K d hd) (MvPolynomial.esymm (Fin d) K d) = 0 := by
  rw [esymm_top_eq_prod, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨d - 1, by omega⟩ : Fin d)) ?_
  rw [MvPolynomial.aeval_X, zeroLast, if_pos rfl]

theorem aeval_zeroLast_vandermondePoly (hd : 0 < d) :
    MvPolynomial.aeval (zeroLast K d hd) (vandermondePoly K d) =
      vandermondeProd (zeroLast K d hd) := by
  rw [vandermondePoly, vandermondeProd, vandermondeProd, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_X]

/-- **The top elementary symmetric function does not divide the discriminant.**  Setting one root
to zero kills the product of the roots while leaving all the differences distinct. -/
theorem esymm_top_not_dvd_sq_vandermondePoly (hd : 0 < d) :
    ¬ (MvPolynomial.esymm (Fin d) K d ∣ vandermondePoly K d * vandermondePoly K d) := by
  rintro ⟨G, hG⟩
  have hspec := congrArg (MvPolynomial.aeval (zeroLast K d hd)) hG
  rw [map_mul, map_mul, aeval_zeroLast_esymm_top hd, zero_mul,
    aeval_zeroLast_vandermondePoly hd] at hspec
  have hne : vandermondeProd (zeroLast K d hd) ≠ 0 :=
    vandermondeProd_ne_zero (zeroLast_injective hd)
  exact hne (by
    rcases mul_eq_zero.1 hspec with h | h
    · exact h
    · exact h)

end GaloisForLFunctions.HTGeometry
