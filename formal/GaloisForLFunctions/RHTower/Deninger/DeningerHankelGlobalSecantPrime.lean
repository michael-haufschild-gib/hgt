import GaloisForLFunctions.RHTower.Deninger.DeningerHankelHigherRankGroebner
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Global integral Hankel secant presentation

Finite monic c-chain normal forms contract exactly to the countable moment-variable ring.  This
module proves that the ideal of all generic `(r+1)` Hankel minors is the kernel of the ordered
`r`-atom parameterization.  It follows that this global ideal is prime over every coefficient
domain and, in particular, over `ℤ`.  The module also records homogeneity and survival of the
zeroth moment coordinate, the two inputs needed for projective-chart normalization.
-/

namespace RHTower
noncomputable section

open MvPolynomial
open scoped BigOperators MonomialOrder

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The countable generic Hankel determinantal ideal is exactly the ordered-atom secant kernel
over every commutative coefficient ring.  Every polynomial is contracted to the finite window
containing its actual variable support, where the integral Gröbner theorem applies. -/
theorem deningerGenericHankelIdeal_eq_secantParameterization_ker
    (R : Type*) [CommRing R] (r : ℕ) :
    deningerGenericHankelIdeal R r =
      RingHom.ker (deningerHankelSecantParameterization R r) := by
  classical
  apply le_antisymm
  · exact deningerGenericHankelIdeal_le_secantParameterization_ker R r
  · intro P hP
    let N := P.vars.sup id + 1
    have hvars : (P.vars : Set ℕ) ⊆ Set.range (fun i : Fin N => i.val) := by
      intro j hj
      have hjle : j ≤ P.vars.sup id := Finset.le_sup (f := id) hj
      exact ⟨⟨j, by dsimp [N]; omega⟩, rfl⟩
    obtain ⟨Q, hQ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P
      (fun i : Fin N => i.val) Fin.val_injective hvars
    have hQker : Q ∈ RingHom.ker (finiteHankelSecantParameterization R N r) := by
      apply RingHom.mem_ker.mpr
      change deningerHankelSecantParameterization R r
        (MvPolynomial.rename Fin.val Q) = 0
      rw [hQ]
      exact RingHom.mem_ker.mp hP
    have hQideal : Q ∈ finiteHankelSecantIdeal R N r := by
      rwa [finiteHankelSecantIdeal_eq_parameterization_ker]
    have hle : finiteHankelSecantIdeal R N r ≤
        Ideal.comap (MvPolynomial.rename Fin.val).toRingHom
          (deningerGenericHankelIdeal R r) := by
      rw [finiteHankelSecantIdeal, Ideal.span_le]
      rintro p ⟨c, hbound, hc, rfl⟩
      change MvPolynomial.rename Fin.val
        (finiteHankelMaximalMinorOver R c hbound) ∈
          deningerGenericHankelIdeal R r
      rw [rename_finiteHankelMaximalMinorOver]
      apply deningerMatrixMinorDet_mem
    have hrenamed := hle hQideal
    change MvPolynomial.rename Fin.val Q ∈
      deningerGenericHankelIdeal R r at hrenamed
    rw [hQ] at hrenamed
    exact hrenamed

/-- Global generic Hankel secant ideals are prime over coefficient domains. -/
theorem deningerGenericHankelIdeal_isPrime
    (R : Type*) [CommRing R] [IsDomain R] (r : ℕ) :
    (deningerGenericHankelIdeal R r).IsPrime := by
  rw [deningerGenericHankelIdeal_eq_secantParameterization_ker]
  exact deningerHankelSecantParameterization_ker_isPrime R r

theorem deningerGenericHankelIdeal_int_isPrime (r : ℕ) :
    (deningerGenericHankelIdeal ℤ r).IsPrime :=
  deningerGenericHankelIdeal_isPrime ℤ r

/-- At every positive rank, the generic secant ideal avoids the zeroth moment coordinate. -/
theorem deningerGenericHankel_X_zero_not_mem (r : ℕ) (hr : 0 < r) :
    MvPolynomial.X 0 ∉ deningerGenericHankelIdeal ℤ r := by
  intro hx
  have hxker := deningerGenericHankelIdeal_le_secantParameterization_ker ℤ r hx
  have hxzero := RingHom.mem_ker.mp hxker
  let j0 : Fin r := ⟨0, hr⟩
  let ev : MvPolynomial (DeningerHankelSecantIndex r) ℤ →+* ℤ :=
    MvPolynomial.eval₂Hom (RingHom.id ℤ) fun p =>
      if p = (j0, (0 : Fin 2)) then 1 else 0
  have heval := congrArg ev hxzero
  rw [deningerHankelSecantParameterization_X] at heval
  simp only [deningerHankelSecantMoment, map_sum, pow_zero, mul_one, map_zero] at heval
  rw [Finset.sum_eq_single j0] at heval
  · dsimp [ev] at heval
    simp at heval
  · intro j hj hj0
    simp [ev, Prod.ext_iff, hj0]
  · intro hj
    exact (hj (Finset.mem_univ j0)).elim

/-- Each generic Hankel minor is homogeneous of its matrix size. -/
theorem deningerGenericHankelMinor_isHomogeneous
    (R : Type*) [CommRing R] (r : ℕ)
    (rows cols : Fin (r + 1) → ℕ) :
    (((deningerGenericMomentHankel R).submatrix rows cols).det).IsHomogeneous (r + 1) := by
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum Finset.univ
  intro σ hσ
  have hp : (∏ i : Fin (r + 1),
      (deningerGenericMomentHankel R).submatrix rows cols (σ i) i).IsHomogeneous
      (∑ _i : Fin (r + 1), 1) := by
    apply MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 1)
    intro i hi
    exact MvPolynomial.isHomogeneous_X R _
  have hc : (MvPolynomial.C (Equiv.Perm.sign σ : ℤ) :
      MvPolynomial ℕ R).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C ℕ ((Equiv.Perm.sign σ : ℤ) : R)
  convert hc.mul hp using 1 <;> simp [deningerGenericMomentHankel]

/-- The global generic Hankel ideal is homogeneous for ordinary total degree. -/
theorem deningerGenericHankelIdeal_isHomogeneous
    (R : Type*) [CommRing R] (r : ℕ) :
    (deningerGenericHankelIdeal R r).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule ℕ R) := by
  rw [deningerGenericHankelIdeal, deningerMatrixMinorIdeal]
  apply Ideal.homogeneous_span
  intro p hp
  obtain ⟨rows, cols, rfl⟩ := hp
  exact ⟨r + 1, deningerGenericHankelMinor_isHomogeneous R r rows cols⟩

end
end RHTower
