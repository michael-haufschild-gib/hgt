import GaloisForLFunctions.HTGeometry.TorusMonomialFamily
import GaloisForLFunctions.HTGeometry.DifferentialIndependentTransfer
import GaloisForLFunctions.HTGeometry.HypertranscendentalPow
import GaloisForLFunctions.HTGeometry.KummerDegreeBound

/-!
# Monomial families of a differentially independent palette

A nonsingular integer matrix carries a differentially independent family to another one: the
adjugate identity exhibits a power of each original coordinate as a monomial in the new ones, so the
new family spans the old in the differential matroid, and a spanning family of the same size is
independent.

Distinct rows give distinct monomials because a nontrivial monomial in algebraically independent
elements is never `1`, so the new family is injective as well.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

section Monomials

variable {C E ι : Type*} [CommRing C] [Nontrivial C] [CommRing E] [Algebra C E] [Fintype ι]
  [DecidableEq ι]

/-- Equal monomials in an algebraically independent family have equal exponents. -/
theorem exponent_eq_of_prod_pow_eq {x : ι → E} (hx : AlgebraicIndependent C x) {p q : ι → ℕ}
    (h : ∏ i, x i ^ p i = ∏ i, x i ^ q i) : p = q := by
  classical
  have haeval : (MvPolynomial.aeval x) (∏ i, (MvPolynomial.X i : MvPolynomial ι C) ^ p i)
      = (MvPolynomial.aeval x) (∏ i, (MvPolynomial.X i : MvPolynomial ι C) ^ q i) := by
    simpa using h
  have hpoly : (∏ i, (MvPolynomial.X i : MvPolynomial ι C) ^ p i)
      = ∏ i, (MvPolynomial.X i : MvPolynomial ι C) ^ q i := hx haeval
  have hmono : ∀ n : ι → ℕ, (∏ i, (MvPolynomial.X i : MvPolynomial ι C) ^ n i)
      = MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm n) (1 : C) := by
    intro n
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    have hzero : n i = 0 := by
      simpa using Finsupp.notMem_support_iff.mp hi
    rw [hzero, pow_zero]
  rw [hmono p, hmono q] at hpoly
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm p)) hpoly
  rw [MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
  by_cases hpq : Finsupp.equivFunOnFinite.symm q = Finsupp.equivFunOnFinite.symm p
  · funext i
    exact congrArg (fun s : ι →₀ ℕ ↦ s i) hpq.symm
  · rw [if_neg hpq] at hcoeff
    exact absurd hcoeff.symm zero_ne_one

end Monomials

section Field

variable {C E ι : Type*} [Field C] [Field E] [Algebra C E] [Fintype ι] [DecidableEq ι]

/-- A nontrivial monomial in an algebraically independent family is not `1`. -/
theorem prod_zpow_eq_one_iff {x : ι → E} (hx : AlgebraicIndependent C x) {e : ι → ℤ}
    (h : ∏ i, x i ^ e i = 1) : e = 0 := by
  classical
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i hi
    exact (hx.transcendental i) (hi ▸ isAlgebraic_zero)
  have hsplit : ∀ i, x i ^ e i = x i ^ ((e i).toNat) / x i ^ ((-(e i)).toNat) := by
    intro i
    by_cases hpos : 0 ≤ e i
    · rw [show (-(e i)).toNat = 0 by omega, pow_zero, div_one]
      rw [← zpow_natCast]
      congr 1
      omega
    · push Not at hpos
      rw [show (e i).toNat = 0 by omega, pow_zero, one_div, ← zpow_natCast, ← zpow_neg]
      congr 1
      omega
  have hprod : ∏ i, x i ^ ((e i).toNat) = ∏ i, x i ^ ((-(e i)).toNat) := by
    have hne : ∏ i, x i ^ ((-(e i)).toNat) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hx0 i)
    have hdiv : (∏ i, x i ^ ((e i).toNat)) / (∏ i, x i ^ ((-(e i)).toNat)) = 1 := by
      rw [← Finset.prod_div_distrib, ← h]
      exact Finset.prod_congr rfl fun i _ ↦ (hsplit i).symm
    exact (div_eq_one_iff_eq hne).mp hdiv
  have hpq := exponent_eq_of_prod_pow_eq hx hprod
  funext i
  have := congrFun hpq i
  simp only [Pi.zero_apply]
  omega

/-- A nonsingular monomial substitution of an algebraically independent family is injective. -/
theorem monomialFamily_injective_of_det_ne_zero {r : ℕ} {x : Fin r → E}
    (hxalg : AlgebraicIndependent C x) {M : Matrix (Fin r) (Fin r) ℤ} (hM : M.det ≠ 0) :
    Function.Injective (monomialFamily M x) := by
  classical
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i hi
    exact (hxalg.transcendental i) (hi ▸ isAlgebraic_zero)
  intro i j hij
  by_contra hne
  have hone : ∏ k, x k ^ (M i k - M j k) = 1 := by
    have hdiv : (∏ k, x k ^ M i k) / (∏ k, x k ^ M j k) = 1 := by
      rw [show (∏ k, x k ^ M i k) = monomialFamily M x i from rfl,
        show (∏ k, x k ^ M j k) = monomialFamily M x j from rfl, hij,
        div_self (monomialFamily_ne_zero M hx0 j)]
    rw [← hdiv, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun k _ ↦ zpow_sub₀ (hx0 k) _ _
  have hrow := prod_zpow_eq_one_iff hxalg hone
  have hMij : M i = M j := by
    funext k
    have hk := congrFun hrow k
    simp only [Pi.zero_apply] at hk
    omega
  exact hM (Matrix.det_zero_of_row_eq hne hMij)

/-- **The adjugate identity in monomial form.**  A power of each coordinate, with exponent the
determinant, is a monomial in the substituted family. -/
theorem pow_det_eq_monomialFamily_adjugate {r : ℕ} {x : Fin r → E} (hx0 : ∀ j, x j ≠ 0)
    (M : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    x i ^ M.det = monomialFamily M.adjugate (monomialFamily M x) i := by
  classical
  rw [← monomialFamily_mul _ _ hx0, Matrix.adjugate_mul, monomialFamily_apply,
    Finset.prod_eq_single i]
  · rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  · intro k _ hki
    rw [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hki), smul_zero, zpow_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi


end Field

section Differential

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E]

omit [Differential C] [DifferentialAlgebra C E] [CharZero E] in
/-- The order-zero level of a differentially independent family is algebraically independent. -/
theorem algebraicIndependent_of_differentialIndependent {ι : Type*} {x : ι → E}
    (hx : DifferentialIndependent C x) : AlgebraicIndependent C x := by
  have hx' : AlgebraicIndependent C (fun p : ι × ℕ ↦ differentialJet p.2 (x p.1)) := hx
  have hcomp := hx'.comp (fun i : ι ↦ (i, 0)) (fun a b hab ↦ congrArg Prod.fst hab)
  simpa [Function.comp_def] using hcomp


/-- **A nonsingular monomial substitution preserves differential independence.**  The adjugate
identity writes a power of each original coordinate as a monomial in the new ones, so the new family
spans the old, and distinct rows give distinct monomials. -/
theorem differentialIndependent_monomialFamily {r : ℕ} {x : Fin r → E}
    (hx : DifferentialIndependent C x) {M : Matrix (Fin r) (Fin r) ℤ} (hM : M.det ≠ 0) :
    DifferentialIndependent C (monomialFamily M x) := by
  classical
  have hxalg : AlgebraicIndependent C x := algebraicIndependent_of_differentialIndependent hx
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i hi
    exact (hxalg.transcendental i) (hi ▸ isAlgebraic_zero)
  refine differentialIndependent_of_range_subset_closure hx
    (monomialFamily_injective_of_det_ne_zero hxalg hM) (fun i ↦ ?_)
  letI : DifferentialAlgebra (↥(differentialAdjoin C (Set.range (monomialFamily M x)))) E :=
    ⟨fun c ↦ derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin C (Set.range (monomialFamily M x))) c⟩
  have hmemPow : x i ^ M.det ∈ differentialAdjoin C (Set.range (monomialFamily M x)) := by
    rw [pow_det_eq_monomialFamily_adjugate hx0 M i, monomialFamily_apply]
    exact prod_mem fun j _ ↦ zpow_mem
      (subset_differentialAdjoin C _ (Set.mem_range_self j)) _
  have hnatPow : x i ^ (M.det.natAbs : ℕ)
      ∈ differentialAdjoin C (Set.range (monomialFamily M x)) := by
    rcases le_or_gt 0 M.det with hpos | hneg
    · have hz : x i ^ ((M.det.natAbs : ℕ) : ℤ)
          ∈ differentialAdjoin C (Set.range (monomialFamily M x)) := by
        rw [show ((M.det.natAbs : ℕ) : ℤ) = M.det by omega]
        exact hmemPow
      rwa [zpow_natCast] at hz
    · have hinv : (x i ^ M.det)⁻¹ ∈ differentialAdjoin C (Set.range (monomialFamily M x)) :=
        inv_mem hmemPow
      rw [← zpow_neg] at hinv
      have hz : x i ^ ((M.det.natAbs : ℕ) : ℤ)
          ∈ differentialAdjoin C (Set.range (monomialFamily M x)) := by
        rw [show ((M.det.natAbs : ℕ) : ℤ) = -M.det by omega]
        exact hinv
      rwa [zpow_natCast] at hz
  have hint : IsIntegral (↥(differentialAdjoin C (Set.range (monomialFamily M x)))) (x i) :=
    isIntegral_of_pow_mem (α := x i)
      (c := (⟨x i ^ (M.det.natAbs : ℕ), hnatPow⟩ :
        ↥(differentialAdjoin C (Set.range (monomialFamily M x)))))
      (Int.natAbs_pos.mpr hM) rfl
  exact differentialAlgebraicOver_of_isAlgebraic hint.isAlgebraic

end Differential

end

end GaloisForLFunctions.HTGeometry
