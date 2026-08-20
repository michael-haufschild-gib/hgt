/-
# Bondarenko--Heap Lemma 9: prime-local exceptional factor

For a prime factor where the source character `ψ_p` equals the quadratic
character `χ_p`, Lemma 9 identifies the local generalized Jacobi sum with the
Ramanujan factor `p - 1` at zero and `-1` away from zero.  This module proves
that exact finite-field factor and transports its zero branch through the
source inverse-incidence shift `r m⁻¹`.
-/
import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaSeven
import GaloisForLFunctions.RHTower.QuadraticJacobiSum

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The exact prime-local exceptional factor in Lemma 9. -/
def oddPrimeQuadraticRamanujanLocalSum
    (p : OddPrime) (y : ZMod p.1) : ℂ :=
  ∑ u : ZMod p.1,
    oddPrimeQuadraticCharacter p (u + y) * oddPrimeQuadraticCharacter p u

/-- At a certified odd prime, the quadratic local factor is the prime
Ramanujan sum: `p - 1` at the zero residue and `-1` at every other residue. -/
theorem oddPrime_quadraticRamanujanLocalSum
    (p : OddPrime) (y : ZMod p.1) :
    oddPrimeQuadraticRamanujanLocalSum p y =
      if y = 0 then (p.1 : ℂ) - 1 else -1 := by
  simpa [oddPrimeQuadraticRamanujanLocalSum] using
    oddPrime_quadratic_shiftCorrelation p y 0

/-- The same local factor at the source shift `r m⁻¹`; its zero branch is
exactly the zero branch of `r`, because the denominator is explicit unit data. -/
theorem oddPrime_quadraticRamanujanLocalSum_unitInverse
    (p : OddPrime) (r : ZMod p.1) (m : (ZMod p.1)ˣ) :
    oddPrimeQuadraticRamanujanLocalSum p (unitInverseIncidenceClass p.1 r m) =
      if r = 0 then (p.1 : ℂ) - 1 else -1 := by
  rw [oddPrime_quadraticRamanujanLocalSum]
  simp only [unitInverseIncidenceClass_eq_zero_iff]

/-- Multiplication by a nonzero prime-field residue is a residue permutation.
This private reindexing device discharges the nonzero branch of the source
local Jacobi-factor calculation. -/
private def oddPrimeMulEquiv (p : OddPrime) (y : ZMod p.1) (hy : y ≠ 0) :
    ZMod p.1 ≃ ZMod p.1 where
  toFun u := y * u
  invFun u := y⁻¹ * u
  left_inv u := by
    change y⁻¹ * (y * u) = u
    rw [← mul_assoc, inv_mul_cancel₀ hy, one_mul]
  right_inv u := by
    change y * (y⁻¹ * u) = u
    rw [← mul_assoc, mul_inv_cancel₀ hy, one_mul]

/-- The local generalized Jacobi sum used by the odd-prime part of Lemma 9. -/
def oddPrimeGeneralizedJacobiLocal
    (p : OddPrime) (ψ : MulChar (ZMod p.1) ℂ) (y : ZMod p.1) : ℂ :=
  ∑ u : ZMod p.1,
    oddPrimeQuadraticCharacter p (u + y) * star (ψ u)

/-- The fixed shift-one generalized Jacobi core for a local character. -/
def oddPrimeGeneralizedJacobiCore
    (p : OddPrime) (ψ : MulChar (ZMod p.1) ℂ) : ℂ :=
  ∑ u : ZMod p.1,
    oddPrimeQuadraticCharacter p (u + 1) * star (ψ u)

/-- Exact prime-local shift factorization.  The zero branch is retained
literally; on every nonzero residue the local sum is the character phase at
that residue times the fixed generalized Jacobi core. -/
theorem oddPrime_generalizedJacobiLocal_scale
    (p : OddPrime) (ψ : MulChar (ZMod p.1) ℂ) (y : ZMod p.1) :
    oddPrimeGeneralizedJacobiLocal p ψ y =
      if y = 0 then oddPrimeGeneralizedJacobiLocal p ψ 0 else
        (oddPrimeQuadraticCharacter p y * star (ψ y)) *
          oddPrimeGeneralizedJacobiCore p ψ := by
  by_cases hy : y = 0
  · simp [hy]
  · simp only [if_neg hy]
    unfold oddPrimeGeneralizedJacobiLocal oddPrimeGeneralizedJacobiCore
    rw [← Equiv.sum_comp (oddPrimeMulEquiv p y hy)
      (fun u : ZMod p.1 =>
        oddPrimeQuadraticCharacter p (u + y) * star (ψ u))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    change oddPrimeQuadraticCharacter p (y * u + y) * star (ψ (y * u)) =
      (oddPrimeQuadraticCharacter p y * star (ψ y)) *
        (oddPrimeQuadraticCharacter p (u + 1) * star (ψ u))
    rw [show y * u + y = y * (u + 1) by ring, map_mul, map_mul, star_mul]
    ring

/-- The fixed local core is exactly mathlib's Jacobi sum, up to the explicit
change-of-variable phase forced by the source's `u + 1` convention. -/
theorem oddPrime_generalizedJacobiCore_eq_jacobiSum
    (p : OddPrime) (ψ : MulChar (ZMod p.1) ℂ) :
    oddPrimeGeneralizedJacobiCore p ψ =
      star (ψ (-1)) * jacobiSum (oddPrimeQuadraticCharacter p) ψ⁻¹ := by
  unfold oddPrimeGeneralizedJacobiCore jacobiSum
  rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod p.1))
    (fun x : ZMod p.1 =>
      oddPrimeQuadraticCharacter p x * ψ⁻¹ (1 - x))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  change oddPrimeQuadraticCharacter p (u + 1) * star (ψ u) =
    star (ψ (-1)) *
      (oddPrimeQuadraticCharacter p (u + 1) * ψ⁻¹ (1 - (u + 1)))
  rw [MulChar.star_apply', MulChar.star_apply']
  rw [show 1 - (u + 1) = -u by ring]
  have hψ : ψ⁻¹ (-1 : ZMod p.1) * ψ⁻¹ (-u) = ψ⁻¹ u := by
    rw [← map_mul]
    congr 1
    ring
  rw [← hψ]
  ring

/-- A multiplicative character has unit norm at every unit of its domain. -/
private theorem mulChar_mul_star_apply_eq_one
    {R : Type*} [CommRing R] [Finite Rˣ]
    (ψ : MulChar R ℂ) (a : R) (ha : IsUnit a) :
    ψ a * star (ψ a) = 1 := by
  rw [MulChar.star_apply', ← MulChar.mul_apply, mul_comm, MulChar.inv_mul]
  exact MulChar.one_apply ha

/-- Complex conjugation of a finite-field Jacobi sum is the Jacobi sum of
the inverse characters. -/
theorem jacobiSum_star
    (p : OddPrime) (χ ψ : MulChar (ZMod p.1) ℂ) :
    star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
  unfold jacobiSum
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [star_mul, MulChar.star_apply', MulChar.star_apply']
  ring

/-- Exact closed norm-square law for the fixed local generalized-Jacobi core.
The trivial and quadratic-match branches have norm square one; every other
local character has norm square exactly `p`. -/
theorem oddPrime_generalizedJacobiCore_normSq
    (p : OddPrime) (ψ : MulChar (ZMod p.1) ℂ) :
    (ψ = 1 ∧
      oddPrimeGeneralizedJacobiCore p ψ * star (oddPrimeGeneralizedJacobiCore p ψ) = 1) ∨
    (ψ ≠ 1 ∧ oddPrimeQuadraticCharacter p * ψ⁻¹ = 1 ∧
      oddPrimeGeneralizedJacobiCore p ψ * star (oddPrimeGeneralizedJacobiCore p ψ) = 1) ∨
    (ψ ≠ 1 ∧ oddPrimeQuadraticCharacter p * ψ⁻¹ ≠ 1 ∧
      oddPrimeGeneralizedJacobiCore p ψ * star (oddPrimeGeneralizedJacobiCore p ψ) =
        (p.1 : ℂ)) := by
  classical
  have hminusOneUnit : IsUnit (-1 : ZMod p.1) :=
    isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)
  have hphase : star (ψ (-1)) * star (star (ψ (-1))) = 1 := by
    rw [star_star]
    simpa [mul_comm] using mulChar_mul_star_apply_eq_one ψ (-1) hminusOneUnit
  have hquadPhase : oddPrimeQuadraticCharacter p (-1) *
      star (oddPrimeQuadraticCharacter p (-1)) = 1 :=
    mulChar_mul_star_apply_eq_one (oddPrimeQuadraticCharacter p) (-1) hminusOneUnit
  rw [oddPrime_generalizedJacobiCore_eq_jacobiSum, star_mul]
  by_cases hψ : ψ = 1
  · left
    refine ⟨hψ, ?_⟩
    subst ψ
    simp only [inv_one]
    have hJ : jacobiSum (1 : MulChar (ZMod p.1) ℂ)
        (oddPrimeQuadraticCharacter p) = -1 :=
      jacobiSum_one_nontrivial (oddPrimeQuadraticCharacter_ne_one p)
    rw [jacobiSum_comm, hJ]
    calc
      _ = star ((1 : MulChar (ZMod p.1) ℂ) (-1)) *
          star (star ((1 : MulChar (ZMod p.1) ℂ) (-1))) := by norm_num
      _ = 1 := hphase
  · right
    by_cases hprod : oddPrimeQuadraticCharacter p * ψ⁻¹ = 1
    · left
      refine ⟨hψ, hprod, ?_⟩
      have hψinv : ψ⁻¹ = (oddPrimeQuadraticCharacter p)⁻¹ := by
        calc
          ψ⁻¹ = 1 * ψ⁻¹ := by simp
          _ = ((oddPrimeQuadraticCharacter p)⁻¹ * oddPrimeQuadraticCharacter p) * ψ⁻¹ := by
            rw [MulChar.inv_mul]
          _ = (oddPrimeQuadraticCharacter p)⁻¹ *
              (oddPrimeQuadraticCharacter p * ψ⁻¹) := mul_assoc _ _ _
          _ = (oddPrimeQuadraticCharacter p)⁻¹ := by rw [hprod, mul_one]
      have hquadInv : (oddPrimeQuadraticCharacter p)⁻¹ =
          oddPrimeQuadraticCharacter p :=
        (oddPrimeQuadraticCharacter_isQuadratic p).inv
      have hphaseQuad : star (ψ (-1)) = oddPrimeQuadraticCharacter p (-1) := by
        rw [MulChar.star_apply', hψinv, hquadInv]
      have hphaseQuadStar : star (star (ψ (-1))) =
          star (oddPrimeQuadraticCharacter p (-1)) :=
        congrArg star hphaseQuad
      have hJ : jacobiSum (oddPrimeQuadraticCharacter p) ψ⁻¹ =
          -oddPrimeQuadraticCharacter p (-1) := by
        rw [hψinv]
        exact jacobiSum_nontrivial_inv (oddPrimeQuadraticCharacter_ne_one p)
      have hstarJ : star (jacobiSum (oddPrimeQuadraticCharacter p) ψ⁻¹) =
          star (-oddPrimeQuadraticCharacter p (-1)) :=
        congrArg star hJ
      rw [hstarJ, hJ, hphaseQuadStar, hphaseQuad, star_neg]
      calc
        _ = (oddPrimeQuadraticCharacter p (-1) *
            star (oddPrimeQuadraticCharacter p (-1))) *
            (oddPrimeQuadraticCharacter p (-1) *
              star (oddPrimeQuadraticCharacter p (-1))) := by ring
        _ = 1 := by rw [hquadPhase]; norm_num
    · right
      refine ⟨hψ, hprod, ?_⟩
      have hψinv : ψ⁻¹ ≠ 1 := inv_ne_one.mpr hψ
      have hJ : jacobiSum (oddPrimeQuadraticCharacter p) ψ⁻¹ *
          star (jacobiSum (oddPrimeQuadraticCharacter p) ψ⁻¹) = (p.1 : ℂ) := by
        rw [jacobiSum_star]
        have hchar : ringChar ℂ ≠ ringChar (ZMod p.1) := by
          intro h
          have hcomplex : ringChar ℂ = 0 := by aesop
          rw [hcomplex, ZMod.ringChar_zmod_n] at h
          exact p.2.1.ne_zero h.symm
        simpa using jacobiSum_mul_jacobiSum_inv hchar
          (oddPrimeQuadraticCharacter_ne_one p) hψinv hprod
      calc
        (star (ψ (-1)) * jacobiSum (oddPrimeQuadraticCharacter p) ψ⁻¹) *
            (star (jacobiSum (oddPrimeQuadraticCharacter p) ψ⁻¹) * star (star (ψ (-1)))) =
            (star (ψ (-1)) * star (star (ψ (-1)))) *
              (jacobiSum (oddPrimeQuadraticCharacter p) ψ⁻¹ *
                star (jacobiSum (oddPrimeQuadraticCharacter p) ψ⁻¹)) := by ring
        _ = (p.1 : ℂ) := by rw [hphase, hJ]; ring

/-- When the local source character is quadratic, its generalized Jacobi
factor is exactly the prime Ramanujan factor. -/
theorem oddPrime_generalizedJacobiLocal_quadratic
    (p : OddPrime) (y : ZMod p.1) :
    oddPrimeGeneralizedJacobiLocal p (oddPrimeQuadraticCharacter p) y =
      if y = 0 then (p.1 : ℂ) - 1 else -1 := by
  unfold oddPrimeGeneralizedJacobiLocal
  simp_rw [MulChar.star_apply', (oddPrimeQuadraticCharacter_isQuadratic p).inv]
  exact oddPrime_quadraticRamanujanLocalSum p y

namespace OddPrimeFamily

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The product of arbitrary local source characters transported through the
certified square-free CRT equivalence. -/
def generalizedJacobiLocalCharacter (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) (u : ZMod P.modulus) : ℂ :=
  ∏ i, ψ i (P.crtEquiv u i)

/-- The odd square-free global generalized Jacobi sum in source coordinates. -/
def generalizedJacobiLocalSum (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) (y : ZMod P.modulus) : ℂ :=
  ∑ u : ZMod P.modulus,
    quadraticCharacter P (u + y) * star (generalizedJacobiLocalCharacter P ψ u)

/-- Exact CRT factorization of the global generalized Jacobi sum into the
already formalized prime-local factors. -/
theorem generalizedJacobiLocalSum_crt_factor
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod P.modulus) :
    generalizedJacobiLocalSum P ψ y =
      ∏ i, oddPrimeGeneralizedJacobiLocal (P.prime i) (ψ i) (P.crtEquiv y i) := by
  unfold generalizedJacobiLocalSum generalizedJacobiLocalCharacter quadraticCharacter
  calc
    _ = ∑ u : ∀ i, ZMod (P.prime i).1,
        oddPrimeFamilyQuadraticCharacter P.prime (u + P.crtEquiv y) *
          star (∏ i, ψ i (u i)) := by
      simp only [map_add]
      exact Equiv.sum_comp P.crtEquiv.toEquiv (fun u : ∀ i, ZMod (P.prime i).1 =>
        oddPrimeFamilyQuadraticCharacter P.prime (u + P.crtEquiv y) *
          star (∏ i, ψ i (u i)))
    _ = ∑ u : ∀ i, ZMod (P.prime i).1, ∏ i,
        oddPrimeQuadraticCharacter (P.prime i) (u i + P.crtEquiv y i) *
          star (ψ i (u i)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [oddPrimeFamilyQuadraticCharacter, star_prod, ← Finset.prod_mul_distrib]
      simp only [Pi.add_apply]
    _ = ∏ i, ∑ a : ZMod (P.prime i).1,
        oddPrimeQuadraticCharacter (P.prime i) (a + P.crtEquiv y i) *
          star (ψ i a) := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.prod_univ_sum (fun i => Finset.univ)
          (fun i a => oddPrimeQuadraticCharacter (P.prime i) (a + P.crtEquiv y i) *
            star (ψ i a))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      rfl

/-- Indices at which the local source character is the quadratic character.
The finite set is constructed internally from the character tuple. -/
noncomputable def exceptionalPrimeIndices (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) : Finset I := by
  classical
  exact Finset.univ.filter fun i => ψ i = oddPrimeQuadraticCharacter (P.prime i)

omit [DecidableEq I] in
/-- Membership in the internally constructed exceptional-prime set is exactly
the local equality `ψ_p = χ_p` used in source Lemma 9. -/
theorem mem_exceptionalPrimeIndices (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) (i : I) :
    i ∈ exceptionalPrimeIndices P ψ ↔ ψ i = oddPrimeQuadraticCharacter (P.prime i) := by
  classical
  simp [exceptionalPrimeIndices]

/-- The literal product of exceptional prime Ramanujan factors. -/
def exceptionalRamanujanProduct (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) (y : ZMod P.modulus) : ℂ :=
  ∏ i ∈ exceptionalPrimeIndices P ψ,
    if P.crtEquiv y i = 0 then ((P.prime i).1 : ℂ) - 1 else -1

/-- Exact source-factor split: the global generalized Jacobi sum is its
exceptional Ramanujan product times the remaining local generalized factors. -/
theorem generalizedJacobiLocalSum_exceptional_split
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod P.modulus) :
    generalizedJacobiLocalSum P ψ y =
      exceptionalRamanujanProduct P ψ y *
        ∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
          oddPrimeGeneralizedJacobiLocal (P.prime i) (ψ i) (P.crtEquiv y i) := by
  rw [generalizedJacobiLocalSum_crt_factor]
  calc
    ∏ i, oddPrimeGeneralizedJacobiLocal (P.prime i) (ψ i) (P.crtEquiv y i) =
        (∏ i ∈ exceptionalPrimeIndices P ψ,
          oddPrimeGeneralizedJacobiLocal (P.prime i) (ψ i) (P.crtEquiv y i)) *
        ∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
          oddPrimeGeneralizedJacobiLocal (P.prime i) (ψ i) (P.crtEquiv y i) := by
      rw [mul_comm]
      exact (Finset.prod_sdiff (Finset.subset_univ _)).symm
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      have hψ : ψ i = oddPrimeQuadraticCharacter (P.prime i) :=
        (mem_exceptionalPrimeIndices P ψ i).mp hi
      rw [hψ, oddPrime_generalizedJacobiLocal_quadratic]

end OddPrimeFamily

end RHTower
