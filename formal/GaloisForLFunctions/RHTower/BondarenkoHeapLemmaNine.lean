/-
# Bondarenko--Heap Lemma 9: prime-local exceptional factor

For a prime factor where the source character `ψ_p` equals the quadratic
character `χ_p`, Lemma 9 identifies the local generalized Jacobi sum with the
Ramanujan factor `p - 1` at zero and `-1` away from zero.  This module proves
that exact finite-field factor and transports its zero branch through the
source inverse-incidence shift `r m⁻¹`.
-/
import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaSeven
import GaloisForLFunctions.RHTower.DirichletCharacterSecondMoment
import GaloisForLFunctions.RHTower.DivisorBound
import GaloisForLFunctions.RHTower.QuadraticJacobiSum
import GaloisForLFunctions.RHTower.SpikeBandConvolution

open scoped BigOperators

noncomputable section

namespace RHTower

/-- A complex-valued multiplicative character has norm at most one at every
ring element: it is zero off the unit group and a root of unity on it. -/
theorem norm_mulChar_apply_le_one {R : Type*} [CommRing R] [Finite Rˣ]
    (χ : MulChar R ℂ) (a : R) :
    ‖χ a‖ ≤ 1 := by
  classical
  letI := Fintype.ofFinite Rˣ
  letI : NeZero (Fintype.card Rˣ) := ⟨Fintype.card_pos.ne'⟩
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    exact le_of_eq (Complex.norm_eq_one_of_mem_rootsOfUnity
      (χ.apply_mem_rootsOfUnity u))
  · rw [χ.map_nonunit ha, norm_zero]
    norm_num

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

/-- The standard additive-character definition of the prime Ramanujan sum. -/
def oddPrimeRamanujanAdditiveSum (p : OddPrime) (y : ZMod p.1) : ℂ :=
  ∑ u ∈ (Finset.univ.erase (0 : ZMod p.1)), ZMod.stdAddChar (u * y)

/-- The additive prime Ramanujan sum is `p - 1` at zero and `-1` elsewhere. -/
theorem oddPrime_ramanujanAdditiveSum
    (p : OddPrime) (y : ZMod p.1) :
    oddPrimeRamanujanAdditiveSum p y =
      if y = 0 then (p.1 : ℂ) - 1 else -1 := by
  have hsum : ∑ u : ZMod p.1, ZMod.stdAddChar (u * y) =
      if y = 0 then (p.1 : ℂ) else 0 := by
    simpa using AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p.1)) y
      (ZMod.isPrimitive_stdAddChar p.1)
  unfold oddPrimeRamanujanAdditiveSum
  have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := fun u : ZMod p.1 =>
    ZMod.stdAddChar (u * y)) (Finset.mem_univ 0)
  rw [show ZMod.stdAddChar (0 * y) = (1 : ℂ) by simp] at hsplit
  rw [hsum] at hsplit
  by_cases hy : y = 0
  · rw [if_pos hy] at hsplit
    rw [if_pos hy]
    calc
      _ = (∑ u ∈ Finset.univ.erase (0 : ZMod p.1), ZMod.stdAddChar (u * y)) + 1 - 1 := by
        ring
      _ = (p.1 : ℂ) - 1 := by rw [hsplit]
  · rw [if_neg hy] at hsplit
    rw [if_neg hy]
    calc
      _ = (∑ u ∈ Finset.univ.erase (0 : ZMod p.1), ZMod.stdAddChar (u * y)) + 1 - 1 := by
        ring
      _ = (0 : ℂ) - 1 := by rw [hsplit]
      _ = -1 := by ring

/-- The absolute value of a prime additive Ramanujan sum is at most the prime. -/
theorem oddPrime_ramanujanAdditiveSum_norm_le_prime
    (p : OddPrime) (y : ZMod p.1) :
    ‖oddPrimeRamanujanAdditiveSum p y‖ ≤ (p.1 : ℝ) := by
  rw [oddPrime_ramanujanAdditiveSum]
  by_cases hy : y = 0
  · rw [if_pos hy]
    let t : ℝ := (p.1 : ℝ) - 1
    have ht : ((p.1 : ℂ) - 1) = (t : ℂ) := by
      dsimp [t]
      norm_cast
    rw [ht, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · dsimp [t]
      linarith [show (1 : ℝ) ≤ p.1 by exact_mod_cast p.2.1.one_le]
    · dsimp [t]
      linarith [show (1 : ℝ) ≤ p.1 by exact_mod_cast p.2.1.one_le]
  · rw [if_neg hy]
    simpa using (show (1 : ℝ) ≤ p.1 by exact_mod_cast p.2.1.one_le)

/-- The exceptional quadratic local Jacobi factor is the literal additive
Ramanujan sum, not merely a function with the same two displayed values. -/
theorem oddPrime_quadraticRamanujanLocalSum_eq_additive
    (p : OddPrime) (y : ZMod p.1) :
    oddPrimeQuadraticRamanujanLocalSum p y = oddPrimeRamanujanAdditiveSum p y := by
  rw [oddPrime_quadraticRamanujanLocalSum, oddPrime_ramanujanAdditiveSum]

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

/-- Internal character algebra for the zero-shift local-factor split. -/
private theorem oddPrimeQuadratic_mul_inv_eq_one_iff
    (p : OddPrime) (ψ : MulChar (ZMod p.1) ℂ) :
    oddPrimeQuadraticCharacter p * ψ⁻¹ = 1 ↔ ψ = oddPrimeQuadraticCharacter p := by
  constructor
  · intro h
    have hmul := congrArg (fun φ : MulChar (ZMod p.1) ℂ => φ * ψ) h
    simpa only [mul_assoc, MulChar.inv_mul, mul_one, one_mul] using hmul.symm
  · intro h
    subst ψ
    rw [mul_comm, MulChar.inv_mul]

/-- Exact zero-shift local dichotomy: the exceptional quadratic character
contributes `p-1`; every other local character cancels completely. -/
theorem oddPrime_generalizedJacobiLocal_zero_cases
    (p : OddPrime) (ψ : MulChar (ZMod p.1) ℂ) :
    (ψ = oddPrimeQuadraticCharacter p ∧
      oddPrimeGeneralizedJacobiLocal p ψ 0 = (p.1 : ℂ) - 1) ∨
    (ψ ≠ oddPrimeQuadraticCharacter p ∧
      oddPrimeGeneralizedJacobiLocal p ψ 0 = 0) := by
  by_cases hψ : ψ = oddPrimeQuadraticCharacter p
  · left
    refine ⟨hψ, ?_⟩
    rw [hψ, oddPrime_generalizedJacobiLocal_quadratic]
    simp
  · right
    refine ⟨hψ, ?_⟩
    unfold oddPrimeGeneralizedJacobiLocal
    simp only [add_zero, MulChar.star_apply']
    simp_rw [← MulChar.mul_apply]
    apply MulChar.sum_eq_zero_of_ne_one
    intro h
    exact hψ (oddPrimeQuadratic_mul_inv_eq_one_iff p ψ |>.mp h)

/-- Internal nonexceptional local factorization, with the zero branch
discharged by exact multiplicative-character cancellation. -/
private theorem oddPrime_generalizedJacobiLocal_of_ne_quadratic
    (p : OddPrime) (ψ : MulChar (ZMod p.1) ℂ)
    (hψ : ψ ≠ oddPrimeQuadraticCharacter p) (y : ZMod p.1) :
    oddPrimeGeneralizedJacobiLocal p ψ y =
      (oddPrimeQuadraticCharacter p y * star (ψ y)) *
        oddPrimeGeneralizedJacobiCore p ψ := by
  by_cases hy : y = 0
  · rcases oddPrime_generalizedJacobiLocal_zero_cases p ψ with h | h
    · exact (hψ h.1).elim
    · subst y
      rw [h.2]
      simp only [MulChar.map_zero, star_zero, zero_mul]
  · rw [oddPrime_generalizedJacobiLocal_scale, if_neg hy]

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

/-- The exceptional square-free Ramanujan product in literal additive-character form. -/
def exceptionalRamanujanAdditiveProduct (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) (y : ZMod P.modulus) : ℂ :=
  ∏ i ∈ exceptionalPrimeIndices P ψ,
    oddPrimeRamanujanAdditiveSum (P.prime i) (P.crtEquiv y i)

omit [DecidableEq I] in
/-- The displayed exceptional factor is exactly the additive-character
Ramanujan product, factor by factor. -/
theorem exceptionalRamanujanProduct_eq_additive
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod P.modulus) :
    exceptionalRamanujanProduct P ψ y = exceptionalRamanujanAdditiveProduct P ψ y := by
  unfold exceptionalRamanujanProduct exceptionalRamanujanAdditiveProduct
  apply Finset.prod_congr rfl
  intro i hi
  rw [oddPrime_ramanujanAdditiveSum]

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

/-- The global generalized Jacobi sum split with its exceptional factor written
as a literal square-free additive Ramanujan product. -/
theorem generalizedJacobiLocalSum_exceptional_additive_split
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod P.modulus) :
    generalizedJacobiLocalSum P ψ y =
      exceptionalRamanujanAdditiveProduct P ψ y *
        ∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
          oddPrimeGeneralizedJacobiLocal (P.prime i) (ψ i) (P.crtEquiv y i) := by
  rw [generalizedJacobiLocalSum_exceptional_split, exceptionalRamanujanProduct_eq_additive]

/-- The residual local-character phase in the source Lemma-9 factorization. -/
def residualJacobiPhase (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) (y : ZMod P.modulus) : ℂ :=
  ∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
    oddPrimeQuadraticCharacter (P.prime i) (P.crtEquiv y i) *
      star (ψ i (P.crtEquiv y i))

/-- Product of the residual fixed local Jacobi cores. -/
def residualJacobiCoreProduct (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) : ℂ :=
  ∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
    oddPrimeGeneralizedJacobiCore (P.prime i) (ψ i)

/-- Integer norm-square factor of the residual fixed Jacobi cores.  The
trivial nonexceptional local character contributes one; every other
nonexceptional local character contributes its prime. -/
def residualJacobiCoreNormSqFactor (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) : ℕ := by
  classical
  exact ∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
    if ψ i = 1 then 1 else (P.prime i).1

/-- Exact norm-square factorization of the residual Jacobi-core product. -/
theorem residualJacobiCoreProduct_normSq
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) :
    residualJacobiCoreProduct P ψ * star (residualJacobiCoreProduct P ψ) =
      (residualJacobiCoreNormSqFactor P ψ : ℂ) := by
  classical
  unfold residualJacobiCoreProduct residualJacobiCoreNormSqFactor
  simp only [star_prod, ← Finset.prod_mul_distrib, Nat.cast_prod, Nat.cast_ite, Nat.cast_one]
  apply Finset.prod_congr rfl
  intro i hi
  have hneq : ψ i ≠ oddPrimeQuadraticCharacter (P.prime i) := by
    intro h
    exact (Finset.mem_sdiff.mp hi).2 ((mem_exceptionalPrimeIndices P ψ i).mpr h)
  rcases oddPrime_generalizedJacobiCore_normSq (P.prime i) (ψ i) with h | h | h
  · simpa [h.1] using h.2
  · have hquad : oddPrimeQuadraticCharacter (P.prime i) = ψ i := by
      calc
        oddPrimeQuadraticCharacter (P.prime i) =
            oddPrimeQuadraticCharacter (P.prime i) * 1 := by simp
        _ = oddPrimeQuadraticCharacter (P.prime i) * ((ψ i)⁻¹ * ψ i) := by
          rw [MulChar.inv_mul]
        _ = (oddPrimeQuadraticCharacter (P.prime i) * (ψ i)⁻¹) * ψ i := by
          rw [mul_assoc]
        _ = 1 * ψ i := by rw [h.2.1]
        _ = ψ i := by simp
    exact (hneq hquad.symm).elim
  · simpa [h.1] using h.2.2

/-- The residual Jacobi-core norm-square factor never exceeds the certified
odd square-free ambient modulus. -/
theorem residualJacobiCoreNormSqFactor_le_modulus
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) :
    residualJacobiCoreNormSqFactor P ψ ≤ P.modulus := by
  classical
  unfold residualJacobiCoreNormSqFactor
  calc
    (∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
        if ψ i = 1 then 1 else (P.prime i).1) ≤
      ∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ, (P.prime i).1 := by
        apply Finset.prod_le_prod
        · intro i hi
          exact Nat.zero_le _
        · intro i hi
          split_ifs
          · exact (P.prime i).2.1.one_le
          · exact Nat.le_refl _
    _ ≤ P.modulus := by
      have hdiv : (∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ, (P.prime i).1) ∣ P.modulus := by
        rw [modulus]
        exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
      have hmodpos : 0 < P.modulus := P.modulus_neZero.out |> Nat.pos_of_ne_zero
      exact Nat.le_of_dvd hmodpos hdiv

/-- The residual Jacobi-core product has exactly the real norm square encoded
by its finite natural factor. -/
theorem residualJacobiCoreProduct_complexNormSq
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) :
    Complex.normSq (residualJacobiCoreProduct P ψ) =
      (residualJacobiCoreNormSqFactor P ψ : ℝ) := by
  have hcomplex : (Complex.normSq (residualJacobiCoreProduct P ψ) : ℂ) =
      (residualJacobiCoreNormSqFactor P ψ : ℂ) := by
    simpa only [Complex.star_def, Complex.mul_conj] using
      residualJacobiCoreProduct_normSq P ψ
  exact_mod_cast hcomplex

/-- Exact squared complex norm of the residual Jacobi-core product. -/
theorem residualJacobiCoreProduct_sq_norm
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) :
    ‖residualJacobiCoreProduct P ψ‖ ^ 2 =
      (residualJacobiCoreNormSqFactor P ψ : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq]
  exact residualJacobiCoreProduct_complexNormSq P ψ

/-- The squared norm of the residual Jacobi-core product is at most the
certified odd square-free ambient modulus. -/
theorem residualJacobiCoreProduct_sq_norm_le_modulus
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) :
    ‖residualJacobiCoreProduct P ψ‖ ^ 2 ≤ (P.modulus : ℝ) := by
  rw [residualJacobiCoreProduct_sq_norm]
  exact_mod_cast residualJacobiCoreNormSqFactor_le_modulus P ψ

/-- Closed square-root estimate for the residual product of nonexceptional
fixed Jacobi cores. -/
theorem residualJacobiCoreProduct_norm_le_sqrt_modulus
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) :
    ‖residualJacobiCoreProduct P ψ‖ ≤ Real.sqrt (P.modulus : ℝ) := by
  have hsq := residualJacobiCoreProduct_sq_norm_le_modulus P ψ
  have hq : 0 ≤ (P.modulus : ℝ) := by positivity
  have hsqrt : Real.sqrt (P.modulus : ℝ) ^ 2 = (P.modulus : ℝ) :=
    Real.sq_sqrt hq
  nlinarith [norm_nonneg (residualJacobiCoreProduct P ψ),
    Real.sqrt_nonneg (P.modulus : ℝ)]

/-- The residual local-character phase in source equation (30) has norm at
most one. -/
theorem residualJacobiPhase_norm_le_one
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod P.modulus) :
    ‖residualJacobiPhase P ψ y‖ ≤ 1 := by
  classical
  unfold residualJacobiPhase
  rw [norm_prod]
  calc
    ∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
        ‖oddPrimeQuadraticCharacter (P.prime i) (P.crtEquiv y i) *
          star (ψ i (P.crtEquiv y i))‖ ≤
      ∏ _i ∈ Finset.univ \ exceptionalPrimeIndices P ψ, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          rw [norm_mul, norm_star]
          have hquad := norm_mulChar_apply_le_one
            (oddPrimeQuadraticCharacter (P.prime i)) (P.crtEquiv y i)
          have hpsi := norm_mulChar_apply_le_one (ψ i) (P.crtEquiv y i)
          nlinarith [norm_nonneg (oddPrimeQuadraticCharacter (P.prime i)
            (P.crtEquiv y i)), norm_nonneg (ψ i (P.crtEquiv y i))]
    _ = 1 := by simp

/-- Exact odd square-free version of source equation (30): the generalized
Jacobi sum is the additive exceptional Ramanujan product times the residual
character phase and residual Jacobi-core product. -/
theorem generalizedJacobiLocalSum_source_factor
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod P.modulus) :
    generalizedJacobiLocalSum P ψ y =
      exceptionalRamanujanAdditiveProduct P ψ y *
        residualJacobiPhase P ψ y * residualJacobiCoreProduct P ψ := by
  rw [generalizedJacobiLocalSum_exceptional_additive_split]
  unfold residualJacobiPhase residualJacobiCoreProduct
  rw [show (∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
      oddPrimeGeneralizedJacobiLocal (P.prime i) (ψ i) (P.crtEquiv y i)) =
      ∏ i ∈ Finset.univ \ exceptionalPrimeIndices P ψ,
        (oddPrimeQuadraticCharacter (P.prime i) (P.crtEquiv y i) *
          star (ψ i (P.crtEquiv y i))) *
          oddPrimeGeneralizedJacobiCore (P.prime i) (ψ i) by
    apply Finset.prod_congr rfl
    intro i hi
    apply oddPrime_generalizedJacobiLocal_of_ne_quadratic
    intro h
    exact (Finset.mem_sdiff.mp hi).2 ((mem_exceptionalPrimeIndices P ψ i).mpr h)]
  rw [Finset.prod_mul_distrib]
  ring

omit [DecidableEq I] in
/-- The exceptional additive Ramanujan product is bounded by its certified
square-free ambient modulus. -/
theorem exceptionalRamanujanAdditiveProduct_norm_le_modulus
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod P.modulus) :
    ‖exceptionalRamanujanAdditiveProduct P ψ y‖ ≤ (P.modulus : ℝ) := by
  rw [exceptionalRamanujanAdditiveProduct, norm_prod]
  calc
    ∏ i ∈ exceptionalPrimeIndices P ψ,
        ‖oddPrimeRamanujanAdditiveSum (P.prime i) (P.crtEquiv y i)‖ ≤
        ∏ i ∈ exceptionalPrimeIndices P ψ, ((P.prime i).1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact norm_nonneg _
      · intro i hi
        exact oddPrime_ramanujanAdditiveSum_norm_le_prime _ _
    _ ≤ (P.modulus : ℝ) := by
      have hdiv : (∏ i ∈ exceptionalPrimeIndices P ψ, (P.prime i).1) ∣ P.modulus := by
        rw [modulus]
        exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
      have hmodpos : 0 < P.modulus := P.modulus_neZero.out |> Nat.pos_of_ne_zero
      exact_mod_cast Nat.le_of_dvd hmodpos hdiv

omit [DecidableEq I] in
/-- At every integer shift, the literal exceptional additive Ramanujan product
is bounded by the source gcd majorant `gcd(q, |r|)`. -/
theorem exceptionalRamanujanAdditiveProduct_norm_le_gcd
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (r : ℤ) :
    ‖exceptionalRamanujanAdditiveProduct P ψ (r : ZMod P.modulus)‖ ≤
      (P.modulus.gcd r.natAbs : ℝ) := by
  let g : I → ℕ := fun i => if ((P.prime i).1 : ℤ) ∣ r then (P.prime i).1 else 1
  have hcoord (i : I) :
      P.crtEquiv (r : ZMod P.modulus) i = 0 ↔ ((P.prime i).1 : ℤ) ∣ r := by
    simpa using P.crtEquiv_intCast_eq_iff_dvd_sub r 0 i
  have hlocal (i : I) :
      ‖oddPrimeRamanujanAdditiveSum (P.prime i)
        (P.crtEquiv (r : ZMod P.modulus) i)‖ ≤ (g i : ℝ) := by
    by_cases h : ((P.prime i).1 : ℤ) ∣ r
    · simpa only [g, if_pos h] using
        oddPrime_ramanujanAdditiveSum_norm_le_prime (P.prime i)
          (P.crtEquiv (r : ZMod P.modulus) i)
    · have hz : P.crtEquiv (r : ZMod P.modulus) i ≠ 0 := fun hz => h (hcoord i |>.mp hz)
      rw [oddPrime_ramanujanAdditiveSum, if_neg hz]
      simp only [g, if_neg h]
      norm_num
  rw [exceptionalRamanujanAdditiveProduct, norm_prod]
  calc
    ∏ i ∈ exceptionalPrimeIndices P ψ,
        ‖oddPrimeRamanujanAdditiveSum (P.prime i)
          (P.crtEquiv (r : ZMod P.modulus) i)‖ ≤
        ∏ i ∈ exceptionalPrimeIndices P ψ, (g i : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact norm_nonneg _
      · intro i hi
        exact hlocal i
    _ ≤ ∏ i, (g i : ℝ) := by
      have hdiv : (∏ i ∈ exceptionalPrimeIndices P ψ, g i) ∣ ∏ i, g i :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
      have hpos : 0 < ∏ i, g i := by
        apply Finset.prod_pos
        intro i hi
        dsimp [g]
        split_ifs
        · exact (P.prime i).2.1.pos
        · norm_num
      exact_mod_cast Nat.le_of_dvd hpos hdiv
    _ = quadraticShiftDivisorMajorant P r := by
      unfold quadraticShiftDivisorMajorant
      dsimp [g]
      apply Finset.prod_congr rfl
      intro i hi
      norm_cast
    _ ≤ P.modulus.gcd r.natAbs := quadraticShiftDivisorMajorant_le_gcd P r

omit [DecidableEq I] in
/-- Multiplying the Lemma-9 additive argument by a unit cannot change which
prime-local Ramanujan factors take their zero branch.  Thus the exact gcd
majorant survives the source shift `r m⁻¹`. -/
theorem exceptionalRamanujanAdditiveProduct_norm_le_gcd_unitInverse
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (r : ℤ) (m : (ZMod P.modulus)ˣ) :
    ‖exceptionalRamanujanAdditiveProduct P ψ
      ((r : ZMod P.modulus) * (↑(m⁻¹) : ZMod P.modulus))‖ ≤
      (P.modulus.gcd r.natAbs : ℝ) := by
  let g : I → ℕ := fun i => if ((P.prime i).1 : ℤ) ∣ r then (P.prime i).1 else 1
  have hbase (i : I) :
      P.crtEquiv (r : ZMod P.modulus) i = 0 ↔ ((P.prime i).1 : ℤ) ∣ r := by
    simpa using P.crtEquiv_intCast_eq_iff_dvd_sub r 0 i
  have hunit (i : I) :
      IsUnit (P.crtEquiv (↑(m⁻¹) : ZMod P.modulus) i) := by
    simpa using IsUnit.map
      ((Pi.evalRingHom (fun j => ZMod (P.prime j).1) i).comp P.crtEquiv.toRingHom)
      (m⁻¹).isUnit
  have hcoord (i : I) :
      P.crtEquiv ((r : ZMod P.modulus) * (↑(m⁻¹) : ZMod P.modulus)) i = 0 ↔
        ((P.prime i).1 : ℤ) ∣ r := by
    rw [map_mul, Pi.mul_apply]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with hzero | hzero
      · exact (hbase i).mp hzero
      · exact (hunit i).ne_zero hzero |>.elim
    · intro h
      rw [(hbase i).mpr h, zero_mul]
  have hlocal (i : I) :
      ‖oddPrimeRamanujanAdditiveSum (P.prime i)
        (P.crtEquiv ((r : ZMod P.modulus) * (↑(m⁻¹) : ZMod P.modulus)) i)‖ ≤ (g i : ℝ) := by
    by_cases h : ((P.prime i).1 : ℤ) ∣ r
    · simpa only [g, if_pos h] using
        oddPrime_ramanujanAdditiveSum_norm_le_prime (P.prime i)
          (P.crtEquiv ((r : ZMod P.modulus) * (↑(m⁻¹) : ZMod P.modulus)) i)
    · have hz : P.crtEquiv ((r : ZMod P.modulus) * (↑(m⁻¹) : ZMod P.modulus)) i ≠ 0 :=
        fun hz => h ((hcoord i).mp hz)
      rw [oddPrimeRamanujanAdditiveSum, if_neg hz]
      simp only [g, if_neg h]
      norm_num
  rw [exceptionalRamanujanAdditiveProduct, norm_prod]
  calc
    ∏ i ∈ exceptionalPrimeIndices P ψ,
        ‖oddPrimeRamanujanAdditiveSum (P.prime i)
          (P.crtEquiv ((r : ZMod P.modulus) * (↑(m⁻¹) : ZMod P.modulus)) i)‖ ≤
      ∏ i ∈ exceptionalPrimeIndices P ψ, (g i : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact norm_nonneg _
        · intro i hi
          exact hlocal i
    _ ≤ ∏ i, (g i : ℝ) := by
      have hdiv : (∏ i ∈ exceptionalPrimeIndices P ψ, g i) ∣ ∏ i, g i :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
      have hpos : 0 < ∏ i, g i := by
        apply Finset.prod_pos
        intro i hi
        dsimp [g]
        split_ifs
        · exact (P.prime i).2.1.pos
        · norm_num
      exact_mod_cast Nat.le_of_dvd hpos hdiv
    _ = quadraticShiftDivisorMajorant P r := by
      unfold quadraticShiftDivisorMajorant
      dsimp [g]
      apply Finset.prod_congr rfl
      intro i hi
      norm_cast
    _ ≤ P.modulus.gcd r.natAbs := quadraticShiftDivisorMajorant_le_gcd P r

/-- Positive-shift gcd mass underlying the Ramanujan-product summation in
source Lemma 9. -/
def ramanujanGcdIntervalMass (P : OddPrimeFamily I) (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R, (P.modulus.gcd r : ℝ)

omit [DecidableEq I] in
/-- Exact totient/divisor evaluation of the positive-shift gcd mass. -/
theorem ramanujanGcdIntervalMass_eq_totient
    (P : OddPrimeFamily I) (R : ℕ) :
    ramanujanGcdIntervalMass P R =
      ∑ e ∈ P.modulus.divisors, (Nat.totient e : ℝ) * ((R / e : ℕ) : ℝ) := by
  classical
  unfold ramanujanGcdIntervalMass
  have hmodpos : 0 < P.modulus := P.modulus_neZero.out |> Nat.pos_of_ne_zero
  have hsub : P.modulus - 1 + 1 = P.modulus := Nat.sub_add_cancel hmodpos
  calc
    _ = ∑ r ∈ Finset.Icc 1 R, ∑ e ∈ P.modulus.divisors,
        if r % e = 0 then (Nat.totient e : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      have hdist : Nat.dist r 0 = r := by
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.zero_le r), Nat.sub_zero]
      have h := gcd_succ_eq_sum_totient_residueClasses (P.modulus - 1) r 0
      rw [hsub, hdist] at h
      exact h
    _ = ∑ e ∈ P.modulus.divisors, (Nat.totient e : ℝ) * ((R / e : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      have hfilter : (Finset.Icc 1 R).filter (fun r => r % e = 0) =
          (Finset.Icc 1 R).filter (fun r => e ∣ r) := by
        ext r
        simp [Nat.dvd_iff_mod_eq_zero]
      rw [hfilter, Finset.sum_const, nsmul_eq_mul]
      have hIcc : Finset.Icc 1 R = Finset.Ioc 0 R := by
        ext r
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
      ring

omit [DecidableEq I] in
/-- Closed divisor-count bound for the positive-shift gcd mass. -/
theorem ramanujanGcdIntervalMass_le_divisorCount
    (P : OddPrimeFamily I) (R : ℕ) :
    ramanujanGcdIntervalMass P R ≤
      (R : ℝ) * (P.modulus.divisors.card : ℝ) := by
  rw [ramanujanGcdIntervalMass_eq_totient]
  calc
    _ ≤ ∑ e ∈ P.modulus.divisors, (R : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      have hterm : Nat.totient e * (R / e) ≤ R := by
        calc
          Nat.totient e * (R / e) ≤ e * (R / e) :=
            Nat.mul_le_mul_right (R / e) (Nat.totient_le e)
          _ = (R / e) * e := Nat.mul_comm _ _
          _ ≤ R := Nat.div_mul_le_self R e
      exact_mod_cast hterm
    _ = (R : ℝ) * (P.modulus.divisors.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Literal two-sided nonzero integer gcd mass from the final summation step
of source Lemma 9. -/
def ramanujanGcdSymmetricIntervalMass (P : OddPrimeFamily I) (R : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0,
    (P.modulus.gcd r.natAbs : ℝ)

omit [DecidableEq I] in
/-- The source range `0 < |r| ≤ R` is exactly two copies of the positive
gcd interval mass. -/
theorem ramanujanGcdSymmetricIntervalMass_eq_two_mul
    (P : OddPrimeFamily I) (R : ℕ) :
    ramanujanGcdSymmetricIntervalMass P R = 2 * ramanujanGcdIntervalMass P R := by
  let f : ℤ → ℝ := fun r => (P.modulus.gcd r.natAbs : ℝ)
  have hsplit := sum_Icc_symm_split (0 : ℤ) f R
  have hfull : ∑ r ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), f r =
      (P.modulus : ℝ) + 2 * ramanujanGcdIntervalMass P R := by
    calc
      _ = f 0 + ∑ r ∈ Finset.Icc 1 R, (f (0 + (r : ℤ)) + f (0 - (r : ℤ))) := by
        simpa only [zero_sub, zero_add] using hsplit
      _ = (P.modulus : ℝ) + 2 * ramanujanGcdIntervalMass P R := by
        simp [f, ramanujanGcdIntervalMass, Finset.sum_add_distrib]
        ring
  have hzero : (0 : ℤ) ∈ Finset.Icc (-(R : ℤ)) (R : ℤ) := by
    simp only [Finset.mem_Icc]
    omega
  have herase := Finset.sum_erase_add (s := Finset.Icc (-(R : ℤ)) (R : ℤ)) f hzero
  unfold ramanujanGcdSymmetricIntervalMass
  change ∑ r ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0, f r = _
  rw [← add_left_inj (a := f 0)]
  rw [herase, hfull]
  simp [f]
  ring

omit [DecidableEq I] in
/-- Closed `2R·d(q)` envelope for the literal two-sided Ramanujan/gcd
summation range. -/
theorem ramanujanGcdSymmetricIntervalMass_le_two_mul_divisorCount
    (P : OddPrimeFamily I) (R : ℕ) :
    ramanujanGcdSymmetricIntervalMass P R ≤
      2 * (R : ℝ) * (P.modulus.divisors.card : ℝ) := by
  rw [ramanujanGcdSymmetricIntervalMass_eq_two_mul]
  nlinarith [ramanujanGcdIntervalMass_le_divisorCount P R]

/-- Actual exceptional additive-Ramanujan mass on the literal source range
`0 < |r| ≤ R`. -/
def exceptionalRamanujanSymmetricNormMass (P : OddPrimeFamily I)
    (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) (R : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0,
    ‖exceptionalRamanujanAdditiveProduct P ψ (r : ZMod P.modulus)‖

omit [DecidableEq I] in
/-- The actual exceptional Ramanujan mass is bounded by its literal gcd mass. -/
theorem exceptionalRamanujanSymmetricNormMass_le_gcdMass
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ) (R : ℕ) :
    exceptionalRamanujanSymmetricNormMass P ψ R ≤ ramanujanGcdSymmetricIntervalMass P R := by
  unfold exceptionalRamanujanSymmetricNormMass ramanujanGcdSymmetricIntervalMass
  apply Finset.sum_le_sum
  intro r hr
  exact exceptionalRamanujanAdditiveProduct_norm_le_gcd P ψ r

omit [DecidableEq I] in
/-- Closed source-scale Ramanujan summation.  Nonpositive exponents are
classified explicitly; at every positive exponent Lean constructs the
divisor-bound constant internally. -/
theorem exceptionalRamanujanSymmetricNormMass_sourceScale
    (P : OddPrimeFamily I) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (R : ℕ) (ε : ℝ) :
    ε ≤ 0 ∨ ∃ C : ℝ, 0 < C ∧
      exceptionalRamanujanSymmetricNormMass P ψ R ≤
        C * (R : ℝ) * (P.modulus : ℝ) ^ ε := by
  by_cases hεnonpos : ε ≤ 0
  · exact Or.inl hεnonpos
  · right
    have hε : 0 < ε := lt_of_not_ge hεnonpos
    obtain ⟨C, hC, hdiv⟩ := _root_.RHTower.card_divisors_le_const_mul_rpow hε
    refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
    have hq1 : 1 ≤ P.modulus := Nat.one_le_iff_ne_zero.mpr P.modulus_neZero.out
    have hmass := exceptionalRamanujanSymmetricNormMass_le_gcdMass P ψ R
    have hgcd := ramanujanGcdSymmetricIntervalMass_le_two_mul_divisorCount P R
    have hfactor : 0 ≤ 2 * (R : ℝ) := by positivity
    calc
      exceptionalRamanujanSymmetricNormMass P ψ R ≤ ramanujanGcdSymmetricIntervalMass P R := hmass
      _ ≤ 2 * (R : ℝ) * (P.modulus.divisors.card : ℝ) := hgcd
      _ ≤ 2 * (R : ℝ) * (C * (P.modulus : ℝ) ^ ε) := by
        exact mul_le_mul_of_nonneg_left (hdiv P.modulus hq1) hfactor
      _ = (2 * C) * (R : ℝ) * (P.modulus : ℝ) ^ ε := by ring

end OddPrimeFamily

end RHTower
