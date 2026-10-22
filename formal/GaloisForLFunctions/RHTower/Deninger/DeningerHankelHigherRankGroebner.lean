import GaloisForLFunctions.RHTower.Deninger.DeningerFiniteHankelSecantSeparation
import GaloisForLFunctions.HTGeometry.IntegralMonicGroebnerTransfer

/-!
# Integral higher-rank Hankel Gröbner and secant-kernel theorem

For every rank bound `r`, finite moment window `Fin N`, and commutative coefficient ring `R`,
the canonical consecutive-row `(r+1)` Hankel minors are a monic degree-lex Gröbner basis and
generate exactly the kernel of the ordered `r`-atom moment parameterization.  No reducedness,
domain, characteristic, or field hypothesis is used for kernel equality or the Gröbner theorem.

The proof combines three integral ingredients: exact diagonal monicity, the c-chain theorem saying
that every nonstandard monomial is divisible by one such diagonal, and coefficient-faithful
separation of all remaining c-chain standard monomials.  Thus polynomial division works unchanged
over rings with nilpotents and zero divisors.
-/

namespace RHTower
noncomputable section

open MvPolynomial
open scoped BigOperators MonomialOrder

/-- Ideal of canonical finite `(r+1) × (r+1)` consecutive-row Hankel minors. -/
def finiteHankelSecantIdeal (R : Type*) [CommRing R] (N r : ℕ) :
    Ideal (MvPolynomial (Fin N) R) :=
  Ideal.span (finiteHankelMaximalMinorSetOver R N (r + 1))

/-- Every canonical maximal Hankel minor vanishes on the ordered `r`-atom moment
parameterization, over arbitrary commutative coefficient rings. -/
theorem finiteHankelSecantIdeal_le_parameterization_ker
    (R : Type*) [CommRing R] (N r : ℕ) :
    finiteHankelSecantIdeal R N r ≤
      RingHom.ker (finiteHankelSecantParameterization R N r) := by
  rw [finiteHankelSecantIdeal, Ideal.span_le]
  intro p hp
  rcases hp with ⟨c, hbound, _hc, rfl⟩
  exact RingHom.mem_ker.mpr
    (finiteHankelSecantParameterization_minor_zero R r c hbound)

/-- Integral Conca--Nam secant presentation: over every commutative ring, including rings with
nilpotents, the finite higher-rank Hankel determinantal ideal is exactly the kernel of the
ordered-atom moment map. -/
theorem finiteHankelSecantIdeal_eq_parameterization_ker
    (R : Type*) [CommRing R] (N r : ℕ) :
    finiteHankelSecantIdeal R N r =
      RingHom.ker (finiteHankelSecantParameterization R N r) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    exact Subsingleton.elim _ _
  letI := hR
  apply le_antisymm
  · exact finiteHankelSecantIdeal_le_parameterization_ker R N r
  · intro p hp
    let B := finiteHankelMaximalMinorSetOver R N (r + 1)
    have hmonic : ∀ b ∈ B, MonomialOrder.degLex.Monic b :=
      finiteHankelMaximalMinorSetOver_degLex_monic R N (r + 1)
    have hunit : ∀ b ∈ B, IsUnit (MonomialOrder.degLex.leadingCoeff b) := by
      intro b hb
      rw [(hmonic b hb).leadingCoeff_eq_one]
      exact isUnit_one
    obtain ⟨g, rem, hpr, _hdeg, hnormal⟩ :=
      MonomialOrder.degLex.div_set hunit p
    let q := Finsupp.linearCombination (MvPolynomial (Fin N) R)
      (fun b : B => (b : MvPolynomial (Fin N) R)) g
    have hq : q ∈ finiteHankelSecantIdeal R N r :=
      MonomialOrder.linearCombination_mem_span B g
    have hqker : q ∈ RingHom.ker (finiteHankelSecantParameterization R N r) :=
      finiteHankelSecantIdeal_le_parameterization_ker R N r hq
    have hpzero : finiteHankelSecantParameterization R N r p = 0 :=
      RingHom.mem_ker.mp hp
    have hqzero : finiteHankelSecantParameterization R N r q = 0 :=
      RingHom.mem_ker.mp hqker
    have hremzero : finiteHankelSecantParameterization R N r rem = 0 := by
      change p = q + rem at hpr
      have hmap := congrArg (finiteHankelSecantParameterization R N r) hpr
      rw [map_add, hpzero, hqzero, zero_add] at hmap
      exact hmap.symm
    have hremReduced : ∀ e ∈ rem.support, FiniteHankelChainReduced N r e := by
      intro e he hnot
      have hnotRed : ¬FiniteHankelChainReduced N r e := by
        intro hred
        exact hred hnot
      obtain ⟨c, hbound, hc, hdiag⟩ :=
        exists_finiteHankelMinor_diagonal_le_of_not_chainReduced hnotRed
      have hb : finiteHankelMaximalMinorOver R c hbound ∈ B :=
        ⟨c, hbound, hc, rfl⟩
      apply hnormal e he (finiteHankelMaximalMinorOver R c hbound) hb
      rwa [finiteHankelMaximalMinorOver_degLex_degree c hbound hc]
    have hrem0 : rem = 0 := by
      by_contra hne
      exact (finiteHankelSecantParameterization_ne_zero_of_reduced
        R N r hremReduced hne) hremzero
    rw [finiteHankelSecantIdeal, hpr, hrem0, add_zero]
    exact hq

/-- Canonical finite higher-rank Hankel minors form a degree-lex Gröbner basis over every
commutative coefficient ring.  Monicity makes this statement valid over zero-divisor and
nilpotent targets, not only over fields. -/
theorem finiteHankelSecant_degLex_isGroebnerBasis
    (R : Type*) [CommRing R] (N r : ℕ) :
    MonomialOrder.degLex.IsGroebnerBasis
      (finiteHankelMaximalMinorSetOver R N (r + 1)) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    intro p _hp hp0
    exact (hp0 (Subsingleton.elim _ _)).elim
  letI := hR
  let B := finiteHankelMaximalMinorSetOver R N (r + 1)
  intro p hp hp0
  have hpker : p ∈ RingHom.ker (finiteHankelSecantParameterization R N r) := by
    rw [← finiteHankelSecantIdeal_eq_parameterization_ker R N r,
      finiteHankelSecantIdeal]
    exact hp
  have hmonic : ∀ b ∈ B, MonomialOrder.degLex.Monic b :=
    finiteHankelMaximalMinorSetOver_degLex_monic R N (r + 1)
  have hunit : ∀ b ∈ B, IsUnit (MonomialOrder.degLex.leadingCoeff b) := by
    intro b hb
    rw [(hmonic b hb).leadingCoeff_eq_one]
    exact isUnit_one
  obtain ⟨g, rem, hpr, hdeg, hnormal⟩ :=
    MonomialOrder.degLex.div_set hunit p
  let q := Finsupp.linearCombination (MvPolynomial (Fin N) R)
    (fun b : B => (b : MvPolynomial (Fin N) R)) g
  have hq : q ∈ finiteHankelSecantIdeal R N r :=
    MonomialOrder.linearCombination_mem_span B g
  have hqker : q ∈ RingHom.ker (finiteHankelSecantParameterization R N r) :=
    finiteHankelSecantIdeal_le_parameterization_ker R N r hq
  have hremzero : finiteHankelSecantParameterization R N r rem = 0 := by
    change p = q + rem at hpr
    have hmap := congrArg (finiteHankelSecantParameterization R N r) hpr
    rw [map_add, RingHom.mem_ker.mp hpker, RingHom.mem_ker.mp hqker,
      zero_add] at hmap
    exact hmap.symm
  have hremReduced : ∀ e ∈ rem.support, FiniteHankelChainReduced N r e := by
    intro e he hnot
    have hnotRed : ¬FiniteHankelChainReduced N r e := by
      intro hred
      exact hred hnot
    obtain ⟨c, hbound, hc, hdiag⟩ :=
      exists_finiteHankelMinor_diagonal_le_of_not_chainReduced hnotRed
    have hb : finiteHankelMaximalMinorOver R c hbound ∈ B :=
      ⟨c, hbound, hc, rfl⟩
    apply hnormal e he (finiteHankelMaximalMinorOver R c hbound) hb
    rwa [finiteHankelMaximalMinorOver_degLex_degree c hbound hc]
  have hrem0 : rem = 0 := by
    by_contra hne
    exact (finiteHankelSecantParameterization_ne_zero_of_reduced
      R N r hremReduced hne) hremzero
  have hpq : p = q := by
    change p = q + rem at hpr
    simpa [hrem0] using hpr
  have hcoeffq : MvPolynomial.coeff (MonomialOrder.degLex.degree p) q ≠ 0 := by
    rw [← hpq]
    exact MonomialOrder.leadingCoeff_ne_zero_iff.mpr hp0
  dsimp [q] at hcoeffq
  rw [Finsupp.linearCombination_apply] at hcoeffq
  have hsum : (∑ b ∈ g.support,
      MvPolynomial.coeff (MonomialOrder.degLex.degree p)
        (g b • (b : MvPolynomial (Fin N) R))) ≠ 0 := by
    change (MvPolynomial.coeffAddMonoidHom
      (MonomialOrder.degLex.degree p))
        (∑ b ∈ g.support, g b • (b : MvPolynomial (Fin N) R)) ≠ 0 at hcoeffq
    rw [map_sum] at hcoeffq
    exact hcoeffq
  obtain ⟨b, hbmem, hbcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hbcoeff' : MvPolynomial.coeff (MonomialOrder.degLex.degree p)
      ((b : MvPolynomial (Fin N) R) * g b) ≠ 0 := by
    simpa [smul_eq_mul, mul_comm] using hbcoeff
  have hbpSupport : MonomialOrder.degLex.degree p ∈
      ((b : MvPolynomial (Fin N) R) * g b).support :=
    MvPolynomial.mem_support_iff.mpr hbcoeff'
  have hprodDegree : MonomialOrder.degLex.degree
      ((b : MvPolynomial (Fin N) R) * g b) =
        MonomialOrder.degLex.degree p := by
    apply MonomialOrder.degLex.toSyn.injective
    exact le_antisymm (hdeg b)
      (MonomialOrder.degLex.le_degree hbpSupport)
  have hgb : g b ≠ 0 := Finsupp.mem_support_iff.mp hbmem
  have hmulDegree : MonomialOrder.degLex.degree
      ((b : MvPolynomial (Fin N) R) * g b) =
        MonomialOrder.degLex.degree (b : MvPolynomial (Fin N) R) +
          MonomialOrder.degLex.degree (g b) :=
    MonomialOrder.degLex.degree_mul_of_isRegular_left
      (hunit b b.property).isRegular hgb
  refine ⟨b, b.property, ?_⟩
  rw [← hprodDegree, hmulDegree]
  intro i
  exact Nat.le_add_right _ _

/-- Over a domain, every finite higher-rank Hankel secant ideal is prime. -/
theorem finiteHankelSecantIdeal_isPrime
    (R : Type*) [CommRing R] [IsDomain R] (N r : ℕ) :
    (finiteHankelSecantIdeal R N r).IsPrime := by
  rw [finiteHankelSecantIdeal_eq_parameterization_ker]
  exact RingHom.ker_isPrime (finiteHankelSecantParameterization R N r)

/-- Integral capstone: every finite canonical higher-rank Hankel determinantal ideal over `ℤ`
is prime. -/
theorem finiteHankelSecantIdeal_int_isPrime (N r : ℕ) :
    (finiteHankelSecantIdeal ℤ N r).IsPrime :=
  finiteHankelSecantIdeal_isPrime ℤ N r

end
end RHTower
