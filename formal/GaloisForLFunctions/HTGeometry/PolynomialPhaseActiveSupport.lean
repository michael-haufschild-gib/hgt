import GaloisForLFunctions.HTGeometry.PolynomialPhaseAperture
import GaloisForLFunctions.HTGeometry.TorusTrigPolynomial
import GaloisForLFunctions.HTGeometry.LinearPhaseObservable
import GaloisForLFunctions.HTGeometry.ActiveLatticeCompressionClassification

/-!
# Active character support of polynomial phase observables

Evaluation of a multivariate polynomial on the product unit torus is its literal
finite Fourier expansion: each natural exponent becomes the same integer torus
character and its Fourier coefficient is the polynomial coefficient.  Thus the
analytic active support and active lattice agree exactly with the polynomial's
monomial support and Taylor-character lattice.
-/

open Complex Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-- A natural multivariate exponent regarded as an integer torus character. -/
def natExponentCharacter (e : d →₀ ℕ) : d → ℤ := fun i => (e i : ℤ)

omit [DecidableEq d] in
/-- A polynomial monomial restricted to the product unit torus is its torus character. -/
theorem eval_monomial_circleCoords_eq_mFourier
    (e : d →₀ ℕ) (x : UnitAddTorus d) :
    (∏ i ∈ e.support, circleCoords x i ^ e i) =
      UnitAddTorus.mFourier (natExponentCharacter e) x := by
  change (∏ i ∈ e.support, circleCoords x i ^ e i) =
    ∏ i, fourier (e i : ℤ) (x i)
  rw [Finset.prod_subset (Finset.subset_univ e.support)]
  · apply Finset.prod_congr rfl
    intro i _
    simp [circleCoords, fourier_apply]
    rw [AddCircle.toCircle_nsmul]
    norm_cast
  · intro i _ hnot
    rw [Finsupp.notMem_support_iff.mp hnot, pow_zero]

omit [DecidableEq d] in
/-- Exact finite Fourier expansion of a polynomial phase observable. -/
theorem torusRestriction_polynomialPhaseObservable
    (Q : MvPolynomial d ℂ) (x : UnitAddTorus d) :
    torusRestriction (polynomialPhaseObservable Q) x =
      ∑ e ∈ Q.support, Q.coeff e *
        UnitAddTorus.mFourier (natExponentCharacter e) x := by
  rw [torusRestriction, polynomialPhaseObservable, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro e _
  rw [eval_monomial_circleCoords_eq_mFourier]

omit [Fintype d] [DecidableEq d] in
theorem natExponentCharacter_injective :
    Function.Injective (natExponentCharacter : (d →₀ ℕ) → (d → ℤ)) := by
  intro e f h
  ext i
  have hi := congrFun h i
  change (e i : ℤ) = (f i : ℤ) at hi
  exact_mod_cast hi

/-- Fourier coefficients distribute over a finite sum of torus characters. -/
theorem mFourierCoeff_finset_sum {ι : Type} (s : Finset ι)
    (a : ι → ℂ) (e : ι → (d → ℤ)) (m : d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (fun x => ∑ j ∈ s, a j * UnitAddTorus.mFourier (e j) x) m =
      ∑ j ∈ s, a j * (if m = e j then 1 else 0) := by
  classical
  have hsplit : (fun x : UnitAddTorus d =>
      UnitAddTorus.mFourier (-m) x •
        ∑ j ∈ s, a j * UnitAddTorus.mFourier (e j) x) =
      fun x => ∑ j ∈ s, a j •
        (UnitAddTorus.mFourier (-m) x • UnitAddTorus.mFourier (e j) x) := by
    funext x
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  rw [UnitAddTorus.mFourierCoeff, hsplit, integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul, smul_eq_mul, ← UnitAddTorus.mFourierCoeff,
      mFourierCoeff_mFourier]
  · intro j _
    exact integrable_torus_of_continuous (by fun_prop)

/-- The active coefficient at a natural monomial character is exactly the
corresponding polynomial coefficient. -/
theorem activeCoeff_polynomialPhaseObservable_natExponent
    (Q : MvPolynomial d ℂ) (e : d →₀ ℕ) :
    activeCoeff (polynomialPhaseObservable Q) (natExponentCharacter e) = Q.coeff e := by
  classical
  rw [activeCoeff]
  rw [show torusRestriction (polynomialPhaseObservable Q) =
      fun x => ∑ q ∈ Q.support, Q.coeff q *
        UnitAddTorus.mFourier (natExponentCharacter q) x by
    funext x
    exact torusRestriction_polynomialPhaseObservable Q x]
  rw [mFourierCoeff_finset_sum]
  by_cases he : e ∈ Q.support
  · rw [Finset.sum_eq_single e]
    · simp
    · intro q _ hne
      have hneq : natExponentCharacter e ≠ natExponentCharacter q :=
        fun hchar => hne (natExponentCharacter_injective hchar.symm)
      rw [if_neg hneq, mul_zero]
    · exact fun h => absurd he h
  · have hcoeff : Q.coeff e = 0 := MvPolynomial.notMem_support_iff.mp he
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro q hq
    have hneq : natExponentCharacter e ≠ natExponentCharacter q := by
      intro hchar
      have heq : e = q := natExponentCharacter_injective hchar
      apply he
      rwa [heq]
    rw [if_neg hneq, mul_zero]

/-- Every integer character not arising from a natural exponent has zero
coefficient in a polynomial phase observable. -/
theorem activeCoeff_polynomialPhaseObservable_eq_zero_of_not_natExponent
    (Q : MvPolynomial d ℂ) (m : d → ℤ)
    (hm : ∀ e : d →₀ ℕ, m ≠ natExponentCharacter e) :
    activeCoeff (polynomialPhaseObservable Q) m = 0 := by
  classical
  rw [activeCoeff]
  rw [show torusRestriction (polynomialPhaseObservable Q) =
      fun x => ∑ q ∈ Q.support, Q.coeff q *
        UnitAddTorus.mFourier (natExponentCharacter q) x by
    funext x
    exact torusRestriction_polynomialPhaseObservable Q x]
  rw [mFourierCoeff_finset_sum]
  apply Finset.sum_eq_zero
  intro q _
  rw [if_neg (hm q), mul_zero]

/-- Exact equality between analytic active Fourier support and polynomial
monomial support. -/
theorem activeSupport_polynomialPhaseObservable (Q : MvPolynomial d ℂ) :
    activeSupport (polynomialPhaseObservable Q) =
      natExponentCharacter '' (Q.support : Set (d →₀ ℕ)) := by
  ext m
  constructor
  · intro hm
    by_contra hnot
    have hnone : ∀ e : d →₀ ℕ, m ≠ natExponentCharacter e := by
      intro e heq
      by_cases he : e ∈ Q.support
      · exact hnot ⟨e, he, heq.symm⟩
      · have hcoeff : Q.coeff e = 0 := MvPolynomial.notMem_support_iff.mp he
        have hactive := activeCoeff_polynomialPhaseObservable_natExponent Q e
        rw [← heq, hcoeff] at hactive
        exact hm hactive
    exact hm (activeCoeff_polynomialPhaseObservable_eq_zero_of_not_natExponent Q m hnone)
  · rintro ⟨e, he, rfl⟩
    change activeCoeff (polynomialPhaseObservable Q) (natExponentCharacter e) ≠ 0
    rw [activeCoeff_polynomialPhaseObservable_natExponent]
    exact MvPolynomial.mem_support_iff.mp he

/-- Character lattice generated by the support of a multivariate polynomial. -/
def polynomialCharacterLattice (Q : MvPolynomial d ℂ) : Submodule ℤ (d → ℤ) :=
  Submodule.span ℤ (natExponentCharacter '' (Q.support : Set (d →₀ ℕ)))

/-- Exact equality of the polynomial Taylor-character lattice and the analytic
active lattice of its phase observable. -/
theorem activeLattice_polynomialPhaseObservable (Q : MvPolynomial d ℂ) :
    activeLattice (polynomialPhaseObservable Q) = polynomialCharacterLattice Q := by
  rw [activeLattice, activeSupport_polynomialPhaseObservable]
  rfl

/-- Natural active-lattice rank of a polynomial is the complex span dimension
of the integer casts of its monomial exponents. -/
theorem activeLatticeNatRank_polynomialPhaseObservable (Q : MvPolynomial d ℂ) :
    activeLatticeNatRank (polynomialPhaseObservable Q) =
      Module.finrank ℂ
        (Submodule.span ℂ
          (intCharacterToComplex ''
            (natExponentCharacter '' (Q.support : Set (d →₀ ℕ))))) := by
  rw [activeLatticeNatRank, activeSupport_polynomialPhaseObservable]

end

end GaloisForLFunctions.HTGeometry
