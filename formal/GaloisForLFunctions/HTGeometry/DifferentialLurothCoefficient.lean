import GaloisForLFunctions.HTGeometry.DifferentialCharacteristicPseudoReduction
import GaloisForLFunctions.HTGeometry.DifferentialExchange
import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# The primitive two-copy coefficient step in differential Lüroth theory

This file builds the coefficient layer after characteristic pseudo-reduction.  A polynomial in two
scalar differential indeterminates is represented as a polynomial in the right jet block with
coefficients in the left jet block.  The finite coefficient family is then cleared from the free
jet fraction field and made primitive before the two-copy cross-difference argument.

No divisibility, characteristic-set reduction, coefficient-ratio theorem, or field-generation
conclusion is assumed.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- Split two scalar differential blocks and then commute the iterated multivariable-polynomial
layers.  The result regards the right block as polynomial variables and the left block as the
coefficient ring. -/
def differentialPolynomialTwoBlockEquiv
    (F : Type*) [CommRing F] :
    DifferentialPolynomial (Unit ⊕ Unit) F ≃ₐ[F]
      MvPolynomial (Unit × ℕ) (DifferentialPolynomial Unit F) :=
  (diffPolySumSplit Unit Unit F).trans
    (MvPolynomial.commAlgEquiv F (Unit × ℕ) (Unit × ℕ))

@[simp]
theorem differentialPolynomialTwoBlockEquiv_X_inl
    {F : Type*} [CommRing F] (n : ℕ) :
    differentialPolynomialTwoBlockEquiv F
        (MvPolynomial.X (Sum.inl (), n)) =
      MvPolynomial.C (MvPolynomial.X ((), n)) := by
  simp [differentialPolynomialTwoBlockEquiv, diffPolySumSplit_X_inl]

@[simp]
theorem differentialPolynomialTwoBlockEquiv_X_inr
    {F : Type*} [CommRing F] (n : ℕ) :
    differentialPolynomialTwoBlockEquiv F
        (MvPolynomial.X (Sum.inr (), n)) =
      MvPolynomial.X ((), n) := by
  simp [differentialPolynomialTwoBlockEquiv, diffPolySumSplit_X_inr]

@[simp]
theorem differentialPolynomialTwoBlockEquiv_C
    {F : Type*} [CommRing F] (c : F) :
    differentialPolynomialTwoBlockEquiv F (MvPolynomial.C c) =
      MvPolynomial.C (MvPolynomial.C c) := by
  simp [differentialPolynomialTwoBlockEquiv, diffPolySumSplit_C]

/-- A left-block differential polynomial becomes a coefficient constant. -/
@[simp]
theorem differentialPolynomialTwoBlockEquiv_left
    {F : Type*} [CommRing F] (P : DifferentialPolynomial Unit F) :
    differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialLeft (κ := Unit) P) = MvPolynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      rcases j with ⟨u, n⟩
      obtain rfl : u = () := Subsingleton.elim _ _
      simp [hP]

/-- A right-block differential polynomial becomes the same polynomial after coefficient
embedding into the left jet ring. -/
@[simp]
theorem differentialPolynomialTwoBlockEquiv_right
    {F : Type*} [CommRing F] (P : DifferentialPolynomial Unit F) :
    differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialRight (ι := Unit) P) =
      MvPolynomial.map MvPolynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      rcases j with ⟨u, n⟩
      obtain rfl : u = () := Subsingleton.elim _ _
      simp [hP]

/-- Coefficient of a right-block jet monomial, valued in the left scalar jet ring. -/
def differentialPolynomialTwoBlockCoefficient
    {F : Type*} [CommRing F]
    (m : (Unit × ℕ) →₀ ℕ) (C : DifferentialPolynomial (Unit ⊕ Unit) F) :
    DifferentialPolynomial Unit F :=
  (differentialPolynomialTwoBlockEquiv F C).coeff m

/-- A multivariable polynomial is primitive over its coefficient ring when every coefficient-ring
constant dividing it is a unit.  This is the exact notion needed for the two-block Gauss step. -/
def MvPolynomialPrimitive
    {R σ : Type*} [CommRing R] (P : MvPolynomial σ R) : Prop :=
  ∀ r : R, MvPolynomial.C r ∣ P → IsUnit r

/-- A primitive-part certificate for a multivariable polynomial.  It records a scalar content,
the primitive quotient, and the exact factorization. -/
structure MvPolynomialPrimitivePart
    {R σ : Type*} [CommRing R] (P : MvPolynomial σ R) where
  content : R
  polynomial : MvPolynomial σ R
  factorization : P = MvPolynomial.C content * polynomial
  primitive : MvPolynomialPrimitive polynomial

/-- Extract the gcd of the finite coefficient support of a multivariable polynomial.  Unlike the
univariate `Polynomial.primPart`, this construction works for an arbitrary (possibly infinite)
variable type because each individual polynomial still has finite support. -/
noncomputable def mvPolynomialPrimitivePart
    {R σ : Type*} [CommRing R] [NormalizedGCDMonoid R]
    (P : MvPolynomial σ R) : MvPolynomialPrimitivePart P := by
  classical
  by_cases hP : P = 0
  · exact
      { content := 0
        polynomial := 1
        factorization := by simp [hP]
        primitive := by
          intro r hr
          rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hr
          exact isUnit_of_dvd_one (by simpa using hr 0) }
  · have hs : P.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      exact fun h ↦ hP (MvPolynomial.support_eq_empty.mp h)
    let q : ((σ →₀ ℕ) → R) := Classical.choose (Finset.extract_gcd P.coeff hs)
    have hq : ∀ m ∈ P.support,
        P.coeff m = P.support.gcd P.coeff * q m :=
      (Classical.choose_spec (Finset.extract_gcd P.coeff hs)).1
    have hqgcd : P.support.gcd q = 1 :=
      (Classical.choose_spec (Finset.extract_gcd P.coeff hs)).2
    let Q : MvPolynomial σ R :=
      ∑ m ∈ P.support, MvPolynomial.monomial m (q m)
    refine
      { content := P.support.gcd P.coeff
        polynomial := Q
        factorization := ?_
        primitive := ?_ }
    · apply MvPolynomial.ext
      intro m
      by_cases hm : m ∈ P.support
      · rw [MvPolynomial.coeff_C_mul, hq m hm]
        simp [Q, MvPolynomial.coeff_sum, hm]
      · have hPm : P.coeff m = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hm
        rw [hPm, MvPolynomial.coeff_C_mul]
        simp [Q, MvPolynomial.coeff_sum, hm]
    · intro r hr
      rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hr
      have hrgcd : r ∣ P.support.gcd q := by
        apply Finset.dvd_gcd
        intro m hm
        have hcoeff : Q.coeff m = q m := by
          simp [Q, MvPolynomial.coeff_sum, hm]
        simpa [hcoeff] using hr m
      rw [hqgcd] at hrgcd
      exact isUnit_of_dvd_one hrgcd

/-- The whole multivariable polynomial ring over a fraction field is itself a localization.  Hence
one nonzero denominator clears all coefficients simultaneously; no enumeration or recursive
coefficient clearing is needed. -/
theorem exists_mvPolynomial_fraction_clear
    {R K σ : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (P : MvPolynomial σ K) :
    ∃ d : nonZeroDivisors R, ∃ Q : MvPolynomial σ R,
      MvPolynomial.map (algebraMap R K) Q =
        MvPolynomial.C (algebraMap R K (d : R)) * P := by
  classical
  letI := MvPolynomial.algebraMvPolynomial (σ := σ) (R := R) (S := K)
  let M : Submonoid R := nonZeroDivisors R
  haveI : IsLocalization (M.map (MvPolynomial.C (σ := σ)))
      (MvPolynomial σ K) := MvPolynomial.isLocalization M K
  obtain ⟨b, hb⟩ := IsLocalization.exists_integer_multiple
    (M.map (MvPolynomial.C (σ := σ))) P
  rcases b.2 with ⟨d, hdM, hdb⟩
  obtain ⟨Q, hQ⟩ := hb
  refine ⟨⟨d, hdM⟩, Q, ?_⟩
  rw [MvPolynomial.algebraMap_def] at hQ
  calc
    MvPolynomial.map (algebraMap R K) Q = (b : MvPolynomial σ R) • P := hQ
    _ = algebraMap (MvPolynomial σ R) (MvPolynomial σ K)
          (MvPolynomial.C d) * P := by
      rw [Algebra.smul_def, hdb]
    _ = MvPolynomial.C (algebraMap R K (d : R)) * P := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]

/-- A nonzero polynomial remains nonzero after common-denominator clearing. -/
theorem exists_mvPolynomial_fraction_clear_ne_zero
    {R K σ : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {P : MvPolynomial σ K} (hP : P ≠ 0) :
    ∃ d : nonZeroDivisors R, ∃ Q : MvPolynomial σ R,
      Q ≠ 0 ∧
      MvPolynomial.map (algebraMap R K) Q =
        MvPolynomial.C (algebraMap R K (d : R)) * P := by
  obtain ⟨d, Q, hQ⟩ :=
    exists_mvPolynomial_fraction_clear (R := R) (K := K) (σ := σ) P
  refine ⟨d, Q, ?_, hQ⟩
  intro hQ0
  rw [hQ0, map_zero, zero_eq_mul] at hQ
  rcases hQ with hd | hP0
  · have hd' : algebraMap R K (d : R) = 0 := by
      simpa using congrArg (MvPolynomial.coeff (0 : σ →₀ ℕ)) hd
    exact (nonZeroDivisors.ne_zero d.2)
      (IsFractionRing.injective R K (by simpa using hd'))
  · exact hP hP0

/-- Primitive common-denominator clearing.  The primitive numerator differs from the original
fraction-field polynomial by one nonzero scalar in the fraction field. -/
theorem exists_primitive_mvPolynomial_fraction_clear
    {R K σ : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {P : MvPolynomial σ K} (hP : P ≠ 0) :
    ∃ Q : MvPolynomial σ R, Q ≠ 0 ∧ MvPolynomialPrimitive Q ∧
      ∃ a : Kˣ, MvPolynomial.map (algebraMap R K) Q =
        MvPolynomial.C (a : K) * P := by
  classical
  obtain ⟨d, A, hA0, hAmap⟩ :=
    exists_mvPolynomial_fraction_clear_ne_zero
      (R := R) (K := K) (σ := σ) hP
  let pp := mvPolynomialPrimitivePart A
  have hQ0 : pp.polynomial ≠ 0 := by
    intro hzero
    apply hA0
    rw [pp.factorization, hzero, mul_zero]
  have hg0 : pp.content ≠ 0 := by
    intro hzero
    apply hA0
    rw [pp.factorization, hzero, MvPolynomial.C_0, zero_mul]
  have hdK : algebraMap R K (d : R) ≠ 0 := by
    intro hzero
    exact (nonZeroDivisors.ne_zero d.2)
      (IsFractionRing.injective R K (by simpa using hzero))
  have hgK : algebraMap R K pp.content ≠ 0 := by
    intro hzero
    exact hg0 (IsFractionRing.injective R K (by simpa using hzero))
  let a : Kˣ := Units.mk0
    (algebraMap R K (d : R) / algebraMap R K pp.content)
    (div_ne_zero hdK hgK)
  refine ⟨pp.polynomial, hQ0, pp.primitive, a, ?_⟩
  have hfacMap := congrArg (MvPolynomial.map (algebraMap R K)) pp.factorization
  simp only [map_mul, MvPolynomial.map_C] at hfacMap
  apply mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hgK)
  calc
    MvPolynomial.C (algebraMap R K pp.content) *
          MvPolynomial.map (algebraMap R K) pp.polynomial =
        MvPolynomial.map (algebraMap R K) A := hfacMap.symm
    _ = MvPolynomial.C (algebraMap R K (d : R)) * P := hAmap
    _ = MvPolynomial.C (algebraMap R K pp.content) *
        (MvPolynomial.C (a : K) * P) := by
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      change MvPolynomial.C (algebraMap R K (d : R)) * P =
        MvPolynomial.C
          (algebraMap R K pp.content *
            (algebraMap R K (d : R) / algebraMap R K pp.content)) * P
      rw [mul_comm (algebraMap R K pp.content), div_mul_cancel₀ _ hgK]

/-- The projective cross-difference of two scalar differential polynomials on two independent
blocks. -/
def differentialPolynomialCrossDifference
    {F : Type*} [CommRing F]
    (P Q : DifferentialPolynomial Unit F) :
    DifferentialPolynomial (Unit ⊕ Unit) F :=
  differentialPolynomialLeft (κ := Unit) Q *
      differentialPolynomialRight (ι := Unit) P -
    differentialPolynomialLeft (κ := Unit) P *
      differentialPolynomialRight (ι := Unit) Q

@[simp]
theorem differentialPolynomialEval_left
    {F E : Type*} [CommRing F] [CommRing E] [Algebra F E] [Differential E]
    (x : Unit → E) (z : Unit → E) (P : DifferentialPolynomial Unit F) :
    differentialPolynomialEval (C := F) (Sum.elim x z)
        (differentialPolynomialLeft (κ := Unit) P) =
      differentialPolynomialEval (C := F) x P := by
  have hring :
      (differentialPolynomialEval (C := F) (Sum.elim x z)).toRingHom.comp
          (differentialPolynomialLeft (C := F) (κ := Unit)).toRingHom =
        (differentialPolynomialEval (C := F) x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [differentialPolynomialEval]
    · rintro ⟨u, n⟩
      simp [differentialPolynomialEval_X]
  exact RingHom.congr_fun hring P

@[simp]
theorem differentialPolynomialEval_right
    {F E : Type*} [CommRing F] [CommRing E] [Algebra F E] [Differential E]
    (x : Unit → E) (z : Unit → E) (P : DifferentialPolynomial Unit F) :
    differentialPolynomialEval (C := F) (Sum.elim x z)
        (differentialPolynomialRight (ι := Unit) P) =
      differentialPolynomialEval (C := F) z P := by
  have hring :
      (differentialPolynomialEval (C := F) (Sum.elim x z)).toRingHom.comp
          (differentialPolynomialRight (C := F) (ι := Unit)).toRingHom =
        (differentialPolynomialEval (C := F) z).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [differentialPolynomialEval]
    · rintro ⟨u, n⟩
      simp [differentialPolynomialEval_X]
  exact RingHom.congr_fun hring P

/-- The cross-difference vanishes after putting the two scalar jet blocks on the diagonal. -/
theorem differentialPolynomialEval_crossDifference_diagonal
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (y : E) (P Q : DifferentialPolynomial Unit F) :
    differentialPolynomialEval (C := F) (Sum.elim (fun _ : Unit ↦ y) (fun _ : Unit ↦ y))
        (differentialPolynomialCrossDifference P Q) = 0 := by
  rw [show differentialPolynomialCrossDifference P Q =
      differentialPolynomialLeft (κ := Unit) Q *
          differentialPolynomialRight (ι := Unit) P -
        differentialPolynomialLeft (κ := Unit) P *
          differentialPolynomialRight (ι := Unit) Q from rfl,
    map_sub, map_mul, map_mul]
  rw [differentialPolynomialEval_left, differentialPolynomialEval_right,
    differentialPolynomialEval_left, differentialPolynomialEval_right]
  ring

/-- Swap the two scalar differential blocks. -/
def differentialPolynomialTwoBlockSwap
    (F : Type*) [CommRing F] :
    DifferentialPolynomial (Unit ⊕ Unit) F →ₐ[F]
      DifferentialPolynomial (Unit ⊕ Unit) F :=
  MvPolynomial.rename
    (fun p : (Unit ⊕ Unit) × ℕ ↦ (Equiv.sumComm Unit Unit p.1, p.2))

@[simp]
theorem differentialPolynomialTwoBlockSwap_left
    {F : Type*} [CommRing F] (P : DifferentialPolynomial Unit F) :
    differentialPolynomialTwoBlockSwap F
        (differentialPolynomialLeft (κ := Unit) P) =
      differentialPolynomialRight (ι := Unit) P := by
  unfold differentialPolynomialTwoBlockSwap differentialPolynomialLeft
    differentialPolynomialRight
  rw [MvPolynomial.rename_rename]
  congr 1

@[simp]
theorem differentialPolynomialTwoBlockSwap_right
    {F : Type*} [CommRing F] (P : DifferentialPolynomial Unit F) :
    differentialPolynomialTwoBlockSwap F
        (differentialPolynomialRight (ι := Unit) P) =
      differentialPolynomialLeft (κ := Unit) P := by
  unfold differentialPolynomialTwoBlockSwap differentialPolynomialLeft
    differentialPolynomialRight
  rw [MvPolynomial.rename_rename]
  congr 1

/-- Swapping the two copies negates the projective cross-difference. -/
theorem differentialPolynomialTwoBlockSwap_crossDifference
    {F : Type*} [CommRing F] (P Q : DifferentialPolynomial Unit F) :
    differentialPolynomialTwoBlockSwap F
        (differentialPolynomialCrossDifference P Q) =
      -differentialPolynomialCrossDifference P Q := by
  simp [differentialPolynomialCrossDifference]
  ring

end

end GaloisForLFunctions
