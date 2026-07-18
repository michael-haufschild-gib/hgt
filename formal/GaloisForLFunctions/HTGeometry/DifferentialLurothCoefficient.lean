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

/-- Reconstruct a two-block differential polynomial from its finite family of right-block
monomials and left-block coefficients. -/
theorem differentialPolynomialTwoBlock_reconstruct
    {F : Type*} [CommRing F]
    (C : DifferentialPolynomial (Unit ⊕ Unit) F) :
    C = ∑ m ∈ (differentialPolynomialTwoBlockEquiv F C).support,
      differentialPolynomialLeft (κ := Unit)
          (differentialPolynomialTwoBlockCoefficient m C) *
        differentialPolynomialRight (ι := Unit)
          (MvPolynomial.monomial m 1) := by
  apply (differentialPolynomialTwoBlockEquiv F).injective
  simp only [map_sum, map_mul, differentialPolynomialTwoBlockEquiv_left,
    differentialPolynomialTwoBlockEquiv_right,
    differentialPolynomialTwoBlockCoefficient, MvPolynomial.map_monomial, map_one]
  simpa using (MvPolynomial.as_sum (differentialPolynomialTwoBlockEquiv F C)).symm

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

/-- Coordinate map from an intermediate field of a free scalar differential field into the
rational field of the formal scalar jet palette. -/
def differentialIntermediateToJetFraction
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    G →ₐ[F] FractionRing (DifferentialPolynomial Unit F) := by
  let hG' : G ≤ differentialAdjoin F (Set.range fun _ : Unit ↦ y) := by
    simpa [Set.range_const] using hG
  exact
    (differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy).symm.toAlgHom.comp
      (IntermediateField.inclusion hG')

theorem differentialIntermediateToJetFraction_injective
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    Function.Injective (differentialIntermediateToJetFraction G hG hy) :=
  (differentialIntermediateToJetFraction G hG hy).injective

/-- The free-jet parametrization sends a formal scalar differential polynomial to its evaluation
at the chosen free element. -/
theorem differentialIndependentAdjoinParametrization_algebraMap_val
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (U : DifferentialPolynomial Unit F) :
    (((differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy)
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)) U) :
      differentialAdjoin F (Set.range fun _ : Unit ↦ y)) : E) =
      differentialPolynomialEval (C := F) (fun _ : Unit ↦ y) U := by
  let A := differentialAdjoin F (Set.range fun _ : Unit ↦ y)
  let e := differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
  have hring :
      (IntermediateField.val A).toRingHom.comp
          (e.toRingEquiv.toRingHom.comp
            (algebraMap (DifferentialPolynomial Unit F)
              (FractionRing (DifferentialPolynomial Unit F)))) =
        (differentialPolynomialEval (C := F) (fun _ : Unit ↦ y)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [A, e, differentialPolynomialEval]
    · rintro ⟨u, n⟩
      obtain rfl : u = () := Subsingleton.elim _ _
      have hx := congrArg Subtype.val
        (differentialIndependentAdjoinParametrization_X
          (fun _ : Unit ↦ y) hy () n)
      simpa [A, e, differentialPolynomialEval_X] using hx
  exact RingHom.congr_fun hring U

/-- A relation over the intermediate field remains a relation after replacing the free element by
the formal scalar jet palette and transporting every coefficient to its rational jet expression. -/
theorem mapped_differentialRelation_eval_freeJet_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G}
    (hP : P ∈ differentialIntermediateRelationIdeal G y) :
    let R := DifferentialPolynomial Unit F
    let K := FractionRing R
    MvPolynomial.aeval
        (fun j : Unit × ℕ ↦ algebraMap R K (MvPolynomial.X j))
        (MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P) = 0 := by
  let R := DifferentialPolynomial Unit F
  let K := FractionRing R
  let x : Unit × ℕ → K :=
    fun j ↦ algebraMap R K (MvPolynomial.X j)
  let A := differentialAdjoin F (Set.range fun _ : Unit ↦ y)
  let e : K ≃ₐ[F] A :=
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
  let hG' : G ≤ A := by
    simpa [A, Set.range_const] using hG
  let inc : G →ₐ[F] A := IntermediateField.inclusion hG'
  let jetA : Unit × ℕ → A := fun j ↦
    ⟨differentialJet j.2 y,
      differentialJet_mem_differentialAdjoin F (Set.mem_range_self ()) j.2⟩
  have hcoeff (g : G) :
      e (differentialIntermediateToJetFraction G hG hy g) = inc g := by
    simp [e, inc, differentialIntermediateToJetFraction, hG']
  have hjet (j : Unit × ℕ) : e (x j) = jetA j := by
    rcases j with ⟨u, n⟩
    obtain rfl : u = () := Subsingleton.elim _ _
    change differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F))
          (MvPolynomial.X ((), n))) =
      ⟨differentialJet n y,
        differentialJet_mem_differentialAdjoin F (Set.mem_range_self ()) n⟩
    exact differentialIndependentAdjoinParametrization_X
      (fun _ : Unit ↦ y) hy () n
  have hring :
      e.toRingEquiv.toRingHom.comp
          ((MvPolynomial.aeval x).toRingHom.comp
            (MvPolynomial.map
              (differentialIntermediateToJetFraction G hG hy).toRingHom)) =
        MvPolynomial.eval₂Hom inc.toRingHom jetA := by
    apply MvPolynomial.ringHom_ext
    · intro g
      simpa using hcoeff g
    · intro j
      simpa using hjet j
  have hright : (MvPolynomial.eval₂Hom inc.toRingHom jetA) P = 0 := by
    have hval :
        (IntermediateField.val A).toRingHom.comp
            (MvPolynomial.eval₂Hom inc.toRingHom jetA) =
          (differentialPolynomialEvalOver (K := G)
            (fun _ : Unit ↦ y)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro g
        simp [A, inc, differentialPolynomialEvalOver]
      · rintro ⟨u, n⟩
        obtain rfl : u = () := Subsingleton.elim _ _
        simp [A, jetA, differentialPolynomialEvalOver]
    apply Subtype.val_injective
    exact (RingHom.congr_fun hval P).trans hP
  apply e.injective
  rw [map_zero]
  exact (RingHom.congr_fun hring P).trans hright

/-- Base change commutes with substitution of the formal variables by themselves. -/
theorem mvPolynomial_aeval_map_algebraMap_self
    {B K σ : Type*} [CommRing B] [CommRing K]
    [Algebra (MvPolynomial σ B) K]
    (P : MvPolynomial σ (MvPolynomial σ B)) :
    MvPolynomial.aeval
        (fun j : σ ↦ algebraMap (MvPolynomial σ B) K
          (MvPolynomial.X j))
        (MvPolynomial.map (algebraMap (MvPolynomial σ B) K) P) =
      algebraMap (MvPolynomial σ B) K
        (MvPolynomial.aeval
          (fun j : σ ↦ (MvPolynomial.X j : MvPolynomial σ B)) P) := by
  have hring :
      (MvPolynomial.aeval
          (fun j : σ ↦ algebraMap (MvPolynomial σ B) K
            (MvPolynomial.X j))).toRingHom.comp
          (MvPolynomial.map (algebraMap (MvPolynomial σ B) K)) =
        (algebraMap (MvPolynomial σ B) K).comp
          (MvPolynomial.aeval
            (fun j : σ ↦ (MvPolynomial.X j : MvPolynomial σ B))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      simp
  exact RingHom.congr_fun hring P

/-- Put the two formal scalar differential blocks on the diagonal while keeping the common left
jet palette formal. -/
def differentialPolynomialTwoBlockDiagonal
    {F : Type*} [CommRing F]
    (C : DifferentialPolynomial (Unit ⊕ Unit) F) :
    DifferentialPolynomial Unit F :=
  MvPolynomial.aeval (fun j : Unit × ℕ ↦ MvPolynomial.X j)
    (differentialPolynomialTwoBlockEquiv F C)

/-- The normalized two-block representative attached to one nonzero relation over the
intermediate field.  Its coefficient family is primitive in the left jet ring, it is nonzero,
and its two blocks agree on the diagonal. -/
structure PrimitiveTwoBlockDifferentialCharacteristic
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G) where
  polynomial : DifferentialPolynomial (Unit ⊕ Unit) F
  ne_zero : polynomial ≠ 0
  primitive : MvPolynomialPrimitive
    (differentialPolynomialTwoBlockEquiv F polynomial)
  scalar : (FractionRing (DifferentialPolynomial Unit F))ˣ
  clearing :
    MvPolynomial.map
        (algebraMap (DifferentialPolynomial Unit F)
          (FractionRing (DifferentialPolynomial Unit F)))
        (differentialPolynomialTwoBlockEquiv F polynomial) =
      MvPolynomial.C (scalar : FractionRing (DifferentialPolynomial Unit F)) *
        MvPolynomial.map (differentialIntermediateToJetFraction G hG hy).toRingHom P
  diagonal : differentialPolynomialTwoBlockDiagonal polynomial = 0

/-- Common-denominator clearing and primitive normalization of a nonzero relation over an
intermediate field of the free scalar differential field. -/
theorem exists_primitiveTwoBlockDifferentialCharacteristic
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G} (hP0 : P ≠ 0)
    (hP : P ∈ differentialIntermediateRelationIdeal G y) :
    Nonempty (PrimitiveTwoBlockDifferentialCharacteristic G hG hy P) := by
  classical
  let R := DifferentialPolynomial Unit F
  let K := FractionRing R
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  have hmapP0 : MvPolynomial.map φ.toRingHom P ≠ 0 := by
    intro hzero
    apply hP0
    apply MvPolynomial.map_injective φ.toRingHom φ.injective
    simpa using hzero
  letI : NormalizationMonoid R :=
    UniqueFactorizationMonoid.normalizationMonoid
  letI : NormalizedGCDMonoid R :=
    UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨Q, hQ0, hQprimitive, a, hQclear⟩ :=
    exists_primitive_mvPolynomial_fraction_clear
      (R := R) (K := K) (σ := Unit × ℕ) hmapP0
  let C : DifferentialPolynomial (Unit ⊕ Unit) F :=
    (differentialPolynomialTwoBlockEquiv F).symm Q
  have hC0 : C ≠ 0 := by
    intro hzero
    apply hQ0
    simpa [C] using congrArg (differentialPolynomialTwoBlockEquiv F) hzero
  have hdiagK :
      algebraMap R K
          (MvPolynomial.aeval (fun j : Unit × ℕ ↦ MvPolynomial.X j) Q) = 0 := by
    calc
      algebraMap R K
          (MvPolynomial.aeval (fun j : Unit × ℕ ↦ MvPolynomial.X j) Q) =
          MvPolynomial.aeval
            (fun j : Unit × ℕ ↦ algebraMap R K (MvPolynomial.X j))
            (MvPolynomial.map (algebraMap R K) Q) :=
              (mvPolynomial_aeval_map_algebraMap_self Q).symm
      _ = MvPolynomial.aeval
            (fun j : Unit × ℕ ↦ algebraMap R K (MvPolynomial.X j))
            (MvPolynomial.C (a : K) * MvPolynomial.map φ.toRingHom P) := by
              rw [hQclear]
      _ = 0 := by
        rw [map_mul, MvPolynomial.aeval_C,
          mapped_differentialRelation_eval_freeJet_eq_zero G hG hy hP, mul_zero]
  have hdiag : differentialPolynomialTwoBlockDiagonal C = 0 := by
    have hQdiag :
        MvPolynomial.aeval
          (fun j : Unit × ℕ ↦ (MvPolynomial.X j : R)) Q = 0 := by
      apply IsFractionRing.injective R K
      simpa using hdiagK
    simpa [differentialPolynomialTwoBlockDiagonal, C] using hQdiag
  exact ⟨
    { polynomial := C
      ne_zero := hC0
      primitive := by simpa [C] using hQprimitive
      scalar := a
      clearing := by simpa [C, R, K, φ] using hQclear
      diagonal := hdiag }⟩

/-- Every left-block coefficient of the primitive representative specializes to the corresponding
characteristic coefficient times the single clearing scalar. -/
theorem PrimitiveTwoBlockDifferentialCharacteristic.coefficient_specialization
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hG : G ≤ differentialAdjoin F ({y} : Set E))
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (P : DifferentialPolynomial Unit G)
    (C : PrimitiveTwoBlockDifferentialCharacteristic G hG hy P)
    (m : (Unit × ℕ) →₀ ℕ) :
    differentialPolynomialEval (C := F) (fun _ : Unit ↦ y)
        (differentialPolynomialTwoBlockCoefficient m C.polynomial) =
      (((differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy)
          (C.scalar : FractionRing (DifferentialPolynomial Unit F)) :
        differentialAdjoin F (Set.range fun _ : Unit ↦ y)) : E) *
        (P.coeff m : E) := by
  let R := DifferentialPolynomial Unit F
  let K := FractionRing R
  let A := differentialAdjoin F (Set.range fun _ : Unit ↦ y)
  let e : K ≃ₐ[F] A :=
    differentialIndependentAdjoinParametrization (fun _ : Unit ↦ y) hy
  let φ : G →ₐ[F] K := differentialIntermediateToJetFraction G hG hy
  have hcoeff := congrArg (MvPolynomial.coeff m) C.clearing
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hcoeff
  have hφ (g : G) : ((e (φ g) : A) : E) = (g : E) := by
    simp [e, φ, A, differentialIntermediateToJetFraction]
  have hval := congrArg (fun z : K ↦ ((e z : A) : E)) hcoeff
  rw [map_mul, hφ] at hval
  rw [← differentialIndependentAdjoinParametrization_algebraMap_val hy]
  exact hval

/-- A bounded-order relation is ordinarily divisible by the minimal characteristic polynomial.
The proof performs pseudo-division only at the characteristic leader, so no iterate of the
characteristic polynomial enters.  Minimality kills the remainder and primeness removes the
explicit initial power. -/
theorem IsMinimalScalarDifferentialPolynomialRank.dvd_of_relation_order_le
    {K : Type*} [Field K]
    {I : Ideal (DifferentialPolynomial Unit K)} (hItop : I ≠ ⊤)
    {P : DifferentialPolynomial Unit K}
    (hP : IsMinimalScalarDifferentialPolynomialRank (I : Set _) P)
    (hPirreducible : Irreducible P)
    (hInitialNot : scalarDifferentialPolynomialInitial P ∉ I)
    {Q : DifferentialPolynomial Unit K} (hQI : Q ∈ I)
    (hQorder : scalarDifferentialPolynomialOrder Q ≤
      scalarDifferentialPolynomialOrder P) :
    P ∣ Q := by
  classical
  let leader := scalarDifferentialPolynomialLeader P
  have hPdegree : MvPolynomial.degreeOf leader P ≠ 0 := by
    rw [← MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
    exact scalarDifferentialPolynomialLeader_mem_vars hP.2.2.1
  let d := supportedMvPolynomialPseudoReductionAt leader Q P hPdegree
  have hRbound : ScalarJetOrderBound
      (scalarDifferentialPolynomialOrder P) d.remainder := by
    intro m hm hmem
    rcases Finset.mem_union.mp (d.remainder_vars_subset hmem) with hmemQ | hmemP
    · exact scalarJetOrderBound_of_order_le hQorder m hm hmemQ
    · exact scalarJetOrderBound_order P m hm hmemP
  have hRorder : scalarDifferentialPolynomialOrder d.remainder ≤
      scalarDifferentialPolynomialOrder P :=
    scalarDifferentialPolynomialOrder_le_of_orderBound hRbound
  have hleftI :
      scalarDifferentialPolynomialInitial P ^ d.exponent * Q ∈ I :=
    I.mul_mem_left _ hQI
  have hrightI : P * d.quotient ∈ I :=
    Ideal.mul_mem_right d.quotient I hP.1
  have hRI : d.remainder ∈ I := by
    rw [show d.remainder =
        scalarDifferentialPolynomialInitial P ^ d.exponent * Q -
          P * d.quotient by
      rw [d.eq_mul_add]
      ring]
    exact I.sub_mem hleftI hrightI
  have hRzero : d.remainder = 0 := by
    by_contra hR0
    by_cases hRvars : d.remainder.vars.Nonempty
    · have hmin := hP.2.2.2 hRI hR0 hRvars
      have horderEq : scalarDifferentialPolynomialOrder P =
          scalarDifferentialPolynomialOrder d.remainder :=
        Nat.le_antisymm hmin.1 hRorder
      have hleaderEq : scalarDifferentialPolynomialLeader d.remainder = leader := by
        unfold scalarDifferentialPolynomialLeader leader
        exact Prod.ext (Subsingleton.elim _ _) horderEq.symm
      have hdegreeMin := hmin.2.1 horderEq
      unfold scalarDifferentialPolynomialLeaderDegree at hdegreeMin
      rw [hleaderEq] at hdegreeMin
      exact (Nat.not_le_of_lt d.remainder_degree_lt) hdegreeMin
    · have hempty : d.remainder.vars = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hRvars
      have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hempty
      have hc : d.remainder.coeff 0 ≠ 0 := by
        intro hc
        apply hR0
        rw [hC, hc]
        simp
      have hunit : IsUnit d.remainder := by
        rw [hC]
        exact IsUnit.map MvPolynomial.C hc.isUnit
      exact hItop (I.eq_top_of_isUnit_mem hRI hunit)
  have hdivProduct :
      P ∣ scalarDifferentialPolynomialInitial P ^ d.exponent * Q := by
    refine ⟨d.quotient, ?_⟩
    simpa [hRzero] using d.eq_mul_add
  rcases hPirreducible.prime.dvd_mul.mp hdivProduct with hpow | hdiv
  · have hdivInitial := hPirreducible.prime.dvd_of_dvd_pow hpow
    apply (hInitialNot ?_).elim
    rcases hdivInitial with ⟨T, hT⟩
    rw [hT]
    exact Ideal.mul_mem_right T I hP.1
  · exact hdiv

/-- Multivariable Gauss contraction for the support-gcd notion of primitive polynomial.  If a
primitive polynomial divides another after extending the coefficient UFD to its fraction field,
then the divisibility already holds over the coefficient ring. -/
theorem MvPolynomialPrimitive.dvd_of_fraction_map_dvd
    {R K σ : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {P Q : MvPolynomial σ R} (hPprimitive : MvPolynomialPrimitive P)
    (hP0 : P ≠ 0)
    (hdiv : MvPolynomial.map (algebraMap R K) P ∣
      MvPolynomial.map (algebraMap R K) Q) :
    P ∣ Q := by
  classical
  obtain ⟨T, hT⟩ := hdiv
  obtain ⟨d, A, hAclear⟩ :=
    exists_mvPolynomial_fraction_clear (R := R) (K := K) (σ := σ) T
  have hmapEq :
      MvPolynomial.map (algebraMap R K) (P * A) =
        MvPolynomial.map (algebraMap R K) (MvPolynomial.C (d : R) * Q) := by
    simp only [map_mul, MvPolynomial.map_C]
    rw [hAclear, hT]
    ring
  have hEq : P * A = MvPolynomial.C (d : R) * Q := by
    exact MvPolynomial.map_injective (algebraMap R K)
      (IsFractionRing.injective R K) hmapEq
  have hProduct : P ∣ MvPolynomial.C (d : R) * Q := by
    rw [← hEq]
    exact dvd_mul_right P A
  apply UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors
    hP0 ?_ hProduct
  intro p hpP hpCd hpprime
  obtain ⟨r, _hrd, hpr⟩ :=
    (MvPolynomial.dvd_C_iff_exists (nonZeroDivisors.ne_zero d.2)).mp hpCd
  have hCrP : MvPolynomial.C r ∣ P := by
    simpa [hpr] using hpP
  have hrunit : IsUnit r := hPprimitive r hCrP
  have hCunit : IsUnit (MvPolynomial.C r : MvPolynomial σ R) :=
    IsUnit.map MvPolynomial.C hrunit
  exact hpprime.not_unit (by simpa [hpr] using hCunit)

/-- Mutual divisibility of two nonzero two-block differential polynomials over a field gives an
exact quotient in the base-field unit group, not merely an arbitrary polynomial-ring unit. -/
theorem twoBlock_eq_baseUnit_mul_of_dvd_dvd
    {F : Type*} [Field F]
    {C D : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hCD : C ∣ D) (hDC : D ∣ C) :
    ∃ c : Fˣ, D = MvPolynomial.C (c : F) * C := by
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hCD hDC
  obtain ⟨r, hr, hur⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  let c : Fˣ := hr.unit
  refine ⟨c, ?_⟩
  calc
    D = C * (u : DifferentialPolynomial (Unit ⊕ Unit) F) := hu.symm
    _ = C * MvPolynomial.C r := by rw [hur]
    _ = MvPolynomial.C r * C := mul_comm _ _
    _ = MvPolynomial.C (c : F) * C := by rw [IsUnit.unit_spec hr]

/-- A nonzero scalar differential relation over an intermediate field of a free scalar
differential field has two coefficients with a genuinely non-base ratio.  Otherwise all
coefficients are one common intermediate-field scalar times a base polynomial, contradicting
differential independence. -/
theorem exists_differentialRelation_coefficientRatio_not_mem_bot
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (G : IntermediateField F E) {y : E}
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    {P : DifferentialPolynomial Unit G} (hP0 : P ≠ 0)
    (hP : P ∈ differentialIntermediateRelationIdeal G y) :
    ∃ m n : (Unit × ℕ) →₀ ℕ, P.coeff n ≠ 0 ∧
      ((P.coeff m / P.coeff n : G) : E) ∉
        (⊥ : IntermediateField F E) := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨n, hn⟩ := Finsupp.ne_iff.mp hP0
  have hnSupport : n ∈ P.support := by
    simpa [MvPolynomial.mem_support_iff] using hn
  have hratioBot (m : (Unit × ℕ) →₀ ℕ) :
      ((P.coeff m / P.coeff n : G) : E) ∈
        (⊥ : IntermediateField F E) :=
    hnone m n hn
  have hratioRange (m : (Unit × ℕ) →₀ ℕ) :
      ((P.coeff m / P.coeff n : G) : E) ∈
        Set.range (algebraMap F E) :=
    (IntermediateField.mem_bot.mp (hratioBot m))
  let c : ((Unit × ℕ) →₀ ℕ) → F :=
    fun m ↦ Classical.choose (hratioRange m)
  have hc (m : (Unit × ℕ) →₀ ℕ) :
      algebraMap F E (c m) = ((P.coeff m / P.coeff n : G) : E) :=
    Classical.choose_spec (hratioRange m)
  have hratioG (m : (Unit × ℕ) →₀ ℕ) :
      P.coeff m / P.coeff n = algebraMap F G (c m) := by
    apply Subtype.val_injective
    exact (hc m).symm
  have hcoeff (m : (Unit × ℕ) →₀ ℕ) :
      P.coeff m = P.coeff n * algebraMap F G (c m) := by
    simpa [mul_comm] using (div_eq_iff hn).mp (hratioG m)
  let B : DifferentialPolynomial Unit F :=
    ∑ m ∈ P.support, MvPolynomial.monomial m (c m)
  have hfactor :
      P = MvPolynomial.C (P.coeff n) *
        MvPolynomial.map (algebraMap F G) B := by
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
    by_cases hm : m ∈ P.support
    · rw [hcoeff m]
      simp [B, MvPolynomial.coeff_sum, hm]
    · have hm0 : P.coeff m = 0 := by
        simpa [MvPolynomial.mem_support_iff] using hm
      rw [hm0]
      simp [B, MvPolynomial.coeff_sum, hm]
  have hB0 : B ≠ 0 := by
    intro hzero
    apply hP0
    rw [hfactor, hzero, map_zero, mul_zero]
  have hEvalP :
      differentialPolynomialEvalOver (K := G) (fun _ : Unit ↦ y) P = 0 := hP
  rw [hfactor, map_mul, differentialPolynomialEvalOver_C,
    differentialPolynomialEvalOver_map_intermediate] at hEvalP
  have hnE : ((P.coeff n : G) : E) ≠ 0 := by
    exact Subtype.coe_ne_coe.mpr hn
  have hEvalB :
      differentialPolynomialEvalOver (K := F) (fun _ : Unit ↦ y) B = 0 :=
    (mul_eq_zero.mp hEvalP).resolve_left hnE
  have hBzero : B = 0 := by
    apply hy.eq_zero_of_aeval_eq_zero
    simpa [differentialPolynomialEvalOver, differentialPolynomialEval] using hEvalB
  exact hB0 hBzero

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
theorem differentialPolynomialTwoBlockEquiv_crossDifference
    {F : Type*} [CommRing F]
    (P Q : DifferentialPolynomial Unit F) :
    differentialPolynomialTwoBlockEquiv F
        (differentialPolynomialCrossDifference P Q) =
      MvPolynomial.C Q * MvPolynomial.map MvPolynomial.C P -
        MvPolynomial.C P * MvPolynomial.map MvPolynomial.C Q := by
  simp [differentialPolynomialCrossDifference]

/-- Coefficient comparison for a two-block projective cross-difference. -/
theorem differentialPolynomialTwoBlockCoefficient_crossDifference
    {F : Type*} [CommRing F]
    (m : (Unit × ℕ) →₀ ℕ)
    (P Q : DifferentialPolynomial Unit F) :
    differentialPolynomialTwoBlockCoefficient m
        (differentialPolynomialCrossDifference P Q) =
      Q * MvPolynomial.C (P.coeff m) -
        P * MvPolynomial.C (Q.coeff m) := by
  simp [differentialPolynomialTwoBlockCoefficient,
    differentialPolynomialTwoBlockEquiv_crossDifference,
    MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map]

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
