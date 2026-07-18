import GaloisForLFunctions.HTGeometry.DifferentialCharacteristicPseudoReduction
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Distinguished-variable Bezout and scalar-extension factor support

This file isolates the algebraic content of Ritt's equation (78).  A finite family of
univariate polynomials over a UFD, with no common nonunit divisor, becomes a Bezout family over
the fraction field.  The fraction-field multipliers are cleared by one common denominator, so
the resulting right-hand side is a nonzero coefficient-ring constant.

The second half applies that identity twice to a multivariable polynomial.  If an irreducible
polynomial is extended from one field to another, every irreducible factor after scalar extension
contains every variable of the original polynomial.  The proof is entirely algebraic: omitting
one variable makes the factor divide every coefficient in that variable, while equation (78) in
any variable of the factor forces a positive-degree polynomial to divide a nonzero constant.
-/

namespace GaloisForLFunctions

noncomputable section

open Polynomial

/-! ## The distinguished-variable equivalence and scalar extension -/

/-- A variable different from the distinguished variable becomes a coefficient variable. -/
@[simp]
theorem mvPolynomialPolynomialEquivAt_X_ne
    {R σ : Type*} [CommSemiring R] {i j : σ} (hji : j ≠ i) :
    mvPolynomialPolynomialEquivAt (K := R) i (MvPolynomial.X j) =
      Polynomial.C (MvPolynomial.X ⟨j, hji⟩) := by
  classical
  unfold mvPolynomialPolynomialEquivAt
  simp [Equiv.optionSubtypeNe_symm_of_ne hji]

/-- The distinguished variable becomes the univariate polynomial variable. -/
@[simp]
theorem mvPolynomialPolynomialEquivAt_X_self
    {R σ : Type*} [CommSemiring R] (i : σ) :
    mvPolynomialPolynomialEquivAt (K := R) i (MvPolynomial.X i) = Polynomial.X := by
  classical
  unfold mvPolynomialPolynomialEquivAt
  simp [Equiv.optionSubtypeNe_symm_self]

/-- A polynomial supported away from the distinguished variable becomes a constant polynomial.
This is the exact inverse-coordinate statement used to expose a factor as a common coefficient
divisor. -/
@[simp]
theorem mvPolynomialPolynomialEquivAt_rename_ne
    {R σ : Type*} [CommSemiring R] (i : σ)
    (P : MvPolynomial {j : σ // j ≠ i} R) :
    mvPolynomialPolynomialEquivAt (K := R) i
        (MvPolynomial.rename Subtype.val P) = Polynomial.C P := by
  classical
  unfold mvPolynomialPolynomialEquivAt
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_rename]
  rw [show (Equiv.optionSubtypeNe i).symm ∘ Subtype.val =
      (some : {j : σ // j ≠ i} → Option {j : σ // j ≠ i}) by
    funext j
    exact Equiv.optionSubtypeNe_symm_of_ne j.2]
  exact optionEquivLeft_rename_some P

/-- Singling out a variable commutes with scalar extension.  This supplies the coefficient-level
identity needed after applying `Polynomial.C_dvd_iff_dvd_coeff`. -/
theorem mvPolynomialPolynomialEquivAt_map
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (i : σ) (P : MvPolynomial σ R) :
    mvPolynomialPolynomialEquivAt (K := S) i (MvPolynomial.map f P) =
      Polynomial.map (MvPolynomial.map f)
        (mvPolynomialPolynomialEquivAt (K := R) i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r =>
      simp [mvPolynomialPolynomialEquivAt]
  | add P Q hP hQ =>
      simpa only [map_add, Polynomial.map_add] using
        congrArg₂ (fun U V ↦ U + V) hP hQ
  | mul_X P j hP =>
      by_cases hji : j = i
      · subst j
        simpa only [map_mul, Polynomial.map_mul, MvPolynomial.map_X,
          mvPolynomialPolynomialEquivAt_X_self, Polynomial.map_X] using
          congrArg (fun U ↦ U * Polynomial.X) hP
      · simpa only [map_mul, Polynomial.map_mul, MvPolynomial.map_X,
          mvPolynomialPolynomialEquivAt_X_ne hji, Polynomial.map_C] using
          congrArg
            (fun U ↦ U * Polynomial.C (MvPolynomial.X ⟨j, hji⟩)) hP

/-! ## Localization and primitive Gauss contraction -/

/-- One denominator clears a univariate polynomial over a fraction field. -/
theorem exists_polynomial_fraction_clear
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (P : Polynomial K) :
    ∃ d : nonZeroDivisors R, ∃ Q : Polynomial R,
      Polynomial.map (algebraMap R K) Q =
        Polynomial.C (algebraMap R K (d : R)) * P := by
  let M : Submonoid R := nonZeroDivisors R
  letI : Algebra (Polynomial R) (Polynomial K) := Polynomial.algebra R K
  haveI : IsLocalization (M.map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization M K
  obtain ⟨b, hb⟩ :=
    IsLocalization.exists_integer_multiple (M.map Polynomial.C) P
  rcases b.2 with ⟨d, hdM, hdb⟩
  obtain ⟨Q, hQ⟩ := hb
  refine ⟨⟨d, hdM⟩, Q, ?_⟩
  rw [Polynomial.algebraMap_def] at hQ
  calc
    Polynomial.map (algebraMap R K) Q = (b : Polynomial R) • P := hQ
    _ = algebraMap (Polynomial R) (Polynomial K) (Polynomial.C d) * P := by
      rw [Algebra.smul_def, hdb]
    _ = Polynomial.C (algebraMap R K d) * P := by
      change Polynomial.map (algebraMap R K) (Polynomial.C d) * P = _
      rw [Polynomial.map_C]

/-- Denominator clearing preserves nonzeroness. -/
theorem exists_polynomial_fraction_clear_ne_zero
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {P : Polynomial K} (hP : P ≠ 0) :
    ∃ d : nonZeroDivisors R, ∃ Q : Polynomial R, Q ≠ 0 ∧
      Polynomial.map (algebraMap R K) Q =
        Polynomial.C (algebraMap R K (d : R)) * P := by
  obtain ⟨d, Q, hQ⟩ := exists_polynomial_fraction_clear (R := R) (K := K) P
  refine ⟨d, Q, ?_, hQ⟩
  intro hQ0
  have hmul : Polynomial.C (algebraMap R K (d : R)) * P = 0 := by
    simpa [hQ0] using hQ.symm
  rcases mul_eq_zero.mp hmul with hd | hP0
  · have hd' : algebraMap R K (d : R) = 0 := by
      simpa using congrArg (fun T : Polynomial K ↦ T.coeff 0) hd
    exact (nonZeroDivisors.ne_zero d.2)
      (IsFractionRing.injective R K (by simpa using hd'))
  · exact hP hP0

/-- Primitive denominator clearing for a univariate polynomial.  The primitive numerator differs
from the fraction-field polynomial by one nonzero scalar. -/
theorem exists_primitive_polynomial_fraction_clear
    {R K : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {P : Polynomial K} (hP : P ≠ 0) :
    ∃ Q : Polynomial R, Q ≠ 0 ∧ Q.IsPrimitive ∧
      ∃ a : Kˣ, Polynomial.map (algebraMap R K) Q =
        Polynomial.C (a : K) * P := by
  obtain ⟨d, A, hA0, hAmap⟩ :=
    exists_polynomial_fraction_clear_ne_zero (R := R) (K := K) hP
  let Q : Polynomial R := A.primPart
  have hQ0 : Q ≠ 0 := A.primPart_ne_zero
  have hc0 : A.content ≠ 0 := by
    intro hc
    exact hA0 (Polynomial.content_eq_zero_iff.mp hc)
  have hdK : algebraMap R K (d : R) ≠ 0 := by
    simpa using
      (IsFractionRing.injective R K).ne (nonZeroDivisors.ne_zero d.2)
  have hcK : algebraMap R K A.content ≠ 0 := by
    simpa using (IsFractionRing.injective R K).ne hc0
  let a : Kˣ := Units.mk0
    (algebraMap R K (d : R) / algebraMap R K A.content)
    (div_ne_zero hdK hcK)
  refine ⟨Q, hQ0, A.isPrimitive_primPart, a, ?_⟩
  have hfacMap := congrArg (Polynomial.map (algebraMap R K))
    A.eq_C_content_mul_primPart
  simp only [Polynomial.map_mul, Polynomial.map_C] at hfacMap
  apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hcK)
  calc
    Polynomial.C (algebraMap R K A.content) *
          Polynomial.map (algebraMap R K) Q =
        Polynomial.map (algebraMap R K) A := hfacMap.symm
    _ = Polynomial.C (algebraMap R K (d : R)) * P := hAmap
    _ = Polynomial.C (algebraMap R K A.content) *
        (Polynomial.C (a : K) * P) := by
      rw [← mul_assoc, ← Polynomial.C_mul]
      change Polynomial.C (algebraMap R K (d : R)) * P =
        Polynomial.C
          (algebraMap R K A.content *
            (algebraMap R K (d : R) / algebraMap R K A.content)) * P
      rw [mul_div_cancel₀ (algebraMap R K (d : R)) hcK]

/-- A polynomial dividing a nonzero constant has degree zero. -/
theorem Polynomial.natDegree_eq_zero_of_dvd_C
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {P : Polynomial R} {c : R} (hP : P ∣ Polynomial.C c) (hc : c ≠ 0) :
    P.natDegree = 0 := by
  exact Nat.eq_zero_of_le_zero
    (by simpa using
      Polynomial.natDegree_le_of_dvd hP (Polynomial.C_ne_zero.mpr hc))

/-- Gauss contraction with no primitivity assumption on the dividend.  Mathlib's standard
fraction-map divisibility theorem asks for both polynomials to be primitive; equation (78) needs
the stronger form where only the divisor is primitive. -/
theorem Polynomial.IsPrimitive.dvd_of_fraction_map_dvd
    {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {P Q : Polynomial R} (hPprimitive : P.IsPrimitive) (hP0 : P ≠ 0)
    (hdiv : Polynomial.map (algebraMap R K) P ∣
      Polynomial.map (algebraMap R K) Q) :
    P ∣ Q := by
  obtain ⟨T, hT⟩ := hdiv
  obtain ⟨d, A, hAclear⟩ :=
    exists_polynomial_fraction_clear (R := R) (K := K) T
  have hmapEq :
      Polynomial.map (algebraMap R K) (P * A) =
        Polynomial.map (algebraMap R K) (Polynomial.C (d : R) * Q) := by
    simp only [Polynomial.map_mul, Polynomial.map_C]
    rw [hAclear, hT]
    ring
  have hEq : P * A = Polynomial.C (d : R) * Q := by
    exact Polynomial.map_injective (algebraMap R K)
      (IsFractionRing.injective R K) hmapEq
  have hProduct : P ∣ Polynomial.C (d : R) * Q := by
    rw [← hEq]
    exact dvd_mul_right P A
  apply UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors
    hP0 ?_ hProduct
  intro p hpP hpCd hpprime
  have hpdeg : p.natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_dvd_C hpCd (nonZeroDivisors.ne_zero d.2)
  have hpC : p = Polynomial.C (p.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hpdeg
  have hcoeffDvd : Polynomial.C (p.coeff 0) ∣ P := by
    rw [hpC] at hpP
    exact hpP
  have hcoeffUnit : IsUnit (p.coeff 0) := hPprimitive _ hcoeffDvd
  have hpUnit : IsUnit p := by
    rw [hpC]
    exact IsUnit.map Polynomial.C hcoeffUnit
  exact hpprime.not_unit hpUnit

/-- A single denominator clears a finite family of fraction-field polynomials. -/
theorem exists_polynomial_family_fraction_clear
    {R K ι : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Finite ι] (P : ι → Polynomial K) :
    ∃ d : nonZeroDivisors R, ∃ Q : ι → Polynomial R, ∀ i,
      Polynomial.map (algebraMap R K) (Q i) =
        Polynomial.C (algebraMap R K (d : R)) * P i := by
  let M : Submonoid R := nonZeroDivisors R
  letI : Algebra (Polynomial R) (Polynomial K) := Polynomial.algebra R K
  haveI : IsLocalization (M.map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization M K
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (M.map Polynomial.C) P
  rcases b.2 with ⟨d, hdM, hdb⟩
  let Q : ι → Polynomial R := fun i ↦ Classical.choose (hb i)
  have hQ (i : ι) :
      algebraMap (Polynomial R) (Polynomial K) (Q i) =
        (b : Polynomial R) • P i := Classical.choose_spec (hb i)
  refine ⟨⟨d, hdM⟩, Q, fun i ↦ ?_⟩
  rw [Polynomial.algebraMap_def] at hQ
  calc
    Polynomial.map (algebraMap R K) (Q i) = (b : Polynomial R) • P i := hQ i
    _ = algebraMap (Polynomial R) (Polynomial K) (Polynomial.C d) * P i := by
      rw [Algebra.smul_def, hdb]
    _ = Polynomial.C (algebraMap R K d) * P i := by
      change Polynomial.map (algebraMap R K) (Polynomial.C d) * P i = _
      rw [Polynomial.map_C]

/-! ## Equation (78) -/

/-- Finite-family distinguished-variable Bezout with denominator clearing.

The hypothesis says exactly that the family has no common nonunit divisor in `R[X]`.  Over the
fraction field its gcd is therefore a unit.  Bezout over the PID `K[X]`, followed by one common
denominator clearing, produces a nonzero `N : R` which is independent of the distinguished
variable. -/
theorem exists_distinguishedVariable_bezout_clear
    {R K ι : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Fintype ι]
    (H : ι → Polynomial R)
    (hcommon : ∀ q : Polynomial R, (∀ i, q ∣ H i) → IsUnit q) :
    ∃ M : ι → Polynomial R, ∃ N : R, N ≠ 0 ∧
      ∑ i, M i * H i = Polynomial.C N := by
  classical
  letI : NormalizationMonoid R :=
    UniqueFactorizationMonoid.normalizationMonoid
  letI : NormalizedGCDMonoid R :=
    UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  let HK : ι → Polynomial K :=
    fun i ↦ Polynomial.map (algebraMap R K) (H i)
  let g : Polynomial K := Finset.univ.gcd HK
  have hsome : ∃ i, H i ≠ 0 := by
    by_contra h
    have hall : ∀ i, H i = 0 := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    have hzeroUnit : IsUnit (0 : Polynomial R) :=
      hcommon 0 (fun i ↦ by simp [hall i])
    exact hzeroUnit.ne_zero rfl
  have hg0 : g ≠ 0 := by
    rw [show g = Finset.univ.gcd HK by rfl, Finset.gcd_ne_zero_iff]
    obtain ⟨i, hi⟩ := hsome
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)).mpr hi
  obtain ⟨q, hq0, hqprimitive, a, hqmap⟩ :=
    exists_primitive_polynomial_fraction_clear (R := R) (K := K) hg0
  have hqdvd (i : ι) : q ∣ H i := by
    apply Polynomial.IsPrimitive.dvd_of_fraction_map_dvd
      (R := R) (K := K) (P := q) (Q := H i) hqprimitive hq0
    have hgdvd : g ∣ HK i := by
      exact Finset.gcd_dvd (Finset.mem_univ i)
    obtain ⟨T, hT⟩ := hgdvd
    refine ⟨Polynomial.C ((a⁻¹ : Kˣ) : K) * T, ?_⟩
    calc
      HK i = g * T := hT
      _ = (Polynomial.C (a : K) *
          Polynomial.C ((a⁻¹ : Kˣ) : K)) * (g * T) := by
        rw [← Polynomial.C_mul]
        simp
      _ = (Polynomial.C (a : K) * g) *
          (Polynomial.C ((a⁻¹ : Kˣ) : K) * T) := by ring
      _ = Polynomial.map (algebraMap R K) q *
          (Polynomial.C ((a⁻¹ : Kˣ) : K) * T) := by rw [hqmap]
  have hqUnit : IsUnit q := hcommon q hqdvd
  have hmapqUnit : IsUnit (Polynomial.map (algebraMap R K) q) :=
    IsUnit.map (Polynomial.mapRingHom (algebraMap R K)) hqUnit
  have hgUnit : IsUnit g := by
    rw [hqmap] at hmapqUnit
    exact isUnit_of_mul_isUnit_right hmapqUnit
  obtain ⟨b, hb⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset ι) HK
  rcases hgUnit with ⟨u, hu⟩
  let B : ι → Polynomial K :=
    fun i ↦ b i * ((u⁻¹ : (Polynomial K)ˣ) : Polynomial K)
  have hbezout : ∑ i, B i * HK i = 1 := by
    calc
      ∑ i, B i * HK i =
          (∑ i, HK i * b i) * ((u⁻¹ : (Polynomial K)ˣ) : Polynomial K) := by
        simp only [B]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = g * ((u⁻¹ : (Polynomial K)ˣ) : Polynomial K) := by rw [← hb]
      _ = 1 := by rw [← hu]; simp
  obtain ⟨d, M, hM⟩ :=
    exists_polynomial_family_fraction_clear (R := R) (K := K) B
  refine ⟨M, (d : R), nonZeroDivisors.ne_zero d.2, ?_⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  calc
    ∑ i, Polynomial.map (algebraMap R K) (M i) * HK i =
        ∑ i, (Polynomial.C (algebraMap R K (d : R)) * B i) * HK i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hM i]
    _ = Polynomial.C (algebraMap R K (d : R)) * (∑ i, B i * HK i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = Polynomial.C (algebraMap R K (d : R)) := by rw [hbezout, mul_one]

/-- Coefficient form of equation (78).  Primitivity of the outer polynomial says that its finite
coefficient family has no common nonunit divisor; the conclusion supplies the cleared Bezout
identity in any second distinguished variable. -/
theorem Polynomial.IsPrimitive.exists_coeff_bezout_clear
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {P : Polynomial (Polynomial R)} (hP : P.IsPrimitive) :
    ∃ M : Fin (P.natDegree + 1) → Polynomial R, ∃ N : R, N ≠ 0 ∧
      ∑ i, M i * P.coeff i = Polynomial.C N := by
  apply exists_distinguishedVariable_bezout_clear
    (K := FractionRing R) (fun i : Fin (P.natDegree + 1) ↦ P.coeff i)
  intro q hq
  apply hP q
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro n
  by_cases hn : n ≤ P.natDegree
  · exact hq ⟨n, Nat.lt_succ_iff.mpr hn⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn)]
    exact dvd_zero q

/-! ## Degree and support API -/

/-- A nonzero nonunit multivariable polynomial over a field contains a variable. -/
theorem mvPolynomial_vars_nonempty_of_ne_zero_of_not_isUnit
    {K σ : Type*} [Field K] {P : MvPolynomial σ K}
    (hP0 : P ≠ 0) (hP : ¬ IsUnit P) :
    P.vars.Nonempty := by
  classical
  by_contra hvars
  have hvars0 : P.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hvars
  have hC : P = MvPolynomial.C (P.coeff 0) :=
    MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars0
  have hc0 : P.coeff 0 ≠ 0 := by
    intro hc
    apply hP0
    rw [hC, hc, MvPolynomial.C_0]
  apply hP
  rw [hC]
  exact IsUnit.map MvPolynomial.C hc0.isUnit

/-- Divisibility in a multivariable polynomial domain cannot remove a variable from the divisor. -/
theorem mvPolynomial_vars_subset_of_dvd
    {R σ : Type*} [CommRing R] [NoZeroDivisors R]
    {P Q : MvPolynomial σ R} (hdiv : P ∣ Q) (hQ0 : Q ≠ 0) :
    P.vars ⊆ Q.vars := by
  classical
  obtain ⟨T, rfl⟩ := hdiv
  have hP0 : P ≠ 0 := by
    intro h
    exact hQ0 (by rw [h, zero_mul])
  have hT0 : T ≠ 0 := by
    intro h
    exact hQ0 (by rw [h, mul_zero])
  intro i hi
  rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hi ⊢
  rw [MvPolynomial.degreeOf_mul_eq hP0 hT0]
  intro hzero
  have hleft : MvPolynomial.degreeOf i P = 0 := by omega
  exact hi hleft

/-! ## Scalar-extension factors retain every original variable -/

/-- Every irreducible factor after an extension of coefficient fields contains every variable of
the original irreducible polynomial.  This is the factor-support form of Ritt's equation (78). -/
theorem irreducible_map_factor_vars_subset
    {F K σ : Type*} [Field F] [Field K] [Algebra F K]
    {P : MvPolynomial σ F} {A : MvPolynomial σ K}
    (hP : Irreducible P) (hA : Irreducible A)
    (hdiv : A ∣ MvPolynomial.map (algebraMap F K) P) :
    P.vars ⊆ A.vars := by
  classical
  intro x hx
  by_contra hxA
  have hxA' : x ∉ A.vars := hxA
  obtain ⟨A₀, hA₀⟩ :=
    MvPolynomial.exists_rename_eq_of_vars_subset_range A
      (Subtype.val : {j : σ // j ≠ x} → σ) Subtype.val_injective (by
        intro j hj
        refine ⟨⟨j, ?_⟩, rfl⟩
        intro hjx
        subst j
        exact hxA' hj)
  have hA₀notUnit : ¬ IsUnit A₀ := by
    intro hunit
    apply hA.not_isUnit
    have hmapUnit : IsUnit
        (MvPolynomial.rename (R := K) (Subtype.val : {j : σ // j ≠ x} → σ) A₀) :=
      IsUnit.map (MvPolynomial.rename (R := K) Subtype.val) hunit
    simpa [hA₀] using hmapUnit
  have hA₀zero : A₀ ≠ 0 := by
    intro hzero
    apply hA.ne_zero
    rw [← hA₀, hzero, map_zero]
  obtain ⟨y, hy⟩ :=
    mvPolynomial_vars_nonempty_of_ne_zero_of_not_isUnit hA₀zero hA₀notUnit

  let eF : MvPolynomial σ F ≃ₐ[F]
      Polynomial (MvPolynomial {j : σ // j ≠ x} F) :=
    mvPolynomialPolynomialEquivAt x
  let eK : MvPolynomial σ K ≃ₐ[K]
      Polynomial (MvPolynomial {j : σ // j ≠ x} K) :=
    mvPolynomialPolynomialEquivAt x
  let P₁ : Polynomial (MvPolynomial {j : σ // j ≠ x} F) := eF P
  let eFy : MvPolynomial {j : σ // j ≠ x} F ≃ₐ[F]
      Polynomial (MvPolynomial {z : {j : σ // j ≠ x} // z ≠ y} F) :=
    mvPolynomialPolynomialEquivAt y
  let eKy : MvPolynomial {j : σ // j ≠ x} K ≃ₐ[K]
      Polynomial (MvPolynomial {z : {j : σ // j ≠ x} // z ≠ y} K) :=
    mvPolynomialPolynomialEquivAt y
  let P₂ : Polynomial
      (Polynomial (MvPolynomial {z : {j : σ // j ≠ x} // z ≠ y} F)) :=
    Polynomial.mapAlgEquiv eFy P₁
  let B : Polynomial (MvPolynomial {z : {j : σ // j ≠ x} // z ≠ y} K) :=
    eKy A₀

  have hP₁irreducible : Irreducible P₁ := by
    exact hP.map eF
  have hxdegree : MvPolynomial.degreeOf x P ≠ 0 :=
    MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hx
  have hP₁degreeEq : MvPolynomial.degreeOf x P = P₁.natDegree := by
    calc
      MvPolynomial.degreeOf x P =
          (mvPolynomialAsPolynomialAt x P).natDegree :=
        mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt x P
      _ = (eF P).natDegree := by
        exact congrArg Polynomial.natDegree
          (mvPolynomialPolynomialEquivAt_apply x P).symm
      _ = P₁.natDegree := rfl
  have hP₁degree : P₁.natDegree ≠ 0 := by
    intro hzero
    exact hxdegree (hP₁degreeEq.trans hzero)
  have hP₂irreducible : Irreducible P₂ := by
    exact hP₁irreducible.map (Polynomial.mapAlgEquiv eFy)
  have hP₂degreeEq : P₂.natDegree = P₁.natDegree := by
    dsimp [P₂]
    exact Polynomial.natDegree_map_eq_of_injective eFy.injective P₁
  have hP₂degree : P₂.natDegree ≠ 0 := by
    intro hzero
    apply hP₁degree
    rw [← hP₂degreeEq, hzero]
  have hP₂primitive : P₂.IsPrimitive :=
    hP₂irreducible.isPrimitive hP₂degree

  have hdiv₁ : Polynomial.C A₀ ∣
      Polynomial.map (MvPolynomial.map (algebraMap F K)) P₁ := by
    have hmapped := map_dvd eK hdiv
    have hleft : eK A = Polynomial.C A₀ := by
      rw [← hA₀]
      exact mvPolynomialPolynomialEquivAt_rename_ne x A₀
    have hright :
        eK (MvPolynomial.map (algebraMap F K) P) =
          Polynomial.map (MvPolynomial.map (algebraMap F K)) P₁ := by
      dsimp [P₁, eF, eK]
      exact mvPolynomialPolynomialEquivAt_map (algebraMap F K) x P
    rw [hleft, hright] at hmapped
    exact hmapped
  have hcoeff (n : ℕ) :
      A₀ ∣ MvPolynomial.map (algebraMap F K) (P₁.coeff n) := by
    have hn := (Polynomial.C_dvd_iff_dvd_coeff A₀ _).mp hdiv₁ n
    simpa using hn

  obtain ⟨M, N, hN0, hbezout⟩ :=
    Polynomial.IsPrimitive.exists_coeff_bezout_clear hP₂primitive
  have hBcoeff (n : ℕ) :
      B ∣ Polynomial.map (MvPolynomial.map (algebraMap F K)) (P₂.coeff n) := by
    have hn := map_dvd eKy (hcoeff n)
    have hmap := mvPolynomialPolynomialEquivAt_map
      (algebraMap F K) y (P₁.coeff n)
    dsimp [B] at hn
    rw [hmap] at hn
    dsimp [B, P₂]
    simpa using hn

  let ψ : MvPolynomial {z : {j : σ // j ≠ x} // z ≠ y} F →+*
      MvPolynomial {z : {j : σ // j ≠ x} // z ≠ y} K :=
    MvPolynomial.map (algebraMap F K)
  have hψinj : Function.Injective ψ := by
    exact MvPolynomial.map_injective (algebraMap F K)
      (FaithfulSMul.algebraMap_injective F K)
  have hNmap0 : ψ N ≠ 0 := by
    intro hzero
    apply hN0
    apply hψinj
    simpa using hzero
  have hmapBezout := congrArg (Polynomial.map ψ) hbezout
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C] at hmapBezout
  have hBsum : B ∣
      ∑ i, Polynomial.map ψ (M i) * Polynomial.map ψ (P₂.coeff i) := by
    apply Finset.dvd_sum
    intro i _
    exact dvd_mul_of_dvd_right (hBcoeff i) _
  have hBC : B ∣ Polynomial.C (ψ N) := by
    rw [hmapBezout] at hBsum
    exact hBsum

  have hydegree : MvPolynomial.degreeOf y A₀ ≠ 0 :=
    MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hy
  have hdegreeEq : MvPolynomial.degreeOf y A₀ = B.natDegree := by
    calc
      MvPolynomial.degreeOf y A₀ =
          (mvPolynomialAsPolynomialAt y A₀).natDegree :=
        mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt y A₀
      _ = (eKy A₀).natDegree := by
        exact congrArg Polynomial.natDegree
          (mvPolynomialPolynomialEquivAt_apply y A₀).symm
      _ = B.natDegree := rfl
  have hBdegree : B.natDegree ≠ 0 := by
    intro hzero
    apply hydegree
    rw [hdegreeEq, hzero]
  have hBle : B.natDegree ≤ (Polynomial.C (ψ N)).natDegree :=
    Polynomial.natDegree_le_of_dvd hBC (Polynomial.C_ne_zero.mpr hNmap0)
  apply hBdegree
  exact Nat.eq_zero_of_le_zero (by simpa using hBle)

/-- An irreducible factor after scalar extension has exactly the same variable set as the original
irreducible polynomial. -/
theorem irreducible_map_factor_vars_eq
    {F K σ : Type*} [Field F] [Field K] [Algebra F K]
    {P : MvPolynomial σ F} {A : MvPolynomial σ K}
    (hP : Irreducible P) (hA : Irreducible A)
    (hdiv : A ∣ MvPolynomial.map (algebraMap F K) P) :
    A.vars = P.vars := by
  apply Finset.Subset.antisymm
  · have hmapP0 : MvPolynomial.map (algebraMap F K) P ≠ 0 := by
      simpa using ((MvPolynomial.map_injective (algebraMap F K)
        (FaithfulSMul.algebraMap_injective F K)).ne hP.ne_zero)
    have hsubset := mvPolynomial_vars_subset_of_dvd hdiv hmapP0
    simpa [MvPolynomial.vars_map_of_injective
      P (FaithfulSMul.algebraMap_injective F K)] using hsubset
  · exact irreducible_map_factor_vars_subset hP hA hdiv

end

end GaloisForLFunctions
