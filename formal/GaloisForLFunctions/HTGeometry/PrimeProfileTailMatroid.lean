import GaloisForLFunctions.HTGeometry.PrimeClockProfileOrbit
import GaloisForLFunctions.HTGeometry.PrimeProfileDynamicCoefficientField

/-!
# The finite-prime tail matroid for arbitrary prime-power profiles

This file supplies the converse, order-zero side of the arbitrary profile classification.  A
finite-prime-ray arithmetic profile belongs to the intrinsic finite-prime coefficient field, and
algebraic independence over that field therefore forces linear independence modulo finite prime
rays.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Polynomial

noncomputable section

/-- If a positive-prime-power profile vanishes on one complete prime ray, the corresponding prime
derivation vanishes identically. -/
theorem primeDeriv_eq_zero_of_primePowerProfile_ray_zero
    (f : ArithmeticFunction ℂ)
    (hsupport : PrimeProfileSupportedOnPositivePrimePowers f)
    (p : Nat.Primes) (hzero : ∀ e : Nat, f ((p : Nat) ^ (e + 1)) = 0) :
    primeDeriv p.1 f = 0 := by
  ext n
  rw [primeDeriv_apply, ArithmeticFunction.zero_apply]
  by_cases hvalue : f (n * p) = 0
  · rw [hvalue, mul_zero]
  · obtain ⟨q, e, hpow⟩ := hsupport hvalue
    have hpdiv : (p : Nat) ∣ (q : Nat) ^ (e + 1) := by
      rw [← hpow]
      exact ⟨n, by rw [Nat.mul_comm]⟩
    have hpq : p = q := by
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow p.2 q.2 hpdiv
    subst q
    have hz := hzero e
    rw [← hpow] at hz
    exact (hvalue hz).elim

/-- Prime derivation reads every positive valuation coordinate with the nonzero multiplicity
factor `e+1`. -/
theorem primeDeriv_apply_primePowerCoordinate
    (f : ArithmeticFunction ℂ) (p : Nat.Primes) (e : Nat) :
    primeDeriv p.1 f ((p : Nat) ^ e) =
      ((e + 1 : Nat) : ℂ) * f ((p : Nat) ^ (e + 1)) := by
  rw [primeDeriv_apply]
  have hfac : ((p : Nat) ^ e * (p : Nat)).factorization (p : Nat) = e + 1 := by
    rw [← pow_succ, Nat.factorization_pow_self p.2]
  rw [hfac, ← pow_succ]

/-- The active rays of a profile and of its prime-derivative readout coincide exactly. -/
theorem primeDeriv_rayActivity_eq (f : ArithmeticFunction ℂ) :
    {p : Nat.Primes |
      ∃ e : Nat, primeDeriv p.1 f ((p : Nat) ^ e) ≠ 0} =
    {p : Nat.Primes | ∃ e : Nat, f ((p : Nat) ^ (e + 1)) ≠ 0} := by
  ext p
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro hz
    apply he
    rw [primeDeriv_apply_primePowerCoordinate, hz, mul_zero]
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [primeDeriv_apply_primePowerCoordinate]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero e)) he

/-- Prime derivation commutes with finite profile linear combinations. -/
theorem primeDeriv_profileLinearCombination
    {I : Type*} [Fintype I]
    (p : Nat.Primes) (g : I -> ArithmeticFunction ℂ) (c : I -> ℂ) :
    primeDeriv p.1 (∑ i, c i • g i) =
      ∑ i, c i • primeDeriv p.1 (g i) := by
  change primeArithmeticDerivation p.1 p.2 (∑ i, c i • g i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (primeArithmeticDerivation p.1 p.2).map_smul (c i) (g i)

/-- Prime activity of a supported arithmetic profile is contained in its literal active-ray
set. -/
theorem finitePrimeActivity_algebraMap_primeProfile_subset
    (f : ArithmeticFunction ℂ)
    (hsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    finitePrimeActivity
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) ⊆
      {p : Nat.Primes | ∃ e : Nat, f ((p : Nat) ^ (e + 1)) ≠ 0} := by
  intro p hp
  by_contra hray
  have hzero : ∀ e : Nat, f ((p : Nat) ^ (e + 1)) = 0 := by
    intro e
    by_contra he
    exact hray ⟨e, he⟩
  apply hp
  rw [primeFractionDerivation_algebraMap,
    primeDeriv_eq_zero_of_primePowerProfile_ray_zero f hsupport p hzero]
  simp

/-- Every arbitrary profile carried by finitely many prime rays belongs to the intrinsic local
coefficient field; no finite valuation-depth hypothesis is needed. -/
theorem algebraMap_primeProfile_mem_finitePrimeCoefficientField_of_local
    (f : ArithmeticFunction ℂ)
    (hsupport : PrimeProfileSupportedOnPositivePrimePowers f)
    (hlocal : PrimePowerClockLocal (primePowerCoordinateProfile f)) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
      finitePrimeCoefficientField := by
  rw [mem_finitePrimeCoefficientField_iff]
  have hrays :
      {p : Nat.Primes | ∃ e : Nat, f ((p : Nat) ^ (e + 1)) ≠ 0}.Finite :=
    (primePowerClockLocal_coordinateProfile_iff f).mp hlocal
  exact hrays.subset
    (finitePrimeActivity_algebraMap_primeProfile_subset f hsupport)

/-- A finite complex linear combination of positive-prime-power profiles remains supported on
positive prime powers. -/
theorem primeProfileLinearCombination_supported
    {I : Type*} [Fintype I]
    (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (c : I -> ℂ) :
    PrimeProfileSupportedOnPositivePrimePowers (∑ i, c i • g i) := by
  classical
  intro n hn
  by_contra hnone
  have hzero : ∀ i, g i n = 0 := by
    intro i
    by_contra hi
    exact hnone (hsupport i hi)
  apply hn
  have hsum : ∀ s : Finset I, (∑ i ∈ s, c i • g i) n = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, ArithmeticFunction.add_apply,
          ArithmeticFunction.smul_map, hzero a, smul_zero, ih, zero_add]
  exact hsum Finset.univ

/-- Linear independence of a finite profile family modulo finite prime rays. -/
def PrimeProfileTailIndependent
    {I : Type*} [Fintype I] (g : I -> ArithmeticFunction ℂ) : Prop :=
  ∀ c : I -> ℂ,
    PrimePowerClockLocal
      (primePowerCoordinateProfile (∑ i, c i • g i)) -> c = 0

/-- **Static converse for arbitrary profiles.**  Algebraic independence over the intrinsic
finite-prime coefficient field forces independence modulo finite prime rays. -/
theorem primeProfileTailIndependent_of_algebraicIndependent
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (hAI : AlgebraicIndependent finitePrimeCoefficientField
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g i))) :
    PrimeProfileTailIndependent g := by
  intro c hlocal
  let x : I -> arithmeticFunctionFractionField := fun i =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g i)
  let f : ArithmeticFunction ℂ := ∑ i, c i • g i
  let r : arithmeticFunctionFractionField :=
    ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i
  have hsupportf : PrimeProfileSupportedOnPositivePrimePowers f :=
    primeProfileLinearCombination_supported g hsupport c
  have hr_eq : r =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f := by
    simp only [r, f, x, map_sum, Algebra.smul_def, map_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField]
  have hrmem : r ∈ finitePrimeCoefficientField := by
    rw [hr_eq]
    exact algebraMap_primeProfile_mem_finitePrimeCoefficientField_of_local
      f hsupportf hlocal
  by_contra hc
  have hc' : c ≠ 0 := hc
  let k : finitePrimeCoefficientField := ⟨r, hrmem⟩
  let P : MvPolynomial I finitePrimeCoefficientField :=
    MvPolynomial.C (-k) +
      ∑ i, MvPolynomial.C
          (algebraMap ℂ finitePrimeCoefficientField (c i)) * MvPolynomial.X i
  have hPeval : MvPolynomial.aeval x P = 0 := by
    simp only [P, map_add, map_neg, MvPolynomial.aeval_C, map_sum, map_mul,
      MvPolynomial.aeval_X]
    change -(k : arithmeticFunctionFractionField) +
      ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i = 0
    change -r + ∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i = 0
    rw [show (∑ i, algebraMap ℂ arithmeticFunctionFractionField (c i) * x i) = r
      from rfl]
    exact neg_add_cancel r
  have hc_exists : ∃ i, c i ≠ 0 := by
    simpa only [Pi.zero_apply] using (Function.ne_iff.mp hc')
  obtain ⟨i, hi⟩ := hc_exists
  have hPne : P ≠ 0 := by
    intro hzero
    have hmon : (0 : Finsupp I Nat) ≠ Finsupp.single i 1 := by
      exact Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    have hcoeff : algebraMap ℂ finitePrimeCoefficientField (c i) = 0 := by
      have hcoeff' := congrArg
        (fun Q : MvPolynomial I finitePrimeCoefficientField =>
          Q.coeff (Finsupp.single i 1)) hzero
      simpa [P, MvPolynomial.coeff_add, MvPolynomial.coeff_C,
        MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_X', Finsupp.single_eq_single_iff, hmon] using hcoeff'
    apply hi
    apply FaithfulSMul.algebraMap_injective ℂ finitePrimeCoefficientField
    simpa using hcoeff
  exact hPne (hAI.eq_zero_of_aeval_eq_zero P hPeval)

/-- The already-formalized cofinite packet theorem supplies the forward static implication. -/
theorem algebraicIndependent_of_cofinitePrimeProfileJetPacket_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (hpacket : CofinitePrimeProfileJetPacket g) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g i)) := by
  let e : I -> I × Fin 1 := fun i => (i, 0)
  have he : Function.Injective e := by
    intro i j hij
    exact congrArg Prod.fst hij
  have hrect :=
    algebraicIndependent_fractionPrimeProfileJets_over_finitePrimeCoefficientField
      g hsupport hpacket 0
  have hsub := hrect.comp e he
  simpa [e, primeProfileJetSource, primeProfileRotatedLogJet] using hsub

/-- Cofinite separated packets imply the expected linear independence in the finite-prime-ray
quotient. -/
theorem primeProfileTailIndependent_of_cofinitePrimeProfileJetPacket
    {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> ArithmeticFunction ℂ)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i))
    (hpacket : CofinitePrimeProfileJetPacket g) :
    PrimeProfileTailIndependent g := by
  exact primeProfileTailIndependent_of_algebraicIndependent g hsupport
    (algebraicIndependent_of_cofinitePrimeProfileJetPacket_zero
      g hsupport hpacket)

end

end GaloisForLFunctions.HTGeometry
