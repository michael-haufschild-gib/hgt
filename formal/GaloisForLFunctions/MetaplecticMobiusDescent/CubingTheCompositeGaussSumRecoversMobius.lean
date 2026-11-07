/-
The ideal Möbius product proof is adapted from OpenAI’s formalization, Apache-2.0.
See LICENSE and NOTICE in this directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.ThePrimaryCubicGaussSumFixesTheSign
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Pi

/-!
# Cubing a composite Gauss sum recovers the Möbius sign

Chinese remaindering identifies the quotient by a product of distinct prime
ideals with the product of their residue fields. Every primitive additive
character restricts to a primitive character on each factor. The composite
cubic Gauss sum therefore factors into local Gauss sums, each with cube
`−p · #F`. After normalization, their product has cube `mu(I) · p/|p|`.

This proof works for every primitive additive character on the quotient; no
choice of local additive phases is needed. A definite primitive character is
also constructed, giving an endpoint with no character-existence premise.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent
namespace ProductGauss
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]

/-- Restrict an additive character to one coordinate of a product ring. -/
def localChar (ψ : AddChar (∀ i, F i) ℂ) (i : ι) : AddChar (F i) ℂ where
  toFun x := ψ (Pi.single i x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [Pi.single_add]
    exact ψ.map_add_eq_mul _ _

omit [∀ i, Fintype (F i)] in
/-- An additive character factors over the coordinate decomposition. -/
theorem character_eq_prod (ψ : AddChar (∀ i, F i) ℂ) (x : ∀ i, F i) :
    ψ x = ∏ i, localChar F ψ i (x i) := by
  have hs (s : Finset ι) :
      ψ (∑ i ∈ s, Pi.single i (x i)) = ∏ i ∈ s, localChar F ψ i (x i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, ψ.map_add_eq_mul, ih]
      rfl
  have hx : (∑ i, Pi.single i (x i)) = x := by
    ext i
    simp
  simpa only [hx] using hs Finset.univ

omit [Fintype ι] [∀ i, Fintype (F i)] in
/-- Primitivity on the product forces primitivity on every factor. -/
theorem localChar_primitive (ψ : AddChar (∀ i, F i) ℂ) (hψ : ψ.IsPrimitive)
    (i : ι) : (localChar F ψ i).IsPrimitive := by
  intro a ha h
  have hsingle : Pi.single i a ≠ (0 : ∀ i, F i) := by
    intro hz
    exact ha (by simpa using congrFun hz i)
  apply hψ hsingle
  ext x
  have hm : Pi.single i a * x = Pi.single i (a * x i) := by
    ext j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Pi.single_eq_of_ne (Ne.symm hij)]
  have hv := congrArg (fun η : AddChar (F i) ℂ => η (x i)) h
  change ψ (Pi.single i (a * x i)) = 1 at hv
  change ψ (Pi.single i a * x) = 1
  rw [hm]
  exact hv

/-- A finite Gauss sum on a product ring factors into its local Gauss sums. -/
theorem factorization (χ : ∀ i, MulChar (F i) ℂ)
    (ψ : AddChar (∀ i, F i) ℂ) :
    (∑ x : ∀ i, F i, (∏ i, χ i (x i)) * ψ x) =
      ∏ i, gaussSum (χ i) (localChar F ψ i) := by
  simp_rw [character_eq_prod F ψ, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => χ i x * localChar F ψ i x)).symm

omit [Fintype ι] [∀ i, Fintype (F i)] in
/-- Primitive coordinate restrictions detect every nonzero multiplicative shift. -/
theorem primitive_of_localChar (ψ : AddChar (∀ i, F i) ℂ)
    (hψ : ∀ i, (localChar F ψ i).IsPrimitive) : ψ.IsPrimitive := by
  intro a ha hz
  have hn : ¬ ∀ i, a i = 0 := by
    intro h
    exact ha (funext h)
  obtain ⟨i, hi⟩ := not_forall.mp hn
  apply hψ i hi
  ext x
  have h := congrArg (fun η : AddChar (∀ i, F i) ℂ => η (Pi.single i x)) hz
  change ψ (a * Pi.single i x) = 1 at h
  have hm : a * Pi.single i x = Pi.single i (a i * x) := by
    ext j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Pi.single_eq_of_ne (Ne.symm hij)]
  change ψ (Pi.single i (a i * x)) = 1
  rw [← hm]
  exact h

/-- The product of the coordinate additive characters. -/
def productChar (ψ : ∀ i, AddChar (F i) ℂ) : AddChar (∀ i, F i) ℂ where
  toFun x := ∏ i, ψ i (x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

omit [∀ i, Fintype (F i)] in
/-- Restricting the product character recovers the chosen local character. -/
theorem localChar_productChar (ψ : ∀ i, AddChar (F i) ℂ) (i : ι) :
    localChar F (productChar F ψ) i = ψ i := by
  ext x
  change (∏ j, ψ j (Pi.single i x j)) = ψ i x
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

omit [∀ i, Fintype (F i)] in
/-- A product of primitive local characters is primitive. -/
theorem productChar_primitive (ψ : ∀ i, AddChar (F i) ℂ)
    (hψ : ∀ i, (ψ i).IsPrimitive) : (productChar F ψ).IsPrimitive := by
  apply primitive_of_localChar F
  intro i
  rw [localChar_productChar]
  exact hψ i

section Transport
variable {R : Type*} [CommRing R]

/-- Primitivity is preserved by a ring isomorphism. -/
theorem primitive_comp_ringEquiv {S : Type*} [CommRing S] (e : S ≃+* R)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom e.toAddMonoidHom).IsPrimitive := by
  intro a ha hz
  apply hψ (by simpa only [map_zero] using e.injective.ne ha)
  ext y
  have h := congrArg (fun η : AddChar S ℂ => η (e.symm y)) hz
  change ψ (e (a * e.symm y)) = 1 at h
  change ψ (e a * y) = 1
  simpa only [map_mul, e.apply_symm_apply] using h

/-- Gauss factorization transported through a ring isomorphism. -/
theorem factorization_equiv [Fintype R] (e : R ≃+* (∀ i, F i))
    (χ : ∀ i, MulChar (F i) ℂ) (ψ : AddChar R ℂ) :
    (∑ x : R, (∏ i, χ i (e x i)) * ψ x) =
      ∏ i, gaussSum (χ i)
        (localChar F (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i) := by
  calc
    _ = ∑ y : ∀ i, F i, (∏ i, χ i (y i)) *
        (ψ.compAddMonoidHom e.symm.toAddMonoidHom) y := by
      apply Fintype.sum_equiv e.toEquiv
      intro x
      change (∏ i, χ i (e x i)) * ψ x =
        (∏ i, χ i (e x i)) * ψ (e.symm (e x))
      rw [e.symm_apply_apply]
    _ = _ := factorization F χ _

end Transport

end ProductGauss
namespace Eisenstein
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (P : ι → Ideal O) [∀ i, (P i).IsMaximal]

/-- Chinese remaindering for a finite family of distinct Eisenstein prime ideals. -/
def primeCRT (hinj : Function.Injective P) :
    (O ⧸ ∏ i, P i) ≃+* (∀ i, O ⧸ P i) := by
  have hcop : Pairwise (Function.onFun IsCoprime P) :=
    fun _ _ hij => Ideal.isCoprime_of_isMaximal (hinj.ne hij)
  have hprod : (∏ i, P i) = ⨅ i, P i := by
    simpa only [Finset.mem_univ, iInf_true] using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := Finset.univ) (fun i _ j _ hij => hcop hij))
  exact (Ideal.quotEquivOfEq hprod).trans
    (Ideal.quotientInfRingEquivPiQuotient P hcop)

/-- The ideal Möbius function records the number of distinct prime factors. -/
theorem primeProduct_moebius (hinj : Function.Injective P) :
    (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) =
      (-1 : ℂ) ^ Fintype.card ι := by
  have hs (S : Finset ι) :
      (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
        (-1 : ℂ) ^ S.card := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one,
        Int.cast_one, Finset.card_empty, pow_zero]
    | @insert i S hi ih =>
      have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
        apply IsCoprime.prod_right
        intro j hj
        exact Ideal.isCoprime_of_isMaximal (hinj.ne (by
          intro h; subst j; exact hi hj))
      have hprime : Prime (P i) :=
        Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
      rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
        hprime.irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
        Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
      ring
  simpa only [Finset.card_univ] using hs Finset.univ

/-- The actual cubic residue sum on the quotient by the product ideal, normalized by the primary generator’s norm. -/
def compositeCubicGauss (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) : ℂ := by
  classical
  let e := primeCRT P hinj
  letI : Fintype (O ⧸ ∏ i, P i) :=
    Fintype.ofEquiv (∀ i, O ⧸ P i) e.symm.toEquiv
  exact (∑ x : O ⧸ ∏ i, P i,
    (∏ i, ringComplex (cubicChar (P i) (hgood i) (e x i))) * ψ x) /
    (‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ)

/-- The normalized composite residue sum is the product of the normalized local sums. -/
theorem compositeCubicGauss_factorization (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) :
    compositeCubicGauss P hinj hgood ψ =
      ∏ i, gaussSum ((cubicChar (P i) (hgood i)).ringHomComp ringComplex)
        (ProductGauss.localChar (fun i => O ⧸ P i)
          (ψ.compAddMonoidHom (primeCRT P hinj).symm.toAddMonoidHom) i) /
            (‖ringComplex (primaryGenerator (P i) (hgood i))‖ : ℂ) := by
  classical
  let e := primeCRT P hinj
  letI : Fintype (O ⧸ ∏ i, P i) :=
    Fintype.ofEquiv (∀ i, O ⧸ P i) e.symm.toEquiv
  have hsum := ProductGauss.factorization_equiv (fun i => O ⧸ P i) e
    (fun i => (cubicChar (P i) (hgood i)).ringHomComp ringComplex) ψ
  change (∑ x : O ⧸ ∏ i, P i,
    (∏ i, ringComplex (cubicChar (P i) (hgood i) (e x i))) * ψ x) / _ = _
  change (∑ x : O ⧸ ∏ i, P i,
    (∏ i, ringComplex (cubicChar (P i) (hgood i) (e x i))) * ψ x) = _ at hsum
  rw [hsum, Finset.prod_div_distrib, map_prod, norm_prod, Complex.ofReal_prod]

/-- For every primitive additive character, the cubed Gauss sum is the ideal Möbius sign times the primary angular part. -/
theorem compositeCubicGauss_cube (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (ψ : AddChar (O ⧸ ∏ i, P i) ℂ)
    (hψ : ψ.IsPrimitive) :
    compositeCubicGauss P hinj hgood ψ ^ 3 =
      (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
        (ringComplex (∏ i, primaryGenerator (P i) (hgood i)) /
          (‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ)) := by
  let η := ψ.compAddMonoidHom (primeCRT P hinj).symm.toAddMonoidHom
  have hη : η.IsPrimitive :=
    ProductGauss.primitive_comp_ringEquiv _ ψ hψ
  have hlocal (i : ι) :
      (gaussSum ((cubicChar (P i) (hgood i)).ringHomComp ringComplex)
        (ProductGauss.localChar (fun i => O ⧸ P i) η i) /
          (‖ringComplex (primaryGenerator (P i) (hgood i))‖ : ℂ)) ^ 3 =
      -(ringComplex (primaryGenerator (P i) (hgood i)) /
          (‖ringComplex (primaryGenerator (P i) (hgood i))‖ : ℂ)) := by
    simpa only [neg_div] using cubicGauss_normalized_cube (P i) (hgood i)
      (primaryGenerator (P i) (hgood i)) (primaryGenerator_spec (P i) (hgood i)).1
      (primaryGenerator_spec (P i) (hgood i)).2 _
      (ProductGauss.localChar_primitive (fun i => O ⧸ P i) η hη i)
  rw [compositeCubicGauss_factorization, ← Finset.prod_pow]
  trans ∏ i, -(ringComplex (primaryGenerator (P i) (hgood i)) /
    (‖ringComplex (primaryGenerator (P i) (hgood i))‖ : ℂ))
  · exact Finset.prod_congr rfl fun i _ => hlocal i
  · rw [Finset.prod_neg, primeProduct_moebius P hinj, Finset.card_univ,
      Finset.prod_div_distrib, map_prod, norm_prod, Complex.ofReal_prod]

/-- A definite primitive additive character on the composite residue ring,
obtained by transporting the product of the local primitive characters. -/
def canonicalProductAddChar (hinj : Function.Injective P) :
    AddChar (O ⧸ ∏ i, P i) ℂ :=
  (ProductGauss.productChar (fun i => O ⧸ P i)
    (fun i => AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P i))).compAddMonoidHom
      (primeCRT P hinj).toAddMonoidHom

/-- The constructed composite character is primitive. -/
theorem canonicalProductAddChar_primitive (hinj : Function.Injective P) :
    (canonicalProductAddChar P hinj).IsPrimitive :=
  ProductGauss.primitive_comp_ringEquiv (primeCRT P hinj) _
    (ProductGauss.productChar_primitive (fun i => O ⧸ P i) _
      (fun i => AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (O ⧸ P i)))

/-- The normalized Gauss sum for a definite primitive additive character on
the quotient by the product ideal. -/
def normalizedCompositeCubicGauss (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) : ℂ :=
  compositeCubicGauss P hinj hgood (canonicalProductAddChar P hinj)

/-- Cubing the actual composite residue sum recovers the ideal Möbius sign
and the angular part of the primary generator. -/
theorem normalizedCompositeCubicGauss_cube (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) :
    normalizedCompositeCubicGauss P hinj hgood ^ 3 =
      (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
        (ringComplex (∏ i, primaryGenerator (P i) (hgood i)) /
          (‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ)) :=
  compositeCubicGauss_cube P hinj hgood _ (canonicalProductAddChar_primitive P hinj)

end Eisenstein
end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.ProductGauss.localChar_primitive
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.ProductGauss.factorization_equiv
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.primeProduct_moebius
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.compositeCubicGauss_cube
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.canonicalProductAddChar_primitive
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.normalizedCompositeCubicGauss_cube
